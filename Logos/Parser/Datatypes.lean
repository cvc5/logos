module

public import Logos.Parser.Core
import all Logos.Parser.Core

public section

/-!
Shared elaboration of datatypes and uninterpreted sort constructors. A generated parser supplies the
views and constructors of its term representation through `DatatypeTerms`.
-/

namespace Logos.Parser

variable {T N R C CL : Type} [BEq T] [BEq N] [Inhabited T]

private def mapFields (f : T → T) (dd : DatatypeBlock T N) : DatatypeBlock T N :=
  dd.map fun (s, d) => (s, d.map (List.map f))

private def paramName (repr : DatatypeTerms T) (k : Nat) : repr.Name :=
  repr.name ("@p" ++ toString k)

-- Keep source datatype names out of the generated `.par_` namespace. Doubling
-- the first dot is injective, including for names already starting with `..`.
private def sourceName (repr : DatatypeTerms T) (s : String) : repr.Name :=
  repr.name (if s.startsWith "." then "." ++ s else s)

private partial def appSpine [Inhabited T] (repr : DatatypeTerms T) :
    DatatypeTermView T repr.Name → List T → T × List T
  | .apply f a, args => appSpine repr (repr.view f) (a :: args)
  | f, args => (repr.build f, args)

private partial def subst (repr : DatatypeTerms T) (templates : List T)
    (p : repr.Name) (a : T) : DatatypeTermView T repr.Name → T
  | .ref q => if p == q then a else repr.build (.ref q)
  | .datatype s dd =>
      let t := repr.build (.datatype s dd)
      if templates.contains t then t
      else repr.build (.datatype s (mapFields (fun t => subst repr templates p a (repr.view t)) dd))
  | .apply t u => repr.build (.apply
      (subst repr templates p a (repr.view t)) (subst repr templates p a (repr.view u)))
  | .constructorType t u =>
      repr.build (.constructorType
        (subst repr templates p a (repr.view t)) (subst repr templates p a (repr.view u)))
  | t => repr.build t

-- Open arguments may use the same canonical parameter names as the template.
private def substs (repr : DatatypeTerms T) (templates : List T)
    (names : List repr.Name) (args : List T) (body : T) : T :=
  let fresh := names.zipIdx.map fun (_, i) => repr.name ("@inst" ++ toString i)
  let body := (names.zip fresh).foldl
    (fun t (p, q) => subst repr templates p (repr.build (.ref q)) (repr.view t)) body
  (fresh.zip args).foldl (fun t (p, a) => subst repr templates p a (repr.view t)) body

-- Rename references belonging to this block. Nested datatype declarations bind
-- their own references and must not be traversed.
private partial def renameRefs [Inhabited T] (repr : DatatypeTerms T) (renames : List (repr.Name × repr.Name)) :
    DatatypeTermView T repr.Name → T
  | .ref p => repr.build (.ref ((renames.find? (fun (q, _) => p == q)).map Prod.snd |>.getD p))
  | .apply f a => repr.build (.apply
      (renameRefs repr renames (repr.view f)) (renameRefs repr renames (repr.view a)))
  | .constructorType f a => repr.build (.constructorType
      (renameRefs repr renames (repr.view f)) (renameRefs repr renames (repr.view a)))
  | t => repr.build t

private def renameBlock (repr : DatatypeTerms T) (dd : DatatypeBlock T repr.Name)
    (names : List repr.Name) : DatatypeBlock T repr.Name :=
  let renames := (dd.map Prod.fst).zip names
  (dd.zip names).map fun ((_, d), name) =>
    (name, d.map (List.map (fun t => renameRefs repr renames (repr.view t))))

/--
What a generic form stands for: a sort, constructor or selector of a parametric
datatype, with the datatype's parameters, its template sort, and the source name
and arity of each datatype of its block; or a sort constructor of an arity.
-/
private inductive Generic (T N : Type) where
  | datatype : List N → T → List (String × Nat) → Generic T N
  | sort : Nat → Generic T N

/-- A term with a parser-local mapping from generic sorts and operators to
their parameter names and datatype templates. -/
private structure ElaboratedTerm (T N : Type) where
  value : T
  generics : List (T × Generic T N)

private abbrev TermElaborationM (T N : Type) := ElaborationM (ElaboratedTerm T N)

-- Recursive datatype references are closed within their declaration block.
private partial def closedType (repr : DatatypeTerms T) (bound : List repr.Name) :
    DatatypeTermView T repr.Name → Bool
  | .ref p => bound.contains p
  | .apply f a | .constructorType f a =>
      closedType repr bound (repr.view f) && closedType repr bound (repr.view a)
  | .datatype _ dd =>
      dd.all fun (_, d) => d.all fun c => c.all fun t =>
        closedType repr (dd.map (·.1) ++ bound) (repr.view t)
  | _ => true

/-- A block of parametric datatypes being instantiated by `instanceOf`. -/
private structure Template (T N : Type) where
  /-- The block, with its datatypes under their internal names. -/
  dd : DatatypeBlock T N
  /-- The source name and arity of each datatype of the block. -/
  info : List (String × Nat)
  /-- The template sorts of the proof, which substitution does not enter. -/
  templates : List T

/-- The template sort of the `k`-th datatype of `tpl`, applied to `args`. -/
private def Template.app [Inhabited T] (repr : DatatypeTerms T) (tpl : Template T repr.Name)
    (k : Nat) (args : List T) : T :=
  let sort := match tpl.dd[k]? with
    | some (name, _) => repr.build (.datatype name tpl.dd)
    | none => repr.stuck
  args.foldl (fun f a => repr.build (.apply f a)) sort

/-- The parameters of the `k`-th datatype of `tpl`, as its fields write them. -/
private def Template.params (repr : DatatypeTerms T) (tpl : Template T repr.Name) (k : Nat) :
    List repr.Name :=
  (List.range ((tpl.info[k]?.map (·.2)).getD 0)).map (paramName repr)

/--
The instances one call of `instanceOf` discovers, numbered in the order they are
found: each one's datatype position and arguments, its name, and the instances
its fields refer to.
-/
private structure Explore (T N : Type) where
  keys : Array (Nat × List T) := #[]
  names : Array N := #[]
  edges : Array (List Nat) := #[]

private abbrev ExploreM (T N : Type) := StateT (Explore T N) (TermElaborationM T N)

/-- A bound on the instances one instantiation may discover; `checkRegular` keeps it finite. -/
private def maxInstances : Nat := 10000

/-- The positions reachable from `i` along `edges`, including `i`. -/
private def reachable (edges : Array (List Nat)) (i : Nat) : List Nat :=
  go (edges.size + 1) [i] [i]
where
  go : Nat → List Nat → List Nat → List Nat
    | 0, _, seen => seen
    | fuel + 1, frontier, seen =>
      let next := (frontier.flatMap (edges.getD · [])).eraseDups.filter (!seen.contains ·)
      if next.isEmpty then seen else go fuel next (seen ++ next)

mutual
-- Open applications remain symbolic in datatype templates. Ground datatype
-- applications are instantiated by `instanceOf`, keyed by the template and *all*
-- arguments; ground uninterpreted applications get an ordinary sort from the
-- same table.
private partial def normalizeSort (repr : DatatypeTerms T) (cfg : Config T R C CL) :
    DatatypeTermView T repr.Name → TermElaborationM T repr.Name T
  | .apply f a => do
      let f ← normalizeSort repr cfg (repr.view f)
      let a ← normalizeSort repr cfg (repr.view a)
      let t := repr.build (.apply f a)
      let (head, args) := appSpine repr (repr.view t) []
      let state ← get
      if let some (_, ty) := state.instances.find? (fun (app, _) => app.value == t) then
        return ty.value
      if let some template := state.datatypes.find? (fun d => d.value == head) then
        if let [(_, .datatype params _ info)] := template.generics then
          if args.length == params.length && args.all (fun a =>
              closedType repr [] (repr.view a) && cfg.isType (repr.typeOf a)) then
            if let .datatype s dd := repr.view head then
              if let some j := dd.findIdx? (·.1 == s) then
                let tpl := { dd, info, templates := state.datatypes.map (·.value) }
                return ← instanceOf repr cfg tpl j args
      if let some (_, arity) := state.constructors.find? (fun (c, _) => c.value == head) then
        if args.length == arity && args.all (fun a =>
            closedType repr [] (repr.view a) && cfg.isType (repr.typeOf a)) then
          let ty := cfg.mkUSort (state.count + 1)
          modify fun s => { s with
            count := state.count + 1,
            instances := (⟨t, []⟩, ⟨ty, []⟩) :: s.instances }
          return ty
      return t
  | .datatype s dd => do
      let t := repr.build (.datatype s dd)
      if (← get).datatypes.any (fun d => d.value == t) then return t
      let dd ← dd.mapM fun (name, d) => do
        let d ← d.mapM fun c => c.mapM fun t => normalizeSort repr cfg (repr.view t)
        return (name, d)
      return repr.build (.datatype s dd)
  | .constructorType t u => do
      return repr.build (.constructorType
        (← normalizeSort repr cfg (repr.view t)) (← normalizeSort repr cfg (repr.view u)))
  | t => pure (repr.build t)

/--
What a field refers to with the `k`-th datatype of `tpl` applied to `args`: the
instance, if it was built before, and otherwise a reference to the instance
being discovered, which is numbered if it is new.  `src` is the instance whose
field this is.
-/
private partial def refInstance (repr : DatatypeTerms T) (cfg : Config T R C CL)
    (tpl : Template T repr.Name) (src : Option Nat) (k : Nat) (args : List T) :
    ExploreM T repr.Name T := do
  let args ← args.mapM fun a => StateT.lift (normalizeSort repr cfg (repr.view a))
  let app := tpl.app repr k args
  if let some (_, ty) := (← StateT.lift get).instances.find? (fun (a, _) => a.value == app) then
    return ty.value
  let idx ← match (← get).keys.findIdx? (· == (k, args)) with
    | some idx => pure idx
    | none => do
      let id ← StateT.lift (modifyGet fun s =>
        (s.datatypeInstanceCount + 1, { s with datatypeInstanceCount := s.datatypeInstanceCount + 1 }))
      let name := repr.name (s!".par_{id}_" ++ (tpl.info[k]?.map (·.1)).getD "")
      modifyGet fun ex => (ex.keys.size,
        { ex with keys := ex.keys.push (k, args), names := ex.names.push name, edges := ex.edges.push [] })
  if let some src := src then
    modify fun ex => { ex with edges := ex.edges.modify src (idx :: ·) }
  return repr.build (.ref ((← get).names.getD idx (repr.name "")))

/-- Replace each reference to a datatype of `tpl` in a field of instance `src` (`refInstance`). -/
private partial def replaceRefs (repr : DatatypeTerms T) (cfg : Config T R C CL)
    (tpl : Template T repr.Name) (src : Nat) (view : DatatypeTermView T repr.Name) :
    ExploreM T repr.Name T := do
  let (head, args) := appSpine repr view []
  if let .ref q := repr.view head then
    if let some k := tpl.dd.findIdx? (·.1 == q) then
      if args.length == (tpl.params repr k).length then
        return ← refInstance repr cfg tpl (some src) k args
  match view with
  | .apply f a => return repr.build (.apply
      (← replaceRefs repr cfg tpl src (repr.view f)) (← replaceRefs repr cfg tpl src (repr.view a)))
  | .constructorType f a => return repr.build (.constructorType
      (← replaceRefs repr cfg tpl src (repr.view f)) (← replaceRefs repr cfg tpl src (repr.view a)))
  | t => return repr.build t

/--
The instance of the `j`-th datatype of `tpl` at the ground sorts `args`.

The instances it needs are discovered first: instantiating the fields of one
instance names the instances of the block's datatypes they refer to, and so on
until no new one appears.  Those that refer to each other in a cycle are built
together as one declaration block, ordered by `productiveOrder`, and blocks are
built after the blocks they refer to, so every reference is either within its
block or to an already built type.  Every instance built is registered, so a
later application with the same template and arguments reuses it.
-/
private partial def instanceOf (repr : DatatypeTerms T) (cfg : Config T R C CL)
    (tpl : Template T repr.Name) (j : Nat) (args : List T) : TermElaborationM T repr.Name T := do
  let discover : ExploreM T repr.Name (T × Array (List (List T))) := do
    let start ← refInstance repr cfg tpl none j args
    let mut fields := #[]
    let mut i := 0
    while i < (← get).keys.size && i < maxInstances do
      let (k, as) := (← get).keys.getD i (0, [])
      let ctors := (tpl.dd[k]?.map (·.2)).getD []
      let ctors ← ctors.mapM fun c => c.mapM fun t => do
        let t := substs repr tpl.templates (tpl.params repr k) as t
        let t ← replaceRefs repr cfg tpl i (repr.view t)
        StateT.lift (normalizeSort repr cfg (repr.view t))
      fields := fields.push ctors
      i := i + 1
    return (start, fields)
  let ((start, fields), ex) ← discover.run {}
  if ex.keys.isEmpty then return start
  if fields.size < ex.keys.size then return repr.stuck
  let n := ex.keys.size
  let reach := (Array.range n).map (reachable ex.edges)
  let component (i : Nat) : List Nat :=
    (List.range n).filter fun k => (reach.getD i []).contains k && (reach.getD k []).contains i
  let name (i : Nat) : repr.Name := ex.names.getD i (repr.name "")
  let mut built : Array (Option T) := Array.replicate n none
  for _ in [0:n] do
    for i in [0:n] do
      let c := component i
      let deps := (c.flatMap (ex.edges.getD · [])).filter (!c.contains ·)
      if c.all (built.getD · none |>.isNone) && deps.all (built.getD · none |>.isSome) then
        -- References to instances of other blocks become their types.
        let close (t : T) : T := deps.eraseDups.foldl (fun t d =>
          match built.getD d none with
          | some ty => subst repr tpl.templates (name d) ty (repr.view t)
          | none => t) t
        let members := c.map fun m => (name m, ((fields.getD m []).map (List.map close)))
        let refs := members.map fun (m, ctors) => (m, ctors.map (List.filterMap fun t =>
          match repr.view t with
          | .ref q => if c.any (name · == q) then some q else none
          | _ => none))
        let block := (productiveOrder refs).filterMap (members[·]?)
        for m in c do
          built := built.set! m (some (repr.build (.datatype (name m) block)))
  let instances := (List.range n).filterMap fun i => do
    let (k, as) ← ex.keys[i]?
    let ty ← built.getD i none
    return ((⟨tpl.app repr k as, []⟩ : ElaboratedTerm T repr.Name), (⟨ty, []⟩ : ElaboratedTerm T repr.Name))
  modify fun s => { s with instances := instances ++ s.instances }
  return (built.getD 0 none).getD repr.stuck
end

-- Recover the applications behind allocated sorts when inferring datatype
-- parameters, e.g. match Box A against the sort allocated for Box Int.
private partial def expandSorts [Inhabited T] (repr : DatatypeTerms T)
    (templates : List T) (instances : List (T × T)) (view : DatatypeTermView T repr.Name) : T :=
  let t := repr.build view
  if templates.contains t then t
  else if let some (app, _) := instances.find? (fun (_, ty) => ty == t) then
    expandSorts repr templates instances (repr.view app)
  else match view with
  | .apply f a => repr.build (.apply
      (expandSorts repr templates instances (repr.view f)) (expandSorts repr templates instances (repr.view a)))
  | .datatype s dd => repr.build (.datatype s
      (mapFields (fun t => expandSorts repr templates instances (repr.view t)) dd))
  | .constructorType t u => repr.build (.constructorType
      (expandSorts repr templates instances (repr.view t)) (expandSorts repr templates instances (repr.view u)))
  | _ => t

private def sortInstances (s : SortState (ElaboratedTerm T N)) : List (T × T) :=
  s.instances.map fun (app, ty) => (app.value, ty.value)

-- Terms leaving the parser carry instantiated datatype declarations.
private def resolved (repr : DatatypeTerms T) (t : ElaboratedTerm T repr.Name) : T :=
  if t.generics.isEmpty then t.value else repr.stuck

private def lift (f : List T → T) (ts : List (ElaboratedTerm T N)) : ElaboratedTerm T N :=
  ⟨f (ts.map (·.value)), ts.flatMap (·.generics)⟩

private def matchParam (names : List N) (p : N) (t : T)
    (bs : Array (Option T)) : Option (Array (Option T)) := do
  let (_, k) ← names.zipIdx.find? (fun (q, _) => p == q)
  let old ← bs[k]?
  if old.isNone || old == some t then some (bs.set! k (some t)) else none

mutual
private partial def matchType (repr : DatatypeTerms T) (names : List repr.Name) :
    DatatypeTermView T repr.Name → DatatypeTermView T repr.Name → Array (Option T) → Option (Array (Option T))
  | .ref p, t, bs =>
      if names.contains p then matchParam names p (repr.build t) bs
      else if repr.build (.ref p) == repr.build t then some bs
      else match t with
        -- Typing resolves only a bare reference to its datatype, so a reference
        -- applied to arguments meets the operand's template sort by name.
        | .datatype s _ => if s == p then some bs else none
        | _ => none
  | .apply f a, .apply g b, bs | .constructorType f a, .constructorType g b, bs => do
      matchType repr names (repr.view a) (repr.view b)
        (← matchType repr names (repr.view f) (repr.view g) bs)
  -- A calculus may resolve bare parameter references into datatype types.
  | .datatype s dd, .datatype t ee, bs =>
      if names.contains s then matchParam names s (repr.build (.datatype t ee)) bs
      else if s == t && dd == ee then some bs
      else if s == t then matchDecl repr names dd ee bs else none
  | .datatype s _, t, bs =>
      if names.contains s then matchParam names s (repr.build t) bs else none
  | t, u, bs => if repr.build t == repr.build u then some bs else none
private partial def matchDecl (repr : DatatypeTerms T) (names : List repr.Name) :
    DatatypeBlock T repr.Name → DatatypeBlock T repr.Name → Array (Option T) → Option (Array (Option T))
  | [], [], bs => some bs
  | (s, d) :: dd, (t, e) :: ee, bs => do
      if s == t then matchDecl repr names dd ee (← matchDt repr names d e bs) else none
  | _, _, _ => none
private partial def matchDt (repr : DatatypeTerms T) (names : List repr.Name) :
    List (List T) → List (List T) → Array (Option T) → Option (Array (Option T))
  | [], [], bs => some bs
  | c :: d, b :: e, bs => do
      matchDt repr names d e (← matchCons repr names c b bs)
  | _, _, _ => none
private partial def matchCons (repr : DatatypeTerms T) (names : List repr.Name) :
    List T → List T → Array (Option T) → Option (Array (Option T))
  | [], [], bs => some bs
  | t :: c, u :: d, bs => do
      matchCons repr names c d (← matchType repr names (repr.view t) (repr.view u) bs)
  | _, _, _ => none
end

private def matchFields (repr : DatatypeTerms T) (templates : List T)
    (instances : List (T × T)) (names : List repr.Name) :
    DatatypeTermView T repr.Name → List T → Array (Option T) → Option (Array (Option T))
  | _, [], bs => some bs
  | .constructorType field rest, a :: args, bs => do
      matchFields repr templates instances names (repr.view rest) args
        (← matchType repr names
          (repr.view (expandSorts repr templates instances (repr.view field)))
          (repr.view (expandSorts repr templates instances (repr.view (repr.typeOf a)))) bs)
  | _, _, _ => none

private def instantiateOp (repr : DatatypeTerms T) :
    DatatypeTermView T repr.Name → DatatypeTermView T repr.Name → Option T
  | .constructor _ _ i, .datatype t dd => some (repr.build (.constructor t dd i))
  | .selector _ _ i j, .datatype t dd => some (repr.build (.selector t dd i j))
  | _, _ => none

private def instantiate (repr : DatatypeTerms T) (instances : List (T × T))
    (generics : List (T × Generic T repr.Name))
    (op ty : T) : Option T := do
  let (_, .datatype _ body _) ← generics.find? (fun (g, _) => g == op) | none
  let (app, _) ← instances.find? (fun (_, inst) => inst == ty)
  let (head, _) := appSpine repr (repr.view app) []
  if head != body then none else
  instantiateOp repr (repr.view op) (repr.view ty)

private def finish (repr : DatatypeTerms T) (term : ElaboratedTerm T repr.Name)
    (args : List T) (inst old : T) : ElaboratedTerm T repr.Name :=
  ⟨args.foldl (fun f a => repr.build (.apply f a)) inst,
    term.generics.eraseP (fun (g, _) => g == old)⟩

private def elaborateOperand (repr : DatatypeTerms T) (term : ElaboratedTerm T repr.Name)
    (index : T) (rebuild : T → T) : List T → TermElaborationM T repr.Name (ElaboratedTerm T repr.Name)
  | a :: args => do
      if let some inst := instantiate repr (sortInstances (← get)) term.generics index (repr.typeOf a) then
        return finish repr term (a :: args) (rebuild inst) index
      return term
  | [] => pure term

private def elaborateHead (repr : DatatypeTerms T) (cfg : Config T R C CL)
    (term : ElaboratedTerm T repr.Name) (head : T) (args : List T) :
    DatatypeTermView T repr.Name → TermElaborationM T repr.Name (ElaboratedTerm T repr.Name)
  | .datatype .. => do
      if let some (_, .datatype names _ _) := term.generics.find? (fun (g, _) => g == head) then
        if names.length == args.length then
          let ty ← normalizeSort repr cfg (repr.view term.value)
          return finish repr term [] ty head
      return term
  | .constructor .. => do
      if let some (_, .datatype names body _) := term.generics.find? (fun (g, _) => g == head) then
        let ty := repr.typeOf head
        let state ← get
        if let some bs := matchFields repr (state.datatypes.map (·.value))
            (sortInstances state) names (repr.view ty) args
            (Array.replicate names.length none) then
          if let some types := bs.toList.mapM id then
            let app := types.foldl (fun f a => repr.build (.apply f a)) body
            let ty ← normalizeSort repr cfg (repr.view app)
            if let some inst := instantiate repr (sortInstances (← get)) term.generics head ty then
              return finish repr term args inst head
      return term
  | .selector .. => elaborateOperand repr term head id args
  | .indexed rebuild index => elaborateOperand repr term index rebuild args
  | _ => pure term

private def elaborate (repr : DatatypeTerms T) (cfg : Config T R C CL)
    (term : ElaboratedTerm T repr.Name) : TermElaborationM T repr.Name (ElaboratedTerm T repr.Name) := do
  let (head, args) := appSpine repr (repr.view term.value) []
  if let some (_, .sort arity) := term.generics.find? (fun (g, _) => g == head) then
    if args.length == arity then
      let ty ← normalizeSort repr cfg (repr.view term.value)
      return finish repr term [] ty head
    return term
  elaborateHead repr cfg term head args (repr.view head)

private def ascribeOp (repr : DatatypeTerms T) (instances : List (T × T))
    (op ty : ElaboratedTerm T repr.Name) : DatatypeTermView T repr.Name → Option (ElaboratedTerm T repr.Name)
  | .constructor .. =>
      if op.generics.isEmpty then
        if repr.typeOf op.value == ty.value then some op else none
      else do
        let inst ← instantiate repr instances op.generics op.value ty.value
        some ⟨inst, []⟩
  | _ => none

private def ascribe (repr : DatatypeTerms T) (isType : T → Bool)
    (op ty : ElaboratedTerm T repr.Name) : TermElaborationM T repr.Name (Option (ElaboratedTerm T repr.Name)) := do
  if isType (repr.typeOf (resolved repr ty)) then
    return ascribeOp repr (sortInstances (← get)) op ty (repr.view op.value)
  return none

private def datatypeBindings (repr : DatatypeTerms T) (cfg : Config T R C CL)
    (dts : List (DatatypeSpec (ElaboratedTerm T repr.Name))) :
    TermElaborationM T repr.Name (Option (List (String × ElaboratedTerm T repr.Name))) := do
  let fields := dts.map fun d =>
    (sourceName repr d.name, d.constructors.map fun c => c.selectors.map fun (_, t) => resolved repr t)
  -- The sort, constructors and selectors of `d`, whose sort is `sort`.
  let ops (d : DatatypeSpec (ElaboratedTerm T repr.Name)) (sort : T)
      (wrap : T → ElaboratedTerm T repr.Name) : List (String × ElaboratedTerm T repr.Name) :=
    match repr.view sort with
    | .datatype name block =>
      (d.name, wrap sort) :: d.constructors.zipIdx.flatMap fun (c, i) =>
        (c.name, wrap (repr.build (.constructor name block i))) ::
          c.selectors.zipIdx.map fun ((sel, _), j) =>
            (sel, wrap (repr.build (.selector name block i j)))
    | _ => [(d.name, wrap sort)]
  if dts.all (·.arity == 0) then
    return some (dts.flatMap fun d =>
      ops d (repr.build (.datatype (sourceName repr d.name) fields)) (⟨·, []⟩))
  -- A parametric block is a template: its datatypes get internal names, and a
  -- use of one is instantiated (`instanceOf`).
  let id := (← get).datatypeCount + 1
  modify fun s => { s with datatypeCount := id }
  let members := dts.zipIdx.map fun (_, i) => repr.name s!"@datatype{id}_{i}"
  let block := renameBlock repr fields members
  let info := dts.map fun d => (d.name, d.arity)
  let generic (d : DatatypeSpec (ElaboratedTerm T repr.Name)) (sort op : T) :
      ElaboratedTerm T repr.Name :=
    ⟨op, [(op, .datatype ((List.range d.arity).map (paramName repr)) sort info)]⟩
  let sorts := members.map fun m => repr.build (.datatype m block)
  modify fun s =>
    { s with datatypes := (dts.zip sorts).map (fun (d, sort) => generic d sort sort) ++ s.datatypes }
  let tpl := { dd := block, info, templates := (← get).datatypes.map (·.value) }
  -- A datatype of arity zero has exactly one instance, built here.
  let bindings ← (dts.zip sorts).zipIdx.mapM fun ((d, sort), i) => do
    if d.arity == 0 then
      return ops d (← instanceOf repr cfg tpl i []) (⟨·, []⟩)
    return ops d sort (generic d sort)
  return some bindings.flatten

private def liftArity : Arity T → Arity (ElaboratedTerm T N)
  | .exact n => .exact n
  | .leftAssoc => .leftAssoc
  | .rightAssoc => .rightAssoc
  | .rightAssocNil nil => .rightAssocNil fun t => ⟨nil (t.map (·.value)), t.toList.flatMap (·.generics)⟩
  | .chainable f => .chainable (lift f)
  | .argList f => .argList (lift f)

private def liftOp (op : OpDecl T) : OpDecl (ElaboratedTerm T N) :=
  { name := op.name, indexArity := op.indexArity, arity := liftArity op.arity,
    build := fun ts => (op.build (ts.map (·.value))).map fun t =>
      ⟨t, ts.flatMap (·.generics)⟩,
    binder := op.binder.map lift }

/-- Internal configuration for terms carrying datatype templates. -/
private def elaborationConfig (repr : DatatypeTerms T) (cfg : Config T R C CL) :
    Config (ElaboratedTerm T repr.Name) R C CL where
  ops := cfg.ops.map liftOp
  macros := cfg.macros
  parseLiteral := fun l => (cfg.parseLiteral l).map (fun t => ⟨t, []⟩)
  isType := fun t => cfg.isType (resolved repr t)
  mkType := ⟨cfg.mkType, []⟩
  wellTyped := fun t => repr.typeOf (resolved repr t) != repr.stuck
  mkUSort := fun i => ⟨cfg.mkUSort i, []⟩
  mkSortConstructor := some fun i arity =>
    let head := cfg.mkUSort i
    ⟨head, [(head, .sort arity)]⟩
  mkUConst := fun i t =>
    let ty := resolved repr t
    ⟨cfg.mkUConst i (if cfg.isType (repr.typeOf ty) then ty else repr.stuck), []⟩
  apply := fun f a => ⟨cfg.apply f.value a.value, f.generics ++ a.generics⟩
  parseRule := cfg.parseRule
  mkAssumePush := cfg.mkAssumePush ∘ resolved repr
  mkStep := fun r ts ps => cfg.mkStep r (ts.map (resolved repr)) ps
  mkStepPop := fun r ts ps => cfg.mkStepPop r (ts.map (resolved repr)) ps
  mkCheckProven := cfg.mkCheckProven.map (· ∘ resolved repr)
  mkCmdList := cfg.mkCmdList
  mkVar := cfg.mkVar.map fun mk s t => ⟨mk s (resolved repr t), []⟩
  datatypes := some
    { mkRef := fun s => ⟨repr.build (.ref (sourceName repr s)), []⟩
      mkDecls := datatypeBindings repr cfg
      mkParam := some fun k => ⟨repr.build (.ref (paramName repr k)), []⟩
      elaborate := elaborate repr cfg
      ascribe := ascribe repr cfg.isType
      isGeneric := fun t => !t.generics.isEmpty }

private def parseConfigured [BEq T] (cfg : Config T R C CL) (ss : List Sexp) :
    Option (DatatypeTerms T) → Except String (List T × CL)
  | none =>
      (parseCommands cfg ss).run' { State.ofOps cfg.ops with macros := .ofList cfg.macros }
  | some repr =>
      letI : Inhabited T := ⟨repr.stuck⟩
      do
        let parserCfg := elaborationConfig repr cfg
        let state := { State.ofOps parserCfg.ops with macros := .ofList parserCfg.macros }
        let (ts, cmds) ← (parseCommands parserCfg ss).run' state
        return (ts.map (resolved repr), cmds)

/-- Parse a proof into its assumptions and its list of commands. -/
def parseProof [BEq T] (cfg : Config T R C CL) (input : String) : Except String (List T × CL) := do
  let ss ← Sexp.Parser.manySexps!.run input
  parseConfigured cfg ss cfg.datatypeTerms

end Logos.Parser
