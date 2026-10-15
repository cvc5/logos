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

private partial def appSpine [Inhabited T] (repr : DatatypeTerms T) :
    DatatypeTermView T repr.Name → List T → T × List T
  | .apply f a, args => appSpine repr (repr.view f) (a :: args)
  | f, args => (repr.build f, args)

private partial def subst (repr : DatatypeTerms T) (p : repr.Name) (a : T) : DatatypeTermView T repr.Name → T
  | .ref q => if p == q then a else repr.build (.ref q)
  | .datatype s dd => repr.build (.datatype s (mapFields (fun t => subst repr p a (repr.view t)) dd))
  | .apply t u => repr.build (.apply (subst repr p a (repr.view t)) (subst repr p a (repr.view u)))
  | .constructorType t u =>
      repr.build (.constructorType (subst repr p a (repr.view t)) (subst repr p a (repr.view u)))
  | t => repr.build t

-- Open arguments may use the same canonical parameter names as the template.
private def substs (repr : DatatypeTerms T) (names : List repr.Name) (args : List T) (body : T) : T :=
  let fresh := names.zipIdx.map fun (_, i) => repr.name ("@inst" ++ toString i)
  let body := (names.zip fresh).foldl
    (fun t (p, q) => subst repr p (repr.build (.ref q)) (repr.view t)) body
  (fresh.zip args).foldl (fun t (p, a) => subst repr p a (repr.view t)) body

private inductive Generic (T N : Type) where
  | datatype : List N → T → Generic T N
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

-- Open applications remain symbolic in datatype templates. Ground applications
-- get one ordinary uninterpreted sort, reused throughout the proof.
private partial def normalizeSort (repr : DatatypeTerms T) (cfg : Config T R C CL) :
    DatatypeTermView T repr.Name → TermElaborationM T repr.Name T
  | .apply f a => do
      let f ← normalizeSort repr cfg (repr.view f)
      let a ← normalizeSort repr cfg (repr.view a)
      let t := repr.build (.apply f a)
      let (head, args) := appSpine repr (repr.view t) []
      let state ← get
      if let some (_, arity) := state.constructors.find? (fun (c, _) => c.value == head) then
        if args.length == arity && args.all (fun a =>
            closedType repr [] (repr.view a) && cfg.isType (repr.typeOf a)) then
          if let some (_, ty) := state.instances.find? (fun (app, _) => app.value == t) then
            return ty.value
          let ty := cfg.mkUSort (state.count + 1)
          modify fun s => { s with
            count := state.count + 1,
            instances := (⟨t, []⟩, ⟨ty, []⟩) :: s.instances }
          return ty
      return t
  | .datatype s dd => do
      let dd ← dd.mapM fun (name, d) => do
        let d ← d.mapM fun c => c.mapM fun t => normalizeSort repr cfg (repr.view t)
        return (name, d)
      return repr.build (.datatype s dd)
  | .constructorType t u => do
      return repr.build (.constructorType
        (← normalizeSort repr cfg (repr.view t)) (← normalizeSort repr cfg (repr.view u)))
  | t => pure (repr.build t)

-- Recover the applications behind allocated sorts when inferring datatype
-- parameters, e.g. match Box A against the sort allocated for Box Int.
private partial def expandSorts [Inhabited T] (repr : DatatypeTerms T) (instances : List (T × T)) :
    DatatypeTermView T repr.Name → T
  | .apply f a => repr.build (.apply
      (expandSorts repr instances (repr.view f)) (expandSorts repr instances (repr.view a)))
  | .datatype s dd => repr.build (.datatype s
      (mapFields (fun t => expandSorts repr instances (repr.view t)) dd))
  | .constructorType t u => repr.build (.constructorType
      (expandSorts repr instances (repr.view t)) (expandSorts repr instances (repr.view u)))
  | t =>
      if let some (app, _) := instances.find? (fun (_, ty) => ty == repr.build t) then
        expandSorts repr instances (repr.view app)
      else repr.build t

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
      else if repr.build (.ref p) == repr.build t then some bs else none
  | .apply f a, .apply g b, bs | .constructorType f a, .constructorType g b, bs => do
      matchType repr names (repr.view a) (repr.view b)
        (← matchType repr names (repr.view f) (repr.view g) bs)
  -- A calculus may resolve bare parameter references into datatype types.
  | .datatype s dd, .datatype t ee, bs =>
      if names.contains s then matchParam names s (repr.build (.datatype t ee)) bs
      else if s == t then matchDecl repr names dd ee bs else none
  | .datatype s _, t, bs => matchParam names s (repr.build t) bs
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

private def matchFields (repr : DatatypeTerms T) (instances : List (T × T)) (names : List repr.Name) :
    DatatypeTermView T repr.Name → List T → Array (Option T) → Option (Array (Option T))
  | _, [], bs => some bs
  | .constructorType field rest, a :: args, bs => do
      matchFields repr instances names (repr.view rest) args
        (← matchType repr names
          (repr.view (expandSorts repr instances (repr.view field)))
          (repr.view (expandSorts repr instances (repr.view (repr.typeOf a)))) bs)
  | _, _, _ => none

private def instantiateOp (repr : DatatypeTerms T) :
    DatatypeTermView T repr.Name → DatatypeTermView T repr.Name → Option T
  | .constructor s _ i, .datatype t dd =>
      if s == t then some (repr.build (.constructor s dd i)) else none
  | .selector s _ i j, .datatype t dd =>
      if s == t then some (repr.build (.selector s dd i j)) else none
  | _, _ => none

private def instantiate (repr : DatatypeTerms T) (instances : List (T × T))
    (generics : List (T × Generic T repr.Name))
    (op ty : T) : Option T := do
  let (_, .datatype names body) ← generics.find? (fun (g, _) => g == op) | none
  let _ ← matchType repr names
    (repr.view (expandSorts repr instances (repr.view body)))
    (repr.view (expandSorts repr instances (repr.view ty))) (Array.replicate names.length none)
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
      if let some (_, .datatype names body) := term.generics.find? (fun (g, _) => g == head) then
        if names.length == args.length then
          let ty ← normalizeSort repr cfg (repr.view (substs repr names args body))
          return finish repr term [] ty head
      return term
  | .constructor .. => do
      if let some (_, .datatype names body) := term.generics.find? (fun (g, _) => g == head) then
        let ty := repr.typeOf head
        if let some bs := matchFields repr (sortInstances (← get)) names (repr.view ty) args
            (Array.replicate names.length none) then
          if let some types := bs.toList.mapM id then
            let ty ← normalizeSort repr cfg (repr.view (substs repr names types body))
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

private def datatypeBindings (repr : DatatypeTerms T)
    (dts : List (DatatypeSpec (ElaboratedTerm T repr.Name))) : Option (List (String × ElaboratedTerm T repr.Name)) :=
  let template := dts.map fun d =>
    (repr.name d.name, d.constructors.map fun c => c.selectors.map fun (_, t) => resolved repr t)
  let arity := (dts.head?.map (·.arity)).getD 0
  let names := (List.range arity).map (paramName repr)
  some <| dts.flatMap fun d =>
    let name := repr.name d.name
    let sort := repr.build (.datatype name template)
    let generic (op : T) : ElaboratedTerm T repr.Name := ⟨op, if arity == 0 then [] else [(op, .datatype names sort)]⟩
    (d.name, generic sort) :: d.constructors.zipIdx.flatMap fun (c, i) =>
      (c.name, generic (repr.build (.constructor name template i))) ::
        c.selectors.zipIdx.map fun ((sel, _), j) =>
          (sel, generic (repr.build (.selector name template i j)))

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
    { mkRef := fun s => ⟨repr.build (.ref (repr.name s)), []⟩
      mkDecls := datatypeBindings repr
      mkParam := some fun k => ⟨repr.build (.ref (paramName repr k)), []⟩
      elaborate := elaborate repr cfg
      ascribe := ascribe repr cfg.isType }

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
