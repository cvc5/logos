module

public import Logos.Parser
import all Logos.Parser

public section

/-!
Signature-independent datatype elaboration. A generated parser supplies the
views and constructors of its term representation through `DatatypeTerms`.
-/

namespace Logos.Parser

/-- A declaration block, with datatypes, constructors and fields in order. -/
abbrev DatatypeBlock (T N : Type) := List (N × List (List T))

/-- The term forms needed for datatype elaboration. Other terms remain opaque. -/
inductive DatatypeTermView (T N : Type) where
  | apply : T → T → DatatypeTermView T N
  | ref : N → DatatypeTermView T N
  | datatype : N → DatatypeBlock T N → DatatypeTermView T N
  | constructorType : T → T → DatatypeTermView T N
  | constructor : N → DatatypeBlock T N → Nat → DatatypeTermView T N
  | selector : N → DatatypeBlock T N → Nat → Nat → DatatypeTermView T N
  | indexed : (T → T) → T → DatatypeTermView T N
  | atom : T → DatatypeTermView T N

/-- The connection between shared elaboration and a calculus's terms. -/
structure DatatypeTerms (T N : Type) where
  name : String → N
  /-- Decompose the forms used by elaboration; leave other terms as atoms. -/
  view : T → DatatypeTermView T N
  /-- Reconstruct a view, with `build (view t) = t`. -/
  build : DatatypeTermView T N → T
  typeOf : T → T
  stuck : T

variable {T N R C CL : Type} [BEq T] [BEq N] [Inhabited T]

private def mapFields (f : T → T) (dd : DatatypeBlock T N) : DatatypeBlock T N :=
  dd.map fun (s, d) => (s, d.map (List.map f))

private def paramName (repr : DatatypeTerms T N) (k : Nat) : N :=
  repr.name ("@p" ++ toString k)

private partial def appSpine [Inhabited T] (repr : DatatypeTerms T N) :
    DatatypeTermView T N → List T → T × List T
  | .apply f a, args => appSpine repr (repr.view f) (a :: args)
  | f, args => (repr.build f, args)

private partial def subst (repr : DatatypeTerms T N) (p : N) (a : T) : DatatypeTermView T N → T
  | .ref q => if p == q then a else repr.build (.ref q)
  | .datatype s dd => repr.build (.datatype s (mapFields (fun t => subst repr p a (repr.view t)) dd))
  | .apply t u => repr.build (.apply (subst repr p a (repr.view t)) (subst repr p a (repr.view u)))
  | .constructorType t u =>
      repr.build (.constructorType (subst repr p a (repr.view t)) (subst repr p a (repr.view u)))
  | t => repr.build t

-- Open arguments may use the same canonical parameter names as the template.
private def substs (repr : DatatypeTerms T N) (names : List N) (args : List T) (body : T) : T :=
  let fresh := names.zipIdx.map fun (_, i) => repr.name ("@inst" ++ toString i)
  let body := (names.zip fresh).foldl
    (fun t (p, q) => subst repr p (repr.build (.ref q)) (repr.view t)) body
  (fresh.zip args).foldl (fun t (p, a) => subst repr p a (repr.view t)) body

/-- A term with a parser-local mapping from generic sorts and operators to
their parameter names and datatype templates. -/
structure ElaboratedTerm (T N : Type) where
  value : T
  generics : List (T × List N × T)

-- Terms leaving the parser carry instantiated datatype declarations.
private def resolved (repr : DatatypeTerms T N) (t : ElaboratedTerm T N) : T :=
  if t.generics.isEmpty then t.value else repr.stuck

private def lift (f : List T → T) (ts : List (ElaboratedTerm T N)) : ElaboratedTerm T N :=
  ⟨f (ts.map (·.value)), ts.flatMap (·.generics)⟩

private def matchParam (names : List N) (p : N) (t : T)
    (bs : Array (Option T)) : Option (Array (Option T)) := do
  let (_, k) ← names.zipIdx.find? (fun (q, _) => p == q)
  let old ← bs[k]?
  if old.isNone || old == some t then some (bs.set! k (some t)) else none

mutual
private partial def matchType (repr : DatatypeTerms T N) (names : List N) :
    DatatypeTermView T N → DatatypeTermView T N → Array (Option T) → Option (Array (Option T))
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
private partial def matchDecl (repr : DatatypeTerms T N) (names : List N) :
    DatatypeBlock T N → DatatypeBlock T N → Array (Option T) → Option (Array (Option T))
  | [], [], bs => some bs
  | (s, d) :: dd, (t, e) :: ee, bs => do
      if s == t then matchDecl repr names dd ee (← matchDt repr names d e bs) else none
  | _, _, _ => none
private partial def matchDt (repr : DatatypeTerms T N) (names : List N) :
    List (List T) → List (List T) → Array (Option T) → Option (Array (Option T))
  | [], [], bs => some bs
  | c :: d, b :: e, bs => do
      matchDt repr names d e (← matchCons repr names c b bs)
  | _, _, _ => none
private partial def matchCons (repr : DatatypeTerms T N) (names : List N) :
    List T → List T → Array (Option T) → Option (Array (Option T))
  | [], [], bs => some bs
  | t :: c, u :: d, bs => do
      matchCons repr names c d (← matchType repr names (repr.view t) (repr.view u) bs)
  | _, _, _ => none
end

private def matchFields (repr : DatatypeTerms T N) (names : List N) :
    DatatypeTermView T N → List T → Array (Option T) → Option (Array (Option T))
  | _, [], bs => some bs
  | .constructorType field rest, a :: args, bs => do
      matchFields repr names (repr.view rest) args
        (← matchType repr names (repr.view field) (repr.view (repr.typeOf a)) bs)
  | _, _, _ => none

private def instantiateOp (repr : DatatypeTerms T N) :
    DatatypeTermView T N → DatatypeTermView T N → Option T
  | .constructor s _ i, .datatype t dd =>
      if s == t then some (repr.build (.constructor s dd i)) else none
  | .selector s _ i j, .datatype t dd =>
      if s == t then some (repr.build (.selector s dd i j)) else none
  | _, _ => none

private def instantiate (repr : DatatypeTerms T N) (generics : List (T × List N × T))
    (op ty : T) : Option T := do
  let (_, names, body) ← generics.find? (fun (g, _) => g == op)
  let _ ← matchType repr names (repr.view body)
    (repr.view ty) (Array.replicate names.length none)
  instantiateOp repr (repr.view op) (repr.view ty)

private def finish (repr : DatatypeTerms T N) (term : ElaboratedTerm T N)
    (args : List T) (inst old : T) : ElaboratedTerm T N :=
  ⟨args.foldl (fun f a => repr.build (.apply f a)) inst,
    term.generics.eraseP (fun (g, _) => g == old)⟩

private def elaborateOperand (repr : DatatypeTerms T N) (term : ElaboratedTerm T N)
    (index : T) (rebuild : T → T) : List T → ElaboratedTerm T N
  | a :: args =>
      if let some inst := instantiate repr term.generics index (repr.typeOf a) then
        finish repr term (a :: args) (rebuild inst) index
      else term
  | [] => term

private def elaborateHead (repr : DatatypeTerms T N) (term : ElaboratedTerm T N)
    (head : T) (args : List T) : DatatypeTermView T N → ElaboratedTerm T N
  | .datatype .. =>
      if let some (_, names, body) := term.generics.find? (fun (g, _) => g == head) then
        if names.length == args.length then
          finish repr term [] (substs repr names args body) head
        else term
      else term
  | .constructor .. => Id.run do
      if let some (_, names, body) := term.generics.find? (fun (g, _) => g == head) then
        let ty := repr.typeOf head
        if let some bs := matchFields repr names (repr.view ty) args (Array.replicate names.length none) then
          if let some types := bs.toList.mapM id then
            if let some inst := instantiate repr term.generics head
                (substs repr names types body) then
              return finish repr term args inst head
      return term
  | .selector .. => elaborateOperand repr term head id args
  | .indexed rebuild index => elaborateOperand repr term index rebuild args
  | _ => term

private def elaborate (repr : DatatypeTerms T N) (term : ElaboratedTerm T N) : ElaboratedTerm T N :=
  let (head, args) := appSpine repr (repr.view term.value) []
  elaborateHead repr term head args (repr.view head)

private def ascribeOp (repr : DatatypeTerms T N) (op ty : ElaboratedTerm T N) :
    DatatypeTermView T N → Option (ElaboratedTerm T N)
  | .constructor .. =>
      if op.generics.isEmpty then
        if repr.typeOf op.value == ty.value then some op else none
      else do
        let inst ← instantiate repr op.generics op.value ty.value
        some ⟨inst, []⟩
  | _ => none

private def ascribe (repr : DatatypeTerms T N) (isType : T → Bool)
    (op ty : ElaboratedTerm T N) : Option (ElaboratedTerm T N) :=
  if isType (repr.typeOf (resolved repr ty)) then ascribeOp repr op ty (repr.view op.value) else none

private def datatypeBindings (repr : DatatypeTerms T N)
    (dts : List (DatatypeSpec (ElaboratedTerm T N))) : Option (List (String × ElaboratedTerm T N)) :=
  let template := dts.map fun d =>
    (repr.name d.name, d.constructors.map fun c => c.selectors.map fun (_, t) => resolved repr t)
  let arity := (dts.head?.map (·.arity)).getD 0
  let names := (List.range arity).map (paramName repr)
  some <| dts.flatMap fun d =>
    let name := repr.name d.name
    let sort := repr.build (.datatype name template)
    let generic (op : T) : ElaboratedTerm T N := ⟨op, if arity == 0 then [] else [(op, names, sort)]⟩
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

/-- Add datatype elaboration to a calculus's generated parser configuration. -/
def withDatatypes (repr : DatatypeTerms T N) (cfg : Config T R C CL) :
    Config (ElaboratedTerm T N) R C CL where
  ops := cfg.ops.map liftOp
  parseLiteral := fun l => (cfg.parseLiteral l).map (fun t => ⟨t, []⟩)
  isType := fun t => cfg.isType (resolved repr t)
  mkType := ⟨cfg.mkType, []⟩
  wellTyped := fun t => repr.typeOf (resolved repr t) != repr.stuck
  mkUSort := fun i => ⟨cfg.mkUSort i, []⟩
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
      elaborate := elaborate repr
      ascribe := ascribe repr cfg.isType }

/-- Read a proof using a signature's configuration, macros and datatype representation. -/
def parseProofWithDatatypes (repr : DatatypeTerms T N) (cfg : Config T R C CL)
    (macros : List (String × Macro)) (proof : String) : Except String (List T × CL) := do
  let cfg := withDatatypes repr cfg
  let state := { State.ofOps cfg.ops with macros := .ofList macros }
  let ss ← Logos.Sexp.Parser.manySexps!.run proof
  let (ts, cmds) ← (parseCommands cfg ss).run' state
  return (ts.map (resolved repr), cmds)

end Logos.Parser
