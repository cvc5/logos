module

/-
A generic, table-driven parser for proofs in the s-expression (Eunoia/Ethos)
syntax produced by `cvc5 --dump-proofs --proof-format=cpc`.

The parser itself is independent of any particular signature: everything that is
specific to a calculus (its operators, its literals and its proof rules) is
supplied by a `Logos.Parser.Config`.  The configuration for the calculus in this
repository (`Cpc.Parser`) is generated from the corresponding Eunoia signature,
so this module is the only hand-written part of the pipeline.
-/

public import Std.Data.HashMap
public import Logos.Sexp
import all Logos.Sexp

public section

namespace Logos.Parser

variable {T R C CL : Type}

/-!
## Operator declarations
-/

/--
How the explicit arguments of an operator are combined into a term.  These
correspond to the argument-list attributes of Eunoia's `declare-const`.
-/
inductive Arity (T : Type) where
  /-- The operator takes exactly `n` explicit arguments. -/
  | exact (n : Nat)
  /-- N-ary, left associative: `(f a b c)` denotes `((a f b) f c)`. -/
  | leftAssoc
  /-- N-ary, right associative: `(f a b c)` denotes `(a f (b f c))`. -/
  | rightAssoc
  /--
  N-ary, right associative with a nil terminator: `(f a b c)` denotes
  `(a f (b f (c f nil)))`.  The terminator is computed from the first argument,
  since in Eunoia it is typically indexed by that argument's type; `none` is
  passed when `f` is applied to no arguments at all.
  -/
  | rightAssocNil (nil : Option T → T)
  /--
  Chainable: `(f a b c)` denotes `mk [(f a b), (f b c)]`, where `mk` builds the
  chaining operator's application (usually an n-ary `and`).  As in Ethos, a
  binary application is *not* wrapped, i.e. `(f a b)` denotes `(f a b)`.
  -/
  | chainable (mk : List T → T)
  /--
  Argument list: `(f a b c)` denotes `(f (mk [a, b, c]))`.  This corresponds
  to Eunoia's `:arg-list` attribute, whose argument names the n-ary operator
  represented here by `mk`.  The annotated operator is unary, and at least one
  argument must be gathered.
  -/
  | argList (mk : List T → T)

/--
The declaration of a single operator of the signature.

`indexArity` is the number of indices the operator takes, i.e. the `k` in
`(_ f i₁ … i_k)`; `build` turns those indices into the head term and is only
ever called with a list of exactly `indexArity` elements.  A name may be
declared more than once as long as the overloads are distinguishable by their
index/argument counts (e.g. unary `-` versus n-ary `-`).
-/
structure OpDecl (T : Type) where
  name : String
  indexArity : Nat := 0
  arity : Arity T
  build : List T → Option T

/-!
## Term-building helpers

These are also used by generated configurations, e.g. to describe the operator
that chains a chainable predicate.
-/

/-- `(a op (b op (c op nil)))`, where `nil` is computed from the first element. -/
def rightAssocNil (apply : T → T → T) (op : T) (nil : Option T → T) (ts : List T) : T :=
  ts.foldr (fun t acc => apply (apply op t) acc) (nil ts.head?)

/-- `((a op b) op c)`; `none` on an empty list. -/
def leftAssoc (apply : T → T → T) (op : T) : List T → Option T
  | [] => none
  | t :: ts => some (ts.foldl (fun acc u => apply (apply op acc) u) t)

/-- `(a op (b op c))`; `none` on an empty list. -/
def rightAssoc (apply : T → T → T) (op : T) : List T → Option T
  | [] => none
  | t :: ts => some (go t ts)
where
  go (t : T) : List T → T
    | [] => t
    | u :: us => apply (apply op t) (go u us)

/-- The pairwise applications `[(op a b), (op b c), …]` of a chainable operator. -/
def chainSteps (apply : T → T → T) (op : T) : List T → List T
  | a :: b :: rest => apply (apply op a) b :: chainSteps apply op (b :: rest)
  | _ => []

/-- Combine the arguments of an operator according to its arity. -/
def mkOpApp (apply : T → T → T) (arity : Arity T) (op : T) (args : List T) : Option T :=
  match arity with
  | .exact _ => some (args.foldl apply op)
  | .leftAssoc => leftAssoc apply op args
  | .rightAssoc => rightAssoc apply op args
  | .rightAssocNil nil => some (rightAssocNil apply op nil args)
  | .chainable mk =>
    match args with
    | [] => none
    | [_] => none
    | [a, b] => some (apply (apply op a) b)
    | args => some (mk (chainSteps apply op args))
  | .argList mk =>
    if args.isEmpty then none else some (apply op (mk args))

/--
Whether an arity admits the given number of explicit arguments.  Operators of a
fixed arity may be under-applied, since terms are curried and producers do print
partially applied operators (e.g. `(_ extract 3 0)` as the argument of `cong`).
-/
def Arity.admits : Arity T → Nat → Bool
  | .exact n, k => k ≤ n
  | .leftAssoc, k => k ≥ 2
  | .rightAssoc, k => k ≥ 2
  | .chainable _, k => k ≥ 2
  | .argList _, k => k > 0
  | .rightAssocNil _, _ => true

/-!
## Literals

Lexing literals is the same for every calculus, so it happens here; a `Config`
only has to say how to turn a lexed literal into a term.
-/

/-- A literal, before it is mapped into the term language of a calculus. -/
inductive Literal where
  /-- An integer literal, e.g. `12` or `-12`. -/
  | numeral (n : Int)
  /-- A rational literal, e.g. `1/2` or `0.5`.  The denominator is positive. -/
  | rational (num den : Int)
  /--
  A string literal; the enclosing quotes are removed, `""` unescaped to `"`, and
  the `\u` escapes of the SMT-LIB theory of strings decoded (`decodeEscapes`).
  -/
  | string (s : String)
  /-- A bit-vector literal, e.g. `#b0110` or `#x1f`, of the given width and value. -/
  | binary (width : Nat) (value : Nat)
deriving Repr, BEq, Inhabited

namespace Literal

private def digitsToNat (base : Nat) (digitValue : Char → Option Nat) :
    List Char → Option Nat
  | [] => none
  | ds => ds.foldlM (fun acc c => do return base * acc + (← digitValue c)) 0

private def binDigit (c : Char) : Option Nat :=
  if c == '0' then some 0 else if c == '1' then some 1 else none

private def decDigit (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat) else none

private def hexDigit (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Replace each `""` by a single `"`, as in the SMT-LIB string escape. -/
private def unescape : List Char → List Char
  | '"' :: '"' :: cs => '"' :: unescape cs
  | c :: cs => c :: unescape cs
  | [] => []

/--
The number of code points a string literal ranges over: `0` to `0x2FFFF`, as in
Ethos and cvc5.  A `\u` escape naming anything at or above this is not an escape.
-/
private def numCodePoints : Nat := 196608

/--
Read the digits of a braced `\u{d…}` escape, from the characters after the `{`:
one to five hex digits followed by `}`.  Returns the code point and how many
characters were read, including the closing brace.
-/
private def readBraced (acc digits : Nat) : List Char → Option (Nat × Nat)
  | '}' :: _ => if digits == 0 then none else some (acc, 1)
  | c :: cs => do
    let d ← hexDigit c
    if digits ≥ 5 then none
    else
      let (v, used) ← readBraced (16 * acc + d) (digits + 1) cs
      some (v, used + 1)
  | [] => none

/--
Read a `\u` escape, from the characters following the `u`: either `{d…}` with one
to five hex digits, or exactly four hex digits with no braces.  Returns the code
point and how many characters it is written with.
-/
private def readEscape : List Char → Option (Nat × Nat)
  | '{' :: cs => (readBraced 0 0 cs).map fun (v, used) => (v, used + 1)
  | d₃ :: d₂ :: d₁ :: d₀ :: _ => do
    let v₃ ← hexDigit d₃; let v₂ ← hexDigit d₂
    let v₁ ← hexDigit d₁; let v₀ ← hexDigit d₀
    some (((v₃ * 16 + v₂) * 16 + v₁) * 16 + v₀, 4)
  | _ => none

/--
Decode the `\u` escapes of a string literal.  These belong to the SMT-LIB
*theory* of strings rather than to its syntax: `"\u{a}"` denotes the
one-character string whose code point is `0xa`, not the six characters it is
written with.  cvc5 prints every non-printable character of a string this way,
so a literal read without decoding them denotes a different string than the one
the proof is about.

A sequence that is not a well-formed escape, or that names a code point at or
above `numCodePoints`, is not an escape and stands for the characters it is
written with, as in Ethos.  A well-formed escape naming a code point Lean cannot
represent as a `Char` -- a surrogate, `0xd800` to `0xdfff` -- gives `none`, since
reading the literal at all would mean reading it as a string it does not denote.
-/
private def decodeEscapes : List Char → Option (List Char)
  | [] => some []
  | '\\' :: 'u' :: cs =>
    let literal := (fun ds => '\\' :: 'u' :: ds) <$> decodeEscapes cs
    match readEscape cs with
    | none => literal
    | some (v, used) =>
      if v ≥ numCodePoints then literal
      else
        let c := Char.ofNat v
        if c.toNat == v then (c :: ·) <$> decodeEscapes (cs.drop used) else none
  | c :: cs => (c :: ·) <$> decodeEscapes cs
termination_by cs => cs.length
decreasing_by
  all_goals (try simp +arith [List.length_drop])
  all_goals omega

/-- Normalize a fraction so that its denominator is positive; fails on `0`. -/
private def mkRational (num den : Int) : Option Literal :=
  if den == 0 then none
  else if den < 0 then some (.rational (-num) (-den))
  else some (.rational num den)

/-- A decimal literal such as `1.5` or `-0.25`, as a fraction. -/
private def ofDecimal (s : String) : Option Literal := do
  let [intPart, fracPart] := s.splitOn "." | none
  if fracPart.isEmpty then none
  let sign := if intPart.startsWith "-" then -1 else 1
  let intPart := if intPart.startsWith "-" then (intPart.drop 1).toString else intPart
  let whole ← digitsToNat 10 decDigit intPart.toList
  let frac ← digitsToNat 10 decDigit fracPart.toList
  let scale := 10 ^ fracPart.length
  mkRational (sign * (Int.ofNat (whole * scale + frac))) (Int.ofNat scale)

/-- Lex an atom as a literal, if it is one. -/
def ofString (value : String) : Option Literal :=
  if value.startsWith "\"" && value.endsWith "\"" && value.length ≥ 2 then
    (decodeEscapes (unescape (value.drop 1).toString.toList.dropLast)).map
      fun cs => .string (String.ofList cs)
  else if value.startsWith "#b" then
    let digits := (value.drop 2).toString.toList
    (digitsToNat 2 binDigit digits).map (.binary digits.length)
  else if value.startsWith "#x" then
    let digits := (value.drop 2).toString.toList
    (digitsToNat 16 hexDigit digits).map (.binary (4 * digits.length))
  else
    match value.splitOn "/" with
    | [num, den] => do mkRational (← num.toInt?) (← den.toInt?)
    | _ => match value.toInt? with
      | some n => some (.numeral n)
      | none => ofDecimal value

end Literal

/-!
## Datatypes
-/

/-- A constructor of a datatype: its name and its selectors, with their argument types. -/
structure ConsSpec (T : Type) where
  name : String
  selectors : List (String × T)

/-- One datatype of a `declare-datatypes` block. -/
structure DatatypeSpec (T : Type) where
  name : String
  constructors : List (ConsSpec T)

/-- How a calculus represents the contents of a `declare-datatypes` block. -/
structure DatatypeOps (T : Type) where
  /--
  A reference to a datatype of the block currently being declared.  Occurrences
  of the block's own datatypes in its constructors' argument types are parsed as
  such references, since the block is not yet built when they are read.
  -/
  mkRef : String → T
  /--
  The bindings (one per sort, constructor and selector) introduced by a block.
  The constructors of a datatype, and the selectors of a constructor, are in
  declaration order; the datatypes are in the order `productiveOrder` settled
  on, which need not be the one they were declared in.
  -/
  mkDecls : List (DatatypeSpec T) → Option (List (String × T))

/-!
## Configuration
-/

/--
Everything the parser needs to know about a particular calculus.

`T` is the type of terms, `R` of proof rules, `C` of commands and `CL` of
command lists.
-/
structure Config (T R C CL : Type) where
  /-- The operators of the signature. -/
  ops : List (OpDecl T)
  /-- Interpret a literal (numeral, rational, string, bit-vector) as a term. -/
  parseLiteral : Literal → Option T
  /-- Whether a term is the sort of sorts, i.e. whether `declare-const` declares a sort. -/
  isType : T → Bool
  /--
  The sort of sorts, from which the type of a `declare-sort` is built.  It is not syntax: `Type` is an ordinary symbol name.
  -/
  mkType : T
  /--
  Whether the calculus can make sense of a term -- for a typed calculus, whether
  it has a type.  This is only used to choose between the several things a name
  may denote: SMT-LIB lets a symbol be declared more than once at different
  types, and lets a user symbol carry the name of one of the signature's own
  operators, so a name can be ambiguous and only its use decides.  The default
  tells the candidates apart not at all, which leaves the most recent
  declaration winning, as it did when a name denoted only one thing.
  -/
  wellTyped : T → Bool := fun _ => true
  /-- The `n`-th uninterpreted sort. -/
  mkUSort : Nat → T
  /-- The `n`-th uninterpreted constant, of the given type. -/
  mkUConst : Nat → T → T
  /-- Function application. -/
  apply : T → T → T
  /-- Interpret the name of a proof rule. -/
  parseRule : String → Option R
  mkAssumePush : T → C
  /-- `mkStep rule args premises`, where premises are offsets into the proof stack. -/
  mkStep : R → List T → List Nat → C
  mkStepPop : R → List T → List Nat → C
  mkCmdList : List C → CL
  /-- Datatype support; `none` if the calculus has no datatypes. -/
  datatypes : Option (DatatypeOps T) := none

/-!
## Parser state
-/

/--
A `define` that takes parameters.  Eunoia has no lambda, so such a definition is
a macro: its body is kept as an s-expression and read again wherever the defined
symbol is applied, with the parameters bound to the arguments given there.
-/
structure Macro where
  /-- The names of the parameters, in order; their declared types are unused. -/
  params : List String
  body : Sexp

structure State (T : Type) where
  /-- Number of uninterpreted sorts declared so far. -/
  usCount : Nat := 0
  /-- Number of uninterpreted constants declared so far. -/
  ufCount : Nat := 0
  /-- Number of proof-stack entries pushed so far. -/
  stackHeight : Nat := 0
  /-- Heights of the currently open `assume-push` scopes, innermost first. -/
  pushHeights : List Nat := []
  /-- Position in the proof stack of each proof step, by name. -/
  idToPos : Std.HashMap String Nat := {}
  /--
  Terms bound by `declare-const`/`define`, by name, most recently bound first.
  A name may be bound more than once: SMT-LIB allows a symbol to be declared at
  several types, and `resolve` picks between them.  A `let` binding or a macro
  parameter instead *shadows*, so it is bound as the only term of its name.
  -/
  terms : Std.HashMap String (List T) := {}
  /-- Macros introduced by a `define` with parameters, by name. -/
  macros : Std.HashMap String Macro := {}
  /-- The macros currently being expanded, used to reject recursive `define`s. -/
  expanding : List String := []
  /-- The operators of the signature, indexed by name. -/
  ops : Std.HashMap String (List (OpDecl T)) := {}

abbrev ParserM (T : Type) := StateT (State T) (Except String)

def State.ofOps (ops : List (OpDecl T)) : State T :=
  { ops := ops.foldl (fun m d => m.insert d.name (m.getD d.name [] ++ [d])) {} }

/-- Record a proof step named `id` at the top of the proof stack. -/
def registerStep (id : String) : ParserM T Unit :=
  modify fun s =>
    { s with idToPos := s.idToPos.insert id s.stackHeight, stackHeight := s.stackHeight + 1 }

/-- Record an `assume-push` step and open a scope at the current height. -/
def registerAssumePush (id : String) : ParserM T Unit :=
  modify fun s =>
    { s with
      idToPos := s.idToPos.insert id s.stackHeight,
      stackHeight := s.stackHeight + 1,
      pushHeights := s.stackHeight :: s.pushHeights }

/-- Record a `step-pop` step, closing the innermost open scope. -/
def registerStepPop (id : String) : ParserM T Unit := do
  let s ← get
  let pushPos :: pushRest := s.pushHeights | throw "Error: step-pop without matching assume-push"
  modify fun s =>
    { s with
      idToPos := s.idToPos.insert id pushPos,
      stackHeight := pushPos + 1,
      pushHeights := pushRest }

/-!
## Terms
-/

/-- Recognize `f` or `(_ f i₁ … i_k)` as the head of an application. -/
def asOpHead : Sexp → Option (String × List Sexp)
  | .atom name => some (name, [])
  | .expr (.atom "_" :: .atom name :: idxs) => some (name, idxs)
  | _ => none

/-- Select the overload of an operator matching the given index and argument counts. -/
def resolveOp (decls : List (OpDecl T)) (numIndices numArgs : Nat) : Option (OpDecl T) :=
  let decls := decls.filter (·.indexArity == numIndices)
  -- An exact-arity overload always wins, so that e.g. `(- x)` is unary negation
  -- even though `-` is also declared as an n-ary operator.
  let isExact (d : OpDecl T) : Bool := match d.arity with
    | .exact n => n == numArgs
    | _ => false
  match decls.find? isExact with
  | some d => some d
  | none => decls.find? (·.arity.admits numArgs)

/--
Select an indexed operator written in Eunoia's flat form, `(f i₁ … iₖ a₁ … aₙ)`.
The indices are part of the ordinary argument list in that syntax.  Prefer an
exactly saturated overload, as `resolveOp` does for explicit indexed syntax.
-/
def resolveFlatOp (decls : List (OpDecl T)) (numArgs : Nat) : Option (OpDecl T) :=
  let decls := decls.filter fun d =>
    d.indexArity > 0 && d.indexArity ≤ numArgs &&
      d.arity.admits (numArgs - d.indexArity)
  let isExact (d : OpDecl T) : Bool := match d.arity with
    | .exact n => n == numArgs - d.indexArity
    | _ => false
  match decls.find? isExact with
  | some d => some d
  | none => decls.head?

/--
Choose between the terms a name may denote, given in order of preference: the
first the calculus finds well typed, or the first outright when none is or when
there is nothing to choose.  A name that denotes just one term is returned
untouched, so a partial application -- which a calculus need not give a type --
is only ever rejected here when there was an alternative to it.
-/
def resolve (cfg : Config T R C CL) : List T → Option T
  | [] => none
  | [t] => some t
  | ts => ts.find? cfg.wellTyped <|> ts.head?

mutual

/-- Parse a term, reporting the failing subterm on error. -/
partial def parseTerm (cfg : Config T R C CL) (s : Sexp) : ParserM T T := do
  try
    parseTermCore cfg s
  catch e =>
    throw s!"{e}\nError: failed to parse term {s}"

partial def parseTermCore (cfg : Config T R C CL) : Sexp → ParserM T T
  | .atom a => do
    -- A bare operator name denotes the (possibly partially applied) head term.
    let decls := ((← get).ops.getD a []).filter (·.indexArity == 0)
    let isNullary (d : OpDecl T) : Bool := match d.arity with
      | .exact 0 => true
      | _ => false
    let opCand : Option T := do
      let d ← decls.find? isNullary <|> decls.head?
      d.build []
    let bound := (← get).terms.getD a []
    if opCand.isNone && !decls.isEmpty && bound.isEmpty then
      throw s!"Error: could not build operator {a}"
    if let some t := resolve cfg (bound ++ opCand.toList) then
      return t
    if let some t := (Literal.ofString a).bind cfg.parseLiteral then
      return t
    if let some m := (← get).macros[a]? then
      throw s!"Error: {a} takes {m.params.length} arguments and cannot be used unapplied"
    if a.startsWith "\"" && a.endsWith "\"" && a.length ≥ 2 then
      -- The only string literal `Literal.ofString` refuses is one whose `\u`
      -- escape names a code point Lean has no `Char` for; see `decodeEscapes`.
      throw s!"Error: the string literal {a} names a code point that is not a \
                character, which Logos cannot represent"
    throw s!"Error: unknown identifier {a}"
  | .expr [] => throw "Error: empty s-expression"
  | .expr [.atom "as", .atom name, ty] =>
    -- CPC uses SMT-LIB's type-ascription syntax for indexed constants such as
    -- `(as set.empty (Set Int))`; its sort is the operator's Eunoia index.
    parseApp cfg name [ty] []
  | .expr [.atom "let", .expr bindings, body] =>
    parseLet cfg bindings body
  | .expr (.atom "_" :: rest) =>
    parseUnderscoreExpr cfg rest []
  | .expr (f :: args) => do
    let args ← args.mapM (parseTerm cfg)
    match f with
    | .expr (.atom "_" :: rest) =>
      parseUnderscoreExpr cfg rest args
    | .expr (.atom "as" :: _) =>
      -- A type ascription is a qualified identifier, so it may head an
      -- application.
      return args.foldl cfg.apply (← parseTerm cfg f)
    | _ =>
      match asOpHead f with
      | some (name, idxs) => parseApp cfg name idxs args
      | none =>
        -- Eunoia marks a curried application with `_`, so the head of an
        -- application is a name, an indexed symbol or a type ascription and
        -- nothing else.  Reading a parenthesized head as a curried application
        -- would accept files Ethos refuses to parse.
        throw s!"Error: expected a symbol, an indexed symbol or a type \
                  ascription as the head of an application, got {f}"

/--
Parse an expression headed by `_`, applied to `args`.  Eunoia writes both an
indexed operator and a curried application with `_`, and only a name can be
indexed: `(_ f a₁ … aₙ)` whose head is itself an expression is an application,
as cvc5 prints partially applied functions.
-/
partial def parseUnderscoreExpr (cfg : Config T R C CL) (rest : List Sexp)
    (args : List T) : ParserM T T := do
  match rest with
  | .atom name :: idxs => parseUnderscoreApp cfg name idxs args
  | f :: inner => do
    let head ← parseTerm cfg f
    let inner ← inner.mapM (parseTerm cfg)
    return (inner ++ args).foldl cfg.apply head
  | [] => throw "Error: expected an operator name or a term after _"

/--
Parse an expression headed by `_`.  If the name has an operator declaration
with the given number of indices, this is SMT-style indexed syntax such as
`(_ extract 1 0)`.  Otherwise `_` is Eunoia's higher-order application marker,
so `(_ BitVec 4)` is parsed like `(BitVec 4)`.  Any outer arguments are then
applied to the resulting term.
-/
partial def parseUnderscoreApp (cfg : Config T R C CL) (name : String)
    (idxs : List Sexp) (args : List T) : ParserM T T := do
  let decls := (← get).ops.getD name []
  if decls.any (·.indexArity == idxs.length) then
    parseApp cfg name idxs args
  else
    let head ← parseTerm cfg (.expr (.atom name :: idxs))
    return args.foldl cfg.apply head

/--
Build the application of the operator (or declared symbol) `name`, indexed by
`idxs`, to the already-parsed `args`.
-/
partial def parseApp (cfg : Config T R C CL) (name : String) (idxs : List Sexp)
    (args : List T) : ParserM T T := do
  if let some m := (← get).macros[name]? then
    if !idxs.isEmpty then
      throw s!"Error: {name} is defined by define and cannot be indexed"
    if args.length < m.params.length then
      throw s!"Error: {name} takes {m.params.length} arguments but is applied to {args.length}"
    -- A macro whose body denotes a function may be applied to further arguments.
    let (args, extra) := args.splitAt m.params.length
    return extra.foldl cfg.apply (← expandMacro cfg name m args)
  let decls := (← get).ops.getD name []
  let bound := (← get).terms.getD name []
  -- A symbol a proof declares takes no indices, so indexed syntax is an
  -- operator and nothing else.
  let boundCands := if idxs.isEmpty then bound.map (fun t => args.foldl cfg.apply t) else []
  let opCand : Option T ←
    if decls.isEmpty then pure none else do
      let idxTerms ← idxs.mapM (parseTerm cfg)
      if let some d := resolveOp decls idxTerms.length args.length then
        pure (some (← buildOpApp cfg name d idxTerms args))
      -- `declare-parameterized-const` uses ordinary arguments for its indices,
      -- and this is the flat form emitted by cvc5: `(extract 1 0 x)` rather than
      -- `((_ extract 1 0) x)`.  Explicit indexed syntax above takes precedence.
      else if let some d := if idxs.isEmpty then resolveFlatOp decls args.length else none then
        let (flatIdxs, flatArgs) := args.splitAt d.indexArity
        pure (some (← buildOpApp cfg name d flatIdxs flatArgs))
      else pure none
  -- A symbol the proof declares shadows the signature operator of the same name,
  -- so its reading is tried first; the operator is still used when the proof's
  -- declaration gives no well-typed reading of this application.
  if let some t := resolve cfg (boundCands ++ opCand.toList) then
    return t
  if !decls.isEmpty then
    throw s!"Error: no declaration of {name} takes {idxs.length} indices and \
              {args.length} arguments"
  if !idxs.isEmpty then
    throw s!"Error: unknown indexed operator {name}"
  return args.foldl cfg.apply (← parseTermCore cfg (.atom name))

/-- Build an already-resolved operator application. -/
partial def buildOpApp (cfg : Config T R C CL) (name : String) (d : OpDecl T)
    (idxs args : List T) : ParserM T T := do
  let some head := d.build idxs | throw s!"Error: bad indices for operator {name}"
  let some t := mkOpApp cfg.apply d.arity head args
    | throw s!"Error: wrong number of arguments ({args.length}) for operator {name}"
  return t

/--
Parse an SMT-LIB `let`.  Binding values are read in the surrounding scope
(parallel-binding semantics), then all names are in scope only for the body.
-/
partial def parseLet (cfg : Config T R C CL) (bindings : List Sexp)
    (body : Sexp) : ParserM T T := do
  let bindings : List (String × Sexp) ← bindings.mapM fun
    | .expr [.atom name, value] => return (name, value)
    | binding => throw s!"Error: expected a let binding, got {binding}"
  let values ← bindings.mapM fun (name, value) => do
    return (name, ← parseTerm cfg value)
  let saved := (← get).terms
  modify fun s =>
    { s with terms := values.foldl (fun terms (name, value) =>
        terms.insert name [value]) s.terms }
  let restore : ParserM T Unit := modify fun s => { s with terms := saved }
  try
    let result ← parseTerm cfg body
    restore
    return result
  catch e =>
    restore
    throw e

/--
Expand the macro `name` at a use site: read its body with the parameters bound to
`args`.  The bindings are undone afterwards, so a parameter shadows any symbol of
the same name only within the body.
-/
partial def expandMacro (cfg : Config T R C CL) (name : String) (m : Macro)
    (args : List T) : ParserM T T := do
  if (← get).expanding.contains name then
    throw s!"Error: recursive define {name}"
  let saved := (← get).terms
  modify fun s =>
    { s with
      terms := (m.params.zip args).foldl (fun ts (p, t) => ts.insert p [t]) s.terms,
      expanding := name :: s.expanding }
  let restore : ParserM T Unit :=
    modify fun s => { s with terms := saved, expanding := s.expanding.tail }
  try
    let t ← parseTerm cfg m.body
    restore
    return t
  catch e =>
    restore
    throw e

end

/-!
## Commands
-/

def parseName : Sexp → ParserM T String
  | .atom a => return a
  | s => throw s!"Error: expected a name, got {s}"

/-- Parse `(name arity)` from the sort list of a `declare-datatypes` block. -/
def parseDatatypeName : Sexp → ParserM T String
  | .expr [.atom name, .atom arity] =>
    if arity == "0" then return name
    else throw s!"Error: parametric datatype {name} (arity {arity}) is not supported"
  | s => throw s!"Error: expected a datatype name and arity, got {s}"

/-- Parse one constructor, `(cname (sel type) …)`. -/
def parseConsSpec (cfg : Config T R C CL) : Sexp → ParserM T (ConsSpec T)
  | .expr (.atom name :: sels) => do
    let selectors ← sels.mapM fun
      | .expr [.atom sel, ty] => do return (sel, ← parseTerm cfg ty)
      | s => throw s!"Error: expected a selector and its type, got {s}"
    return { name, selectors }
  | s => throw s!"Error: expected a datatype constructor, got {s}"

/--
The datatypes of the block that one constructor's fields reference.  A field
references one of them exactly when its type is written as the bare name of a
datatype of the block: those become the block's type references, and they are
the only fields the specification follows to witness a datatype.
-/
private def consRefs (names : List String) : Sexp → List String
  | .expr (_ :: sels) =>
    sels.filterMap fun
      | .expr [_, .atom ty] => if names.contains ty then some ty else none
      | _ => none
  | _ => []

/-- `consRefs` of each constructor of one datatype body. -/
private def bodyRefs (names : List String) : Sexp → List (List String)
  | .expr ctors => ctors.map (consRefs names)
  | _ => []

/--
Whether a datatype whose constructors reference `ctors` can be given a value
using only the datatypes in `placed`: one of its constructors has to reference
nothing outside them.
-/
private def witnessableBy (placed : List String) (ctors : List (List String)) : Bool :=
  ctors.any fun refs => refs.all placed.contains

/--
The order a `declare-datatypes` block has to be given in, as a permutation of
the positions of `dts`, which pairs each datatype's name with the references of
each of its constructors.

The specification witnesses a datatype only through references to entries
declared *later* in its block (`smt_type_default`, see
`docs/smt-model-definitions.pdf`), so a block that declares a datatype before
the ones witnessing it has no inhabited datatype at all, and then every type it
declares is ill-formed -- including the ones that are witnessed, since
well-formedness of a datatype asks it of the whole block.  Nothing else about a
block depends on the order it is written in, so the parser puts it in one that
works.

Datatypes are ranked by the round in which they become witnessable: those with
a constructor referencing nothing else in the block are rank 1, those witnessed
by rank-1 datatypes are rank 2, and so on.  Listing them by *decreasing* rank is
productive, because a datatype's witnessing constructor references strictly
lower ranks only, which then come after it.  Ranks are found by saturation, one
round per pass, which needs no more passes than there are datatypes.  Equal
ranks keep the order they were written in, so a block that is already in a
productive order is left exactly as it was.  Datatypes that never become
witnessable have no finite value; they are left at the front, being rejected
whatever the order.
-/
private def productiveOrder (dts : List (String × List (List String))) : List Nat :=
  go dts.length [] dts.zipIdx []
where
  go : Nat → List String → List ((String × List (List String)) × Nat) → List Nat → List Nat
    | 0, _, remaining, order => remaining.map (·.2) ++ order
    | fuel + 1, placed, remaining, order =>
      let (ready, rest) := remaining.partition fun d => witnessableBy placed d.1.2
      if ready.isEmpty then remaining.map (·.2) ++ order
      else go fuel (placed ++ ready.map (·.1.1)) rest (ready.map (·.2) ++ order)

/--
Parse a `declare-datatypes` block and bind the sorts, constructors and selectors
it introduces.
-/
def parseDatatypes (cfg : Config T R C CL) (sorts bodies : List Sexp) : ParserM T Unit := do
  let some dtOps := cfg.datatypes
    | throw "Error: this calculus does not support declare-datatypes"
  let names ← sorts.mapM parseDatatypeName
  if names.length != bodies.length then
    throw s!"Error: {names.length} datatype names but {bodies.length} datatype bodies"
  -- While the block is being read, occurrences of its own datatypes in the
  -- constructors' argument types are parsed as references.
  let saved := (← get).terms
  modify fun s =>
    { s with terms := names.foldl (fun m n => m.insert n [dtOps.mkRef n]) s.terms }
  let specs ← (names.zip bodies).mapM fun (name, body) => do
    let .expr ctors := body | throw s!"Error: expected a list of constructors, got {body}"
    if let .atom "par" :: _ := ctors then
      throw s!"Error: parametric datatype {name} is not supported"
    let constructors ← ctors.mapM (parseConsSpec cfg)
    return ({ name, constructors } : DatatypeSpec T)
  modify fun s => { s with terms := saved }
  -- The block is built in an order that witnesses its datatypes, which is not
  -- necessarily the one it was written in; see `productiveOrder`.
  let order := productiveOrder (names.zip (bodies.map (bodyRefs names)))
  let some bindings := dtOps.mkDecls (order.filterMap (specs[·]?))
    | throw s!"Error: could not build the declaration of {String.intercalate ", " names}"
  modify fun s =>
    { s with terms := bindings.foldl (fun m (n, t) => m.insert n (t :: m.getD n [])) s.terms }

/-!
## Declarations
-/

/-- Bind `name` to a fresh uninterpreted sort or constant, according to `ty`. -/
def declareSymbol (cfg : Config T R C CL) (name : String) (ty : T) : ParserM T Unit :=
  if cfg.isType ty then
    modify fun s =>
      { s with
        usCount := s.usCount + 1,
        terms := s.terms.insert name
          (cfg.mkUSort (s.usCount + 1) :: s.terms.getD name []) }
  else
    modify fun s =>
      { s with
        ufCount := s.ufCount + 1,
        terms := s.terms.insert name
          (cfg.mkUConst (s.ufCount + 1) ty :: s.terms.getD name []) }

/--
The type `(-> t₁ … tₙ res)` of a symbol declared by `declare-fun`.  It is built from the signature's own `->` operator, so a
calculus without function types simply rejects these commands with more than
zero arguments.
-/
def parseFunType (cfg : Config T R C CL) (args : List Sexp) (res : Sexp) : ParserM T T :=
  match args with
  | [] => parseTerm cfg res
  | args => parseTerm cfg (.expr (.atom "->" :: (args ++ [res])))

/--
The type `(-> Type … Type)` of a sort of arity `n`, declared by `declare-sort`,
built from the sort of sorts itself (`Config.mkType`).
-/
def parseSortType (cfg : Config T R C CL) (n : Nat) : ParserM T T :=
  match n with
  | 0 => return cfg.mkType
  | n + 1 => do
    let arrow ← parseTerm cfg (.atom "->")
    return (rightAssoc cfg.apply arrow (List.replicate (n + 2) cfg.mkType)).getD cfg.mkType

/--
Parse the parameter list of a `define`.  Only the parameter names are recorded:
the body is read where the macro is used, so its parameters are given the types
of the arguments they stand for.
-/
def parseMacroParams : List Sexp → ParserM T (List String)
  | [] => return []
  | .expr (.atom name :: _ :: _) :: rest => return name :: (← parseMacroParams rest)
  | s :: _ => throw s!"Error: expected a parameter and its type, got {s}"

/-- Parse the arity of a `declare-sort`. -/
def parseArity : Sexp → ParserM T Nat
  | .atom a =>
    match a.toNat? with
    | some n => return n
    | none => throw s!"Error: expected a sort arity, got {a}"
  | s => throw s!"Error: expected a sort arity, got {s}"

/-- Resolve a premise, given by step name, to its offset from the top of the stack. -/
def parsePremise (p : Sexp) : ParserM T Nat := do
  let name ← parseName p
  let some pos := (← get).idToPos[name]? | throw s!"Error: unknown premise {name}"
  let height := (← get).stackHeight
  if height ≤ pos then throw s!"Error: premise {name} is not in scope"
  return height - pos - 1

/-- The `:rule`/`:premises`/`:args` annotations of a `step` or `step-pop`. -/
structure StepAnnots where
  rule : Option String := none
  premises : List Sexp := []
  args : List Sexp := []

def parseAnnots (ctx : Sexp) : List Sexp → ParserM T StepAnnots :=
  go {}
where
  go (acc : StepAnnots) : List Sexp → ParserM T StepAnnots
    | [] => return acc
    | .atom ":rule" :: v :: rest => do go { acc with rule := some (← parseName v) } rest
    | .atom ":premises" :: .expr ps :: rest => go { acc with premises := ps } rest
    | .atom ":args" :: .expr as :: rest => go { acc with args := as } rest
    | k :: _ => throw s!"Error: unexpected annotation {k} in {ctx}"

/--
Drop the conclusion of a step if one is present; Logos recomputes conclusions
from the rule, so the printed one is redundant.
-/
def dropConclusion : List Sexp → List Sexp
  | [] => []
  | c :: rest =>
    match c with
    | .atom a => if a.startsWith ":" then c :: rest else rest
    | .expr _ => rest

/-- The result of parsing one top-level command. -/
inductive Command (T C : Type) where
  /-- An `assume`, which becomes an assumption of the proof. -/
  | assumption (t : T)
  /-- A proof-stack command. -/
  | cmd (c : C)
  /--
  A command that does not extend the proof: a declaration or definition, which
  only updates the parser state, or an ignored command such as `include`.
  -/
  | decl

def parseCommand (cfg : Config T R C CL) (s : Sexp) : ParserM T (Command T C) := do
  try
    go s
  catch e =>
    throw s!"{e}\nError: failed to parse command {s}"
where
  annots (rest : List Sexp) : ParserM T (R × List T × List Nat) := do
    let annots ← parseAnnots s (dropConclusion rest)
    let some ruleName := annots.rule | throw s!"Error: missing :rule in {s}"
    let some rule := cfg.parseRule ruleName | throw s!"Error: unknown rule {ruleName}"
    let premises ← annots.premises.mapM parsePremise
    let args ← annots.args.mapM (parseTerm cfg)
    return (rule, args, premises)
  go : Sexp → ParserM T (Command T C)
    | .expr [.atom "declare-const", name, ty] => do
      declareSymbol cfg (← parseName name) (← parseTerm cfg ty)
      return .decl
    | .expr [.atom "declare-fun", name, .expr args, ty] => do
      declareSymbol cfg (← parseName name) (← parseFunType cfg args ty)
      return .decl
    | .expr [.atom "declare-sort", name, arity] => do
      -- `(declare-sort S n)` declares a symbol of type `(-> Type … Type)`; for
      -- `n = 0` that is `Type` itself, i.e. an uninterpreted sort.
      let arity ← parseArity arity
      declareSymbol cfg (← parseName name) (← parseSortType cfg arity)
      return .decl
    | .expr [.atom "declare-datatypes", .expr sorts, .expr bodies] => do
      parseDatatypes cfg sorts bodies
      return .decl
    | .expr [.atom "define", name, .expr [], body] => do
      -- A definition without parameters is read once, where it is given.
      let name ← parseName name
      let body ← parseTerm cfg body
      modify fun s => { s with terms := s.terms.insert name (body :: s.terms.getD name []) }
      return .decl
    | .expr [.atom "define", name, .expr params, body] => do
      let name ← parseName name
      let params ← parseMacroParams params
      modify fun s => { s with macros := s.macros.insert name { params, body } }
      return .decl
    | .expr (.atom "include" :: _) =>
      -- Logos has the whole signature built in, so included files are ignored.
      return .decl
    | .expr (.atom "reference" :: _) =>
      -- The input problem is not checked against, so references are ignored.
      return .decl
    | .expr [.atom "assume", name, t] => do
      let name ← parseName name
      let t ← parseTerm cfg t
      registerStep name
      return .assumption t
    | .expr [.atom "assume-push", name, t] => do
      let name ← parseName name
      let t ← parseTerm cfg t
      registerAssumePush name
      return .cmd (cfg.mkAssumePush t)
    | .expr (.atom "step" :: name :: rest) => do
      let name ← parseName name
      let (rule, args, premises) ← annots rest
      registerStep name
      return .cmd (cfg.mkStep rule args premises)
    | .expr (.atom "step-pop" :: name :: rest) => do
      let name ← parseName name
      let (rule, args, premises) ← annots rest
      registerStepPop name
      return .cmd (cfg.mkStepPop rule args premises)
    | s => throw s!"Error: unrecognized command {s}, expected one of declare-const, \
                    declare-fun, declare-sort, declare-datatypes, define, \
                    include, reference, assume, assume-push, step or step-pop"

/--
A proof is a bare sequence of commands.  cvc5 prints one wrapped in the
parentheses of the `get-proof` response it is answering, and that wrapper is not
a Eunoia command: Ethos refuses such a file at its first token, and so does this
parser.  The shape is recognized only to say so, since the catch-all of
`parseCommand` would otherwise quote the whole proof back as the offending
command.
-/
private def isWrappedProof : List Sexp → Bool
  | [.expr (.expr _ :: _)] => true
  | _ => false

def parseCommands (cfg : Config T R C CL) (ss : List Sexp) : ParserM T (List T × CL) := do
  if isWrappedProof ss then
    throw "Error: the proof is wrapped in a pair of parentheses, which is not a \
           Eunoia command; cvc5 emits them around the proof as the response to \
           `get-proof`, so strip them along with the leading `unsat` line"
  let mut assums := #[]
  let mut cmds := #[]
  for s in ss do
    match ← parseCommand cfg s with
    | .assumption t =>
      if !cmds.isEmpty then
        throw s!"Error: assumption after the first proof step: {s}"
      assums := assums.push t
    | .cmd c => cmds := cmds.push c
    | .decl => pure ()
  return (assums.toList, cfg.mkCmdList cmds.toList)

/-- Parse a proof into its assumptions and its list of commands. -/
def parseProof (cfg : Config T R C CL) (input : String) : Except String (List T × CL) := do
  let ss ← Sexp.Parser.manySexps!.run input
  (parseCommands cfg ss).run' (State.ofOps cfg.ops)

end Logos.Parser
