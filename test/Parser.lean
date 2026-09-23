module

public import Logos.Parser
import all Logos.Parser

namespace Logos.Parser.Tests

private inductive TestTerm where
  | atom (name : String)
  | app (fn arg : TestTerm)
  | gathered (args : List TestTerm)
  | type
  | usort (i : Nat)
  | uconst (i : Nat) (ty : TestTerm)
deriving BEq, Repr

private def mkApply : TestTerm → TestTerm → TestTerm := .app
private def gather : List TestTerm → TestTerm := .gathered

private def f : TestTerm := .atom "f"
private def a : TestTerm := .atom "a"
private def b : TestTerm := .atom "b"

example :
    mkOpApp mkApply (.argList gather) f [a, b] =
      some (.app f (.gathered [a, b])) := by
  rfl

example : mkOpApp mkApply (.argList gather) f [] = none := by
  rfl

example : (Arity.argList gather).admits 0 = false := by
  rfl

example : (Arity.argList gather).admits 1 = true := by
  rfl

example : (Arity.argList gather).admits 3 = true := by
  rfl

/-!
## Literals

The `\u` escapes of a string literal belong to the SMT-LIB theory of strings, so
they are decoded here rather than left as the characters they are written with.
The behaviour on a malformed escape follows Ethos: it is not an escape, and
stands for its own characters.
-/

#guard Literal.ofString "\"a\"" == some (.string "a")
#guard Literal.ofString "\"\\u{a}\"" == some (.string "\n")
#guard Literal.ofString "\"\\u0041\"" == some (.string "A")
#guard Literal.ofString "\"ab\\u{63}de\"" == some (.string "abcde")

-- `""` is the one escape of the syntax, and is undone before `\u` is read.
#guard Literal.ofString "\"a\"\"b\"" == some (.string "a\"b")

-- Not escapes: no digits, an unterminated brace, more than five digits, fewer
-- than four digits without a brace, and a code point above the largest one.
#guard Literal.ofString "\"\\u{}\"" == some (.string "\\u{}")
#guard Literal.ofString "\"\\u{61\"" == some (.string "\\u{61")
#guard Literal.ofString "\"\\u{000061}\"" == some (.string "\\u{000061}")
#guard Literal.ofString "\"\\u004\"" == some (.string "\\u004")
#guard Literal.ofString "\"\\u{30000}\"" == some (.string "\\u{30000}")

-- The largest code point there is, and a surrogate, which has no `Char`.
#guard Literal.ofString "\"\\u{2ffff}\"" == some (.string (String.singleton (Char.ofNat 0x2ffff)))
#guard Literal.ofString "\"\\uD800\"" == none

/-!
## Commands

A minimal signature, with just enough operators to write the types of declared
symbols, exercises the command grammar independently of any calculus.
-/

private abbrev TestCmd := String × List TestTerm × List Nat

private def testConfig : Config TestTerm String TestCmd (List TestCmd) where
  ops := [
    { name := "->", arity := .rightAssoc, build := fun | [] => some (.atom "->") | _ => none },
    { name := "indexed", indexArity := 1, arity := .exact 1,
      build := fun | [i] => some (.app (.atom "indexed") i) | _ => none }
  ]
  parseLiteral := fun _ => none
  isType := (· == .type)
  mkType := .type
  mkUSort := .usort
  mkUConst := .uconst
  apply := .app
  parseRule := some
  mkAssumePush := fun t => ("assume-push", [t], [])
  mkStep := fun rule args premises => (rule, args, premises)
  mkStepPop := fun rule args premises => ("pop:" ++ rule, args, premises)
  mkCmdList := id

/-- The assumptions of a parsed proof, or `none` if it does not parse. -/
private def assumptions (input : String) : Option (List TestTerm) :=
  match parseProof testConfig input with
  | .ok (assums, _) => some assums
  | .error _ => none

/-!
### Choosing between the readings of a name

`resolve` is how the several declarations of one name are told apart.  A
calculus that cannot tell them apart -- the default `wellTyped` -- leaves the
first, which is the most recently declared.
-/

private def typedConfig : Config TestTerm String TestCmd (List TestCmd) :=
  { testConfig with wellTyped := (· == a) }

#guard resolve typedConfig ([] : List TestTerm) == none
-- A name with one reading is never rejected, well typed or not.
#guard resolve typedConfig [b] == some b
#guard resolve typedConfig [b, a] == some a
-- With no well-typed reading to be had, the first stands, and so does the error
-- it leads to.
#guard resolve typedConfig [b, f] == some b
#guard resolve testConfig [b, a] == some b

private def arrow (dom cod : TestTerm) : TestTerm := .app (.app (.atom "->") dom) cod

-- `include` is ignored, `declare-sort` declares an uninterpreted sort and
-- `declare-fun` a symbol of the corresponding function type.
#guard assumptions
    "(include \"../theories/Builtin.eo\")
     (declare-sort U 0)
     (declare-fun f (U) U)
     (declare-const x U)
     (assume @p0 (f x))"
  == some [.app (.uconst 1 (arrow (.usort 1) (.usort 1))) (.uconst 2 (.usort 1))]

-- A `declare-sort` of non-zero arity declares a symbol of type `(-> Type … Type)`.
#guard assumptions
    "(declare-sort U 0)
     (declare-sort Box 1)
     (declare-const b (Box U))
     (assume @p0 b)"
  == some [.uconst 2 (.app (.uconst 1 (arrow .type .type)) (.usort 1))]

-- When no indexed declaration matches, `_` is a higher-order application
-- marker: `(_ Box U)` and `(Box U)` denote the same type.
#guard assumptions
    "(declare-sort U 0)
     (declare-sort Box 1)
     (declare-const b (_ Box U))
     (assume @p0 b)"
  == some [.uconst 2 (.app (.uconst 1 (arrow .type .type)) (.usort 1))]

-- `Type` is not syntax: a user symbol of that name is an ordinary sort, and does
-- not affect what a later `declare-sort` declares.
#guard assumptions
    "(declare-sort Type 0)
     (declare-sort Poly 0)
     (declare-sort Box 1)
     (declare-const x Poly)
     (assume @p0 x)"
  == some [.uconst 2 (.usort 2)]

-- `reference` is ignored as well.
#guard assumptions
    "(reference \"problem.smt2\")
     (declare-sort U 0)
     (declare-const x U)
     (assume @p0 x)"
  == some [.uconst 1 (.usort 1)]

/-!
### `define`

A `define` with parameters is a macro: it is expanded wherever it is applied.
-/

private def binary : String := "(declare-sort U 0) (declare-fun g (U U) U)
  (declare-const a U) (declare-const b U)"

private def gTy : TestTerm := arrow (.usort 1) (arrow (.usort 1) (.usort 1))

/-!
### Indexed applications and binders
-/

-- Eunoia puts indices in the ordinary argument list, whereas SMT-LIB wraps
-- them in `(_ ...)`; both spellings build the same operator application.
#guard assumptions (binary ++ "(assume @p0 (indexed a b))") ==
  assumptions (binary ++ "(assume @p0 ((_ indexed a) b))")

-- Eunoia marks a curried application with `_`, so a parenthesized head that
-- does not is rejected rather than read as one; Ethos refuses the same file.
#guard assumptions (binary ++ "(assume @p0 ((g a) b))") == none
#guard assumptions (binary ++ "(assume @p0 (_ (_ g a) b))") ==
  assumptions (binary ++ "(assume @p0 (g a b))")

-- `let` bindings are parallel, and their scope ends after the body.
#guard assumptions (binary ++
    "(assume @p0 (let ((a b) (b a)) (g a b))) (assume @p1 (g a b))") ==
  assumptions (binary ++ "(assume @p0 (g b a)) (assume @p1 (g a b))")

-- The body is read with the parameters bound to the arguments at the use site.
#guard assumptions (binary ++ "(define swap ((x U) (y U)) (g y x)) (assume @p0 (swap a b))")
  == some [.app (.app (.uconst 1 gTy) (.uconst 3 (.usort 1))) (.uconst 2 (.usort 1))]

-- Macros may be used in the body of another macro.
#guard assumptions (binary ++
    "(define dup ((x U)) (g x x)) (define dupA () (dup a)) (assume @p0 (dupA))")
  == some [.app (.app (.uconst 1 gTy) (.uconst 2 (.usort 1))) (.uconst 2 (.usort 1))]

-- A parameter shadows a symbol of the same name only inside the body.
#guard assumptions (binary ++
    "(define f ((a U)) (g a a)) (assume @p0 (f b)) (assume @p1 a)")
  == some
    [.app (.app (.uconst 1 gTy) (.uconst 3 (.usort 1))) (.uconst 3 (.usort 1)),
     .uconst 2 (.usort 1)]

-- A macro whose body denotes a function may be applied to further arguments.
#guard assumptions (binary ++ "(define ap ((h U)) (g h)) (assume @p0 (ap a b))")
  == some [.app (.app (.uconst 1 gTy) (.uconst 2 (.usort 1))) (.uconst 3 (.usort 1))]

-- A macro may not be under-applied, or used unapplied.
#guard assumptions (binary ++ "(define swap ((x U) (y U)) (g y x)) (assume @p0 (swap a))")
  == none
#guard assumptions (binary ++ "(define swap ((x U) (y U)) (g y x)) (assume @p0 swap)")
  == none

-- A recursive `define` is rejected rather than expanded forever.
#guard assumptions (binary ++ "(define f ((x U)) (g x (f x))) (assume @p0 (f a))")
  == none

-- A `define` without parameters is still read where it is given.
#guard assumptions (binary ++ "(define ga () (g a a)) (assume @p0 ga)")
  == some [.app (.app (.uconst 1 gTy) (.uconst 2 (.usort 1))) (.uconst 2 (.usort 1))]

-- A name declared twice keeps both declarations; with no way to tell them
-- apart, the more recent one is what a use of the name means.
#guard assumptions
    "(declare-sort U 0)
     (declare-const x U)
     (declare-const x U)
     (assume @p0 x)"
  == some [.uconst 2 (.usort 1)]

/-!
### Declared names are symbols

A name a command or binder introduces is a symbol, as in Ethos.  A bound name is
looked up before a literal is, so accepting a literal there would change what
that literal means for the rest of the proof.
-/

#guard assumptions "(declare-sort U 0) (declare-const 5 U) (assume @p0 5)" == none
#guard assumptions "(declare-sort U 0) (declare-const #b1 U) (assume @p0 #b1)" == none
#guard assumptions (binary ++ "(declare-const :k U) (assume @p0 a)") == none
#guard assumptions (binary ++ "(declare-const \"s\" U) (assume @p0 a)") == none
#guard assumptions (binary ++ "(declare-sort 1/2 0) (assume @p0 a)") == none
#guard assumptions (binary ++ "(declare-fun 1.5 (U) U) (assume @p0 a)") == none
-- Each of those differs from an accepted proof only in the name it declares.
#guard (assumptions (binary ++ "(declare-const k U) (declare-sort h 0) (assume @p0 a)")).isSome
#guard assumptions (binary ++ "(define 7 () a) (assume @p0 7)") == none
#guard assumptions (binary ++ "(define h ((7 U)) (g a a)) (assume @p0 (h a))") == none
#guard assumptions (binary ++ "(assume @p0 (let ((7 a)) 7))") == none
-- A quoted symbol is a symbol, whatever it quotes.
#guard assumptions "(declare-sort U 0) (declare-const |5| U) (assume @p0 |5|)"
  == some [.uconst 1 (.usort 1)]

/-!
### The shape of a proof file

A proof is a bare sequence of commands.  cvc5 prints one inside the parentheses
of the `get-proof` response it is answering; that wrapper is refused rather than
unwrapped, as Ethos refuses it.
-/

-- Commands standing on their own are read.
#guard assumptions "(declare-sort U 0) (declare-const a U) (assume @p0 a)"
  == some [.uconst 1 (.usort 1)]

-- The same commands wrapped in a pair of parentheses are not.
#guard assumptions "((declare-sort U 0) (declare-const a U) (assume @p0 a))"
  == none

-- A file holding one command is that command, not a wrapper around one.
#guard assumptions "(declare-sort U 0)" == some []
#guard assumptions "((declare-sort U 0))" == none

end Logos.Parser.Tests
