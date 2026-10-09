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
      build := fun | [i] => some (.app (.atom "indexed") i) | _ => none },
    { name := "all", arity := .exact 2,
      build := fun | [] => some (.atom "all") | _ => none, binder := some gather }
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
  mkVar := some fun name ty => .app (.atom ("var " ++ name)) ty

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
### Binders

A binder applied to a sorted variable list gathers the variables it makes into
its first argument, and binds them in the rest of the application only.
-/

private def var (name : String) : TestTerm := .app (.atom ("var " ++ name)) (.usort 1)

-- A quoted symbol names the variable its bars enclose.
#guard assumptions (binary ++ "(assume @p0 (all ((x U) (|y| U)) (g x |y|)))") ==
  some [.app (.app (.atom "all") (.gathered [var "x", var "y"]))
    (.app (.app (.uconst 1 gTy) (var "x")) (var "y"))]

#guard assumptions (binary ++ "(assume @p0 (g (all ((a U)) a) a))") ==
  some [.app (.app (.uconst 1 gTy) (.app (.app (.atom "all") (.gathered [var "a"])) (var "a")))
    (.uconst 2 (.usort 1))]

-- Without a variable list, the first argument is an ordinary term.
#guard assumptions (binary ++ "(assume @p0 (all a b))") ==
  some [.app (.app (.atom "all") (.uconst 2 (.usort 1))) (.uconst 3 (.usort 1))]

-- A symbol the proof declares under the binder's name is not a binder.
#guard assumptions (binary ++ "(declare-const all U) (assume @p0 (all ((x U)) x))") == none

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

/-!
### Parametric datatypes

A calculus with parametric datatypes supplies the hooks of `DatatypeOps`.  These
record what the parser hands them: a constructor is bound to its field types,
and `elaborate` marks every application it is given.
-/

private def dtOps : DatatypeOps TestTerm where
  mkRef n := .atom s!"ref {n}"
  mkParam := some fun k => .atom s!"param {k}"
  mkDecls dts := some <| dts.flatMap fun d =>
    (d.name, .atom s!"sort {d.name}/{d.arity}") ::
      d.constructors.flatMap fun c =>
        (c.name, .app (.atom s!"cons {c.name}") (.gathered (c.selectors.map (·.2)))) ::
          c.selectors.map fun (sel, _) => (sel, .atom s!"sel {sel}")
  elaborate t := .app (.atom "elab") t
  ascribe
    | c@(.app (.atom _) _), sort => some (.app (.app (.atom "as") c) sort)
    | _, _ => none

private def dtConfig : Config TestTerm String TestCmd (List TestCmd) :=
  { testConfig with datatypes := some dtOps }

private def dtAssumptions (input : String) : Option (List TestTerm) :=
  match parseProof dtConfig input with
  | .ok (assums, _) => some assums
  | .error _ => none

private def list : String :=
  "(declare-datatypes ((List 1)) ((par (X) ((nil) (cons (head X) (tail (List X)))))))"

private def consOf (name : String) (fields : List TestTerm) : TestTerm :=
  .app (.atom s!"cons {name}") (.gathered fields)

-- A parameter is read as the parameter it is, and the datatype applied to its
-- parameters as the reference to it.
#guard dtAssumptions (list ++ "(assume @p0 cons)") ==
  some [consOf "cons" [.atom "param 0", .atom "ref List"]]

-- `declare-datatype` reads the arity from the `par`.
#guard dtAssumptions
    "(declare-datatype List (par (X) ((nil) (cons (head X) (tail (List X)))))) (assume @p0 cons)"
  == dtAssumptions (list ++ "(assume @p0 cons)")

-- Parameters are matched by position, so each body may name them differently.
#guard dtAssumptions
    "(declare-datatypes ((Tree 1) (Forest 1))
       ((par (X) ((node (val X) (kids (Forest X)))))
        (par (Y) ((leaf) (grow (t (Tree Y)) (rest (Forest Y)))))))
     (assume @p0 node) (assume @p1 grow)"
  == some [consOf "node" [.atom "param 0", .atom "ref Forest"],
           consOf "grow" [.atom "ref Tree", .atom "ref Forest"]]

-- The parameters are bound only while the block is read.
#guard dtAssumptions (list ++ "(assume @p0 X)") == none

private def listU : String := "(declare-sort U 0)" ++ list ++
  "(declare-const x U) (declare-const l (List U))"

private def listUSort : TestTerm := .app (.atom "elab") (.app (.atom "sort List/1") (.usort 1))

-- Applying the sort, applying a constructor, and applying an operator indexed
-- by a constructor are each handed to `elaborate`.
#guard dtAssumptions (listU ++ "(assume @p0 l)") == some [.uconst 2 listUSort]
#guard dtAssumptions (listU ++ "(assume @p0 (cons x l))") ==
  some [.app (.atom "elab")
    (.app (.app (consOf "cons" [.atom "param 0", .atom "ref List"]) (.uconst 1 (.usort 1)))
      (.uconst 2 listUSort))]
#guard dtAssumptions (listU ++ "(assume @p0 ((_ indexed nil) l))") ==
  some [.app (.atom "elab") (.app (.app (.atom "indexed") (consOf "nil" [])) (.uconst 2 listUSort))]

-- `as` gives a constructor the instance its sort names.
#guard dtAssumptions (listU ++ "(assume @p0 (as nil (List U)))") ==
  some [.app (.app (.atom "as") (consOf "nil" [])) listUSort]

-- A datatype of a block of arity zero is unchanged.
#guard dtAssumptions "(declare-datatypes ((D 0)) (((a) (b (s D))))) (assume @p0 b)" ==
  some [consOf "b" [.atom "ref D"]]

-- Refused: a `par` whose parameters are not as many as the arity says, or not
-- distinct; a body that is not `par` although the arity is not zero; and a
-- block whose datatypes have different arities.
#guard dtAssumptions "(declare-datatypes ((L 2)) ((par (X) ((n))))) (assume @p0 n)" == none
#guard dtAssumptions "(declare-datatypes ((L 0)) ((par (X) ((n))))) (assume @p0 n)" == none
#guard dtAssumptions "(declare-datatypes ((L 2)) ((par (X X) ((n))))) (assume @p0 n)" == none
#guard dtAssumptions "(declare-datatypes ((L 1)) (((n)))) (assume @p0 n)" == none
#guard dtAssumptions
    "(declare-datatypes ((A 1) (B 0)) ((par (X) ((a (f X)))) ((b)))) (assume @p0 b)" == none

-- Refused: a datatype of the block used in it without its parameters, or with
-- anything else than them (non-uniform recursion).
#guard dtAssumptions
    "(declare-datatypes ((L 1)) ((par (X) ((n) (c (t L)))))) (assume @p0 n)" == none
#guard dtAssumptions
    "(declare-datatypes ((L 1)) ((par (X) ((n) (c (t (L (L X)))))))) (assume @p0 n)" == none

-- Refused: a datatype nested inside an earlier parametric one.  Using an
-- instance of that one at a type from outside the block is fine.
#guard dtAssumptions (listU ++
    "(declare-datatypes ((Tree 0)) (((node (kids (List Tree)))))) (assume @p0 node)") == none
#guard (dtAssumptions (listU ++
    "(declare-datatypes ((Tree 0)) (((node (vals (List U)))))) (assume @p0 node)")).isSome

-- A calculus without `mkParam` refuses parametric datatypes outright.
#guard parseProof { dtConfig with datatypes := some { dtOps with mkParam := none } }
    (list ++ "(assume @p0 cons)") |>.toOption |>.isNone

end Logos.Parser.Tests
