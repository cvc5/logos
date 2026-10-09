import Cpc.Parser

namespace Cpc.Parser.Tests

open Eo SmtEval

/-- The assumptions of a parsed CPC proof, or `none` if it does not parse. -/
private def assumptions (input : String) : Option (List Term) :=
  match Eo.parseProof input with
  | .ok (assums, _) => some assums
  | .error _ => none

-- Nullary definitions from the CPC signature are available without repeating
-- their `define` commands in the proof.
#guard assumptions "(assume @p0 String)" ==
  some [.Apply (.UOp UserOp.Seq) (.UOp UserOp.Char)]

#guard assumptions "(assume @p0 @bv_empty)" == some [.Binary 0 0]

-- `_` is also Eunoia's higher-order application marker.  It remains distinct
-- from indexed syntax because `BitVec` has no one-index declaration.
#guard assumptions "(assume @p0 (_ BitVec 4))" ==
  some [.Apply (.UOp UserOp.BitVec) (.Numeral 4)]

-- Parameterized definitions are preloaded as macros and expand at their use
-- sites.  These exercise both generated CPC macros.
#guard assumptions "(assume @p0 (@bv 3 4))" ==
  some [.Apply (.UOp1 UserOp1.int_to_bv (.Numeral 4)) (.Numeral 3)]

#guard assumptions "(assume @p0 (@var \"x\" Int))" ==
  some [.Var (.String (native_string_lit "x")) (.UOp UserOp.Int)]

/-!
## Syntax emitted by cvc5

Parameterized constants in CPC use flat Eunoia applications, while SMT-LIB
uses `(_ ...)`.  Numeric, symbolic, and internal-operator indices must all
produce the same terms in the two spellings.
-/

#guard assumptions "(assume @p0 (extract 1 0 #b1010))" ==
  assumptions "(assume @p0 ((_ extract 1 0) #b1010))"

-- Eunoia marks a curried application with `_`, so `(extract 1 0)` in head
-- position is not the indexed operator.  Reading it as one accepted proofs
-- Ethos refuses to parse, which is what `((extract 1 0) a)` provoked.
#guard assumptions "(assume @p0 ((extract 1 0) #b1010))" == none

#guard assumptions "(assume @p0 (@bit 0 #b1))" ==
  assumptions "(assume @p0 ((_ @bit 0) #b1))"

private def datatypePrelude : String :=
  "(declare-datatypes ((D 0)) (((a) (b)))) (declare-const d D)"

#guard assumptions (datatypePrelude ++ "(assume @p0 (is a d))") ==
  assumptions (datatypePrelude ++ "(assume @p0 ((_ is a) d))")

-- SMT-LIB type ascription supplies the same sort index as Eunoia's `_` form.
#guard assumptions "(assume @p0 (as set.empty (Set Int)))" ==
  assumptions "(assume @p0 (_ set.empty (Set Int)))"

-- Let-bound names are substituted only in the body.
#guard assumptions
    "(declare-const x Bool)
     (assume @p0 (let ((_let_1 x)) _let_1))
     (assume @p1 x)" ==
  assumptions
    "(declare-const x Bool)
     (assume @p0 x)
     (assume @p1 x)"

-- `declare-datatype` is SMT-LIB's form of a block declaring one datatype.
#guard assumptions
    "(declare-datatype L ((nl) (cns (hd Int) (tl L)))) (declare-const x L)
     (assume @p0 (= (tl (cns 1 x)) nl))" ==
  assumptions
    "(declare-datatypes ((L 0)) (((nl) (cns (hd Int) (tl L))))) (declare-const x L)
     (assume @p0 (= (tl (cns 1 x)) nl))"

#guard (assumptions
    "(declare-datatypes ((L 0)) (((nl) (cns (hd Int) (tl L))))) (declare-const x L)
     (assume @p0 (= (tl (cns 1 x)) nl))").isSome

-- Its parametric form is accepted, as the plural's is.
#guard assumptions
    "(declare-datatype L (par (X) ((nl) (cns (hd X) (tl (L X)))))) (assume @p0 true)"
  == some [.Boolean true]

-- A constructor, selector or datatype is named by a symbol.  Read as a
-- constructor, `#b1` would stop meaning the bit-vector literal.
#guard assumptions "(declare-datatypes ((D 0)) (((c (s Int)) (#b1)))) (assume @p0 (= #b1 #b1))"
  == none
#guard assumptions "(declare-datatypes ((D 0)) (((c (#b1 Int)) (e)))) (assume @p0 true)"
  == none
#guard assumptions "(declare-datatypes ((#b1 0)) (((c) (e)))) (assume @p0 true)"
  == none
#guard (assumptions "(declare-datatypes ((D 0)) (((c (s Int)) (e)))) (assume @p0 (= e e))").isSome

/-!
## Binders

`forall` and `exists` carry Eunoia's `:binder @list`: a sorted variable list
denotes the `@list` of the variables `(@var name type)`, which are bound in the
body.  A variable is the same term wherever its name and type are.
-/

private def quantPrelude : String := "(declare-const P (-> Int Int Bool))"

#guard assumptions (quantPrelude ++ "(assume @p0 (forall ((x Int) (y Int)) (P x y)))") ==
  assumptions (quantPrelude ++
    "(assume @p0 (forall (@list (@var \"x\" Int) (@var \"y\" Int))
       (P (@var \"x\" Int) (@var \"y\" Int))))")

#guard assumptions (quantPrelude ++ "(assume @p0 (exists ((x Int)) (P x x)))") ==
  assumptions (quantPrelude ++
    "(assume @p0 (exists (@list (@var \"x\" Int)) (P (@var \"x\" Int) (@var \"x\" Int))))")

#guard (assumptions (quantPrelude ++ "(assume @p0 (forall ((x Int)) (P x x)))")).isSome

-- A variable shadows a symbol of the same name in the body, and only there.
#guard assumptions (quantPrelude ++
    "(declare-const x Int) (assume @p0 (and (forall ((x Int)) (P x x)) (P x x)))") ==
  assumptions (quantPrelude ++
    "(declare-const x Int)
     (assume @p0 (and (forall (@list (@var \"x\" Int)) (P (@var \"x\" Int) (@var \"x\" Int)))
                      (P x x)))")

-- A variable is named by a symbol.
#guard assumptions (quantPrelude ++ "(assume @p0 (forall ((7 Int)) (P 7 7)))") == none

/-!
## Datatype block order

The specification witnesses a datatype of a `declare-datatypes` block only
through references to entries declared after it, so the parser reorders a block
that was not written that way (`Logos.Parser.productiveOrder`).  Only the order
changes: a block denotes the same datatypes however it is sorted.
-/

private def mutualUse : String :=
  "(declare-const a A) (assume @p0 (= (unA a) (unA a)))"

-- The two spellings of one mutually recursive block denote the same terms.
#guard assumptions
    ("(declare-datatypes ((A 0) (B 0)) (((mkA (unA B))) ((mkB (unB A)) (nilB))))"
      ++ mutualUse) ==
  assumptions
    ("(declare-datatypes ((B 0) (A 0)) (((mkB (unB A)) (nilB)) ((mkA (unA B)))))"
      ++ mutualUse)

-- A chain of three, written back to front.
#guard assumptions
    "(declare-datatypes ((C 0) (B 0) (A 0)) (((mkC)) ((mkB (unB C))) ((mkA (unA B)))))
     (declare-const a A) (assume @p0 (= a a))" ==
  assumptions
    "(declare-datatypes ((A 0) (B 0) (C 0)) (((mkA (unA B))) ((mkB (unB C))) ((mkC))))
     (declare-const a A) (assume @p0 (= a a))"

-- A block is reordered only where it has to be.  Both spellings below are
-- already productive, since each datatype has a constructor taking no field of
-- the block, so each is left as written and the two stay distinct.
#guard assumptions
    "(declare-datatypes ((D 0) (L 0))
       (((node (children L)) (leaf)) ((lnil) (lcons (hd D) (tl L)))))
     (declare-const d D) (assume @p0 (= d d))" !=
  assumptions
    "(declare-datatypes ((L 0) (D 0))
       (((lnil) (lcons (hd D) (tl L))) ((node (children L)) (leaf))))
     (declare-const d D) (assume @p0 (= d d))"

/-!
## Overloaded names

SMT-LIB lets a symbol be declared more than once at different types, and lets a
proof's own symbol carry the name of one of the signature's operators.  A name
is then ambiguous, and the reading that has a type is the one meant.
-/

private def overloadPrelude : String :=
  "(declare-sort A 0) (declare-sort B 0)
   (declare-const f (-> A Bool)) (declare-const f (-> B Bool))
   (declare-const a A) (declare-const b B)"

-- Each use of `f` resolves to the declaration its argument fits, in either
-- order, even though the second declaration is the more recent one.
#guard assumptions (overloadPrelude ++ "(assume @p0 (f a))") ==
  some [.Apply (.UConst 1 (.Apply (.Apply .FunType (.USort 1)) .Bool)) (.UConst 3 (.USort 1))]

#guard assumptions (overloadPrelude ++ "(assume @p0 (f b))") ==
  some [.Apply (.UConst 2 (.Apply (.Apply .FunType (.USort 2)) .Bool)) (.UConst 4 (.USort 2))]

-- A symbol named after a builtin operator: `is` is also the datatype tester,
-- which does not fit an uninterpreted sort, so the declared symbol is meant.
#guard assumptions
    "(declare-sort F 0) (declare-const is (-> F Bool)) (declare-const c F)
     (assume @p0 (is c))" ==
  some [.Apply (.UConst 1 (.Apply (.Apply .FunType (.USort 1)) .Bool)) (.UConst 2 (.USort 1))]

-- The builtin still wins where it is the reading that fits.
#guard assumptions (datatypePrelude ++ "(declare-const is (-> D Bool))
     (assume @p0 (is a d))") ==
  assumptions (datatypePrelude ++ "(assume @p0 (is a d))")

/-!
## The order of assume and step

A proof is read as an assumption set together with the steps that refute it, so
every `assume` stands before the first proof step.  Ethos accepts one anywhere;
`docs/parser.md` records the difference.
-/

-- The same three commands, differing only in where the `assume` stands.
#guard (assumptions
    "(declare-const x Bool)
     (assume @p0 x)
     (step @p1 :rule evaluate :args ((not true)))").isSome

#guard assumptions
    "(declare-const x Bool)
     (step @p1 :rule evaluate :args ((not true)))
     (assume @p0 x)" == none

end Cpc.Parser.Tests
