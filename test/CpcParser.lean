import Cpc.Parser
import Cpc.SmtTranslate

namespace Cpc.Parser.Tests

open Eo SmtEval Smtm

/-- The assumptions of a parsed CPC proof, or `none` if it does not parse. -/
private def assumptions (input : String) : Option (List Term) :=
  match Eo.parseProof input with
  | .ok (assums, _) => some assums
  | .error _ => none

-- Sort applications share an allocator with ordinary sorts and reuse the same
-- instance across repeated uses, aliases and higher-order application syntax.
private def sortConstructorPrelude : String :=
  "(declare-sort U 0) (declare-sort Box 1)"

#guard assumptions (sortConstructorPrelude ++
    "(define BU () (Box U))
     (assume @p0 BU) (assume @p1 (_ Box U))
     (assume @p2 (Box Int)) (assume @p3 (Box (Box U)))
     (declare-sort V 0) (assume @p4 V)") ==
  some [.USort 3, .USort 3, .USort 4, .USort 5, .USort 6]

#guard assumptions (sortConstructorPrelude ++
    "(declare-sort Pair 2) (define PU () (Pair U))
     (assume @p0 (PU Int)) (assume @p1 (Pair U Int))
     (assume @p2 (Pair Int U))") == some [.USort 4, .USort 4, .USort 5]

#guard assumptions (sortConstructorPrelude ++
    "(assume @p0 Box) (assume @p1 (Box Box))") == some [.Stuck, .Stuck]
#guard (assumptions (sortConstructorPrelude ++
    "(declare-const b (Box U)) (assume @p0 (= b b))")).map
    (List.map (fun t => __smtx_typeof (__eo_to_smt t))) == some [SmtType.Bool]

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

-- Parameters and recursive datatype references share one representation.
-- Constructor inference must bind X while preserving the recursive L field.
private def parametricListPrelude : String :=
  "(declare-datatype L (par (X) ((nl) (cns (hd X) (tl (L X))))))
   (declare-const xs (L Int))"

private def listConstructorUse : String := "(assume @p0 (= (hd (cns 1 xs)) 1))"

#guard (assumptions (parametricListPrelude ++ listConstructorUse)).map
    (List.map __eo_typeof) == some [.Bool]
#guard (assumptions (parametricListPrelude ++ "(assume @p0 (= (as nl (L Int)) (tl xs)))")).map
    (List.map __eo_typeof) == some [.Bool]

-- Instantiating the outer list must preserve the inner list's own references.
#guard (assumptions (parametricListPrelude ++
    "(declare-const xss (L (L Int))) (assume @p0 (= (hd (cns xs xss)) xs))")).map
    (List.map __eo_typeof) == some [.Bool]

-- Indexed operators instantiate their generic constructor or selector index.
private def listIndexedUses : String :=
  "(assume @p0 ((_ is cns) xs)) (assume @p1 (= ((_ update hd) xs 1) xs))"

#guard (assumptions (parametricListPrelude ++ listIndexedUses)).map
    (List.map __eo_typeof) == some [.Bool, .Bool]

-- Datatype applications are normalized at the parser boundary, including
-- standalone sorts passed as proof arguments.
private def listType (field : Term) : Term :=
  .DatatypeType (native_string_lit ".par_1_L")
    (.cons (native_string_lit ".par_1_L")
      (.sum .unit (.sum (.cons field (.cons (.DatatypeTypeRef (native_string_lit ".par_1_L")) .unit)) .null)) .nil)

#guard assumptions (parametricListPrelude ++ "(assume @p0 (L Int))") ==
  some [listType (.UOp .Int)]

private def reflArgument : Except String (List Term × CCmdList) → Option Term
  | .ok (_, .cons (.step .refl (.cons t .nil) .nil) .nil) => some t
  | _ => none

#guard reflArgument (Eo.parseProof
    (parametricListPrelude ++ "(step @p0 :rule refl :args ((L Int)))")) ==
  some (listType (.UOp .Int))

-- An unapplied generic sort stays in the parser's metadata and cannot escape
-- as an ordinary datatype type.
#guard assumptions (parametricListPrelude ++ "(assume @p0 L)") == some [.Stuck]
#guard assumptions (parametricListPrelude ++ "(assume @p0 (L L))") == some [.Stuck]

-- A partial sort application keeps its parameters in parser metadata, even
-- when it is named by a definition and completed later.
private def parametricPairPrelude : String :=
  "(declare-datatype P (par (X Y) ((pair (fst X) (snd Y)))))"

#guard assumptions (parametricPairPrelude ++ "(assume @p0 (P Int))") == some [.Stuck]
#guard assumptions (parametricPairPrelude ++
    "(define PI () (P Int)) (assume @p0 (PI Bool))") ==
  assumptions (parametricPairPrelude ++ "(assume @p0 (P Int Bool))")

-- A template can use an earlier datatype with its parameters in a different
-- order; both templates are instantiated before their operators reach the core.
private def swappedPairUse : String :=
  parametricPairPrelude ++
  "(declare-datatype Q (par (X Y) ((wrap (unwrap (P Y X))))))
   (declare-const q (Q Int Bool))
   (assume @p0 (= (wrap (pair true 1)) q))
   (assume @p1 (= (snd (unwrap q)) 1))"

#guard (assumptions swappedPairUse).map (List.map __eo_typeof) == some [.Bool, .Bool]
#guard (assumptions swappedPairUse).map
    (List.map (fun t => __smtx_typeof (__eo_to_smt t))) == some [SmtType.Bool, SmtType.Bool]

-- Open sort applications in datatype fields are instantiated with the datatype.
-- Inference recovers the argument of Box from the operand's allocated sort.
private def boxedDatatypeUses : String :=
  "(declare-sort Box 1)
   (declare-datatype D (par (A) ((empty) (wrap (unbox (Box A))))))
   (declare-const b (Box Int)) (declare-const d (D Int))
   (assume @p0 (= (wrap b) d))
   (assume @p1 (= (unbox d) b))
   (assume @p2 (= (as empty (D Int)) (as empty (D Int))))
   (assume @p3 ((_ is wrap) d))
   (assume @p4 (= ((_ update unbox) d b) d))
   (declare-const bb (Box Bool)) (declare-const db (D Bool))
   (assume @p5 (= (wrap bb) db))"

#guard (assumptions boxedDatatypeUses).map (List.map __eo_typeof) ==
  some [.Bool, .Bool, .Bool, .Bool, .Bool, .Bool]
#guard (assumptions boxedDatatypeUses).map
    (List.map (fun t => __smtx_typeof (__eo_to_smt t))) ==
  some [SmtType.Bool, SmtType.Bool, SmtType.Bool, SmtType.Bool, SmtType.Bool, SmtType.Bool]

-- A datatype argument can itself contain an open parameter while its template
-- is read; it must not be allocated as a ground sort prematurely.
private def boxedListUses : String :=
  parametricListPrelude ++
  "(declare-sort Box 1)
   (declare-datatype W (par (A) ((pack (unpack (Box (L A)))))))
   (declare-const b (Box (L Int))) (declare-const w (W Int))
   (assume @p0 (= (pack b) w))
   (assume @p1 (= (unpack w) b))"

#guard (assumptions boxedListUses).map (List.map __eo_typeof) == some [.Bool, .Bool]
#guard (assumptions boxedListUses).map
    (List.map (fun t => __smtx_typeof (__eo_to_smt t))) == some [SmtType.Bool, SmtType.Bool]

-- Spec translates the instantiated declarations produced by the parser.
#guard (assumptions (parametricListPrelude ++ listConstructorUse)).map
    (List.map (fun t => __smtx_typeof (__eo_to_smt t))) == some [SmtType.Bool]
#guard (assumptions (parametricListPrelude ++ listIndexedUses)).map
    (List.map (fun t => __smtx_typeof (__eo_to_smt t))) == some [SmtType.Bool, SmtType.Bool]
#guard (assumptions (parametricListPrelude ++
    "(declare-const xss (L (L Int))) (assume @p0 (= (hd (cns xs xss)) xs))")).map
    (List.map (fun t => __smtx_typeof (__eo_to_smt t))) == some [SmtType.Bool]

-- Unused parameters still distinguish instances, both before and after SMT
-- translation. Aliases and repeated applications reuse the same identity.
private def phantomPrelude : String :=
  "(declare-datatype P (par (A B) ((empty) (wrap (value Int)))))"

#guard match assumptions (phantomPrelude ++
    "(define PI () (P Int)) (define PIB () (PI Bool))
     (assume @p0 PIB) (assume @p1 (P Int Int)) (assume @p2 (P Bool Int))
     (assume @p3 (P Int Bool))") with
  | some [a, b, c, d] => a == d && a != b && a != c && b != c &&
      __eo_to_smt_type a != __eo_to_smt_type b &&
      __eo_to_smt_type b != __eo_to_smt_type c
  | _ => false

-- An open phantom application must retain its arguments until the enclosing
-- template is instantiated. Inference must also recover them from an operand.
private def nestedPhantomUses : String := phantomPrelude ++
  "(declare-datatype W (par (A B) ((pack (unpack (P B A))))))
   (declare-const x (W Int Bool)) (declare-const y (W Bool Int))
   (assume @p0 (= (pack (as empty (P Bool Int))) x))
   (assume @p1 (= (pack (as empty (P Int Bool))) y))
   (assume @p2 (= (unpack x) (as empty (P Bool Int))))
   (assume @p3 (W Int Bool)) (assume @p4 (W Bool Int))"

#guard match assumptions nestedPhantomUses with
  | some [a, b, c, x, y] =>
      [a, b, c].map __eo_typeof == [.Bool, .Bool, .Bool] &&
      [a, b, c].map (fun t => __smtx_typeof (__eo_to_smt t)) ==
        [SmtType.Bool, SmtType.Bool, SmtType.Bool] && x != y
  | _ => false

-- The recursive operand carries even a parameter absent from every field.
private def phantomRecursiveUses : String :=
  "(declare-datatype C (par (A) ((end) (more (tail (C A))))))
   (declare-const c (C Int))
   (assume @p0 (= (tail (more c)) c))
   (assume @p1 ((_ is more) c))
   (assume @p2 (= ((_ update tail) c c) c))"

#guard (assumptions phantomRecursiveUses).map
    (List.map (fun t => __smtx_typeof (__eo_to_smt t))) ==
  some [SmtType.Bool, SmtType.Bool, SmtType.Bool]

-- Instantiating either member of a mutual block registers both. Constructor
-- inference and selectors must agree with explicit applications of each sort.
private def mutualParametricUses : String :=
  "(declare-datatypes ((Tree 1) (Forest 1))
     ((par (A) ((node (kids (Forest A)))))
      (par (B) ((leaf) (grow (tree (Tree B)) (rest (Forest B)))))))
   (declare-const ts (Forest Int)) (declare-const t (Tree Int))
   (assume @p0 (= (node ts) t))
   (assume @p1 (= (kids (node ts)) ts))
   (assume @p2 (= (tree (grow t ts)) t))
   (assume @p3 (= (rest (grow t ts)) ts))"

#guard (assumptions mutualParametricUses).map
    (List.map (fun t => __smtx_typeof (__eo_to_smt t))) ==
  some [SmtType.Bool, SmtType.Bool, SmtType.Bool, SmtType.Bool]

-- A block may mix arities. Its datatype of arity zero has one instance, which
-- shares a declaration with the instance it refers to and refers back to it.
private def mixedArityUses : String :=
  "(declare-datatypes ((A 1) (B 0))
     ((par (X) ((leafA (va X)) (mkA (ab B))))
      ((leafB) (mkB (ba (A Int))))))
   (declare-const x (A Int)) (declare-const y (A Bool)) (declare-const b B)
   (assume @p0 (= (ba (mkB x)) x))
   (assume @p1 (= ((as mkA (A Bool)) b) y))
   (assume @p2 (= (ab (ba b)) b))"

#guard (assumptions mixedArityUses).map
    (List.map (fun t => __smtx_typeof (__eo_to_smt t))) ==
  some [SmtType.Bool, SmtType.Bool, SmtType.Bool]

-- Instances that refer to each other at swapped or ground arguments are built
-- as the blocks they form: (A Int Bool) with (B Bool Int), and (L Bool) after (L Int).
private def nonUniformUses : String :=
  "(declare-datatypes ((A 2) (B 2))
     ((par (X Y) ((a0) (mkA (ab (B Y X)))))
      (par (X Y) ((b0) (mkB (ba (A Y X)))))))
   (declare-datatype L (par (X) ((nil) (c (h X) (t (L Int))))))
   (declare-const x (A Int Bool)) (declare-const y (B Bool Int)) (declare-const l (L Bool))
   (assume @p0 (= (ab x) y))
   (assume @p1 (= (mkA (mkB x)) x))
   (assume @p2 (= (h (t l)) 1))
   (assume @p3 (= (c true (c 1 (as nil (L Int)))) l))"

#guard (assumptions nonUniformUses).map
    (List.map (fun t => __smtx_typeof (__eo_to_smt t))) ==
  some [SmtType.Bool, SmtType.Bool, SmtType.Bool, SmtType.Bool]

-- Refused: a datatype needing infinitely many instances, and a declared sort
-- applying a parametric datatype to the wrong number of arguments.
#guard assumptions
    "(declare-datatype O (par (X) ((none) (some (val X)))))
     (declare-datatype N (par (X) ((nil) (cons (hd X) (tl (N (O X)))))))
     (assume @p0 true)" == none
#guard assumptions (parametricListPrelude ++ "(declare-const y (L Int Int)) (assume @p0 true)") == none
#guard assumptions (parametricListPrelude ++ "(declare-const y L) (assume @p0 true)") == none

-- Declaration identity is part of the key even for structurally equal blocks.
#guard match assumptions
    "(declare-datatype P (par (A) ((first)))) (define Old () (P Int))
     (declare-datatype P (par (A) ((second))))
     (assume @p0 Old) (assume @p1 (P Int))" with
  | some [a, b] => a != b
  | _ => false

-- Source names resembling generated ones are escaped injectively, including
-- declarations encountered after an instance has already been allocated.
#guard match assumptions
    "(declare-datatype P (par (A) ((empty) (wrap (value Int)))))
     (define PI () (P Int))
     (declare-datatype .par_1_P ((empty1) (wrap1 (value1 Int))))
     (declare-datatype ..par_1_P ((empty2) (wrap2 (value2 Int))))
     (assume @p0 PI) (assume @p1 .par_1_P) (assume @p2 ..par_1_P)" with
  | some [a, b, c] => a != b && a != c && b != c &&
      [a, b, c].all (fun t => __eo_to_smt_type t != SmtType.None)
  | _ => false

#guard (assumptions
    "(declare-datatype .D ((end) (more (tail .D))))
     (declare-const d .D) (assume @p0 (= (tail (more d)) d))").map
    (List.map (fun t => __smtx_typeof (__eo_to_smt t))) == some [SmtType.Bool]

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
