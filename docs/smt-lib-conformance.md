# Conformance to SMT-LIB

Logos's soundness theorem is stated against `Cpc/SmtModel.lean`, a formalization
of SMT-LIB semantics written independently of the checker. It parts company with
SMT-LIB in five ways, and they are different kinds of thing:

- **Narrowings.** The semantics admits fewer models than SMT-LIB does in three
  places: arrays, uninterpreted sorts, and uninterpreted functions of more than
  one argument. These change what `correct` claims, and are most of this page.
- **Extensions.** Sets and sequences are not in SMT-LIB at all, and neither are
  the auxiliary operators the semantics adds. Conformance is not defined for
  them, so nothing here is measured against the standard.
- **Refusals.** Parametric datatypes needing infinitely many instances are
  rejected rather than interpreted, which costs coverage and nothing else.
- **Higher-order input is out of scope.** Function values are names, and
  equality on them is intensional, deliberately. On a formula that compares
  functions or quantifies over them, the semantics and SMT-LIB 2.7 can disagree
  in either direction.
- **Lenient typing.** A few terms SMT-LIB rejects as ill-sorted are given a
  meaning here. No term SMT-LIB accepts changes meaning.

**None of them is a gap in the proof.** The theorem is proven, and it says what
it says about the semantics it is stated against. What the narrowings record is
that the model class is slightly smaller than SMT-LIB's, so `correct` claims
slightly less than the words *these assumptions are unsatisfiable* are normally
taken to mean. Each takes quantifiers to reach; on quantifier-free input the two
agree. The higher-order difference is confined to input that is not first-order,
which SMT-LIB 2.6 does not have.

## What `correct` means, exactly

Unsatisfiability in the specification is *false under every well-formed model*
(`smt_satisfiability` in `Cpc/SmtModel.lean`), where a model assigns each symbol
a value of the right SMT type (`model_wf`, in the same file), and the values
available at a type are the inhabitants of `SmtValue` at that type.

That value inductive is where the narrowing happens. Read on the standard
theories alone, every model of this semantics is an SMT-LIB model, and not every
SMT-LIB model is one of these — so

> SMT-LIB says unsatisfiable **⟹** Logos says unsatisfiable, and not the reverse.

The consequence worth stating plainly: a formula that is satisfiable in SMT-LIB
only by a model this semantics cannot express is treated here as
unsatisfiable. Nothing in the checker will notice, because the restriction is in
what a model *is*, not in what a term means, so no `incomplete` verdict fires.
The channel by which that could produce a wrong `correct` is a CPC rule that is
sound for this model class and unsound for SMT-LIB's: its Lean proof would go
through, and proofs using it would be accepted.

| narrowing | this semantics | SMT-LIB | where it bites |
| --- | --- | --- | --- |
| arrays are almost constant | a default plus finitely many overrides | the full function space | quantifiers over arrays or indices |
| uninterpreted sorts are countable | any finite size, or countably infinite | any nonempty cardinality | quantifiers forcing a sort to be as large as `Real` |
| partial applications are countable | countably many at each function sort | one for each argument | quantifiers over a function's non-final `Real` argument |

## Arrays are almost-constant maps

An array value is `SmtMap`, which is `default T v` overridden at finitely many
points by `cons k v m` (`Cpc/SmtModelDefs.lean`). So every array in every model
is constant except at finitely many indices, where SMT-LIB's `ArraysEx`
interprets `(Array I E)` as the whole function space from `I` to `E`.

It bites where a formula forces an array that is not almost constant:

```smt2
(declare-const a (Array Int Int))
(assert (forall ((i Int)) (= (select a i) i)))
```

satisfiable in SMT-LIB by the identity, and false under every model here.

It does not bite on quantifier-free array formulas, where a satisfiable formula
has an almost-constant model — the same property array decision procedures are
built on.

## Uninterpreted sorts are at most countable

A model chooses the size of each uninterpreted sort (`usortCard`, in
`Cpc/SmtModel.lean`): a positive number gives a finite sort, and `0` gives a
countably infinite one. Every such size SMT-LIB allows is available, so a
formula bounding a sort is satisfiable here as it is there:

```smt2
(declare-sort U 0)
(assert (forall ((a U) (b U) (c U)) (or (= a b) (= a c) (= b c))))
```

What is missing is the uncountable sizes. A value of a sort is `UValue i n` for a
natural `n` (`Cpc/SmtModelDefs.lean`), so there are never more values than
naturals, while `Real` has more than that. That bites where a formula forces a
sort to be as large as `Real`:

```smt2
(declare-sort U 0)
(declare-fun g (U) Real)
(assert (forall ((r Real)) (exists ((u U)) (= (g u) r))))
```

satisfiable in SMT-LIB, taking `U` to be the reals and `g` the identity, and
false under every model here: the image of a countable sort is countable. A
quantifier-free formula is unaffected, since it only ever constrains finitely
many values of a sort.

## Partial applications are countable

An uninterpreted function of several arguments is curried: `(declare-fun f (A B)
C)` has the type `(FunType A (FunType B C))`. Applying it to one argument
therefore has to produce a value of a function type, and the only such value is a
name, `SmtValue.Fun` (`Cpc/SmtModelDefs.lean`). There are countably many names, so
`f` can produce only countably many different functions of its second argument,
however many values its first argument ranges over.

It bites where a formula forces uncountably many of them:

```smt2
(declare-fun lt (Real Real) Bool)
(assert (forall ((x Real) (y Real)) (= (lt x y) (< x y))))
```

satisfiable in SMT-LIB, with `lt` being `<`, and false under every model here:
`(lt x)` must be a different function for each real `x`, which would need more
names than exist.

The final argument is never affected, so a unary function may be any
type-respecting function, as may `(declare-fun f (Int Real) Bool)`. It takes a
sort with uncountably many values in a non-final position, which means `Real` or
a sort built from it. A quantifier-free formula is unaffected, since it only ever
applies a function at finitely many arguments.

## Extensions: what the standard does not define

Sets and sequences are cvc5 extensions rather than SMT-LIB theories, and the
standard `String` sort is modeled here as a sequence over a `Char` sort the
standard does not have. The semantics also carries auxiliary operators of its
own: total division and modulus, purification, and the difference witnesses for
arrays and sequences. **There is no SMT-LIB meaning for any of these to differ
from**, so the reference for them is CPC's meaning, not the standard's, and the
proofs of the rules that use them are what ties the two together.

Two facts about them are worth knowing anyway. Every set value is finite
(canonicity forces the map default to `false`, in `Cpc/SmtModel.lean`), which
the available set operators preserve; and out-of-bounds `seq.nth` is
underspecified through a model-dependent function, `@oob_seq_nth`, in the same
way SMT-LIB underspecifies partial standard operators.

## A coverage limit, not a semantic one: non-regular parametric datatypes

The parser instantiates parametric datatypes as it reads them, building each
instance a proof uses together with every instance that one needs (see
[`parser.md`](parser.md)). SMT-LIB also allows a datatype whose instances need
infinitely many others, such as

```smt2
(declare-datatype N (par (X) ((nil) (cons (hd X) (tl (N (Option X)))))))
```

where `(N Int)` needs `(N (Option Int))`, which needs `(N (Option (Option Int)))`,
and so on. Such a block is refused during parsing, in `Logos/Parser/Core.lean`
(`checkRegular`), and the run exits 1 without a verdict. This costs coverage
and nothing else: a proof over such a datatype is not checked, rather than
checked against the wrong meaning. Every other parametric datatype SMT-LIB
allows is accepted, including blocks mixing arities and datatypes whose own
datatypes appear in their fields at permuted or ground arguments.

## A coverage limit: string escapes naming a surrogate

SMT-LIB's alphabet includes the surrogate code points, so `"\u{d800}"` is a string
literal of one character. The parser rejects such an escape, since Lean has no
`Char` for it (see [`parser.md`](parser.md)). This costs coverage and nothing
else. The semantics itself has these characters, and `(str.from_code 55296)`
denotes one.

## Uninterpreted sort constructors

The parser supports declarations such as `(declare-sort Box 1)` by mapping each
ground application, such as `(Box Int)`, to an ordinary uninterpreted sort.
Repeated uses of the same constructor and arguments share a sort; different
instances get distinct sort IDs. The specification uses its existing `USort`
representation. `test/regress/sexp/test-declare-sort.cpc` exercises this path.

## Higher-order input is out of scope

Logos is meant for first-order input. The semantics can express function-sorted
terms, because CPC uses them internally, but it does not give them their
SMT-LIB 2.7 meaning, and that is deliberate.

A function value is `SmtValue.Fun name T U` (`Cpc/SmtModelDefs.lean`): a name,
whose behaviour the model supplies (`native_eval_fun_apply` in
`Cpc/SmtModel.lean`). Two consequences follow.

- **Equality on functions is intensional.** `=` compares values structurally
  (`__smtx_model_eval_eq`), so two names with the same behaviour are unequal.
  SMT-LIB 2.7 interprets `(-> A B)` as the total functions from `A` to `B`,
  where `=` is extensional.
- **Function sorts range over named functions.** A variable of sort `(-> A B)`
  ranges over `Fun s A B` for every string `s` (the quantifier domain is the
  well-typed canonical values, and every `Fun` is canonical). That is countably
  many values, possibly with repetitions, rather than the full function space.

Unlike the narrowings, this cuts both ways. It admits models SMT-LIB does not
have:

```smt2
(declare-const f (-> Int Int))
(declare-const g (-> Int Int))
(assert (forall ((x Int)) (= (f x) (g x))))
(assert (not (= f g)))
```

is unsatisfiable in SMT-LIB 2.7 and satisfiable here. And it rules out ones
SMT-LIB has:

```smt2
(assert (forall ((f (-> Bool Bool)) (g (-> Bool Bool)))
          (=> (forall ((x Bool)) (= (f x) (g x))) (= f g))))
```

is valid in SMT-LIB 2.7 and false under every model here: of any five names, two
behave the same as `Bool -> Bool` functions, and `=` still calls them distinct.
That second direction is the one that matters for `correct`.

None of this is reachable from first-order input. A first-order formula applies
declared functions but never uses one as an argument: it does not compare
functions, quantify over them or partially apply them. On such a formula a
function value is only ever applied, and evaluation sees only its behaviour. That
names are countable does still reach first-order input by one route, the
partial applications evaluation makes internally, which is listed above as a
narrowing.

## Lenient typing

`__smtx_typeof` (`Cpc/SmtModel.lean`) accepts a few terms that SMT-LIB rejects as
ill-sorted, and gives them a meaning. No term SMT-LIB accepts is affected, so
this matters only for input that is not well-sorted SMT-LIB to begin with.

| term | SMT-LIB | here |
| --- | --- | --- |
| `(_ BitVec 0)`, `((_ int_to_bv 0) t)` | widths are at least 1 | width 0 is a type, with one value |
| `(/ x y)` with `x`, `y` of sort `Int` | `/` is `Real Real Real` only | both arguments converted to `Real` |
| `(abs r)` with `r` of sort `Real` | `abs` is `Int Int` only | the absolute value of `r` |
| `((_ divisible n) t)` | `n` a numeral, `n > 0` | `n` any `Int` term; `0` means `t = 0`, and negative `n` acts as `abs n` |

## Quantifying over `RegLan`

A variable of sort `RegLan` ranges over the values `SmtValue.RegLan`, which are
regular expressions, compared by the language they denote. So quantification
over `RegLan` ranges over the regular languages only. No SMT-LIB logic
quantifies over `RegLan`, so this is outside the standard's logics either way.

## Sorts that are refused

`__smtx_type_wf` (`Cpc/SmtModel.lean`) rejects a function sort whose argument is
a function or `RegLan`, and arrays, sequences, sets and datatype fields whose
element is a function or `RegLan`. A term of such a sort has no translation, so a
proof whose assumptions mention one is reported `incomplete`. This costs
coverage and nothing else.

## What is faithful, and is easy to assume otherwise

- **`Real` is the real numbers.** `SmtValue.Real` carries Mathlib's `Real`
  (`Cpc/SmtReal.lean`), and quantification over `Real` ranges over all of it, so
  `(assert (= (* x x) 2.0))` is satisfiable. Only the literals of the term language
  are rational, as they are in SMT-LIB, and each denotes its image in the reals.
- **Division by zero, `mod` by zero and real division by zero** are
  underspecified exactly as SMT-LIB requires: each evaluates by applying a
  model-dependent function (`@div_by_zero`, `@mod_by_zero`, `@qdiv_by_zero`), so
  models disagreeing about `(div 1 0)` are all admitted, and nothing here fixes a
  value for it.
- **The character alphabet** is SMT-LIB's, code points `0` to `196607`
  (`native_char_valid`, `Cpc/SmtEval.lean`).
- **Uninterpreted functions** are not subject to the almost-constant restriction
  arrays carry. A unary one may be any type-respecting function; one of more
  arguments may be too, apart from the limit on partial applications above.
  Quantifying over a function sort is the higher-order case above.

## Where this is written down elsewhere

The write-up, [`smt-model-definitions.pdf`](smt-model-definitions.pdf), states the
same three kinds in its introduction and then each narrowing again at the
definition that introduces it — arrays under the type constructors and again
where maps are defined, partial applications where function values are, and the
cardinality of a sort where uninterpreted sort values are. The parser's refusals
are in [`parser.md`](parser.md). This page is the list as it matters to
somebody running the checker; the write-up is where the definitions and their
reasoning are.
