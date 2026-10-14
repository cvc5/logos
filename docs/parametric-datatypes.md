# Parametric datatypes

This page is the plan for supporting SMT-LIB parametric datatypes
(`(declare-datatypes ((List 1)) ((par (X) ((nil) (cons (head X) (tail (List X))))))))`),
and the instructions for the parts of it that `ethos-eoc` generates. Today they are
refused (see [`smt-lib-conformance.md`](smt-lib-conformance.md)).

Status:

| part | where | state |
| --- | --- | --- |
| generic parser | `Logos/Parser.lean` (hand-written) | done: reads `par`, enforces the restrictions below, calls the calculus's hooks |
| term representation, typing, builtins | `Cpc/LogosTerm.lean`, `Cpc/Logos.lean` (generated) | to do in eoc |
| translation to SMT-LIB | `Cpc/Spec.lean`, from `install/defs/Cpc.eos` (generated) | to do in eoc |
| parser hooks for CPC | `Cpc/Parser.lean` (generated) | to do in eoc; until then CPC leaves `mkParam` unset and refuses `par` |
| model semantics | `Cpc/SmtModel.lean` | **no change** |
| proofs | `Cpc/Proofs`, `CpcMini/Proofs` | to do after regeneration |

## The design in one paragraph

SMT-LIB has no polymorphic terms: `par` is a template for declarations and every
term has a ground sort, so the model semantics stays monomorphic. The EO layer
represents an *instance* such as `(List Int)` as **one node** whose declaration
carries the type arguments, `DatatypeType "List" (params [Int] tdd)`, where the
template `tdd` writes the parameters as `DtParam k`. Constructors and selectors
carry the same wrapped declaration, so `cons` at `Int` is
`DtCons "List" (params [Int] tdd) 1`. Substitution is lazy: it happens where a
declaration is already resolved (`__eo_dtc_resolve`), so everything that resolves
today is instantiated for free, and the translation to SMT-LIB substitutes before
translating. The parser *proposes* the instance at each use; `__eo_typeof`
*checks* it, so a wrong guess is rejected, never given a different meaning.

## Why this shape

- **An instance must not be an `Apply` chain.** CPC's `$dt_get_constructors` has a
  case `(($dt_get_constructors (DC T)) ($dt_get_constructors DC))`, compiled to
  `__dt_get_constructors` in `Cpc/Logos.lean`. On an `Apply`-shaped `(List Int)`
  it would strip the arguments and return constructors that do not know their
  instance, and `$dt_inst_cons_of` would stop finding the constructor it looks
  for. On a single node that case never fires and `eo::dt_constructors` returns
  the instance's own constructors. Ethos instead shares one `cons` symbol across
  instances and annotates only ambiguous constructors; CPC's programs cannot see
  the difference.
- **The arguments go in the declaration, not in new fields.** Adding an argument
  list to `DatatypeType`, `DtCons` and `DtSel` would touch about 1,900 pattern
  matches in about 70 proof files. A wrapper constructor on `DatatypeDecl`
  touches about 200 in about 19, and keeps every existing lemma about `DtCons`
  and `DtSel` in its present shape.
- **Instances are not given distinct names.** Because the EO type keeps its
  arguments, `(Box Int)` and `(Box Bool)` stay distinct at the EO level even when
  a phantom parameter makes their SMT-LIB declarations identical. Identifying
  them in the model is harmless: they are isomorphic and no well-sorted term
  mixes them. (Check when doing the proofs that nothing relies on
  `__eo_to_smt_type` being injective.)

## What eoc generates

### 1. `Cpc/LogosTerm.lean`

In the mutual block:

```lean
inductive Term
  ...
  | DtParam : native_Nat -> Term          -- the k-th type parameter of a template

inductive DatatypeDecl
  | nil
  | cons : native_String -> Datatype -> DatatypeDecl -> DatatypeDecl
  | params : DatatypeArgs -> DatatypeDecl -> DatatypeDecl   -- an instance of a template

inductive DatatypeArgs                    -- the type arguments of an instance
  | nil
  | cons : Term -> DatatypeArgs -> DatatypeArgs
```

`params` only ever wraps a whole block. A reference to a datatype of the same
block stays a bare `DatatypeTypeRef s`: the parser only accepts such references
applied to exactly the block's parameters, in order (see the restrictions), so
the arguments are implicit.

### 2. `Cpc/Logos.lean` builtins

- `__eo_subst_params (a : DatatypeArgs) : Term -> Term`
  - `DtParam k` is the `k`-th element of `a` (`Stuck` if there is none);
  - it recurses through `Apply`, so `(Seq X)` and `(Array X Y)` are substituted;
  - on `DatatypeType s (params a' dd')` it substitutes into `a'` and **not** into
    `dd'`, whose `DtParam`s are that other template's;
  - everything else, `DatatypeTypeRef` included, is unchanged.
- `__eo_dtc_resolve c dd`: when `dd = params a tdd`, apply `__eo_subst_params a`
  to each field type as well as resolving references. A `DatatypeTypeRef s` still
  resolves to `DatatypeType s dd`, the *wrapped* declaration, which is what makes
  uniform mutual recursion come out right.
- `__eo_dd_lookup s (params a dd) = __eo_dd_lookup s dd`, and likewise wherever a
  function walks a declaration looking for a name (`has_dt`-style functions).
- `__eo_dt_constructors` and `__eo_dt_selectors`: unchanged; they already carry
  `dd`.
- `__eo_typeof`:
  - `DtParam k` has type `Stuck`;
  - `DatatypeType s dd`, `DtCons s dd i` and `DtSel s dd i j` are guarded by
    `__eo_dd_args_wf dd`: every argument of a `params` wrapper has type `Type`
    and every `DtParam` index in the template is below the number of arguments.
    A *generic* declaration, whose arguments are `[DtParam 0, …]`, therefore has
    no type: that is the safety net for the parser.

### 3. `Cpc/Spec.lean` (from `install/defs/Cpc.eos`)

- `__eo_to_smt_datatype_decl (params a tdd) =
  __eo_to_smt_datatype_decl (__eo_dd_subst_params a tdd)`, where
  `__eo_dd_subst_params` applies `__eo_subst_params` to every field type and
  leaves `DatatypeTypeRef`s alone. The SMT-LIB side then resolves those
  references into the instance's own declaration, as it does for a monomorphic
  block today.
- `__eo_to_smt_type (DtParam k) = SmtType.None`.
- The reserved-name check (`$eo_to_smt_reserved_datatype_name`) is unchanged.

### 4. `Cpc/SmtModel.lean`

Nothing. `SmtType.Datatype s dd` with a monomorphic `dd` is already exactly what
SMT-LIB means by an instance of a parametric datatype.

### 5. `Cpc/Parser.lean`: the hooks

The generic parser (`Logos.Parser.DatatypeOps`) now has three optional hooks and
passes each datatype's arity in `DatatypeSpec.arity`. eoc emits them for CPC:

- `mkParam := some fun k => Term.DtParam k`. Setting it is what turns parametric
  datatypes on; while it is `none` the parser refuses `par` as it does today.
- `mkDecls` (existing): for a block of arity `n`, build the template `tdd` as
  today (the parameters were read as `mkParam k`), and bind each name to its
  *generic* form, with arguments `[DtParam 0, …, DtParam (n-1)]`:
  `DatatypeType s (params gen tdd)`, `DtCons s (params gen tdd) i`,
  `DtSel s (params gen tdd) i j`. For `n = 0` bind exactly what is bound today,
  with no wrapper, so monomorphic datatypes are untouched.
- `elaborate : Term → Term`. The parser calls it on every application it builds
  (head applied to at least one argument), after the arguments have been
  elaborated. It returns the term unchanged unless its head is generic:
  - `DatatypeType s (params gen tdd)` applied to `n` arguments: replace `gen` by
    the arguments and drop the applications, giving the single-node instance.
  - `DtCons s (params gen tdd) i` applied to arguments `a₁ … aₘ`: match the
    constructor's field types (resolved with the generic arguments) against
    `__eo_typeof aⱼ`, binding each `DtParam k` to the type it meets. If every
    parameter is bound, rebuild the head with those arguments and reapply;
    otherwise return the term unchanged (it will then fail to type).
  - `DtSel s (params gen tdd) i j` applied to `a`: if `__eo_typeof a` is
    `DatatypeType s (params args tdd)`, rebuild the selector with `args`.
  - `(UOp1 is c) a` and `(UOp1 update s) a u` with a generic `c` or `s`: take the
    arguments from `__eo_typeof a` in the same way.
  Matching is first-order and needs no unification: argument types are ground.
- `ascribe : Term → Term → Option Term`, for `(as c S)`: if `c` is a generic
  constructor and `S` is an instance `DatatypeType s (params args tdd)` of the
  same template, return `c` rebuilt with `args`; a constructor with fields may be
  ascribed with its result sort as well. Otherwise `none`.

Whatever these hooks return is checked by `__eo_typeof` (the parser's
`wellTyped`), so they are part of the elaborator, not of the trusted
specification.

### 6. `CpcMini`

If it is regenerated with the same `Term`, it gets the same constructors and its
proofs need the same new cases.

## Restrictions (phase 1), enforced by the generic parser

- All datatypes of one block have the same arity, and each body of a block of
  arity `n` is `(par (X₁ … Xₙ) (…))` with distinct parameter names. Parameters are
  matched by position, so they may be named differently in each body.
- Inside a parametric block, a datatype of the block is written applied to
  exactly its parameters in order, `(List X)`, and is read as the reference
  `mkRef "List"`. Any other use of it, bare or applied to anything else
  (non-uniform recursion, e.g. `(List (Pair X X))`), is refused.
- A datatype of the block may not appear inside the arguments of an earlier
  parametric datatype (a *nested* datatype, e.g. `(List Tree)` in the declaration
  of `Tree`). This is refused in every block, parametric or not.

## Proofs, after regeneration

- The central new lemma generalizes `eo_to_smt_dtc_resolve_of_no_none`
  (`Cpc/Proofs/Translation/Inversions.lean`). A template field translates to
  `None` because of `DtParam`, so the statement becomes, roughly,
  `to_smt (eo_resolve c (params a tdd)) =
   smtx_resolve (to_smt (subst a c)) (to_smt_decl (params a tdd))`,
  with a small lemma that substitution commutes with resolution.
- Mechanical: a `params` case wherever a function recurses on `DatatypeDecl`, and
  a `DtParam` case, which `__eo_typeof = Stuck` dismisses in most typed lemmas.
- Unchanged: the datatype rule proofs. After translation they see only a
  monomorphic `SmtTerm.DtCons s dd`.

## Tests to add once CPC is regenerated

In `test/CpcParser.lean` and `test/regress/sexp`: `(List Int)` alone; `(List Int)`
and `(List Bool)` in one proof; a phantom parameter (`Box`); a parameter
instantiated with an uninterpreted sort; `(as nil (List Int))`; `dt_split` and
`dt_inst` on an instance; and refusals of nested and non-uniform declarations.
The existing test that CPC refuses `par` is then inverted.

## Phase 2: nested datatypes

Even if one got past the parser, a nested occurrence fails safely: inside `Tree`
the field `(List Tree)` translates to `List`'s declaration with
`X := TypeRef "Tree"`, a reference that `List`'s block cannot resolve, so
`__smtx_type_wf` is false and the result is `incomplete`. Supporting it means
flattening `List<Tree>` into `Tree`'s block in `__eo_to_smt_type`, with a
standalone `(List Tree)` guaranteed to translate to the same
`Datatype "List…" treeBlock`. It is self-contained and can come later.
