# The Logos parser

Logos has a fully functional CPC parser, meaning that it accepts the same syntax for proofs as
Ethos: the s-expression (Eunoia) syntax emitted by `cvc5 --dump-proofs --proof-format=cpc`.  See
the [README](../README.md) for building and running the executables.

The parser is unverified; it is outside the correctness theorem, which is stated about the
assumptions the parser reads out of a file.

## Structure

The parser has a shared implementation and a generated configuration for each calculus.
`Logos/Parser.lean` exposes the shared `Logos.Parser.parseProof` entry point.
Its implementation reads the command and term grammar, resolves premise references,
and elaborates datatype sorts, constructors and selectors. These details live in
`Logos/Parser/Core.lean` and `Logos/Parser/Datatypes.lean`.
`Cpc/Parser.lean` is auto-generated from the calculus alongside `Cpc/Logos.lean`: it lists
the operator declarations, macros and proof rules of CPC, supplies the term adapter and
command constructors, and calls `Logos.Parser.parseProof parserConfig`.
The configuration's `datatypeTerms` field supplies name conversion, term views and
constructors, its type query, and its stuck term through `Logos.Parser.DatatypeTerms`.
Datatype elaboration is internal to the shared parser.

Because the configuration is generated, an operator's surface syntax comes from its Eunoia
declaration metadata.  The generic `.argList` arity implements Eunoia's `:arg-list` attribute:
the surface arguments are gathered with the declared n-ary helper and passed as the annotated
operator's single argument.  `scripts/check-parser-tables.py` checks that the generated table
covers every operator and proof rule; it runs in the `regressions` CI group.

## Commands

A proof file is a bare sequence of commands.  `cvc5 --dump-proofs
--proof-format=cpc` emits one as the response to `get-proof`: a leading `unsat`
line, then the commands inside a further pair of parentheses.  Both have to be
stripped.  That pair is not a Eunoia command, and Logos refuses a file carrying
it exactly as Ethos does, recognizing the shape only to report which parentheses
to remove.

The parser supports the commands `declare-const`, `declare-fun`, `declare-sort`,
`declare-datatype`, `declare-datatypes`, `define`, `assume`, `assume-push`, `step` and
`step-pop`.  `declare-datatype` is SMT-LIB's form of a `declare-datatypes` block
declaring one datatype, and is read as that block.
A name that a declaration, a datatype, a `define`, a macro parameter or a `let` binding
introduces is a symbol, as in Ethos: a literal (`5`, `#b1`, `1/2`, `"s"`) or a keyword
is refused there, since binding one would change what that literal means for the rest
of the proof.
Every `assume` must stand before the first proof step, since a proof is read as an
assumption set together with the steps that refute it; an `assume` after a `step`,
`assume-push` or `step-pop` is refused, where Ethos accepts one anywhere.
`include` and `reference` commands are ignored: Logos has the signature built in and does not
check the proof against the original input problem.
A `declare-sort` of arity `0` declares an uninterpreted sort; a positive arity declares
a sort constructor. The parser stores each constructor's identity and arity and maps
its ground applications to ordinary uninterpreted sorts. Repeated applications share
the same sort ID, using the same allocator as ordinary sort declarations. Applications
containing datatype parameters stay symbolic until those parameters are instantiated.
The parser retains the applications behind allocated sorts for datatype constructor
inference. The sort of sorts is not itself syntax: `Type` is an ordinary symbol name,
which cvc5 output declares (e.g. proofs from Verus).
A `define` with parameters is a macro, since Eunoia has no lambda: its body is kept as an
s-expression and read again wherever the defined symbol is applied, with the parameters bound
to the arguments given there.  Consequently a parameter's declared type is not used, an error
in the body is reported at the use site, and a recursive `define` is rejected.  A `define`
without parameters is read where it is given, as before.
Datatypes may be mutually recursive.  The generic parser reads parametric datatypes (a
non-zero arity with `par` bodies) for a calculus that supplies the hooks of `DatatypeOps`:
the parameters are read as `mkParam`, and each use of a generic sort, constructor or selector
is handed to `elaborate` (or `ascribe`, for `as`). The datatypes of one block may have
different arities, including zero. As SMT-LIB requires, a datatype of the block is applied
to as many arguments as its arity, and those arguments do not mention the block, so
`(List (List X))` is refused in the declaration of `List`; nor may it be nested in an earlier
parametric datatype, as in `(List Tree)`. Otherwise its arguments are arbitrary: the
parameters in another order, a ground sort such as `(L Int)` inside `L`, or a larger sort.
The one block SMT-LIB allows that the parser refuses is one where an instance needs
infinitely many others, such as `N` with a field `(N (Option X))`: the parser builds every
instance it needs, so it cannot represent one. A block is refused when a parameter flows,
through an argument larger than itself, around a cycle of references back to itself
(`checkRegular` in `Logos/Parser/Core.lean`), which is exactly the case where the instances
are infinite. In particular, a block where each argument of a datatype of the block is a
parameter or a ground sort is always accepted. A sort given to `declare-const` or
`declare-fun` that applies a parametric sort to too few or too many arguments is refused.
The shared elaboration in `Logos/Parser/Datatypes.lean` supplies these hooks and infers
constructor instances from arguments and selector instances from their operand's type.
Parameter lists and datatype templates live in parser metadata, with no parametric
datatype constructor in `Eo.Term`. The parser instantiates sort applications as it reads
them, so assumptions and proof commands contain monomorphic declarations.
Instantiating `(A Int Bool)` first finds the instances it needs, by instantiating the
fields of each instance found until no new one appears, and then declares them: instances
that refer to each other in a cycle form one block, and a block is declared after the
blocks it refers to. In the block `((A 2) (B 2))` with fields `(B Y X)` and `(A Y X)`,
`(A Int Bool)` and `(B Bool Int)` form one block; in `L` with a field `(L Int)`, `(L Bool)`
refers to a separate, earlier block for `(L Int)`. A datatype of arity zero in a
parametric block has one instance, declared with the block.
Each instance receives a name of the form `.par_1_P`, numbered in the order instances are
found. Its identity is cached by the declaration block, the datatype and the complete list
of type arguments, including unused parameters: `(P Int)` and `(P Bool)` remain distinct
even if their fields have identical types. Every instance found by one instantiation is
registered, so a later application of another datatype of the block at the same arguments
reuses it, and their recursive references, constructors and selectors use the generated
names. The parser retains the template and arguments for constructor inference;
open applications in templates are named only after their arguments are ground.
To prevent collisions, source datatype names beginning with `.` acquire one extra
leading dot internally. This also applies to their recursive references and does
not change how those names are written in proof files.
`Spec.lean` translates those declarations directly;
it does not instantiate parametric datatypes. Clients constructing EO terms without the
parser must supply the instantiated declarations themselves.
The order of a `declare-datatypes` block matters: the specification witnesses a datatype only
through references to entries declared *later* in its block (`smt_type_default`,
`docs/smt-model-definitions.tex`), so a block declaring a datatype before the ones witnessing
it has no well-formed type at all.  The parser therefore reorders a block that was not written
that way, by decreasing rank in the saturation `productiveOrder` describes, which leaves a
block that is already productive exactly as it was.  A block denotes the same datatypes
however it is sorted, so this is the order and nothing else; but it is the parser that says so,
and the parser is not verified.  The native front end (`docs/lean-native-proofs.md`) does not
go through here and is not normalized: a script names its declaration block directly, and one
not in a productive order is reported `incomplete`.
The conclusion a `step` or `step-pop` may state is read as a term and, as in Ethos, checked
against the one its rule derives: the parser emits the calculus's `check_proven` command
(`Config.mkCheckProven`) after the step, which leaves the checker stuck unless the two are
the same term.  A configuration without that command reads the conclusion and drops it,
so a malformed conclusion is refused but a well-formed wrong one is not.

## Terms

An expression headed by `_` uses indexed-operator syntax when a matching indexed declaration
exists (for example, `(_ extract 1 0)`); otherwise `_` is a higher-order application marker,
so `(_ BitVec 4)` is equivalent to `(BitVec 4)`.
Parameterized operators also accept Eunoia's flat application syntax, which is what cvc5 emits:
for example, `(extract 1 0 x)` is equivalent to `((_ extract 1 0) x)`.  SMT-LIB type
ascriptions such as `(as set.empty (Set Int))` supply the ascribed sort as the operator index.
Term-level `let` uses parallel bindings whose names are scoped to its body.
An operator with Eunoia's `:binder` attribute (`forall` and `exists` in CPC) may be
applied to a sorted variable list, as in `(forall ((x Int) (y Int)) F)`.  As in Ethos,
that denotes `(forall (@list x y) F)`, where each variable is `(@var "x" Int)`, the same
term wherever its name and type are, and is bound in the rest of the application; a
first argument that is not a variable list is an ordinary term.  The configuration
supplies the list constructor (`OpDecl.binder`) and the variables (`Config.mkVar`).
`lambda` is a binder in CPC too, but Logos has no representation for it, so a term
using it is not read.
A name may be declared more than once, as SMT-LIB allows, and a proof's own symbol may
carry the name of one of the signature's operators; every declaration of a name is kept,
and a use of it means the reading the calculus gives a type to (`Config.wellTyped`, which
`Cpc.Parser` decides with `__eo_typeof`).  A name with only one reading is never rejected
this way, so a partially applied operator, which has no type, still parses.  A `let`
binding and a macro parameter shadow instead of overloading.

## Literals

Literals are lexed by `Logos.Parser.Literal.ofString`, which a configuration only has to map
into its own term language: integers (`12`, `-12`), rationals in both fractional and decimal
form (`1/2`, `-1.25`), bit-vectors in binary and hexadecimal (`#b0110`, `#x1f`) and strings
with the SMT-LIB `""` escape.  A string literal's `\u{d…}` and `\ud₃d₂d₁d₀` escapes are
decoded as well, since they belong to the SMT-LIB theory of strings rather than to its
syntax: `"\u{a}"` is one character, not six.  A malformed escape stands for its own
characters, as in Ethos; a well-formed one naming a surrogate is rejected, since Lean has
no `Char` for it.
