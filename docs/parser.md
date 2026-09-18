# The Logos parser

Logos has a fully functional CPC parser, meaning that it accepts the same syntax for proofs as
Ethos: the s-expression (Eunoia) syntax emitted by `cvc5 --dump-proofs --proof-format=cpc`.  See
the [README](../README.md) for building and running the executables.

The parser is unverified; it is outside the correctness theorem, which is stated about the
assumptions the parser reads out of a file.

## Structure

The parser is split into two parts.
`Logos/Parser.lean` is signature-independent: it reads the command and term grammar and
resolves premise references, but knows nothing about any particular operator or proof rule.
Everything signature-specific is a `Logos.Parser.Config`, and that is auto-generated from
the calculus alongside `Cpc/Logos.lean` — `Cpc/Parser.lean` lists the operator
declarations and proof rules of CPC.

Because the configuration is generated, an operator's surface syntax comes from its Eunoia
declaration metadata.  The generic `.argList` arity implements Eunoia's `:arg-list` attribute:
the surface arguments are gathered with the declared n-ary helper and passed as the annotated
operator's single argument.  `scripts/check-parser-tables.py` checks that the generated table
covers every operator and proof rule; it runs in the `regressions` CI group.

## Commands

The parser supports the commands `declare-const`, `declare-fun`, `declare-sort`,
`declare-datatypes`, `define`, `assume`, `assume-push`, `step` and `step-pop`.
Every `assume` must stand before the first proof step, since a proof is read as an
assumption set together with the steps that refute it; an `assume` after a `step`,
`assume-push` or `step-pop` is refused, where Ethos accepts one anywhere.
`include` and `reference` commands are ignored: Logos has the signature built in and does not
check the proof against the original input problem.
A `declare-sort` of arity `n` declares a symbol whose type is the sort of sorts, or a function
type into it, so that arity `0` declares an uninterpreted sort.  The sort of sorts is not itself
syntax: `Type` is an ordinary symbol name, which cvc5 output declares (e.g. proofs from Verus).
A `define` with parameters is a macro, since Eunoia has no lambda: its body is kept as an
s-expression and read again wherever the defined symbol is applied, with the parameters bound
to the arguments given there.  Consequently a parameter's declared type is not used, an error
in the body is reported at the use site, and a recursive `define` is rejected.  A `define`
without parameters is read where it is given, as before.
Datatypes may be mutually recursive; parametric datatypes (a non-zero arity, or a `par` body)
are rejected, since Logos has no representation for them.
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
The conclusion printed on a `step` is ignored, since Logos recomputes it from the rule.

## Terms

An expression headed by `_` uses indexed-operator syntax when a matching indexed declaration
exists (for example, `(_ extract 1 0)`); otherwise `_` is a higher-order application marker,
so `(_ BitVec 4)` is equivalent to `(BitVec 4)`.
Parameterized operators also accept Eunoia's flat application syntax, which is what cvc5 emits:
for example, `(extract 1 0 x)` is equivalent to `((_ extract 1 0) x)`.  SMT-LIB type
ascriptions such as `(as set.empty (Set Int))` supply the ascribed sort as the operator index.
Term-level `let` uses parallel bindings whose names are scoped to its body.
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
