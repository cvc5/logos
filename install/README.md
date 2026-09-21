# Regenerating the calculus

`Cpc` and `CpcMini` are compiled from the Eunoia definition of CPC rather than
written by hand. This directory is what does that:

```text
install/install-cpc.sh       regenerate Cpc, and with --all CpcMini too
install/install-sig.sh       compile one signature into one package
install/get-eo-compiler.sh   fetch and build the compiler
install/defs/Cpc.eos         what the symbols of CPC mean, kept in git
install/defs/Cpc.cached.eo   the signature they compile, kept in git
install/deps/                the Ethos tree and the compiler, ignored by git
```

## Usage

```bash
install/get-eo-compiler.sh                          # once
install/install-cpc.sh ~/cvc5/proofs/eo/cpc/Cpc.eo  # regenerate Cpc
scripts/build.sh Cpc                                # check the result
```

Passing the signature is the whole of a normal update. It can be any Eunoia
signature reachable on the machine, including one being edited; `Cpc.eo`
includes the rest of `proofs/eo` by relative path, so it has to sit in a
complete copy of that subtree. The run records what it compiled in
`install/defs/Cpc.cached.eo`.

A plain run is of `Cpc` alone. `CpcMini` is the reduced package of the same
calculus, and it follows the signature too, so a change that moves what `Cpc`
compiles to has to move it as well. `--all` is both:

```bash
install/install-cpc.sh --all ~/cvc5/proofs/eo/cpc/Cpc.eo
scripts/build.sh Cpc CpcMini
```

With no signature to hand, `--cached` compiles that recorded copy:

```bash
install/install-cpc.sh --cached                # regenerate Cpc from it
install/install-cpc.sh --all --cached --check  # ask whether both still match
```

The options most often added to any of those:

```text
--all                write CpcMini as well as Cpc
--mini               write CpcMini instead of Cpc
--check              install nothing; ask whether what would be written is
                     already what the signature compiles to
--ethos PATH         compile with an Ethos checkout you already have
```

Both scripts take `--help` for the rest of their options.

`install-cpc.sh` exits 0 when it did what it was asked and 1 when it did not,
and nothing else. Under `--check` that is 0 when every package it looked at is
up to date and 1 when one of them is not, whether because it differs or because
the signature never compiled; which of those happened is in the output rather
than in the status.

Requirements: `cmake` >= 3.12, a C++17 compiler, the GMP development headers
(`libgmp-dev` on Debian and Ubuntu, `gmp` on Homebrew), `python3`, `tar`, and
either `wget` or `curl`.

## What is generated and what is not

The signature-wide modules of the package, and one file per proof rule:

```text
Cpc/Logos.lean       Cpc/SmtModelDefs.lean   Cpc/Spec.lean
Cpc/LogosTerm.lean   Cpc/SmtValueOrder.lean  Cpc/Proofs/RuleLemmas.lean
Cpc/Parser.lean      Cpc/SmtModel.lean       Cpc/Proofs/Rules/<Rule>.lean
Cpc/SmtEval.lean
```

Each of those signature-wide modules is installed with a banner saying it is
auto-generated, that an install overwrites it, and where the semantics it
realizes are written down (`docs/smt-model-definitions.pdf`). Rule files do not
get one: the compiler's stub is where the proof then goes, so it stops being
generated code the moment it is worth keeping.

Everything else is hand-written and is left alone: `Cpc/Api*.lean`,
`Cpc/Diagnostics.lean`, `Cpc/Native.lean` and `Cpc/Native/`, and everything under
`Cpc/Proofs/` other than `RuleLemmas.lean` and `Rules/`.

Rule files are preserved. The compiler emits each rule as its statement with
`sorry` for a proof, and the proofs live in those same files, so an existing
file is kept and only a rule with no file yet gets the stub:

* a rule newly added to CPC appears as a `sorry` stub to discharge
* a rule whose *statement* changed keeps its old file and fails to build, which
  is how a proof needing attention shows up — build after an install to find
  them
* a reinstall over an up-to-date tree changes nothing; to see what the
  compiler emits for a rule that already has a file, delete it and install
  again

`--check` reports what an install would write and writes nothing, exiting 1 if
anything at all would change. It performs the install into a throwaway copy and
compares, so every other option means the same under `--check` as without it.

## The cached signature

`install/defs/Cpc.cached.eo` is the signature the packages were compiled from,
kept here as a single file: every `(include "...")` replaced by the text of the
file it names, each file appearing once, and comments dropped. It compiles to
the same Lean as the original tree, byte for byte, so `--cached` needs nothing
outside this repository — which is what the `regeneration` CI group uses to
check that the generated packages still match their signature.

An install of `Cpc` and `CpcMini` records the signature it compiled, and is the
only thing that writes the copy, so it and the packages stay in step. Two runs
record nothing and say so: `--rules`, which compiles a reduced calculus, and
`--package`, which installs something these two are not.

With an explicit signature, `--check` also compares the flattened source with
the cached copy whenever an install would record it. A changed signature must
be recorded even when it compiles to identical Lean; a source-comment-only
change does not affect the flattened copy. Missing or differing caches fail
the check, as does a failure to flatten the source. This applies to `CpcMini`
with its default rules too, but not to explicit `--rules`, custom packages, or
`--cached`. The check leaves both the package and the cached copy untouched.

The header of the file names the path the signature had, not the checkout or
the commit; the scripts print the commit they read, for the message of the
commit that updates the copy.

## The semantics

`install/defs/Cpc.eos` says what each symbol of the signature means, as a
transformation into the deep embedding, and this repository is where it lives.
The core SMT-LIB semantics it is written against live with the eoc compiler
rather than here: `tools/eoc/semantics/smt.eos` in
[cvc5/ethos](https://github.com/cvc5/ethos).

`Spec.lean` and the `SmtModel` modules are what the two compile to, so changing
what CPC means changes what satisfiability means in Logos.

In practice they only need to change when a new theory symbol is added, when
the formalized semantics of an operator is being revised, or when the Eunoia
compiler changes. Either can be replaced for a run: `--semantics PATH` names
another configuration of what the symbols of the signature mean, and
`--smt-semantics PATH` another of what the SMT-LIB symbols they are written
against mean. Both are options of `install-cpc.sh` and of `install-sig.sh`. For
example, to extend both semantics along with the signature:

```bash
install/install-cpc.sh ~/cvc5/proofs/eo/cpc/Cpc.eo \
  --semantics <my cpc semantics> --smt-semantics <my smt semantics>
```

This regenerates the Logos source against something other than the pair the
checked-in packages are of, so `--check` reports the tree as out of date until
the change lands in `install/defs/Cpc.eos` and in the `smt.eos` of the pinned
compiler.

## install-sig.sh

`install-cpc.sh` is `install-sig.sh` run once per package it was asked for.
Reach for `install-sig.sh` directly for a reduced calculus or a package of your
own; `install-cpc.sh` refuses `--package` rather than pass it on, since which
packages it writes is what `--all` and `--mini` say.

`--rules` selects more than which rule files are installed: the compiler builds
the whole package around only the rules given, so the signature-wide modules
describe a calculus containing just those. Running
`install/install-sig.sh --rules symm` against `Cpc` therefore guts the package
rather than refreshing one rule. Use it with `--package` or `--mini`.

`--mini` is the same install into `CpcMini` with the five rules
`symm contra refl scope trans`, no parser, imports rewritten to `CpcMini`, and
`partial def` rewritten to `def`.

`--ethos` redirects the build directory as well as the driver, in preference
to what `install/deps/eoc-env.sh` recorded, so a local checkout is never mixed
with `install/deps/`.

## Pinning

The Ethos commit is not an option. It is hardcoded as `ETHOS_VERSION` in
`get-eo-compiler.sh`. For internal development only,
`scripts/bump-eoc-version.py` moves it to the current head of `cvc5/ethos`'s `main` and
copies that same revision's `tools/eoc/semantics/development-cpc.eos` into the
authoritative `install/defs/Cpc.eos`. It then runs `get-eo-compiler.sh` and
`install/install-cpc.sh --all --cached`, regenerating both `Cpc` and `CpcMini`.
The full commit hash is recorded, so later installations use that revision even
after `main` advances. The helper does not fetch a new CPC signature or run the
Lean proof checks.

The Eunoia signature that Logos is compiled against is pinned by copy:
`install/defs/Cpc.cached.eo` is the one the packages were compiled from, and
`--cached` compiles exactly that. The `regeneration` CI group is what holds
the generated Lean to it.
