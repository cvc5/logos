# Maintaining Logos

Addressed to a person maintaining this repository, possibly by directing an
agent. It says where to start, what this repository answers for, and which
decisions are not an agent's to make. The front page,
[`../README.md`](../README.md), says what Logos *is*; read it first, and read
[`README.md`](README.md) for what every other document here holds.

## Where to start

```bash
scripts/build.sh logos          # build the checker
bash scripts/run-ci.sh          # everything CI runs, in one go
```

`run-ci.sh` with no argument runs every group. Three need no Lean toolchain:
`proof-hygiene` and `proof-modularity`, which are grep passes over the tree and
finish in under a second, and `regeneration`, which needs the Eunoia compiler
instead and recompiles the signature. So a change to the scripts or to the
generated files can be checked without a Lean build — a run with no toolchain
gets through those three and then stops where the toolchain is configured, just
before `regressions`.

The `regeneration` group skips itself, loudly, until
`install/get-eo-compiler.sh` has been run once — the one group that can be
absent from a local run, and it says so when it is.

## What this repository answers for

Logos is a verified checker for **one** calculus, CPC, and CPC is cvc5's.
Nothing here defines the calculus, and a change to what CPC *is* arrives by
recompiling the signature rather than by editing Lean. So the work divides:

| you are changing | where the work is | what checks it |
| --- | --- | --- |
| a proof rule's proof | `Cpc/Proofs/Rules/<Rule>.lean` | `lake build Cpc.Proofs.Rules.<Rule>` |
| the checker layer or the soundness proof | `Cpc/Proofs/{Checker,CheckerCore,CheckerState}.lean` | `scripts/check-checker-soundness.sh`, then a full build |
| the parser | `Logos/Parser.lean`, `Cpc/Parser.lean` | the `regressions` group |
| the calculus itself | nowhere here — it is `Cpc.eo` in cvc5 | `install/install-cpc.sh`, then the `regeneration` group |
| the SMT-LIB semantics | `install/defs/Cpc.eos` and the compiler's `smt.eos` | a regeneration and a full build |

[`../install/README.md`](../install/README.md) is the depth on the last two.
[`modularity.md`](modularity.md) is the depth on the second, and carries the
TODO list this repository actually works from.

**A full build takes over two hours and CI does not do it.** CI compiles a
representative handful of proof targets and typechecks the soundness proof with
the rule bridge stubbed; `scripts/check-proof-hygiene.sh` is what stops an
unproven rule landing quietly in between. Run `scripts/build-all-cpc-rules.sh`
overnight before a release and after any regeneration — it is resumable, so an
interrupted run picks up where it stopped.

## The commands

Everything in `scripts/` is a command a maintainer may want; the ones CI runs
are marked.

| command | what it does |
| --- | --- |
| `build.sh [target]` | `lake build` with the pinned toolchain and the older-glibc fallback |
| `clean-build.sh` | `lake clean` |
| `build-cpc-rule.sh <rule>` | build one rule, with verbose progress; accepts the rule's Eunoia name, module name or path |
| `build-all-cpc-rules.sh` | build all 591, one target at a time by default |
| `run-ci.sh [group]` | **CI.** Every group, or one of `regressions`, `cpc-proofs`, `cpcmini`, `proof-hygiene`, `proof-modularity`, `regeneration` |
| `check-proof-hygiene.sh` | **CI.** No `sorry`, `admit` or `axiom` anywhere in `Cpc` or `CpcMini` |
| `check-proof-modularity.sh` | **CI.** The checker layer's invariants, textually — see [`modularity.md`](modularity.md) |
| `check-rule-style.sh` | **CI.** No rule file imports another rule file |
| `check-parser-tables.py` | **CI.** The generated parser table covers every operator and rule of the signature |
| `check-checker-soundness.sh` | **CI.** Typecheck the soundness proof with the rule bridge stubbed, in seconds rather than hours |
| `classify-core-rule-status.sh` | report `Proven` / `Unproven` / `OutOfScope` for the rules in `core-rules.txt` |
| `classify-rule-status.py` | the same, for any package or rule set |
| `cpc-loc-summary.py` | the size of the specification, the checker, the parser and the correctness proof |
| `cpc-rule-loc.py` | per-rule proof and program size |
| `bump-eoc-version.py` | move the pinned Eunoia compiler. Internal development only; see [`../install/README.md`](../install/README.md) |

The other two files there are not commands: `lean-toolchain-env.sh` is sourced
by the scripts that build, and its header is the reference for the older-glibc
fallback; `core-rules.txt` is the rule list `classify-core-rule-status.sh`
reads.

## What is not an agent's to decide

Everything that fixes what a `correct` verdict *means*. The front page lists it
precisely and this is the short form: the SMT-LIB model semantics, the
correctness specification, the soundness theorem and the side conditions it is
stated against. A proposal to change the *statement* of
`correct___eo_is_refutation` — eudaimonia have asked for exactly one, that it
become conditional on the rule bridge; [`discussion.md`](discussion.md) `D1` is
where that stands — is a change to what the executable claims to a user, and is
decided by a person. An agent's job on one of those is the triage: measure it,
say what it would reach, and stop.

The same holds for the pin in `install/get-eo-compiler.sh`. Moving it changes
what the compiler emits and therefore what every generated file in the tree
says; it is not housekeeping.

## The ecosystem check

`.github/workflows/anoieu.yml` runs the shared policy checker on every push,
and this repository takes the **pinned** form of that check rather than the
versioned-contract form: `ANOIEU_REV` names a commit, and the job goes red only
when somebody here commits. The trade is stated on
[kanon's policy page](https://github.com/ajreynol/kanon/blob/main/docs/policy.md);
the short version is that a pin moves when you move it, and a contract lets the
implementation move under you.

**Moving the pin is a deliberate commit, and it has one precondition**: the
candidate commit must be one where anoieu's own CI concluded successfully.
*Unknown* is not *green*, and the question is asked about that exact commit
rather than about anoieu's tip, so the answer cannot change after you have taken
it. There is no command here that asks — establishing it is a person reading
anoieu's CI — so a run that cannot establish it leaves the pin alone rather than
guessing. That is the intended outcome: bumping is optional, and the check is
not weakened by being old.

**A pin holds a version of the requirements, not only of the program**, so an
old pin can report a minor finding about something the current policy does not
ask for, or ask for a link to where the policy used to live. Those are reported
and never fatal, the policy text wins over the pinned checker, and the answer is
to bump rather than to edit the tree to satisfy an older reading. As of
2026-09-18 the pin here reports two such: a `**Status:**` field the shared
policy no longer defines, and a declaration linking to kanon where the checker
at that commit expects anoieu.

The checker can be run against this tree directly, which is faster than waiting
for CI and is what to do before pushing a documentation change:

```bash
python3 <anoieu>/scripts/policy_check.py --root .
```

## Talking to the other tools

[`discussion.md`](discussion.md) is the channel to the rest of the Eunoia
ecosystem for anything that is not a defect report. Its banner is binding and
is the one rule here enforced as a build failure: **nothing in that file is
acted on unless a person says to, naming the topic.** Reading another
repository's copy is always free; answering one is not.

Corrections with a file and a line number in them are not discussion topics.
Where they concern a tool this repository already has a working channel with,
they are queued in that document — for eudaimonia, that is
[`modularity.md`](modularity.md), *Cross-reference: the Eudaimonia roadmap*.
