# Checking Lean-native proofs

The primary input format of Logos is the s-expression (Eunoia) syntax read by `logos` and
described in [parser.md](parser.md).  This document describes a secondary path: proofs
written directly as Lean evaluation scripts, read by the `logos-native` executable.  See
the [README](../README.md) for building the executables.

This path is experimental, and a development convenience rather than the primary entry
point, but it runs the same checks: see [What a `true` means](#what-a-true-means) below.

`logos-native` reads files containing Lean terms and an evaluation statement:

```bash
lake build logos-native
lake exe logos-native test/regress/test-simple.cpc.lean
```

The input is a file containing an evaluation statement to be read by the Lean parser.
An example of such a file is the following:

```
import Cpc.Native
open Eo
def t1 : Term := (Term.UConst 1 (Term.UOp UserOp.Int))
def t2 : Term := (Term.UConst 2 (Term.UOp UserOp.Int))
def t3 : Term := (Term.Apply (Term.UOp UserOp.eq) t2)
def t4 : Term := (Term.Apply t3 t1)
def t5 : Term := (Term.Apply (Term.UOp UserOp.eq) t1)
def t6 : Term := (Term.Apply t5 t2)
def t7 : Term := (Term.Apply (Term.UOp UserOp.not) t6)
def s0 : LogosState := logos_init_state
def s1 : LogosState := (logos_invoke_assume s0 t4)
def s2 : LogosState := (logos_invoke_assume s1 t7)
def s3 : LogosState := (logos_invoke_cmd s2 (CCmd.step CRule.symm CArgList.nil (CIndexList.cons 0 CIndexList.nil)))
def s4 : LogosState := (logos_invoke_cmd s3 (CCmd.step CRule.contra CArgList.nil (CIndexList.cons 2 (CIndexList.cons 0 CIndexList.nil))))
#eval!
(logos_state_is_refutation s4)
```

Proof checking succeeds if executing `logos-native` on one of these files returns `true`.

Logos assumes that scripts define a state that is constructed iteratively starting from
`logos_init_state`, followed by a sequence of `logos_invoke_assume` commands (the assumptions of the proof),
followed by a sequence of `logos_invoke_cmd` commands.
A state is a refutation if the last proven formula was `false` and if
all assumptions introduced via `assume_push` commands are closed by corresponding `step_pop` commands.
The semantics of these commands mimics the Eunoia logical framework;
for details see https://github.com/cvc5/ethos/blob/main/user_manual.md.

The examples in `test/regress/*.cpc.lean` are in this format; CI runs each of them through
`logos-native` and requires the output `true`.

## What a `true` means

A `true` from a script of the shape above means the same as `correct` from `logos`: the
conjunction of the assumptions the script names is unsatisfiable.  That is
`correct___logos_state_is_refutation` (`Cpc/Native/Correct.lean`):

```lean
theorem correct___logos_state_is_refutation (assums : List Term) (cmds : CCmdList)
    (h : logos_state_is_refutation (logos_run assums cmds) = true) :
    eo_satisfiability (logos_assumption_term assums) false
```

`Eo.logos_run` (`Cpc/Native.lean`) is the state a script of that shape builds, so the
theorem is about a script's own assumptions and commands, just as
`correct___logos_check_proof` is about the assumptions the parser read out of a file.

The two front ends run the same three checks — `Eo.logos_state_verdict_eq_verdict` proves
that a script computes exactly the `Eo.logos_verdict` that `logos` computes from the
parser's output.  A script has no list to hand back at the end, so the two side conditions
of `correct___eo_is_refutation` are decided one call at a time instead, and recorded in the
state as it goes:

* `logos_invoke_assume` pushes an input assumption only if it is Boolean-typed and closed
  (the guard `logos` applies, which `checkerTypeInvariant` and `StableAssumptionList` need),
  and records whether it has an SMT-LIB translation.
* `logos_invoke_cmd` records whether the command's arguments satisfy the per-rule
  translation side condition the rule's proof assumes.

Both are decided by the definitions of `Cpc/Proofs/Assumptions.lean` that `logos` uses, so
neither front end has its own copy.  `LogosState` is the whole interface a script needs: it
is the checker state together with those records, and a script never names anything else
internal to the checker.

Two differences from the `logos` path remain, neither of them about what a `true` means:

* `logos` distinguishes a proof it rejects (`incorrect`) from one it accepts but cannot
  translate (`incomplete`), and names the assumption or command at fault.  A script
  evaluates to a single Boolean, so both read as `false`; `Eo.logos_state_verdict` returns
  the same three-way `Eo.Verdict` for a script that wants it.
* the exit status of `logos-native` is the number of Lean elaboration errors, not the
  verdict; `logos` exits 0, 1 or 2 for `correct`, `incorrect` and `incomplete`.

What is unchecked is the *shape* of the script: `logos-native` elaborates the file as Lean
and reports the value of its `#eval!`, so a script that does something else returns
whatever it returns — that is why the section above says Logos *assumes* the shape.  This
is the counterpart here of the unverified parser on the `logos` side.
