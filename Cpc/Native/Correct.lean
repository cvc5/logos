module

public import Cpc.Native
import all Cpc.Native
public import Cpc.ApiCorrect
import all Cpc.ApiCorrect

public section

/-!
# Soundness of the `logos-native` executable

`Cpc/ApiCorrect.lean` restates `correct___eo_is_refutation` about what the `logos`
executable runs.  This module does the same for the experimental Lean-native
front end (`MainNative.lean`, `docs/lean-native-proofs.md`), whose input is a
Lean script rather than a proof file.

It is a separate module because it imports `Cpc.Proofs.Checker`, which
`Cpc/Native.lean` does not: the front end itself has to stay cheap to build.
-/

open Eo
open SmtEval
open Smtm

/--
Soundness of `logos-native`, stated about the script it reads.

A Lean-native proof script builds a `LogosState` from `logos_init_state` by a
sequence of `logos_invoke_assume` calls followed by a sequence of
`logos_invoke_cmd` calls, which is `Eo.logos_run assums cmds` for the assumptions
and commands it names; `logos-native` reports the `logos_state_is_refutation` the
script evaluates.  So a `true` from such a script means the conjunction of the
assumptions it names is unsatisfiable -- exactly what `correct` from `logos` means
for the assumptions its parser read.

What is unverified here is the counterpart of the parser on the `logos` side:
nothing checks that a script builds its state this way.

`logos_state_verdict_eq_verdict` (`Cpc/Native.lean`) is what makes this the same
theorem: a script of that shape computes `logos_verdict` of its own assumptions
and commands, so the three checks are discharged there.
-/
theorem correct___logos_state_is_refutation (assums : List Term) (cmds : CCmdList)
    (h : logos_state_is_refutation (logos_run assums cmds) = true) :
    eo_satisfiability (logos_assumption_term assums) false := by
  apply correct___logos_verdict assums cmds
  rw [← logos_state_verdict_eq_verdict assums cmds]
  exact (logos_state_is_refutation_eq_correct _).mp h
