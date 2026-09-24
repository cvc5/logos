module

public import Cpc.Proofs.CheckerState
import all Cpc.Proofs.CheckerState
public import Cpc.Proofs.Closed.Support
import all Cpc.Proofs.Closed.Support

/-!
# The variable-stability invariant

The checker invariant carrying the `StableWhenTrueInAnyVarModel` side
condition, kept apart from the rest because it is the one invariant a calculus
may not need.

It exists so that binder-sensitive rules -- `instantiate`, `skolemize`,
`alpha_equiv` -- can be handed premise truth in a *variable-variant* model,
which is the `RulePremiseEvidence.true_in_var_model` field.  A calculus whose
rules never look under a binder can define `StableWhenTrueInAnyVarModel` as
`True`, as `CpcMini` does, and everything here is then discharged for free by
`checkerAssumptionStabilityInvariant_any`.

Keeping it in its own module is what lets `Cpc/Proofs/CheckerState.lean` stay
free of it entirely, and confines the rest of the commitment to the five decls
of `Cpc/Proofs/CheckerCore.lean` that mention it.
-/

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 0
/-- Every assumption of an input list remains true under variable-model changes. -/
inductive StableAssumptionList (M : SmtModel) : CArgList -> Prop
  | base : StableAssumptionList M CArgList.nil
  | step (A : Term) (rest : CArgList) :
      StableWhenTrueInAnyVarModel A ->
      StableAssumptionList M rest ->
      StableAssumptionList M (CArgList.cons A rest)
/-- The model-dependent stability side condition for commands that introduce assumptions. -/
def cmdAssumptionStabilityOk (M : SmtModel) : CCmd -> Prop
  | CCmd.assume_push A => StableWhenTrueInAnyVarModel A
  | _ => True
/-- Every command in a checker command list satisfies `cmdAssumptionStabilityOk`. -/
inductive CmdListAssumptionStabilityOk (M : SmtModel) : CCmdList -> Prop
  | nil : CmdListAssumptionStabilityOk M CCmdList.nil
  | cons (c : CCmd) (cs : CCmdList) :
      cmdAssumptionStabilityOk M c ->
      CmdListAssumptionStabilityOk M cs ->
      CmdListAssumptionStabilityOk M (CCmdList.cons c cs)
/- Variable-model stability for assumptions.

   The local truth invariant already records stability for derived facts.
   Assumptions and local pushes are base facts, so the checker needs one
   extra invariant for precisely those entries if they may be used as
   binder-congruence premises.
-/
/-- Assumptions and pushed assumptions remain true under variable-model changes whenever true. -/
def checkerAssumptionStabilityInvariant (M : SmtModel) : CState -> Prop
  | CState.nil => True
  | CState.cons (CStateObj.assume A) s =>
      StableWhenTrueInAnyVarModel A ∧ checkerAssumptionStabilityInvariant M s
  | CState.cons (CStateObj.assume_push A) s =>
      StableWhenTrueInAnyVarModel A ∧ checkerAssumptionStabilityInvariant M s
  | CState.cons (CStateObj.proven _) s =>
      checkerAssumptionStabilityInvariant M s
  | CState.Stuck => True
/-- Describes `checkerAssumptionStabilityInvariant` on the stuck state. -/
theorem checkerAssumptionStabilityInvariant_stuck (M : SmtModel) :
  checkerAssumptionStabilityInvariant M CState.Stuck :=
by
  trivial
/-- Derives `checkerAssumptionStabilityInvariant` from `stateStepPopSuffix`. -/
theorem checkerAssumptionStabilityInvariant_of_stateStepPopSuffix (M : SmtModel) :
  forall {cur root : CState},
    stateStepPopSuffix cur root ->
    checkerAssumptionStabilityInvariant M root ->
    checkerAssumptionStabilityInvariant M cur
:=
by
  intro cur root hSuffix
  induction hSuffix with
  | refl _ =>
      intro hsRoot
      exact hsRoot
  | proven P hSuffix ih =>
      intro hsRoot
      exact ih (by simpa [checkerAssumptionStabilityInvariant] using hsRoot)
/-- Shows how `checkerAssumptionStabilityInvariant` behaves on suffix tails. -/
theorem checkerAssumptionStabilityInvariant_tail (M : SmtModel) :
  forall {so : CStateObj} {s : CState},
    checkerAssumptionStabilityInvariant M (CState.cons so s) ->
    checkerAssumptionStabilityInvariant M s
:=
by
  intro so s hs
  cases so with
  | assume A =>
      exact hs.2
  | assume_push A =>
      exact hs.2
  | proven P =>
      simpa [checkerAssumptionStabilityInvariant] using hs
/-- The assumption-stability invariant is independent of the current model. -/
theorem checkerAssumptionStabilityInvariant_rebase (M N : SmtModel) :
  forall {s : CState},
    checkerAssumptionStabilityInvariant M s ->
    checkerAssumptionStabilityInvariant N s
:=
by
  intro s hs
  induction s with
  | nil =>
      trivial
  | Stuck =>
      trivial
  | cons so s ih =>
      cases so with
      | assume A =>
          exact ⟨hs.1, ih hs.2⟩
      | assume_push A =>
          exact ⟨hs.1, ih hs.2⟩
      | proven P =>
          exact ih (by simpa [checkerAssumptionStabilityInvariant] using hs)
/-- Transfers the active input assumptions across a variable-model change. -/
theorem stateAssumes_true_in_var_model_of_assumptionStability
    (M : SmtModel) (hM : model_wf M) :
  forall {s : CState},
    checkerAssumptionStabilityInvariant M s ->
    eo_interprets M (stateAssumes s) true ->
    forall (N : SmtModel),
      model_wf N ->
      model_agrees_on_globals M N ->
      eo_interprets N (stateAssumes s) true
:=
by
  intro s hStable hAss
  induction s with
  | nil =>
      intro N hN hAgree
      simpa [stateAssumes] using eo_interprets_true N
  | Stuck =>
      intro N hN hAgree
      exact False.elim (eo_interprets_stuck_true_absurd M (by simpa [stateAssumes] using hAss))
  | cons so s ih =>
      intro N hN hAgree
      cases so with
      | assume A =>
          have hA : eo_interprets M A true :=
            eo_interprets_and_left M A (stateAssumes s) hAss
          have hTailAss : eo_interprets M (stateAssumes s) true :=
            eo_interprets_and_right M A (stateAssumes s) hAss
          have hA' : eo_interprets N A true :=
            hStable.1 M hM hA N hN hAgree
          have hTail' : eo_interprets N (stateAssumes s) true :=
            ih hStable.2 hTailAss N hN hAgree
          simpa [stateAssumes] using
            eo_interprets_and_intro N A (stateAssumes s) hA' hTail'
      | assume_push A =>
          exact ih hStable.2 (by simpa [stateAssumes] using hAss) N hN hAgree
      | proven P =>
          exact ih (by simpa [checkerAssumptionStabilityInvariant] using hStable)
            (by simpa [stateAssumes] using hAss) N hN hAgree
/-- Transfers the active pushed assumptions across a variable-model change. -/
theorem statePushes_true_in_var_model_of_assumptionStability
    (M : SmtModel) (hM : model_wf M) :
  forall {s : CState},
    checkerAssumptionStabilityInvariant M s ->
    eo_interprets M (statePushes s) true ->
    forall (N : SmtModel),
      model_wf N ->
      model_agrees_on_globals M N ->
      eo_interprets N (statePushes s) true
:=
by
  intro s hStable hPush
  induction s with
  | nil =>
      intro N hN hAgree
      simpa [statePushes] using eo_interprets_true N
  | Stuck =>
      intro N hN hAgree
      exact False.elim (eo_interprets_stuck_true_absurd M (by simpa [statePushes] using hPush))
  | cons so s ih =>
      intro N hN hAgree
      cases so with
      | assume A =>
          exact ih hStable.2 (by simpa [statePushes] using hPush) N hN hAgree
      | assume_push A =>
          have hA : eo_interprets M A true :=
            eo_interprets_and_left M A (statePushes s) hPush
          have hTailPush : eo_interprets M (statePushes s) true :=
            eo_interprets_and_right M A (statePushes s) hPush
          have hA' : eo_interprets N A true :=
            hStable.1 M hM hA N hN hAgree
          have hTail' : eo_interprets N (statePushes s) true :=
            ih hStable.2 hTailPush N hN hAgree
          simpa [statePushes] using
            eo_interprets_and_intro N A (statePushes s) hA' hTail'
      | proven P =>
          exact ih (by simpa [checkerAssumptionStabilityInvariant] using hStable)
            (by simpa [statePushes] using hPush) N hN hAgree
/-- Describes `checkerAssumptionStabilityInvariant` after `assume_list`. -/
theorem checkerAssumptionStabilityInvariant_after_assume_list
    (M : SmtModel) (F : CArgList) :
  StableAssumptionList M F ->
  checkerAssumptionStabilityInvariant M (__eo_invoke_assume_list CState.nil F)
:=
by
  intro hStable
  induction hStable with
  | base =>
      simp [__eo_invoke_assume_list, checkerAssumptionStabilityInvariant]
  | step A rest hA hRest ih =>
      by_cases hGuard : assumptionCheckGuard A = Term.Boolean true
      · change checkerAssumptionStabilityInvariant M
          (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest))
        rw [push_input_assume_eq_cons_of_guard_true A
          (__eo_invoke_assume_list CState.nil rest) hGuard]
        simpa [checkerAssumptionStabilityInvariant] using
          (show StableWhenTrueInAnyVarModel A ∧
              checkerAssumptionStabilityInvariant M
                (__eo_invoke_assume_list CState.nil rest) from
            ⟨hA, ih⟩)
      · change checkerAssumptionStabilityInvariant M
          (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest))
        rw [push_input_assume_eq_stuck_of_guard_ne_true A
          (__eo_invoke_assume_list CState.nil rest) hGuard]
        exact checkerAssumptionStabilityInvariant_stuck M
/-- A successful checked input-assumption pass yields stable assumptions. -/
theorem stableAssumptionList_of_stateOk_assume_list (M : SmtModel) :
  forall {F : CArgList},
    stateOk (__eo_invoke_assume_list CState.nil F) ->
    StableAssumptionList M F
:=
by
  intro F
  induction F with
  | nil =>
      intro hOk
      exact StableAssumptionList.base
  | cons A rest ih =>
      intro hOk
      have hPushOk :
          stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest)) := by
        simpa [__eo_invoke_assume_list, assumptionCheckGuard] using hOk
      have hClosed : __eo_is_closed A = Term.Boolean true :=
        push_input_assume_closed_of_stateOk A
          (__eo_invoke_assume_list CState.nil rest) hPushOk
      have hRestOk : stateOk (__eo_invoke_assume_list CState.nil rest) :=
        push_input_assume_reflects_stateOk A
          (__eo_invoke_assume_list CState.nil rest) hPushOk
      exact StableAssumptionList.step A rest
        (stableWhenTrueInAnyVarModel_of_closed A hClosed)
        (ih hRestOk)
/-- A successful checked command invocation yields any stability invariant that the command introduces. -/
theorem cmdAssumptionStabilityOk_of_stateOk_invoke_cmd (M : SmtModel) :
  forall (s : CState) (c : CCmd),
    stateOk (__eo_invoke_cmd s c) ->
    cmdAssumptionStabilityOk M c
:=
by
  intro s c
  cases c with
  | assume_push A =>
      cases s with
      | nil =>
          intro hOk
          have hPushOk :
              stateOk (__eo_push_assume_check (assumptionCheckGuard A) A CState.nil) := by
            simpa [__eo_invoke_cmd, assumptionCheckGuard] using hOk
          exact stableWhenTrueInAnyVarModel_of_closed A
            (push_assume_closed_of_stateOk A CState.nil hPushOk)
      | Stuck =>
          intro hOk
          simp [__eo_invoke_cmd, stateOk] at hOk
      | cons so s =>
          intro hOk
          have hPushOk :
              stateOk (__eo_push_assume_check (assumptionCheckGuard A) A
                (CState.cons so s)) := by
            simpa [__eo_invoke_cmd, assumptionCheckGuard] using hOk
          exact stableWhenTrueInAnyVarModel_of_closed A
            (push_assume_closed_of_stateOk A (CState.cons so s) hPushOk)
  | check_proven proven =>
      intro hOk
      simp [cmdAssumptionStabilityOk]
  | step r args premises =>
      intro hOk
      simp [cmdAssumptionStabilityOk]
  | step_pop r args premises =>
      intro hOk
      simp [cmdAssumptionStabilityOk]
/-- A successful checked command list yields stability for every command-introduced assumption. -/
theorem cmdListAssumptionStabilityOk_of_stateOk_invoke_cmd_list (M : SmtModel) :
  forall (s : CState) (cs : CCmdList),
    stateOk (__eo_invoke_cmd_list s cs) ->
    CmdListAssumptionStabilityOk M cs
:=
by
  intro s cs
  induction cs generalizing s with
  | nil =>
      intro hOk
      exact CmdListAssumptionStabilityOk.nil
  | cons c cs ih =>
      intro hOk
      have hTailOk :
          stateOk (__eo_invoke_cmd_list (__eo_invoke_cmd s c) cs) := by
        simpa [__eo_invoke_cmd_list] using hOk
      have hStepOk : stateOk (__eo_invoke_cmd s c) :=
        invoke_cmd_list_reflects_stateOk (__eo_invoke_cmd s c) cs hTailOk
      exact CmdListAssumptionStabilityOk.cons c cs
        (cmdAssumptionStabilityOk_of_stateOk_invoke_cmd M s c hStepOk)
        (ih (__eo_invoke_cmd s c) hTailOk)

/-!
## Preservation of the stability invariant by the checker commands
-/

/-- Shows that `push_assume` preserves `checkerAssumptionStabilityInvariant`. -/
theorem push_assume_preserves_assumptionStabilityInvariant
    (M : SmtModel) (s : CState) (A : Term) :
  StableWhenTrueInAnyVarModel A ->
  checkerAssumptionStabilityInvariant M s ->
  checkerAssumptionStabilityInvariant M
    (__eo_push_assume_check (assumptionCheckGuard A) A s) :=
by
  intro hA hs
  by_cases hGuard : assumptionCheckGuard A = Term.Boolean true
  · have hsimpa :
        StableWhenTrueInAnyVarModel A ∧ checkerAssumptionStabilityInvariant M s :=
      ⟨hA, hs⟩
    try simp [hGuard] at hsimpa ⊢
    exact hsimpa
  · simpa [push_assume_eq_stuck_of_guard_ne_true, hGuard] using
      checkerAssumptionStabilityInvariant_stuck M

/-- Shows that `push_proven` preserves `checkerAssumptionStabilityInvariant`. -/
theorem push_proven_preserves_assumptionStabilityInvariant
    (M : SmtModel) (s : CState) (P : Term) :
  checkerAssumptionStabilityInvariant M s ->
  checkerAssumptionStabilityInvariant M (__eo_push_proven P s) :=
by
  intro hs
  by_cases hTy : __eo_typeof P = Term.Bool
  · simpa [push_proven_eq_cons_of_typeof_bool, hTy,
      checkerAssumptionStabilityInvariant] using hs
  · simpa [push_proven_eq_stuck_of_typeof_ne_bool, hTy] using
      checkerAssumptionStabilityInvariant_stuck M

/-- Shows that `invoke_step` preserves `checkerAssumptionStabilityInvariant`. -/
theorem invoke_step_preserves_assumptionStabilityInvariant
    (M : SmtModel) (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerAssumptionStabilityInvariant M s ->
  checkerAssumptionStabilityInvariant M (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hs
  rw [invoke_step_eq_of_nonstuck s hNotStuck r args premises]
  exact push_proven_preserves_assumptionStabilityInvariant M s
    (__eo_cmd_step_proven s r args premises) hs

/-- Auxiliary lemma for `invoke_cmd_step_pop_preserves_assumptionStabilityInvariant`. -/
theorem invoke_cmd_step_pop_preserves_assumptionStabilityInvariant_aux (M : SmtModel) :
  forall (root cur : CState) (r : CRule) (args : CArgList) (premises : CIndexList),
    checkerAssumptionStabilityInvariant M cur ->
    stateAssumptionSuffix cur ->
    checkerAssumptionStabilityInvariant M (__eo_invoke_cmd_step_pop root cur r args premises)
:=
by
  intro root cur
  induction cur with
  | nil =>
      intro r args premises hCur hSuffix
      simpa [__eo_invoke_cmd_step_pop] using checkerAssumptionStabilityInvariant_stuck M
  | Stuck =>
      intro r args premises hCur hSuffix
      cases hSuffix
  | cons so cur ih =>
      intro r args premises hCur hSuffix
      cases so with
      | assume_push A =>
          have hTail : checkerAssumptionStabilityInvariant M cur :=
            checkerAssumptionStabilityInvariant_tail M hCur
          simpa [__eo_invoke_cmd_step_pop] using
            push_proven_preserves_assumptionStabilityInvariant M cur
              (__eo_cmd_step_pop_proven root r args A premises) hTail
      | assume A =>
          have hTail : stateAssumptionTail cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          have hStuck : __eo_invoke_cmd_step_pop root cur r args premises = CState.Stuck :=
            invoke_cmd_step_pop_of_assumptionTail root cur r args premises hTail
          simpa [__eo_invoke_cmd_step_pop, hStuck] using
            checkerAssumptionStabilityInvariant_stuck M
      | proven P =>
          have hTailSuffix : stateAssumptionSuffix cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          simpa [__eo_invoke_cmd_step_pop] using
            ih r args premises (checkerAssumptionStabilityInvariant_tail M hCur)
              hTailSuffix

/-- Shows that `invoke_cmd_step_pop` preserves `checkerAssumptionStabilityInvariant`. -/
theorem invoke_cmd_step_pop_preserves_assumptionStabilityInvariant
    (M : SmtModel) (s : CState) (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerAssumptionStabilityInvariant M s ->
  stateAssumptionSuffix s ->
  checkerAssumptionStabilityInvariant M (__eo_invoke_cmd_step_pop s s r args premises) :=
by
  intro hs hSuffix
  exact invoke_cmd_step_pop_preserves_assumptionStabilityInvariant_aux M s s r args premises
    hs hSuffix

/-- Shows that `invoke_cmd` preserves `checkerAssumptionStabilityInvariant_nonstuck`. -/
theorem invoke_cmd_preserves_assumptionStabilityInvariant_nonstuck (M : SmtModel) :
  forall s : CState, forall c : CCmd,
    checkerAssumptionStabilityInvariant M s ->
    cmdAssumptionStabilityOk M c ->
    stateAssumptionSuffix s ->
    s ≠ CState.Stuck ->
    checkerAssumptionStabilityInvariant M (__eo_invoke_cmd s c)
:=
by
  intro s c hs hCmdStable hSuffix hNotStuck
  cases c with
  | assume_push A =>
      cases s with
      | nil =>
          change checkerAssumptionStabilityInvariant M
            (__eo_push_assume_check (assumptionCheckGuard A) A CState.nil)
          exact push_assume_preserves_assumptionStabilityInvariant M CState.nil A
            hCmdStable hs
      | cons so s =>
          change checkerAssumptionStabilityInvariant M
            (__eo_push_assume_check (assumptionCheckGuard A) A (CState.cons so s))
          exact push_assume_preserves_assumptionStabilityInvariant M (CState.cons so s) A
            hCmdStable hs
      | Stuck =>
          exact False.elim (hNotStuck rfl)
  | check_proven proven =>
      cases s with
      | nil =>
          simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerAssumptionStabilityInvariant]
      | Stuck =>
          exact False.elim (hNotStuck rfl)
      | cons so s =>
          cases so with
          | assume A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven,
                checkerAssumptionStabilityInvariant]
          | assume_push A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven,
                checkerAssumptionStabilityInvariant]
          | proven F =>
              cases hEq : __eo_eq F proven <;>
                try
                  (simpa [__eo_push_proven_check, hEq] using
                    checkerAssumptionStabilityInvariant_stuck M)
              case Boolean b =>
                cases b with
                | false =>
                    simpa [__eo_push_proven_check, hEq] using
                      checkerAssumptionStabilityInvariant_stuck M
                | true =>
                    simpa [__eo_push_proven_check, hEq,
                      checkerAssumptionStabilityInvariant] using hs
  | step r args premises =>
      exact invoke_step_preserves_assumptionStabilityInvariant M s hNotStuck
        r args premises hs
  | step_pop r args premises =>
      cases s with
      | nil =>
          simpa [__eo_invoke_cmd] using
            invoke_cmd_step_pop_preserves_assumptionStabilityInvariant M CState.nil
              r args premises hs hSuffix
      | cons so s =>
          simpa [__eo_invoke_cmd] using
            invoke_cmd_step_pop_preserves_assumptionStabilityInvariant M
              (CState.cons so s) r args premises hs hSuffix
      | Stuck =>
          exact False.elim (hNotStuck rfl)

/-!
## The calculus-independent view of this invariant

`Proofs/Checker.lean` is written against the four names below rather than
against the stability invariant itself.  What it needs is *an* extra invariant
on the checker state that every command preserves -- not this particular one.

A calculus that needs no extra invariant points `checkerExtraInvariant` at
`fun _ _ => True`; one that needs a different invariant points these four at
it, supplies the preservation theorem, and `Checker.lean` is unchanged.  They
are `abbrev`s so that the generated `Proofs/RuleLemmas.lean`, which names the
underlying invariant, accepts them without a wrapper.
-/

/-- The extra, calculus-supplied component of `checkerStateInvariant`. -/
abbrev checkerExtraInvariant (M : SmtModel) (s : CState) : Prop :=
  checkerAssumptionStabilityInvariant M s

/-- The extra side condition a single checker command must satisfy. -/
abbrev cmdExtraOk (M : SmtModel) (c : CCmd) : Prop :=
  cmdAssumptionStabilityOk M c

/-- `cmdExtraOk` for every command of a checker command list. -/
abbrev CmdListExtraOk (M : SmtModel) (cs : CCmdList) : Prop :=
  CmdListAssumptionStabilityOk M cs

/-- The extra side condition on an input assumption list. -/
abbrev extraAssumptionListOk (M : SmtModel) (F : CArgList) : Prop :=
  StableAssumptionList M F

/-- Describes `checkerExtraInvariant` on the stuck state. -/
theorem checkerExtraInvariant_stuck (M : SmtModel) :
  checkerExtraInvariant M CState.Stuck :=
  checkerAssumptionStabilityInvariant_stuck M

/-- Describes `checkerExtraInvariant` after `assume_list`. -/
theorem checkerExtraInvariant_after_assume_list (M : SmtModel) (F : CArgList) :
  extraAssumptionListOk M F ->
  checkerExtraInvariant M (__eo_invoke_assume_list CState.nil F) :=
  checkerAssumptionStabilityInvariant_after_assume_list M F

/-- A successful checked input-assumption pass yields `extraAssumptionListOk`. -/
theorem extraAssumptionListOk_of_stateOk_assume_list (M : SmtModel) {F : CArgList} :
  stateOk (__eo_invoke_assume_list CState.nil F) ->
  extraAssumptionListOk M F :=
  stableAssumptionList_of_stateOk_assume_list M

/-- A successful checked command list satisfies `CmdListExtraOk`. -/
theorem cmdListExtraOk_of_stateOk_invoke_cmd_list (M : SmtModel)
    (s : CState) (cs : CCmdList) :
  stateOk (__eo_invoke_cmd_list s cs) ->
  CmdListExtraOk M cs :=
  cmdListAssumptionStabilityOk_of_stateOk_invoke_cmd_list M s cs

/-- Shows that `invoke_cmd` preserves `checkerExtraInvariant`. -/
theorem invoke_cmd_preserves_extraInvariant_nonstuck (M : SmtModel)
    (s : CState) (c : CCmd) :
  checkerExtraInvariant M s ->
  cmdExtraOk M c ->
  stateAssumptionSuffix s ->
  s ≠ CState.Stuck ->
  checkerExtraInvariant M (__eo_invoke_cmd s c) :=
  invoke_cmd_preserves_assumptionStabilityInvariant_nonstuck M s c
