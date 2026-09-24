module

public import CpcMini.Proofs.RuleLemmas
import all CpcMini.Proofs.CheckerCore

public section

open Eo
open SmtEval
open Smtm

/-- Shows that `invoke_step` preserves `localTruthInvariant_of_stuck`. -/
theorem invoke_step_preserves_localTruthInvariant_of_stuck
    (M : SmtModel) (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  __eo_cmd_step_proven s r args premises = Term.Stuck ->
  checkerLocalTruthInvariant M (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hStep
  have hStuck :
      __eo_invoke_cmd s (CCmd.step r args premises) = CState.Stuck :=
    invoke_step_eq_stuck_of_nonstuck s hNotStuck r args premises hStep
  simpa [hStuck] using checkerLocalTruthInvariant_stuck M

/-- Shows that `invoke_step` preserves `localTruthInvariant_of_contextual_true`. -/
theorem invoke_step_preserves_localTruthInvariant_of_contextual_true
    (M : SmtModel) (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) (P : Term) :
  checkerLocalTruthInvariant M s ->
  __eo_cmd_step_proven s r args premises = P ->
  P ≠ Term.Stuck ->
  ContextualTruth M (stateAssumes s) (statePushes s) P ->
  checkerLocalTruthInvariant M (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hs hStep hNe hP
  by_cases hTy : __eo_typeof P = Term.Bool
  · have hPost :
        __eo_invoke_cmd s (CCmd.step r args premises) = CState.cons (CStateObj.proven P) s :=
      invoke_step_eq_cons_of_nonstuck s hNotStuck r args premises P hStep hTy
    simpa [hPost] using
      push_proven_preserves_localTruthInvariant_of_contextual_true M s P hs hP
  · have hPost :
        __eo_invoke_cmd s (CCmd.step r args premises) = CState.Stuck :=
      invoke_step_eq_stuck_of_typeof_ne_bool s hNotStuck r args premises P hStep hTy
    simpa [hPost] using checkerLocalTruthInvariant_stuck M

/-- Shows that `invoke_step` preserves `localTruthInvariant`. -/
theorem invoke_step_preserves_localTruthInvariant
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerLocalTruthInvariant M s ->
  checkerExtraInvariant M s ->
  checkerTypeInvariant s ->
  checkerTranslationInvariant s ->
  cmdTranslationOk (CCmd.step r args premises) ->
  checkerLocalTruthInvariant M (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hs hsStable hsTy hsTrans hCmdTrans
  by_cases hTy : __eo_typeof (__eo_cmd_step_proven s r args premises) = Term.Bool
  · have hProg : __eo_cmd_step_proven s r args premises ≠ Term.Stuck :=
      term_ne_stuck_of_typeof_bool hTy
    have hFacts :
        CmdStepFacts M s (__eo_cmd_step_proven s r args premises) :=
      cmd_step_proven_facts_of_invariants M hM s hNotStuck r args premises
        hs hsStable hsTy hsTrans hCmdTrans hTy
    exact invoke_step_preserves_localTruthInvariant_of_contextual_true M s hNotStuck
      r args premises (__eo_cmd_step_proven s r args premises) hs rfl hProg
      hFacts.contextualTruth
  · have hPost :
          __eo_invoke_cmd s (CCmd.step r args premises) = CState.Stuck :=
        invoke_step_eq_stuck_of_typeof_ne_bool s hNotStuck r args premises
          (__eo_cmd_step_proven s r args premises) rfl hTy
    simpa [hPost] using checkerLocalTruthInvariant_stuck M

/-- Shows that `invoke_step` preserves `typeInvariant_of_stuck`. -/
theorem invoke_step_preserves_typeInvariant_of_stuck
    (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  __eo_cmd_step_proven s r args premises = Term.Stuck ->
  checkerTypeInvariant (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hStep
  have hStuck :
      __eo_invoke_cmd s (CCmd.step r args premises) = CState.Stuck :=
    invoke_step_eq_stuck_of_nonstuck s hNotStuck r args premises hStep
  simpa [hStuck] using checkerTypeInvariant_stuck

/-- Shows that `invoke_step` preserves `typeInvariant_of_nonstuck`. -/
theorem invoke_step_preserves_typeInvariant_of_nonstuck
    (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) (P : Term) :
  checkerTypeInvariant s ->
  __eo_cmd_step_proven s r args premises = P ->
  P ≠ Term.Stuck ->
  checkerTypeInvariant (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hs hStep hNe
  by_cases hTy : __eo_typeof P = Term.Bool
  · have hPost :
        __eo_invoke_cmd s (CCmd.step r args premises) = CState.cons (CStateObj.proven P) s :=
      invoke_step_eq_cons_of_nonstuck s hNotStuck r args premises P hStep hTy
    have hPush :
        checkerTypeInvariant (__eo_push_proven P s) :=
      push_proven_preserves_typeInvariant s P hs
    rw [push_proven_eq_cons_of_typeof_bool P s hTy] at hPush
    simpa [hPost] using hPush
  · have hPost :
        __eo_invoke_cmd s (CCmd.step r args premises) = CState.Stuck :=
      invoke_step_eq_stuck_of_typeof_ne_bool s hNotStuck r args premises P hStep hTy
    simpa [hPost] using checkerTypeInvariant_stuck

/-- Shows that `invoke_step` preserves `typeInvariant`. -/
theorem invoke_step_preserves_typeInvariant
    (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerTypeInvariant s ->
  checkerTypeInvariant (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hs
  by_cases hTy : __eo_typeof (__eo_cmd_step_proven s r args premises) = Term.Bool
  · have hProg : __eo_cmd_step_proven s r args premises ≠ Term.Stuck :=
      term_ne_stuck_of_typeof_bool hTy
    exact invoke_step_preserves_typeInvariant_of_nonstuck s hNotStuck
      r args premises (__eo_cmd_step_proven s r args premises) hs rfl hProg
  · have hPost :
          __eo_invoke_cmd s (CCmd.step r args premises) = CState.Stuck :=
        invoke_step_eq_stuck_of_typeof_ne_bool s hNotStuck r args premises
          (__eo_cmd_step_proven s r args premises) rfl hTy
    simpa [hPost] using checkerTypeInvariant_stuck

/-- Shows that `invoke_step` preserves `translationInvariant`. -/
theorem invoke_step_preserves_translationInvariant
    (M : SmtModel) (_hM : model_wf M)
    (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerLocalTruthInvariant M s ->
  checkerExtraInvariant M s ->
  checkerTypeInvariant s ->
  checkerTranslationInvariant s ->
  cmdTranslationOk (CCmd.step r args premises) ->
  checkerTranslationInvariant (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hs hsStable hsTy hsTrans hCmdTrans
  by_cases hTy : __eo_typeof (__eo_cmd_step_proven s r args premises) = Term.Bool
  · have hFacts :
        CmdStepFacts M s (__eo_cmd_step_proven s r args premises) :=
      cmd_step_proven_facts_of_invariants M _hM s hNotStuck r args premises
        hs hsStable hsTy hsTrans hCmdTrans hTy
    have hPTrans :
        RuleProofs.eo_has_smt_translation (__eo_cmd_step_proven s r args premises) :=
      hFacts.has_smt_translation
    have hPost :
          __eo_invoke_cmd s (CCmd.step r args premises) =
            CState.cons (CStateObj.proven (__eo_cmd_step_proven s r args premises)) s :=
        invoke_step_eq_cons_of_nonstuck s hNotStuck r args premises
          (__eo_cmd_step_proven s r args premises) rfl hTy
    have hPush :
        checkerTranslationInvariant
          (__eo_push_proven (__eo_cmd_step_proven s r args premises) s) :=
      push_proven_preserves_translationInvariant s
        (__eo_cmd_step_proven s r args premises) hsTrans hPTrans
    rw [push_proven_eq_cons_of_typeof_bool (__eo_cmd_step_proven s r args premises) s hTy] at hPush
    simpa [hPost] using hPush
  · have hPost :
          __eo_invoke_cmd s (CCmd.step r args premises) = CState.Stuck :=
        invoke_step_eq_stuck_of_typeof_ne_bool s hNotStuck r args premises
          (__eo_cmd_step_proven s r args premises) rfl hTy
    simpa [hPost] using checkerTranslationInvariant_stuck

/-- Auxiliary lemma for `invoke_cmd_step_pop_preserves_localTruthInvariant`. -/
theorem invoke_cmd_step_pop_preserves_localTruthInvariant_aux
    (M : SmtModel) (hM : model_wf M) :
  forall (root cur : CState) (r : CRule) (args : CArgList) (premises : CIndexList),
    checkerLocalTruthInvariant M root ->
    checkerLocalTruthInvariant M cur ->
    checkerExtraInvariant M root ->
    checkerTypeInvariant root ->
    checkerTranslationInvariant root ->
    stateAssumptionSuffix cur ->
    stateStepPopSuffix cur root ->
    checkerLocalTruthInvariant M (__eo_invoke_cmd_step_pop root cur r args premises)
:=
by
  intro root cur
  induction cur with
  | nil =>
      intro r args premises hsRoot hCur hsRootStable hsRootTy hsRootTrans hSuffix hCurSuffix
      simpa [__eo_invoke_cmd_step_pop] using checkerLocalTruthInvariant_stuck M
  | Stuck =>
      intro r args premises hsRoot hCur hsRootStable hsRootTy hsRootTrans hSuffix hCurSuffix
      cases hSuffix
  | cons so cur ih =>
      intro r args premises hsRoot hCur hsRootStable hsRootTy hsRootTrans hSuffix hCurSuffix
      cases so with
      | assume_push A =>
          cases hStep : native_teq (__eo_cmd_step_pop_proven root r args A premises) Term.Stuck with
          | false =>
              have hTail : checkerLocalTruthInvariant M cur := by
                simpa [checkerLocalTruthInvariant] using hCur
              by_cases hTy : __eo_typeof (__eo_cmd_step_pop_proven root r args A premises) = Term.Bool
              · have hPost :
                    __eo_invoke_cmd_step_pop root (CState.cons (CStateObj.assume_push A) cur) r args premises =
                      CState.cons (CStateObj.proven (__eo_cmd_step_pop_proven root r args A premises)) cur := by
                  simp [__eo_invoke_cmd_step_pop, push_proven_eq_cons_of_typeof_bool, hTy]
                have hFacts :
                    CmdStepFacts M cur
                      (__eo_cmd_step_pop_proven root r args A premises) :=
                  cmd_step_pop_proven_facts_of_invariants M hM root cur A r args premises
                    hsRoot hsRootStable hsRootTy hsRootTrans hCurSuffix hTy
                simpa [hPost] using
                  push_proven_preserves_localTruthInvariant_of_contextual_true M cur
                    (__eo_cmd_step_pop_proven root r args A premises) hTail
                    hFacts.contextualTruth
              · have hPost :
                    __eo_invoke_cmd_step_pop root (CState.cons (CStateObj.assume_push A) cur) r args premises =
                      CState.Stuck := by
                  simp [__eo_invoke_cmd_step_pop, push_proven_eq_stuck_of_typeof_ne_bool, hTy]
                simpa [hPost] using checkerLocalTruthInvariant_stuck M
          | true =>
              have hEq : __eo_cmd_step_pop_proven root r args A premises = Term.Stuck := by
                simpa [native_teq] using hStep
              simpa [__eo_invoke_cmd_step_pop, hEq, push_proven_eq_stuck_of_eq_stuck] using
                checkerLocalTruthInvariant_stuck M
      | assume A =>
          have hTail : stateAssumptionTail cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          have hStuck : __eo_invoke_cmd_step_pop root cur r args premises = CState.Stuck :=
            invoke_cmd_step_pop_of_assumptionTail root cur r args premises hTail
          simpa [__eo_invoke_cmd_step_pop, hStuck] using checkerLocalTruthInvariant_stuck M
      | proven P =>
          have hCurTail : checkerLocalTruthInvariant M cur :=
            checkerLocalTruthInvariant_tail M hCur
          have hSuffixTail : stateAssumptionSuffix cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          have hCurSuffixTail : stateStepPopSuffix cur root := by
            exact stateStepPopSuffix_trans
              (stateStepPopSuffix.proven P (stateStepPopSuffix.refl cur))
              hCurSuffix
          exact ih r args premises hsRoot hCurTail hsRootStable hsRootTy hsRootTrans
            hSuffixTail hCurSuffixTail

/-- Shows that `invoke_cmd_step_pop` preserves `localTruthInvariant`. -/
theorem invoke_cmd_step_pop_preserves_localTruthInvariant
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerLocalTruthInvariant M s ->
  checkerExtraInvariant M s ->
  checkerTypeInvariant s ->
  checkerTranslationInvariant s ->
  stateAssumptionSuffix s ->
  checkerLocalTruthInvariant M (__eo_invoke_cmd_step_pop s s r args premises) :=
by
  intro hs hsStable hsTy hsTrans hSuffix
  exact invoke_cmd_step_pop_preserves_localTruthInvariant_aux M hM s s r args premises
    hs hs hsStable hsTy hsTrans hSuffix (stateStepPopSuffix.refl s)

/-- Auxiliary lemma for `invoke_cmd_step_pop_preserves_typeInvariant`. -/
theorem invoke_cmd_step_pop_preserves_typeInvariant_aux :
  forall (root cur : CState) (r : CRule) (args : CArgList) (premises : CIndexList),
    checkerTypeInvariant cur ->
    stateAssumptionSuffix cur ->
    checkerTypeInvariant (__eo_invoke_cmd_step_pop root cur r args premises)
:=
by
  intro root cur
  induction cur with
  | nil =>
      intro r args premises hCur hSuffix
      simpa [__eo_invoke_cmd_step_pop] using checkerTypeInvariant_stuck
  | Stuck =>
      intro r args premises hCur hSuffix
      cases hSuffix
  | cons so cur ih =>
      intro r args premises hCur hSuffix
      cases so with
      | assume_push A =>
          have hTail : checkerTypeInvariant cur :=
            checkerTypeInvariant_tail hCur
          simpa [__eo_invoke_cmd_step_pop] using
            push_proven_preserves_typeInvariant cur (__eo_cmd_step_pop_proven root r args A premises) hTail
      | assume A =>
          have hTail : stateAssumptionTail cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          have hTailSuffix : stateAssumptionSuffix cur := stateAssumptionSuffix_of_tail hTail
          simpa [__eo_invoke_cmd_step_pop] using
            ih r args premises (checkerTypeInvariant_tail hCur) hTailSuffix
      | proven P =>
          have hTailSuffix : stateAssumptionSuffix cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          simpa [__eo_invoke_cmd_step_pop] using
            ih r args premises (checkerTypeInvariant_tail hCur) hTailSuffix

/-- Shows that `invoke_cmd_step_pop` preserves `typeInvariant`. -/
theorem invoke_cmd_step_pop_preserves_typeInvariant
    (s : CState) (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerTypeInvariant s ->
  stateAssumptionSuffix s ->
  checkerTypeInvariant (__eo_invoke_cmd_step_pop s s r args premises) :=
by
  intro hs hSuffix
  exact invoke_cmd_step_pop_preserves_typeInvariant_aux s s r args premises hs hSuffix

/-- Auxiliary lemma for `invoke_cmd_step_pop_preserves_translationInvariant`. -/
theorem invoke_cmd_step_pop_preserves_translationInvariant_aux
    (M : SmtModel) (hM : model_wf M) :
  forall (root cur : CState) (r : CRule) (args : CArgList) (premises : CIndexList),
    checkerLocalTruthInvariant M root ->
    checkerExtraInvariant M root ->
    checkerTypeInvariant root ->
    checkerTypeInvariant cur ->
    checkerTranslationInvariant root ->
    checkerTranslationInvariant cur ->
    stateAssumptionSuffix cur ->
    stateStepPopSuffix cur root ->
    checkerTranslationInvariant (__eo_invoke_cmd_step_pop root cur r args premises)
:=
by
  intro root cur
  induction cur with
  | nil =>
      intro r args premises hsRoot hsRootStable hsRootTy hsCurTy hsRootTrans hsCurTrans hSuffix hCurSuffix
      simpa [__eo_invoke_cmd_step_pop] using checkerTranslationInvariant_stuck
  | Stuck =>
      intro r args premises hsRoot hsRootStable hsRootTy hsCurTy hsRootTrans hsCurTrans hSuffix hCurSuffix
      cases hSuffix
  | cons so cur ih =>
      intro r args premises hsRoot hsRootStable hsRootTy hsCurTy hsRootTrans hsCurTrans hSuffix hCurSuffix
      cases so with
      | assume_push A =>
          cases hStep : native_teq (__eo_cmd_step_pop_proven root r args A premises) Term.Stuck with
          | false =>
              have hTail : checkerTranslationInvariant cur :=
                checkerTranslationInvariant_tail hsCurTrans
              by_cases hTy : __eo_typeof (__eo_cmd_step_pop_proven root r args A premises) = Term.Bool
              · have hPost :
                    __eo_invoke_cmd_step_pop root (CState.cons (CStateObj.assume_push A) cur) r args premises =
                      CState.cons (CStateObj.proven (__eo_cmd_step_pop_proven root r args A premises)) cur := by
                  simp [__eo_invoke_cmd_step_pop, push_proven_eq_cons_of_typeof_bool, hTy]
                have hFacts :
                    CmdStepFacts M cur
                      (__eo_cmd_step_pop_proven root r args A premises) :=
                  cmd_step_pop_proven_facts_of_invariants M hM root cur A r args premises
                    hsRoot hsRootStable hsRootTy hsRootTrans hCurSuffix hTy
                have hPTrans :
                    RuleProofs.eo_has_smt_translation (__eo_cmd_step_pop_proven root r args A premises) :=
                  hFacts.has_smt_translation
                have hPush :
                    checkerTranslationInvariant
                      (__eo_push_proven (__eo_cmd_step_pop_proven root r args A premises) cur) :=
                  push_proven_preserves_translationInvariant cur
                    (__eo_cmd_step_pop_proven root r args A premises) hTail hPTrans
                rw [push_proven_eq_cons_of_typeof_bool (__eo_cmd_step_pop_proven root r args A premises) cur hTy] at hPush
                simpa [hPost] using hPush
              · have hPost :
                    __eo_invoke_cmd_step_pop root (CState.cons (CStateObj.assume_push A) cur) r args premises =
                      CState.Stuck := by
                  simp [__eo_invoke_cmd_step_pop, push_proven_eq_stuck_of_typeof_ne_bool, hTy]
                simpa [hPost] using checkerTranslationInvariant_stuck
          | true =>
              have hEq : __eo_cmd_step_pop_proven root r args A premises = Term.Stuck := by
                simpa [native_teq] using hStep
              simpa [__eo_invoke_cmd_step_pop, hEq, push_proven_eq_stuck_of_eq_stuck] using
                checkerTranslationInvariant_stuck
      | assume A =>
          have hTail : stateAssumptionTail cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          have hStuck : __eo_invoke_cmd_step_pop root cur r args premises = CState.Stuck :=
            invoke_cmd_step_pop_of_assumptionTail root cur r args premises hTail
          simpa [__eo_invoke_cmd_step_pop, hStuck] using checkerTranslationInvariant_stuck
      | proven P =>
          have hTailSuffix : stateAssumptionSuffix cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          have hCurSuffixTail : stateStepPopSuffix cur root := by
            exact stateStepPopSuffix_trans
              (stateStepPopSuffix.proven P (stateStepPopSuffix.refl cur))
              hCurSuffix
          simpa [__eo_invoke_cmd_step_pop] using
            ih r args premises hsRoot hsRootStable hsRootTy
              (checkerTypeInvariant_tail hsCurTy) hsRootTrans
              (checkerTranslationInvariant_tail hsCurTrans) hTailSuffix
              hCurSuffixTail

/-- Shows that `invoke_cmd_step_pop` preserves `translationInvariant`. -/
theorem invoke_cmd_step_pop_preserves_translationInvariant
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerLocalTruthInvariant M s ->
  checkerExtraInvariant M s ->
  checkerTypeInvariant s ->
  checkerTranslationInvariant s ->
  stateAssumptionSuffix s ->
  checkerTranslationInvariant (__eo_invoke_cmd_step_pop s s r args premises) :=
by
  intro hs hsStable hsTy hsTrans hSuffix
  exact invoke_cmd_step_pop_preserves_translationInvariant_aux M hM s s r args premises
    hs hsStable hsTy hsTy hsTrans hsTrans hSuffix (stateStepPopSuffix.refl s)

/-- Auxiliary lemma for `invoke_cmd_step_pop_preserves_shapeInvariant`. -/
theorem invoke_cmd_step_pop_preserves_shapeInvariant_aux :
  forall (root cur : CState) (r : CRule) (args : CArgList) (premises : CIndexList),
    stateAssumptionSuffix cur ->
    checkerShapeInvariant (__eo_invoke_cmd_step_pop root cur r args premises)
:=
by
  intro root cur
  induction cur with
  | nil =>
      intro r args premises hSuffix
      simp [__eo_invoke_cmd_step_pop, checkerShapeInvariant]
  | Stuck =>
      intro r args premises hSuffix
      cases hSuffix
  | cons so cur ih =>
      intro r args premises hSuffix
      cases so with
      | assume_push A =>
          cases hStep : native_teq (__eo_cmd_step_pop_proven root r args A premises) Term.Stuck with
          | false =>
              have hTailSuffix : stateAssumptionSuffix cur := by
                simpa [stateAssumptionSuffix] using hSuffix
              by_cases hTy : __eo_typeof (__eo_cmd_step_pop_proven root r args A premises) = Term.Bool
              · have hPost :
                    __eo_invoke_cmd_step_pop root (CState.cons (CStateObj.assume_push A) cur) r args premises =
                      CState.cons (CStateObj.proven (__eo_cmd_step_pop_proven root r args A premises)) cur := by
                  simp [__eo_invoke_cmd_step_pop, push_proven_eq_cons_of_typeof_bool, hTy]
                simpa [hPost, checkerShapeInvariant, stateAssumptionSuffix] using hTailSuffix
              · have hPost :
                    __eo_invoke_cmd_step_pop root (CState.cons (CStateObj.assume_push A) cur) r args premises =
                      CState.Stuck := by
                  simp [__eo_invoke_cmd_step_pop, push_proven_eq_stuck_of_typeof_ne_bool, hTy]
                simp [hPost, checkerShapeInvariant]
          | true =>
              have hEq : __eo_cmd_step_pop_proven root r args A premises = Term.Stuck := by
                simp [native_teq] at hStep
                exact hStep
              simp [__eo_invoke_cmd_step_pop, hEq, push_proven_eq_stuck_of_eq_stuck, checkerShapeInvariant]
      | assume A =>
          have hTail : stateAssumptionTail cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          have hStuck : __eo_invoke_cmd_step_pop root cur r args premises = CState.Stuck :=
            invoke_cmd_step_pop_of_assumptionTail root cur r args premises hTail
          simp [__eo_invoke_cmd_step_pop, hStuck, checkerShapeInvariant]
      | proven P =>
          have hTailSuffix : stateAssumptionSuffix cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          simpa [__eo_invoke_cmd_step_pop] using ih r args premises hTailSuffix

/-- Shows that `invoke_cmd_step_pop` preserves `shapeInvariant`. -/
theorem invoke_cmd_step_pop_preserves_shapeInvariant
    (s : CState) (r : CRule) (args : CArgList) (premises : CIndexList) :
  stateAssumptionSuffix s ->
  checkerShapeInvariant (__eo_invoke_cmd_step_pop s s r args premises) :=
by
  intro hSuffix
  exact invoke_cmd_step_pop_preserves_shapeInvariant_aux s s r args premises hSuffix

/-- Shows that `invoke_cmd` preserves `localTruthInvariant_nonstuck`. -/
theorem invoke_cmd_preserves_localTruthInvariant_nonstuck (M : SmtModel) :
  forall _hM : model_wf M,
  forall s : CState, forall c : CCmd,
    checkerLocalTruthInvariant M s ->
    checkerExtraInvariant M s ->
    checkerTypeInvariant s ->
    checkerTranslationInvariant s ->
    cmdTranslationOk c ->
    stateAssumptionSuffix s ->
    s ≠ CState.Stuck ->
    checkerLocalTruthInvariant M (__eo_invoke_cmd s c)
:=
by
  intro hM s c hs hsStable hsTy hsTrans hCmdTrans hSuffix hNotStuck
  cases c with
  | assume_push A =>
      cases s with
      | nil =>
          change checkerLocalTruthInvariant M (__eo_push_assume_check (assumptionCheckGuard A) A CState.nil)
          exact push_assume_preserves_localTruthInvariant M CState.nil A hs
      | cons so s =>
          change checkerLocalTruthInvariant M (__eo_push_assume_check (assumptionCheckGuard A) A (CState.cons so s))
          exact push_assume_preserves_localTruthInvariant M (CState.cons so s) A hs
      | Stuck =>
          exact False.elim (hNotStuck rfl)
  | check_proven proven =>
      cases s with
      | nil =>
          simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerLocalTruthInvariant]
      | Stuck =>
          exact False.elim (hNotStuck rfl)
      | cons so s =>
          cases so with
          | assume A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerLocalTruthInvariant]
          | assume_push A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerLocalTruthInvariant]
          | proven F =>
              cases hEq : __eo_eq F proven <;>
                try
                  (simpa [__eo_push_proven_check, hEq] using
                    checkerLocalTruthInvariant_stuck M)
              case Boolean b =>
                cases b with
                | false =>
                    simpa [__eo_push_proven_check, hEq] using
                      checkerLocalTruthInvariant_stuck M
                | true =>
                    simpa [__eo_push_proven_check, hEq] using hs
  | step r args premises =>
      exact invoke_step_preserves_localTruthInvariant M hM s hNotStuck r args premises
        hs hsStable hsTy hsTrans hCmdTrans
  | step_pop r args premises =>
      cases s with
      | nil =>
          simpa [__eo_invoke_cmd] using
            invoke_cmd_step_pop_preserves_localTruthInvariant M hM CState.nil r args premises
              hs hsStable hsTy hsTrans hSuffix
      | cons so s =>
          simpa [__eo_invoke_cmd] using
            invoke_cmd_step_pop_preserves_localTruthInvariant M hM (CState.cons so s) r args premises
              hs hsStable hsTy hsTrans hSuffix
      | Stuck =>
          exact False.elim (hNotStuck rfl)

/-- Shows that `invoke_cmd` preserves `shapeInvariant_nonstuck`. -/
theorem invoke_cmd_preserves_shapeInvariant_nonstuck :
  forall s : CState, forall c : CCmd,
    checkerShapeInvariant s ->
    s ≠ CState.Stuck ->
    checkerShapeInvariant (__eo_invoke_cmd s c)
:=
by
  intro s c hShape hNotStuck
  have hSuffix : stateAssumptionSuffix s :=
    suffix_of_checkerShapeInvariant_nonstuck hShape hNotStuck
  cases c with
  | assume_push A =>
      cases s with
      | nil =>
          by_cases hGuard : assumptionCheckGuard A = Term.Boolean true
          · change checkerShapeInvariant
              (__eo_push_assume_check (assumptionCheckGuard A) A CState.nil)
            rw [push_assume_eq_cons_of_guard_true A CState.nil hGuard]
            simp [checkerShapeInvariant, stateAssumptionSuffix]
          · change checkerShapeInvariant
              (__eo_push_assume_check (assumptionCheckGuard A) A CState.nil)
            rw [push_assume_eq_stuck_of_guard_ne_true A CState.nil hGuard]
            simp [checkerShapeInvariant]
      | cons so s =>
          by_cases hGuard : assumptionCheckGuard A = Term.Boolean true
          · change checkerShapeInvariant
              (__eo_push_assume_check (assumptionCheckGuard A) A (CState.cons so s))
            rw [push_assume_eq_cons_of_guard_true A (CState.cons so s) hGuard]
            simpa [checkerShapeInvariant, stateAssumptionSuffix] using hSuffix
          · change checkerShapeInvariant
              (__eo_push_assume_check (assumptionCheckGuard A) A (CState.cons so s))
            rw [push_assume_eq_stuck_of_guard_ne_true A (CState.cons so s) hGuard]
            simp [checkerShapeInvariant]
      | Stuck =>
          exact False.elim (hNotStuck rfl)
  | check_proven proven =>
      cases s with
      | nil =>
          simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerShapeInvariant]
      | Stuck =>
          exact False.elim (hNotStuck rfl)
      | cons so s =>
          cases so with
          | assume A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerShapeInvariant]
          | assume_push A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerShapeInvariant]
          | proven F =>
              have hSuffixTail : stateAssumptionSuffix s := by
                simpa [stateAssumptionSuffix] using hSuffix
              cases hEq : __eo_eq F proven <;>
                try
                  (simp [__eo_push_proven_check, hEq, checkerShapeInvariant])
              case Boolean b =>
                cases b with
                | false =>
                    simp
                | true =>
                    simpa [__eo_push_proven_check, hEq, checkerShapeInvariant,
                      stateAssumptionSuffix] using
                      hSuffixTail
  | step r args premises =>
      cases s with
      | nil =>
          by_cases hTy : __eo_typeof (__eo_cmd_step_proven CState.nil r args premises) = Term.Bool
          · simp [__eo_invoke_cmd, push_proven_eq_cons_of_typeof_bool, hTy, checkerShapeInvariant,
              stateAssumptionSuffix]
          · simp [__eo_invoke_cmd, push_proven_eq_stuck_of_typeof_ne_bool, hTy, checkerShapeInvariant]
      | Stuck =>
          exact False.elim (hNotStuck rfl)
      | cons so s =>
          by_cases hTy : __eo_typeof (__eo_cmd_step_proven (CState.cons so s) r args premises) = Term.Bool
          · have hsimpa := hSuffix; (try simp [__eo_invoke_cmd, push_proven_eq_cons_of_typeof_bool, hTy, checkerShapeInvariant] at hsimpa ⊢); exact hsimpa
          · simp [__eo_invoke_cmd, push_proven_eq_stuck_of_typeof_ne_bool, hTy, checkerShapeInvariant]
  | step_pop r args premises =>
      cases s with
      | nil =>
          simpa [__eo_invoke_cmd] using invoke_cmd_step_pop_preserves_shapeInvariant CState.nil r args premises hSuffix
      | cons so s =>
          simpa [__eo_invoke_cmd] using
            invoke_cmd_step_pop_preserves_shapeInvariant (CState.cons so s) r args premises hSuffix
      | Stuck =>
          exact False.elim (hNotStuck rfl)

/-- Shows that `invoke_cmd` preserves `truthInvariant_nonstuck`. -/
theorem invoke_cmd_preserves_truthInvariant_nonstuck (M : SmtModel) :
  forall _hM : model_wf M,
  forall s : CState, forall c : CCmd,
    checkerLocalTruthInvariant M s ->
    checkerExtraInvariant M s ->
    checkerTypeInvariant s ->
    checkerTranslationInvariant s ->
    cmdTranslationOk c ->
    stateAssumptionSuffix s ->
    s ≠ CState.Stuck ->
    checkerTruthInvariant M (__eo_invoke_cmd s c)
:=
by
  intro hM s c hs hsStable hsTy hsTrans hCmdTrans hSuffix hNotStuck
  exact checkerLocalTruthInvariant_implies_truthInvariant M <|
    invoke_cmd_preserves_localTruthInvariant_nonstuck M hM s c hs hsStable hsTy hsTrans hCmdTrans hSuffix hNotStuck

/-- Shows that `invoke_cmd` preserves `typeInvariant_nonstuck`. -/
theorem invoke_cmd_preserves_typeInvariant_nonstuck :
  forall s : CState, forall c : CCmd,
    checkerTypeInvariant s ->
    stateAssumptionSuffix s ->
    s ≠ CState.Stuck ->
    checkerTypeInvariant (__eo_invoke_cmd s c)
:=
by
  intro s c hs hSuffix hNotStuck
  cases c with
  | assume_push A =>
      cases s with
      | nil =>
          change checkerTypeInvariant (__eo_push_assume_check (assumptionCheckGuard A) A CState.nil)
          exact push_assume_preserves_typeInvariant CState.nil A hs
      | cons so s =>
          change checkerTypeInvariant (__eo_push_assume_check (assumptionCheckGuard A) A (CState.cons so s))
          exact push_assume_preserves_typeInvariant (CState.cons so s) A hs
      | Stuck =>
          exact False.elim (hNotStuck rfl)
  | check_proven proven =>
      cases s with
      | nil =>
          simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerTypeInvariant]
      | Stuck =>
          exact False.elim (hNotStuck rfl)
      | cons so s =>
          cases so with
          | assume A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerTypeInvariant]
          | assume_push A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerTypeInvariant]
          | proven F =>
              have hHead := checkerTypeInvariant_head_proven F s hs
              have hTail : checkerTypeInvariant s := checkerTypeInvariant_tail hs
              cases hEq : __eo_eq F proven with
              | Boolean b =>
                  cases b with
                  | false =>
                      simp [__eo_invoke_cmd, __eo_push_proven_check, hEq, checkerTypeInvariant]
                  | true =>
                      simpa [__eo_invoke_cmd, __eo_push_proven_check, hEq, checkerTypeInvariant,
                        hHead.1, hHead.2] using hTail
              | _ =>
                  simp [__eo_invoke_cmd, __eo_push_proven_check, hEq, checkerTypeInvariant]
  | step r args premises =>
      exact invoke_step_preserves_typeInvariant s hNotStuck r args premises hs
  | step_pop r args premises =>
      cases s with
      | nil =>
          simpa [__eo_invoke_cmd] using
            invoke_cmd_step_pop_preserves_typeInvariant CState.nil r args premises hs hSuffix
      | cons so s =>
          simpa [__eo_invoke_cmd] using
            invoke_cmd_step_pop_preserves_typeInvariant (CState.cons so s) r args premises hs hSuffix
      | Stuck =>
          exact False.elim (hNotStuck rfl)

/-- Shows that `invoke_cmd` preserves `translationInvariant_nonstuck`. -/
theorem invoke_cmd_preserves_translationInvariant_nonstuck (M : SmtModel) :
  forall _hM : model_wf M,
  forall s : CState, forall c : CCmd,
    checkerLocalTruthInvariant M s ->
    checkerExtraInvariant M s ->
    checkerTypeInvariant s ->
    checkerTranslationInvariant s ->
    cmdTranslationOk c ->
    stateAssumptionSuffix s ->
    s ≠ CState.Stuck ->
    checkerTranslationInvariant (__eo_invoke_cmd s c)
:=
by
  intro hM s c hs hsStable hsTy hsTrans hCmdTrans hSuffix hNotStuck
  cases c with
  | assume_push A =>
      cases s with
      | nil =>
          change checkerTranslationInvariant (__eo_push_assume_check (assumptionCheckGuard A) A CState.nil)
          exact push_assume_preserves_translationInvariant CState.nil A hsTrans hCmdTrans
      | cons so s =>
          change checkerTranslationInvariant (__eo_push_assume_check (assumptionCheckGuard A) A (CState.cons so s))
          exact push_assume_preserves_translationInvariant (CState.cons so s) A hsTrans hCmdTrans
      | Stuck =>
          exact False.elim (hNotStuck rfl)
  | check_proven proven =>
      cases s with
      | nil =>
          simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerTranslationInvariant]
      | Stuck =>
          exact False.elim (hNotStuck rfl)
      | cons so s =>
          cases so with
          | assume A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerTranslationInvariant]
          | assume_push A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerTranslationInvariant]
          | proven F =>
              have hHead := checkerTranslationInvariant_head_proven F s hsTrans
              have hTail : checkerTranslationInvariant s := checkerTranslationInvariant_tail hsTrans
              cases hEq : __eo_eq F proven with
              | Boolean b =>
                  cases b with
                  | false =>
                      simp [__eo_invoke_cmd, __eo_push_proven_check, hEq, checkerTranslationInvariant]
                  | true =>
                      simpa [__eo_invoke_cmd, __eo_push_proven_check, hEq, checkerTranslationInvariant] using
                        (show RuleProofs.eo_has_smt_translation F ∧ checkerTranslationInvariant s from ⟨hHead, hTail⟩)
              | _ =>
                  simp [__eo_invoke_cmd, __eo_push_proven_check, hEq, checkerTranslationInvariant]
  | step r args premises =>
      exact invoke_step_preserves_translationInvariant M hM s hNotStuck r args premises
        hs hsStable hsTy hsTrans hCmdTrans
  | step_pop r args premises =>
      cases s with
      | nil =>
          simpa [__eo_invoke_cmd] using
            invoke_cmd_step_pop_preserves_translationInvariant M hM CState.nil r args premises
              hs hsStable hsTy hsTrans hSuffix
      | cons so s =>
          simpa [__eo_invoke_cmd] using
            invoke_cmd_step_pop_preserves_translationInvariant M hM (CState.cons so s) r args premises
              hs hsStable hsTy hsTrans hSuffix
      | Stuck =>
          exact False.elim (hNotStuck rfl)

/-- Shows that `invoke_cmd` preserves `stateInvariant_nonstuck`. -/
theorem invoke_cmd_preserves_stateInvariant_nonstuck (M : SmtModel) :
  forall _hM : model_wf M,
  forall s : CState, forall c : CCmd,
    checkerStateInvariant M s ->
    cmdTranslationOk c ->
    cmdExtraOk M c ->
    s ≠ CState.Stuck ->
    checkerStateInvariant M (__eo_invoke_cmd s c)
:=
by
  intro hM s c hs hCmdTrans hCmdStable hNotStuck
  have hSuffix := suffix_of_checkerShapeInvariant_nonstuck hs.1 hNotStuck
  have hLocal :
      checkerLocalTruthInvariant M (__eo_invoke_cmd s c) :=
    invoke_cmd_preserves_localTruthInvariant_nonstuck M hM s c hs.2.1 hs.2.2.1
      hs.2.2.2.1 hs.2.2.2.2 hCmdTrans hSuffix hNotStuck
  have hStable :
      checkerExtraInvariant M (__eo_invoke_cmd s c) :=
    invoke_cmd_preserves_extraInvariant_nonstuck M s c hs.2.2.1
      hCmdStable hSuffix hNotStuck
  have hType :
      checkerTypeInvariant (__eo_invoke_cmd s c) :=
    invoke_cmd_preserves_typeInvariant_nonstuck s c hs.2.2.2.1 hSuffix hNotStuck
  have hTrans :
      checkerTranslationInvariant (__eo_invoke_cmd s c) :=
    invoke_cmd_preserves_translationInvariant_nonstuck M hM s c hs.2.1 hs.2.2.1
      hs.2.2.2.1 hs.2.2.2.2 hCmdTrans hSuffix hNotStuck
  have hShape :
      checkerShapeInvariant (__eo_invoke_cmd s c) :=
    invoke_cmd_preserves_shapeInvariant_nonstuck s c hs.1 hNotStuck
  exact ⟨hShape, hLocal, hStable, hType, hTrans⟩

/-- Shows that `invoke_cmd` preserves `stateInvariant`. -/
theorem invoke_cmd_preserves_stateInvariant (M : SmtModel) :
  forall _hM : model_wf M,
  forall s : CState, forall c : CCmd,
    checkerStateInvariant M s ->
    cmdTranslationOk c ->
    cmdExtraOk M c ->
    checkerStateInvariant M (__eo_invoke_cmd s c)
:=
by
  intro hM s c hs hCmdTrans hCmdStable
  by_cases hStuck : s = CState.Stuck
  · subst hStuck
    have hInvStuck : checkerStateInvariant M CState.Stuck := by
      exact ⟨trivial, checkerLocalTruthInvariant_stuck M,
        checkerExtraInvariant_stuck M, checkerTypeInvariant_stuck,
        checkerTranslationInvariant_stuck⟩
    cases c <;> simpa [__eo_invoke_cmd, checkerStateInvariant] using hInvStuck
  · exact invoke_cmd_preserves_stateInvariant_nonstuck M hM s c hs hCmdTrans
      hCmdStable hStuck

/-- Shows that `invoke_cmd_list` preserves `stateInvariant`. -/
theorem invoke_cmd_list_preserves_stateInvariant (M : SmtModel) :
  forall _hM : model_wf M,
  forall s : CState, forall cs : CCmdList,
    checkerStateInvariant M s ->
    CmdListTranslationOk cs ->
    CmdListExtraOk M cs ->
    checkerStateInvariant M (__eo_invoke_cmd_list s cs)
:=
by
  intro hM s cs
  induction cs generalizing s with
  | nil =>
      intro hs hTrans hStable
      simpa [__eo_invoke_cmd_list] using hs
  | cons c cs ih =>
      intro hs hTrans hStable
      cases hTrans with
      | cons _ _ hCmd hTail =>
          cases hStable with
          | cons _ _ hCmdStable hTailStable =>
              have hstep : checkerStateInvariant M (__eo_invoke_cmd s c) :=
                invoke_cmd_preserves_stateInvariant M hM s c hs hCmd hCmdStable
              simpa [__eo_invoke_cmd_list] using
                ih (__eo_invoke_cmd s c) hstep hTail hTailStable

/-- A checked, translatable assumption list translates to a Boolean-typed SMT term.
The Boolean typing comes from the checker's assumption guard (via `stateOk`); translatability
alone only guarantees a non-`None` translation. -/
theorem eo_has_bool_type_of_translatableAssumptionList (F : CArgList) :
  TranslatableAssumptionList F ->
  stateOk (__eo_invoke_assume_list CState.nil F) ->
  RuleProofs.eo_has_bool_type (argListAssumes F) := by
  induction F with
  | nil =>
      intro _ _
      exact RuleProofs.eo_has_bool_type_true
  | cons A rest ih =>
      intro hF hOk
      obtain ⟨hA, hRestTrans⟩ := hF
      have hPushOk :
          stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest)) := by
        have hsimpa := hOk
        try simp [__eo_invoke_assume_list] at hsimpa ⊢
        exact hsimpa
      have hTyA : __eo_typeof A = Term.Bool :=
        push_input_assume_typeof_bool_of_stateOk A
          (__eo_invoke_assume_list CState.nil rest) hPushOk
      have hRestOk : stateOk (__eo_invoke_assume_list CState.nil rest) :=
        push_input_assume_reflects_stateOk A
          (__eo_invoke_assume_list CState.nil rest) hPushOk
      exact RuleProofs.eo_has_bool_type_and_of_bool_args A (argListAssumes rest)
        (RuleProofs.eo_typeof_bool_implies_has_bool_type A hA hTyA)
        (ih hRestTrans hRestOk)

/- correctness theorem for the checker -/
/-- Main soundness theorem showing that a successful checker run yields an EO refutation. -/
theorem correct___eo_is_refutation (F : CArgList) (pf : CCmdList) :
  TranslatableAssumptionList F ->
  CmdListTranslationOk pf ->
  (eo_is_refutation F pf) ->
  eo_satisfiability (argListAssumes F) false :=
by
  intro hFTrans hPfTrans hRef
  have hNoInterp :
      forall M : SmtModel, model_wf M -> ¬ (eo_interprets M (argListAssumes F) true) := by
    intro M hM hF
    cases hRef with
    | intro hChecker =>
        let S0 := __eo_invoke_assume_list CState.nil F
        let S1 := __eo_invoke_cmd_list S0 pf
        have hS1Ok : stateOk S1 := by
          simpa [S0, S1] using final_stateOk_of_checker_true F pf hChecker
        have hS0Ok : stateOk S0 := by
          simpa [S1] using invoke_cmd_list_reflects_stateOk S0 pf hS1Ok
        have hFStable : extraAssumptionListOk M F :=
          extraAssumptionListOk_of_stateOk_assume_list M hS0Ok
        have hInit : checkerStateInvariant M S0 := by
          simpa [S0] using checkerStateInvariant_after_assume_list M F hS0Ok
            hFTrans hFStable
        have hPfStable : CmdListExtraOk M pf :=
          cmdListExtraOk_of_stateOk_invoke_cmd_list M S0 pf hS1Ok
        have hSteps : checkerStateInvariant M S1 := by
          simpa [S0, S1] using invoke_cmd_list_preserves_stateInvariant M hM S0 pf
            hInit hPfTrans hPfStable
        exact refutation_contradiction_of_truthInvariant M F pf hF
          (checkerLocalTruthInvariant_implies_truthInvariant M hSteps.2.1) hChecker
  have hS0Ok : stateOk (__eo_invoke_assume_list CState.nil F) := by
    cases hRef with
    | intro hChecker =>
        exact invoke_cmd_list_reflects_stateOk (__eo_invoke_assume_list CState.nil F) pf
          (final_stateOk_of_checker_true F pf hChecker)
  exact RuleProofs.smt_satisfiability_false_of_no_true (argListAssumes F)
    (eo_has_bool_type_of_translatableAssumptionList F hFTrans hS0Ok) hNoInterp
