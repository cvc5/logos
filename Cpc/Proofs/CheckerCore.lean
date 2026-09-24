module

public import Cpc.Proofs.CheckerState
import all Cpc.Proofs.CheckerState
public import Cpc.Proofs.Invariants.Stability
import all Cpc.Proofs.Invariants.Stability

/-!
# Checker invariants and the rule bridge

Each invariant says what holds of every object on the checker stack; together
they are `checkerStateInvariant`, which `Cpc/Proofs/Checker.lean` shows every
checker command preserves.

`CmdStepFacts` and `cmd_step_facts_of_rule_properties` are the seam the
generated `Cpc/Proofs/RuleLemmas.lean` targets: they turn what a rule proves
about its premises into what the checker needs about its conclusion.
-/

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 0
/- Indexed truth invariant: under globally true assumptions and local pushes,
   every indexed state entry is true. Since `CStateObj.Stuck` has been
   removed, indexed lookup can be handled directly from the semantic context,
   without extra per-rule premise side lemmas. -/
/-- Global truth invariant requiring every proven term in the state to evaluate to `true`. -/
def checkerTruthInvariant (M : SmtModel) : CState -> Prop
  | CState.Stuck => True
  | s =>
      ∀ n : native_Int,
        eo_interprets M (stateAssumes s) true ->
        eo_interprets M (statePushes s) true ->
        eo_interprets M (__eo_state_proven_nth s n) true
/-- Describes `checkerTruthInvariant` on the stuck state. -/
theorem checkerTruthInvariant_stuck (M : SmtModel) :
  checkerTruthInvariant M CState.Stuck :=
by
  trivial
/- Structural checker-side typing invariant.

   Every state entry recorded by the checker carries a checker-side Bool guard.
   This matches the operational checks for initial assumptions, `assume_push`,
   and `push_proven`.
-/
/-- Type invariant requiring every stored assumption and proven term to have EO Boolean type. -/
def checkerTypeInvariant : CState -> Prop
  | CState.nil => True
  | CState.cons (CStateObj.assume A) s =>
      A ≠ Term.Stuck ∧ __eo_typeof A = Term.Bool ∧ checkerTypeInvariant s
  | CState.cons (CStateObj.assume_push A) s =>
      A ≠ Term.Stuck ∧ __eo_typeof A = Term.Bool ∧ checkerTypeInvariant s
  | CState.cons (CStateObj.proven P) s =>
      P ≠ Term.Stuck ∧ __eo_typeof P = Term.Bool ∧ checkerTypeInvariant s
  | CState.Stuck => True
/-- Describes `checkerTypeInvariant` on the stuck state. -/
theorem checkerTypeInvariant_stuck :
  checkerTypeInvariant CState.Stuck :=
by
  trivial
/-- Translation invariant requiring an SMT translation for every stored assumption and proven term. -/
def checkerTranslationInvariant : CState -> Prop
  | CState.nil => True
  | CState.cons (CStateObj.assume A) s =>
      RuleProofs.eo_has_smt_translation A ∧ checkerTranslationInvariant s
  | CState.cons (CStateObj.assume_push A) s =>
      RuleProofs.eo_has_smt_translation A ∧ checkerTranslationInvariant s
  | CState.cons (CStateObj.proven P) s =>
      RuleProofs.eo_has_smt_translation P ∧ checkerTranslationInvariant s
  | CState.Stuck => True
/-- Describes `checkerTranslationInvariant` on the stuck state. -/
theorem checkerTranslationInvariant_stuck :
  checkerTranslationInvariant CState.Stuck :=
by
  trivial
/- Local recursive truth invariant.

   A proved formula is stored together with the tail state whose assumptions
   and local pushes form the context in which that proof is valid. This is the
   invariant shape that matches `step_pop`, since popping a local assumption
   keeps the tail unchanged and only replaces the scoped prefix by one new
   proved implication. -/
/-- Local truth invariant relating each proven term to the assumptions that were active when it was derived. -/
def checkerLocalTruthInvariant (M : SmtModel) : CState -> Prop
  | CState.nil => True
  | CState.cons (CStateObj.proven P) s =>
      ContextualTruth M (stateAssumes s) (statePushes s) P ∧
      checkerLocalTruthInvariant M s
  | CState.cons _ s => checkerLocalTruthInvariant M s
  | CState.Stuck => True
/-- Describes `checkerLocalTruthInvariant` on the stuck state. -/
theorem checkerLocalTruthInvariant_stuck (M : SmtModel) :
  checkerLocalTruthInvariant M CState.Stuck :=
by
  trivial
/-- Shows how `checkerTypeInvariant` behaves on suffix tails. -/
theorem checkerTypeInvariant_tail :
  forall {so : CStateObj} {s : CState},
    checkerTypeInvariant (CState.cons so s) ->
    checkerTypeInvariant s
:=
by
  intro so s hs
  cases so with
  | assume A =>
      exact hs.2.2
  | assume_push A =>
      exact hs.2.2
  | proven P =>
      exact hs.2.2
/-- Lemma about `checkerTypeInvariant_head_assume`. -/
theorem checkerTypeInvariant_head_assume
    (A : Term) (s : CState) :
  checkerTypeInvariant (CState.cons (CStateObj.assume A) s) ->
  A ≠ Term.Stuck ∧ __eo_typeof A = Term.Bool :=
by
  intro hs
  exact ⟨hs.1, hs.2.1⟩
/-- Lemma about `checkerTypeInvariant_head_assume_push`. -/
theorem checkerTypeInvariant_head_assume_push
    (A : Term) (s : CState) :
  checkerTypeInvariant (CState.cons (CStateObj.assume_push A) s) ->
  A ≠ Term.Stuck ∧ __eo_typeof A = Term.Bool :=
by
  intro hs
  exact ⟨hs.1, hs.2.1⟩
/-- Lemma about `checkerTypeInvariant_head_proven`. -/
theorem checkerTypeInvariant_head_proven
    (P : Term) (s : CState) :
  checkerTypeInvariant (CState.cons (CStateObj.proven P) s) ->
  P ≠ Term.Stuck ∧ __eo_typeof P = Term.Bool :=
by
  intro hs
  exact ⟨hs.1, hs.2.1⟩
/-- Retrieves the `checkerTypeInvariant` fact at a given index. -/
theorem checkerTypeInvariant_at :
  forall {s : CState},
    checkerTypeInvariant s ->
    forall n : native_Int,
      __eo_state_proven_nth s n ≠ Term.Stuck ∧
      __eo_typeof (__eo_state_proven_nth s n) = Term.Bool
:=
by
  intro s hs
  induction s with
  | nil =>
      intro n
      constructor
      · simp [__eo_state_proven_nth]
      · change __eo_typeof (Term.Boolean true) = Term.Bool
        native_decide
  | Stuck =>
      intro n
      constructor
      · simp [__eo_state_proven_nth]
      · change __eo_typeof (Term.Boolean true) = Term.Bool
        native_decide
  | cons so s ih =>
      intro n
      by_cases hZero : n = 0
      · subst hZero
        cases so with
        | assume A =>
            simpa [__eo_state_proven_nth, __eo_StateObj_proven] using checkerTypeInvariant_head_assume A s hs
        | assume_push A =>
            simpa [__eo_state_proven_nth, __eo_StateObj_proven] using checkerTypeInvariant_head_assume_push A s hs
        | proven P =>
            simpa [__eo_state_proven_nth, __eo_StateObj_proven] using checkerTypeInvariant_head_proven P s hs
      · cases so with
        | assume A =>
            simpa [__eo_state_proven_nth, hZero] using
              ih (checkerTypeInvariant_tail hs) (native_zplus n (native_zneg 1))
        | assume_push A =>
            simpa [__eo_state_proven_nth, hZero] using
              ih (checkerTypeInvariant_tail hs) (native_zplus n (native_zneg 1))
        | proven P =>
            simpa [__eo_state_proven_nth, hZero] using
              ih (checkerTypeInvariant_tail hs) (native_zplus n (native_zneg 1))
/-- Shows how `checkerTranslationInvariant` behaves on suffix tails. -/
theorem checkerTranslationInvariant_tail :
  forall {so : CStateObj} {s : CState},
    checkerTranslationInvariant (CState.cons so s) ->
    checkerTranslationInvariant s
:=
by
  intro so s hs
  cases so <;> exact hs.2
/-- Lemma about `checkerTranslationInvariant_head_assume`. -/
theorem checkerTranslationInvariant_head_assume
    (A : Term) (s : CState) :
  checkerTranslationInvariant (CState.cons (CStateObj.assume A) s) ->
  RuleProofs.eo_has_smt_translation A :=
by
  intro hs
  exact hs.1
/-- Lemma about `checkerTranslationInvariant_head_assume_push`. -/
theorem checkerTranslationInvariant_head_assume_push
    (A : Term) (s : CState) :
  checkerTranslationInvariant (CState.cons (CStateObj.assume_push A) s) ->
  RuleProofs.eo_has_smt_translation A :=
by
  intro hs
  exact hs.1
/-- Lemma about `checkerTranslationInvariant_head_proven`. -/
theorem checkerTranslationInvariant_head_proven
    (P : Term) (s : CState) :
  checkerTranslationInvariant (CState.cons (CStateObj.proven P) s) ->
  RuleProofs.eo_has_smt_translation P :=
by
  intro hs
  exact hs.1
/-- Retrieves the `checkerTranslationInvariant` fact at a given index. -/
theorem checkerTranslationInvariant_at :
  forall {s : CState},
    checkerTranslationInvariant s ->
    forall n : native_Int,
      RuleProofs.eo_has_smt_translation (__eo_state_proven_nth s n)
:=
by
  intro s hs
  induction s with
  | nil =>
      intro n
      simpa [__eo_state_proven_nth] using eo_has_smt_translation_true
  | Stuck =>
      intro n
      simpa [__eo_state_proven_nth] using eo_has_smt_translation_true
  | cons so s ih =>
      intro n
      by_cases hZero : n = 0
      · subst hZero
        cases so with
        | assume A =>
            simpa [__eo_state_proven_nth, __eo_StateObj_proven] using checkerTranslationInvariant_head_assume A s hs
        | assume_push A =>
            simpa [__eo_state_proven_nth, __eo_StateObj_proven] using checkerTranslationInvariant_head_assume_push A s hs
        | proven P =>
            simpa [__eo_state_proven_nth, __eo_StateObj_proven] using checkerTranslationInvariant_head_proven P s hs
      · cases so with
        | assume A =>
            simpa [__eo_state_proven_nth, hZero] using
              ih (checkerTranslationInvariant_tail hs) (native_zplus n (native_zneg 1))
        | assume_push A =>
            simpa [__eo_state_proven_nth, hZero] using
              ih (checkerTranslationInvariant_tail hs) (native_zplus n (native_zneg 1))
        | proven P =>
            simpa [__eo_state_proven_nth, hZero] using
              ih (checkerTranslationInvariant_tail hs) (native_zplus n (native_zneg 1))
/-- Retrieves the `checkerEntry_has_bool_type` fact at a given index. -/
theorem checkerEntry_has_bool_type_at :
  forall {s : CState},
    checkerTypeInvariant s ->
    checkerTranslationInvariant s ->
    forall n : native_Int,
      RuleProofs.eo_has_bool_type (__eo_state_proven_nth s n)
:=
by
  intro s hsTy hsTrans n
  rcases checkerTypeInvariant_at hsTy n with ⟨_hNe, hTy⟩
  have hTrans : RuleProofs.eo_has_smt_translation (__eo_state_proven_nth s n) :=
    checkerTranslationInvariant_at hsTrans n
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type
    (__eo_state_proven_nth s n) hTrans hTy
/-- Derives `checkerTypeInvariant` from `stateStepPopSuffix`. -/
theorem checkerTypeInvariant_of_stateStepPopSuffix :
  forall {cur root : CState},
    stateStepPopSuffix cur root ->
    checkerTypeInvariant root ->
    checkerTypeInvariant cur
:=
by
  intro cur root hSuffix
  induction hSuffix with
  | refl _ =>
      intro hsRoot
      exact hsRoot
  | proven P hSuffix ih =>
      intro hsRoot
      exact ih (checkerTypeInvariant_tail hsRoot)
/-- Derives `checkerTranslationInvariant` from `stateStepPopSuffix`. -/
theorem checkerTranslationInvariant_of_stateStepPopSuffix :
  forall {cur root : CState},
    stateStepPopSuffix cur root ->
    checkerTranslationInvariant root ->
    checkerTranslationInvariant cur
:=
by
  intro cur root hSuffix
  induction hSuffix with
  | refl _ =>
      intro hsRoot
      exact hsRoot
  | proven P hSuffix ih =>
      intro hsRoot
      exact ih (checkerTranslationInvariant_tail hsRoot)
/-- Shows how `checkerLocalTruthInvariant` behaves on suffix tails. -/
theorem checkerLocalTruthInvariant_tail (M : SmtModel) :
  forall {so : CStateObj} {s : CState},
    checkerLocalTruthInvariant M (CState.cons so s) ->
    checkerLocalTruthInvariant M s
:=
by
  intro so s hs
  cases so with
  | assume A =>
      simpa [checkerLocalTruthInvariant] using hs
  | assume_push A =>
      simpa [checkerLocalTruthInvariant] using hs
  | proven P =>
      exact hs.2
/-- Lemma about `checkerLocalTruthInvariant_head_proven`. -/
theorem checkerLocalTruthInvariant_head_proven
    (M : SmtModel) (s : CState) (P : Term) :
  checkerLocalTruthInvariant M (CState.cons (CStateObj.proven P) s) ->
  eo_interprets M (stateAssumes s) true ->
  eo_interprets M (statePushes s) true ->
  eo_interprets M P true :=
by
  intro hs hAss hPush
  exact hs.1.true_here hAss hPush
/-- Retrieves the `checkerLocalTruthInvariant` fact at a given index. -/
theorem checkerLocalTruthInvariant_at (M : SmtModel) :
  forall {s : CState},
    checkerLocalTruthInvariant M s ->
    forall n : native_Int,
      eo_interprets M (stateAssumes s) true ->
      eo_interprets M (statePushes s) true ->
      eo_interprets M (__eo_state_proven_nth s n) true
:=
by
  intro s hs
  induction s with
  | nil =>
      intro n hAss hPush
      simpa [__eo_state_proven_nth] using eo_interprets_true M
  | Stuck =>
      intro n hAss hPush
      exact False.elim (eo_interprets_stuck_true_absurd M (by simpa [stateAssumes] using hAss))
  | cons so s ih =>
      intro n hAss hPush
      by_cases hZero : n = 0
      · subst hZero
        cases so with
        | assume A =>
            simpa [__eo_state_proven_nth, __eo_StateObj_proven] using
              eo_interprets_and_left M A (stateAssumes s) hAss
        | assume_push A =>
            simpa [__eo_state_proven_nth, __eo_StateObj_proven] using
              eo_interprets_and_left M A (statePushes s) hPush
        | proven P =>
            have hAss' : eo_interprets M (stateAssumes s) true := by
              simpa [stateAssumes] using hAss
            have hPush' : eo_interprets M (statePushes s) true := by
              simpa [statePushes] using hPush
            simpa [__eo_state_proven_nth, __eo_StateObj_proven] using hs.1.true_here hAss' hPush'
      · cases so with
        | assume A =>
            have hAssTail : eo_interprets M (stateAssumes s) true :=
              eo_interprets_and_right M A (stateAssumes s) hAss
            simpa [__eo_state_proven_nth, hZero] using
              ih (by simpa [checkerLocalTruthInvariant] using hs)
                (native_zplus n (native_zneg 1)) hAssTail hPush
        | assume_push A =>
            have hPushTail : eo_interprets M (statePushes s) true :=
              eo_interprets_and_right M A (statePushes s) hPush
            simpa [__eo_state_proven_nth, hZero] using
              ih (by simpa [checkerLocalTruthInvariant] using hs)
                (native_zplus n (native_zneg 1)) hAss hPushTail
        | proven P =>
            simpa [__eo_state_proven_nth, hZero] using
              ih hs.2 (native_zplus n (native_zneg 1))
                (by simpa [stateAssumes] using hAss)
                (by simpa [statePushes] using hPush)
/-- Retrieves an indexed local-truth fact in any variable-variant model. -/
theorem checkerLocalTruthInvariant_at_var_model (M : SmtModel) :
  forall {s : CState},
    checkerLocalTruthInvariant M s ->
    forall (N : SmtModel),
      model_wf N ->
      model_agrees_on_globals M N ->
      forall n : native_Int,
        eo_interprets N (stateAssumes s) true ->
        eo_interprets N (statePushes s) true ->
        eo_interprets N (__eo_state_proven_nth s n) true
:=
by
  intro s hs
  induction s with
  | nil =>
      intro N hN hAgree n hAss hPush
      simpa [__eo_state_proven_nth] using eo_interprets_true N
  | Stuck =>
      intro N hN hAgree n hAss hPush
      exact False.elim (eo_interprets_stuck_true_absurd N (by simpa [stateAssumes] using hAss))
  | cons so s ih =>
      intro N hN hAgree n hAss hPush
      by_cases hZero : n = 0
      · subst hZero
        cases so with
        | assume A =>
            simpa [__eo_state_proven_nth, __eo_StateObj_proven] using
              eo_interprets_and_left N A (stateAssumes s) hAss
        | assume_push A =>
            simpa [__eo_state_proven_nth, __eo_StateObj_proven] using
              eo_interprets_and_left N A (statePushes s) hPush
        | proven P =>
            have hAss' : eo_interprets N (stateAssumes s) true := by
              simpa [stateAssumes] using hAss
            have hPush' : eo_interprets N (statePushes s) true := by
              simpa [statePushes] using hPush
            simpa [__eo_state_proven_nth, __eo_StateObj_proven] using
              hs.1.true_in_var_model N hN hAgree hAss' hPush'
      · cases so with
        | assume A =>
            have hAssTail : eo_interprets N (stateAssumes s) true :=
              eo_interprets_and_right N A (stateAssumes s) hAss
            simpa [__eo_state_proven_nth, hZero] using
              ih (by simpa [checkerLocalTruthInvariant] using hs)
                N hN hAgree (native_zplus n (native_zneg 1)) hAssTail hPush
        | assume_push A =>
            have hPushTail : eo_interprets N (statePushes s) true :=
              eo_interprets_and_right N A (statePushes s) hPush
            simpa [__eo_state_proven_nth, hZero] using
              ih (by simpa [checkerLocalTruthInvariant] using hs)
                N hN hAgree (native_zplus n (native_zneg 1)) hAss hPushTail
        | proven P =>
            simpa [__eo_state_proven_nth, hZero] using
              ih hs.2 N hN hAgree (native_zplus n (native_zneg 1))
                (by simpa [stateAssumes] using hAss)
                (by simpa [statePushes] using hPush)
/-- Retrieves an indexed fact in a variable-variant model using a stable true context. -/
theorem checkerLocalTruthInvariant_at_stable_var_model (M : SmtModel) :
  forall {s : CState},
    model_wf M ->
    checkerLocalTruthInvariant M s ->
    checkerExtraInvariant M s ->
    eo_interprets M (stateAssumes s) true ->
    eo_interprets M (statePushes s) true ->
    forall (N : SmtModel),
      model_wf N ->
      model_agrees_on_globals M N ->
      forall n : native_Int,
        eo_interprets N (__eo_state_proven_nth s n) true
:=
by
  intro s hM hs hStable hAss hPush
  induction s with
  | nil =>
      intro N hN hAgree n
      simpa [__eo_state_proven_nth] using eo_interprets_true N
  | Stuck =>
      intro N hN hAgree n
      exact False.elim (eo_interprets_stuck_true_absurd M (by simpa [stateAssumes] using hAss))
  | cons so s ih =>
      intro N hN hAgree n
      by_cases hZero : n = 0
      · subst hZero
        cases so with
        | assume A =>
            have hA : eo_interprets M A true :=
              eo_interprets_and_left M A (stateAssumes s) hAss
            exact hStable.1 M hM hA N hN hAgree
        | assume_push A =>
            have hA : eo_interprets M A true :=
              eo_interprets_and_left M A (statePushes s) hPush
            exact hStable.1 M hM hA N hN hAgree
        | proven P =>
            have hAssTail : eo_interprets M (stateAssumes s) true := by
              simpa [stateAssumes] using hAss
            have hPushTail : eo_interprets M (statePushes s) true := by
              simpa [statePushes] using hPush
            have hAssN : eo_interprets N (stateAssumes s) true :=
              stateAssumes_true_in_var_model_of_assumptionStability M hM
                (by simpa [checkerAssumptionStabilityInvariant] using hStable)
                hAssTail N hN hAgree
            have hPushN : eo_interprets N (statePushes s) true :=
              statePushes_true_in_var_model_of_assumptionStability M hM
                (by simpa [checkerAssumptionStabilityInvariant] using hStable)
                hPushTail N hN hAgree
            simpa [__eo_state_proven_nth, __eo_StateObj_proven] using
              hs.1.true_in_var_model N hN hAgree hAssN hPushN
      · cases so with
        | assume A =>
            have hAssTail : eo_interprets M (stateAssumes s) true :=
              eo_interprets_and_right M A (stateAssumes s) hAss
            simpa [__eo_state_proven_nth, hZero] using
              ih (by simpa [checkerLocalTruthInvariant] using hs)
                hStable.2 hAssTail hPush N hN hAgree
                (native_zplus n (native_zneg 1))
        | assume_push A =>
            have hPushTail : eo_interprets M (statePushes s) true :=
              eo_interprets_and_right M A (statePushes s) hPush
            simpa [__eo_state_proven_nth, hZero] using
              ih (by simpa [checkerLocalTruthInvariant] using hs)
                hStable.2 hAss hPushTail N hN hAgree
                (native_zplus n (native_zneg 1))
        | proven P =>
            have hAssTail : eo_interprets M (stateAssumes s) true := by
              simpa [stateAssumes] using hAss
            have hPushTail : eo_interprets M (statePushes s) true := by
              simpa [statePushes] using hPush
            simpa [__eo_state_proven_nth, hZero] using
              ih hs.2
                (by simpa [checkerAssumptionStabilityInvariant] using hStable)
                hAssTail hPushTail N hN hAgree (native_zplus n (native_zneg 1))
/-- Shows that `checkerLocalTruthInvariant` implies `truthInvariant`. -/
theorem checkerLocalTruthInvariant_implies_truthInvariant (M : SmtModel) :
  forall {s : CState},
    checkerLocalTruthInvariant M s ->
    checkerTruthInvariant M s
:=
by
  intro s hs
  cases s with
  | Stuck =>
      exact checkerTruthInvariant_stuck M
  | nil =>
      intro n hAss hPush
      exact checkerLocalTruthInvariant_at M hs n hAss hPush
  | cons so s =>
      intro n hAss hPush
      exact checkerLocalTruthInvariant_at M hs n hAss hPush
/-- Describes `checkerLocalTruthInvariant` after `assume_list`. -/
theorem checkerLocalTruthInvariant_after_assume_list (M : SmtModel) (F : CArgList) :
  checkerLocalTruthInvariant M (__eo_invoke_assume_list CState.nil F)
:=
by
  induction F with
  | nil =>
      simp [__eo_invoke_assume_list, checkerLocalTruthInvariant]
  | cons A rest ih =>
      by_cases hGuard : assumptionCheckGuard A = Term.Boolean true
      · change checkerLocalTruthInvariant M
          (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest))
        rw [push_input_assume_eq_cons_of_guard_true A
          (__eo_invoke_assume_list CState.nil rest) hGuard]
        simpa [checkerLocalTruthInvariant] using ih
      · change checkerLocalTruthInvariant M
          (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest))
        rw [push_input_assume_eq_stuck_of_guard_ne_true A
          (__eo_invoke_assume_list CState.nil rest) hGuard]
        exact checkerLocalTruthInvariant_stuck M
/-- Describes `checkerTypeInvariant` after `assume_list`. -/
theorem checkerTypeInvariant_after_assume_list (F : CArgList) :
  stateOk (__eo_invoke_assume_list CState.nil F) ->
  checkerTypeInvariant (__eo_invoke_assume_list CState.nil F)
:=
by
  intro hOk
  induction F with
  | nil =>
      simp [__eo_invoke_assume_list, checkerTypeInvariant]
  | cons A rest ih =>
      have hPushOk :
          stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest)) := by
        simpa [__eo_invoke_assume_list, assumptionCheckGuard] using hOk
      have hTy : __eo_typeof A = Term.Bool :=
        push_input_assume_typeof_bool_of_stateOk A
          (__eo_invoke_assume_list CState.nil rest) hPushOk
      have hA : A ≠ Term.Stuck := term_ne_stuck_of_typeof_bool hTy
      have hRestOk :
          stateOk (__eo_invoke_assume_list CState.nil rest) :=
        push_input_assume_reflects_stateOk A
          (__eo_invoke_assume_list CState.nil rest) hPushOk
      have hPushEq := push_input_assume_eq_cons_of_stateOk A
        (__eo_invoke_assume_list CState.nil rest) hPushOk
      change checkerTypeInvariant
        (__eo_push_input_assume_check (assumptionCheckGuard A) A
          (__eo_invoke_assume_list CState.nil rest))
      rw [hPushEq]
      simpa [checkerTypeInvariant, hA] using
        (show __eo_typeof A = Term.Bool ∧
            checkerTypeInvariant (__eo_invoke_assume_list CState.nil rest) from
          ⟨hTy, ih hRestOk⟩)
/-- Describes `checkerTranslationInvariant` after `assume_list`. -/
theorem checkerTranslationInvariant_after_assume_list (F : CArgList) :
  TranslatableAssumptionList F ->
  checkerTranslationInvariant (__eo_invoke_assume_list CState.nil F)
:=
by
  induction F with
  | nil =>
      intro _
      simp [__eo_invoke_assume_list, checkerTranslationInvariant]
  | cons A rest ih =>
      intro hTrans
      obtain ⟨hA, hRestTrans⟩ := hTrans
      by_cases hGuard : assumptionCheckGuard A = Term.Boolean true
      · change checkerTranslationInvariant
          (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest))
        rw [push_input_assume_eq_cons_of_guard_true A
          (__eo_invoke_assume_list CState.nil rest) hGuard]
        simpa [checkerTranslationInvariant] using
          (show RuleProofs.eo_has_smt_translation A ∧
              checkerTranslationInvariant (__eo_invoke_assume_list CState.nil rest) from
            ⟨hA, ih hRestTrans⟩)
      · change checkerTranslationInvariant
          (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest))
        rw [push_input_assume_eq_stuck_of_guard_ne_true A
          (__eo_invoke_assume_list CState.nil rest) hGuard]
        exact checkerTranslationInvariant_stuck
/-- Shows that `push_assume` preserves `localTruthInvariant`. -/
theorem push_assume_preserves_localTruthInvariant
    (M : SmtModel) (s : CState) (A : Term) :
  checkerLocalTruthInvariant M s ->
  checkerLocalTruthInvariant M (__eo_push_assume_check (assumptionCheckGuard A) A s) :=
by
  intro hs
  by_cases hGuard : assumptionCheckGuard A = Term.Boolean true
  · simpa [push_assume_eq_cons_of_guard_true, hGuard,
      checkerLocalTruthInvariant, __eo_push_assume_check] using hs
  · simpa [push_assume_eq_stuck_of_guard_ne_true, hGuard] using
      checkerLocalTruthInvariant_stuck M
/-- Shows that `push_assume` preserves `typeInvariant`. -/
theorem push_assume_preserves_typeInvariant
    (s : CState) (A : Term) :
  checkerTypeInvariant s ->
  checkerTypeInvariant (__eo_push_assume_check (assumptionCheckGuard A) A s) :=
by
  intro hs
  by_cases hGuard : assumptionCheckGuard A = Term.Boolean true
  · have hTy : __eo_typeof A = Term.Bool :=
      (eo_is_bool_type_eq_true_iff A).1
        (assumptionCheckGuard_eq_true_cases A hGuard).1
    have hA : A ≠ Term.Stuck := term_ne_stuck_of_typeof_bool hTy
    rw [push_assume_eq_cons_of_guard_true A s hGuard]
    simpa [checkerTypeInvariant, hA] using
      (show __eo_typeof A = Term.Bool ∧ checkerTypeInvariant s from ⟨hTy, hs⟩)
  · simpa [push_assume_eq_stuck_of_guard_ne_true, hGuard] using
      checkerTypeInvariant_stuck
/-- Shows that `push_assume` preserves `translationInvariant`. -/
theorem push_assume_preserves_translationInvariant
    (s : CState) (A : Term) :
  checkerTranslationInvariant s ->
  RuleProofs.eo_has_smt_translation A ->
  checkerTranslationInvariant (__eo_push_assume_check (assumptionCheckGuard A) A s) :=
by
  intro hs hA
  by_cases hGuard : assumptionCheckGuard A = Term.Boolean true
  · simpa [push_assume_eq_cons_of_guard_true, hGuard,
      checkerTranslationInvariant, __eo_push_assume_check] using
      (show RuleProofs.eo_has_smt_translation A ∧ checkerTranslationInvariant s from ⟨hA, hs⟩)
  · simpa [push_assume_eq_stuck_of_guard_ne_true, hGuard] using
      checkerTranslationInvariant_stuck
/-- Shows that `push_proven` preserves `typeInvariant`. -/
theorem push_proven_preserves_typeInvariant
    (s : CState) (P : Term) :
  checkerTypeInvariant s ->
  checkerTypeInvariant (__eo_push_proven P s) :=
by
  intro hs
  by_cases hTy : __eo_typeof P = Term.Bool
  · have hP : P ≠ Term.Stuck := term_ne_stuck_of_typeof_bool hTy
    simpa [push_proven_eq_cons_of_typeof_bool, hTy, checkerTypeInvariant, hP] using hs
  · simpa [push_proven_eq_stuck_of_typeof_ne_bool, hTy] using checkerTypeInvariant_stuck
/-- Shows that `push_proven` preserves `translationInvariant`. -/
theorem push_proven_preserves_translationInvariant
    (s : CState) (P : Term) :
  checkerTranslationInvariant s ->
  RuleProofs.eo_has_smt_translation P ->
  checkerTranslationInvariant (__eo_push_proven P s) :=
by
  intro hs hP
  by_cases hTy : __eo_typeof P = Term.Bool
  · simpa [push_proven_eq_cons_of_typeof_bool, hTy, checkerTranslationInvariant] using
      (show RuleProofs.eo_has_smt_translation P ∧ checkerTranslationInvariant s from ⟨hP, hs⟩)
  · simpa [push_proven_eq_stuck_of_typeof_ne_bool, hTy] using checkerTranslationInvariant_stuck
/-- Shows that `push_proven` preserves `localTruthInvariant_of_contextual_true`. -/
theorem push_proven_preserves_localTruthInvariant_of_contextual_true
    (M : SmtModel) (s : CState) (P : Term) :
  checkerLocalTruthInvariant M s ->
  ContextualTruth M (stateAssumes s) (statePushes s) P ->
  checkerLocalTruthInvariant M (CState.cons (CStateObj.proven P) s) :=
by
  intro hs hP
  exact ⟨hP, hs⟩
/-- Shape invariant asserting that the checker state forms a valid assumption suffix chain. -/
def checkerShapeInvariant : CState -> Prop
  | CState.Stuck => True
  | s => stateAssumptionSuffix s
/-- Derives `checkerShapeInvariant` from `suffix`. -/
theorem checkerShapeInvariant_of_suffix {s : CState} :
  stateAssumptionSuffix s ->
  checkerShapeInvariant s :=
by
  cases s <;> simp [checkerShapeInvariant, stateAssumptionSuffix]
/-- Derives `suffix` from `checkerShapeInvariant_nonstuck`. -/
theorem suffix_of_checkerShapeInvariant_nonstuck {s : CState} :
  checkerShapeInvariant s ->
  s ≠ CState.Stuck ->
  stateAssumptionSuffix s :=
by
  intro hShape hNotStuck
  cases s with
  | Stuck =>
      exact False.elim (hNotStuck rfl)
  | nil =>
      simpa [checkerShapeInvariant]
  | cons so s =>
      simpa [checkerShapeInvariant] using hShape
/-- Combined checker invariant bundling shape, truth, stability, typing, and translation. -/
def checkerStateInvariant (M : SmtModel) (s : CState) : Prop :=
  checkerShapeInvariant s ∧
  checkerLocalTruthInvariant M s ∧
  checkerExtraInvariant M s ∧
  checkerTypeInvariant s ∧
  checkerTranslationInvariant s
/-- Retrieves the `checkerTruthInvariant` fact at a given index. -/
theorem checkerTruthInvariant_at (M : SmtModel) {s : CState} :
  checkerTruthInvariant M s ->
  ∀ n : native_Int,
    eo_interprets M (stateAssumes s) true ->
    eo_interprets M (statePushes s) true ->
    eo_interprets M (__eo_state_proven_nth s n) true
:=
by
  intro hs n hAss hPush
  cases s with
  | Stuck =>
      exact False.elim (eo_interprets_stuck_true_absurd M (by simpa [stateAssumes] using hAss))
  | nil =>
      have hs' : ∀ n : native_Int,
          eo_interprets M (stateAssumes CState.nil) true ->
          eo_interprets M (statePushes CState.nil) true ->
          eo_interprets M (__eo_state_proven_nth CState.nil n) true := by
        simpa [checkerTruthInvariant] using hs
      exact hs' n hAss hPush
  | cons so s =>
      have hs' : ∀ n : native_Int,
          eo_interprets M (stateAssumes (CState.cons so s)) true ->
          eo_interprets M (statePushes (CState.cons so s)) true ->
          eo_interprets M (__eo_state_proven_nth (CState.cons so s) n) true := by
        simpa [checkerTruthInvariant] using hs
      exact hs' n hAss hPush
/-- Shows that `push_assume` preserves `truthInvariant`. -/
theorem push_assume_preserves_truthInvariant
    (M : SmtModel) (s : CState) (A : Term) :
  checkerTruthInvariant M s ->
  checkerTruthInvariant M (__eo_push_assume_check (assumptionCheckGuard A) A s) :=
by
  intro hs
  by_cases hGuard : assumptionCheckGuard A = Term.Boolean true
  · rw [push_assume_eq_cons_of_guard_true A s hGuard]
    intro n hAss hPush
    by_cases hZero : n = 0
    · subst hZero
      have hPush' :
          eo_interprets M
            (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) (statePushes s)) true := by
        simpa [push_assume_eq_cons_of_guard_true, hGuard, statePushes] using hPush
      simpa [push_assume_eq_cons_of_guard_true, hGuard, __eo_state_proven_nth, __eo_StateObj_proven] using
        eo_interprets_and_left M A (statePushes s) hPush'
    · have hAss' : eo_interprets M (stateAssumes s) true := by
        simpa [push_assume_eq_cons_of_guard_true, hGuard, stateAssumes] using hAss
      have hPush' :
          eo_interprets M
            (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) (statePushes s)) true := by
        simpa [push_assume_eq_cons_of_guard_true, hGuard, statePushes] using hPush
      have hPushTail : eo_interprets M (statePushes s) true :=
        eo_interprets_and_right M A (statePushes s) hPush'
      simpa [push_assume_eq_cons_of_guard_true, hGuard, __eo_state_proven_nth, hZero] using
        checkerTruthInvariant_at M hs
          (native_zplus n (native_zneg 1)) hAss' hPushTail
  · simpa [push_assume_eq_stuck_of_guard_ne_true, hGuard] using checkerTruthInvariant_stuck M
/-- Shows that `push_proven` preserves `truthInvariant_of_contextual_true`. -/
theorem push_proven_preserves_truthInvariant_of_contextual_true
    (M : SmtModel) (s : CState) (P : Term) :
  checkerTruthInvariant M s ->
  (eo_interprets M (stateAssumes s) true ->
   eo_interprets M (statePushes s) true ->
   eo_interprets M P true) ->
  checkerTruthInvariant M (CState.cons (CStateObj.proven P) s) :=
by
  intro hs hP n hAss hPush
  by_cases hZero : n = 0
  · subst hZero
    have hAss' : eo_interprets M (stateAssumes s) true := by
      simpa [stateAssumes] using hAss
    have hPush' : eo_interprets M (statePushes s) true := by
      simpa [statePushes] using hPush
    simpa [__eo_state_proven_nth, __eo_StateObj_proven] using hP hAss' hPush'
  · have hAss' : eo_interprets M (stateAssumes s) true := by
      simpa [stateAssumes] using hAss
    have hPush' : eo_interprets M (statePushes s) true := by
      simpa [statePushes] using hPush
    simpa [__eo_state_proven_nth, hZero] using
      checkerTruthInvariant_at M hs
        (native_zplus n (native_zneg 1)) hAss' hPush'
/-- Describes `checkerTruthInvariant` after `assume_list`. -/
theorem checkerTruthInvariant_after_assume_list (M : SmtModel) (F : CArgList) :
  stateOk (__eo_invoke_assume_list CState.nil F) ->
  checkerTruthInvariant M (__eo_invoke_assume_list CState.nil F)
:=
by
  intro hOk
  have hNotStuck :
      __eo_invoke_assume_list CState.nil F ≠ CState.Stuck :=
    stateOk_not_stuck hOk
  have hProvens :
      stateProvens (__eo_invoke_assume_list CState.nil F) = Term.Boolean true :=
    stateProvens_invoke_assume_list hOk
  cases hS : __eo_invoke_assume_list CState.nil F with
  | nil =>
      intro n hAss hPush
      have hProvens' : stateProvens CState.nil = Term.Boolean true := by
        simpa [hS] using hProvens
      have hProv :
          eo_interprets M (stateProvens CState.nil) true := by
        rw [hProvens']
        exact eo_interprets_true M
      exact state_proven_nth_true_of_context M CState.nil n hAss hPush hProv
  | cons so s =>
      intro n hAss hPush
      have hProvens' : stateProvens (CState.cons so s) = Term.Boolean true := by
        simpa [hS] using hProvens
      have hProv :
          eo_interprets M (stateProvens (CState.cons so s)) true := by
        rw [hProvens']
        exact eo_interprets_true M
      exact state_proven_nth_true_of_context M (CState.cons so s) n hAss hPush hProv
  | Stuck =>
      exact False.elim (hNotStuck hS)
/-- Describes `checkerStateInvariant` after `assume_list`. -/
theorem checkerStateInvariant_after_assume_list (M : SmtModel) (F : CArgList) :
  stateOk (__eo_invoke_assume_list CState.nil F) ->
  TranslatableAssumptionList F ->
  extraAssumptionListOk M F ->
  checkerStateInvariant M (__eo_invoke_assume_list CState.nil F)
:=
by
  intro hOk hTrans hStable
  exact ⟨
    checkerShapeInvariant_of_suffix (stateAssumptionSuffix_invoke_assume_list hOk),
    checkerLocalTruthInvariant_after_assume_list M F,
    checkerExtraInvariant_after_assume_list M F hStable,
    checkerTypeInvariant_after_assume_list F hOk,
    checkerTranslationInvariant_after_assume_list F hTrans
  ⟩
/-- Derives `refutation_contradiction` from `truthInvariant`. -/
theorem refutation_contradiction_of_truthInvariant
    (M : SmtModel) (F : CArgList) (pf : CCmdList) :
  eo_interprets M (argListAssumes F) true ->
  checkerTruthInvariant M (__eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf) ->
  (__eo_checker_is_refutation F pf) = true ->
  False :=
by
  intro hF hTruth hChecker
  let S1 := __eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf
  rcases final_state_shape_of_checker_true F pf hChecker with ⟨s, hShape, hClosed⟩
  have hAssumes : eo_interprets M (stateAssumes (CState.cons (CStateObj.proven (Term.Boolean false)) s)) true := by
    have hAssumesEq : stateAssumes S1 = argListAssumes F := by
      simpa [S1] using stateAssumes_of_checker_true F pf hChecker
    have hAssumesEqS : stateAssumes s = argListAssumes F := by
      simpa [S1, hShape, stateAssumes] using hAssumesEq
    simpa [stateAssumes, hAssumesEqS] using hF
  have hPushes : eo_interprets M (statePushes (CState.cons (CStateObj.proven (Term.Boolean false)) s)) true := by
    have hPushesEq : statePushes s = Term.Boolean true :=
      statePushes_of_state_closed_true hClosed
    simpa [statePushes, hPushesEq] using eo_interprets_true M
  have hFalseTrue :
      eo_interprets M (Term.Boolean false) true := by
    have hAt := checkerTruthInvariant_at M
      (by simpa [S1, hShape] using hTruth)
      0 hAssumes hPushes
    simpa [__eo_state_proven_nth, __eo_StateObj_proven] using hAt
  exact eo_interprets_false_true_absurd M hFalseTrue
/-- Lemma about `premiseTermList_has_bool_type`. -/
theorem premiseTermList_has_bool_type (s : CState) :
  forall (premises : CIndexList),
    checkerTypeInvariant s ->
    checkerTranslationInvariant s ->
    AllHaveBoolType (premiseTermList s premises)
:=
by
  intro premises
  induction premises with
  | nil =>
      intro hsTy hsTrans t ht
      cases ht
  | cons n premises ih =>
      intro hsTy hsTrans t ht
      simp [premiseTermList] at ht
      rcases ht with rfl | ht
      · exact checkerEntry_has_bool_type_at hsTy hsTrans n
      · exact ih hsTy hsTrans t ht
/-- Lemma about `premiseTermList_has_smt_translation`. -/
theorem premiseTermList_has_smt_translation (s : CState) :
  forall (premises : CIndexList),
    checkerTranslationInvariant s ->
    AllHaveSmtTranslation (premiseTermList s premises)
:=
by
  intro premises
  induction premises with
  | nil =>
      intro hsTrans t ht
      cases ht
  | cons n premises ih =>
      intro hsTrans t ht
      simp [premiseTermList] at ht
      rcases ht with rfl | ht
      · exact checkerTranslationInvariant_at hsTrans n
      · exact ih hsTrans t ht
/-- Lemma about `premiseTermList_has_typeof_bool`. -/
theorem premiseTermList_has_typeof_bool (s : CState) :
  forall (premises : CIndexList),
    checkerTypeInvariant s ->
    AllTypeofBool (premiseTermList s premises)
:=
by
  intro premises
  induction premises with
  | nil =>
      intro hsTy t ht
      cases ht
  | cons n premises ih =>
      intro hsTy t ht
      simp [premiseTermList] at ht
      rcases ht with rfl | ht
      · exact (checkerTypeInvariant_at hsTy n).2
      · exact ih hsTy t ht
/-- Derives `premiseTermList_true` from `truthInvariant`. -/
theorem premiseTermList_true_of_truthInvariant
    (M : SmtModel) (s : CState) :
  forall (premises : CIndexList),
    checkerTruthInvariant M s ->
    eo_interprets M (stateAssumes s) true ->
    eo_interprets M (statePushes s) true ->
    AllInterpretedTrue M (premiseTermList s premises)
:=
by
  intro premises
  induction premises with
  | nil =>
      intro hs hAss hPush t ht
      cases ht
  | cons n premises ih =>
      intro hs hAss hPush t ht
      simp [premiseTermList] at ht
      rcases ht with rfl | ht
      · exact checkerTruthInvariant_at M hs n hAss hPush
      · exact ih hs hAss hPush t ht
/-- Derives premise truth in a variable-variant model from the local invariant. -/
theorem premiseTermList_true_of_localTruthInvariant_var_model
    (M : SmtModel) (s : CState) :
  forall (premises : CIndexList),
    checkerLocalTruthInvariant M s ->
    forall (N : SmtModel),
      model_wf N ->
      model_agrees_on_globals M N ->
      eo_interprets N (stateAssumes s) true ->
      eo_interprets N (statePushes s) true ->
      AllInterpretedTrue N (premiseTermList s premises)
:=
by
  intro premises
  induction premises with
  | nil =>
      intro hs N hN hAgree hAss hPush t ht
      cases ht
  | cons n premises ih =>
      intro hs N hN hAgree hAss hPush t ht
      simp [premiseTermList] at ht
      rcases ht with rfl | ht
      · exact checkerLocalTruthInvariant_at_var_model M hs N hN hAgree n hAss hPush
      · exact ih hs N hN hAgree hAss hPush t ht
/-- Derives premise truth in a variable-variant model from a stable true context. -/
theorem premiseTermList_true_of_localTruthInvariant_stable_var_model
    (M : SmtModel) (s : CState) :
  forall (premises : CIndexList),
    model_wf M ->
    checkerLocalTruthInvariant M s ->
    checkerExtraInvariant M s ->
    eo_interprets M (stateAssumes s) true ->
    eo_interprets M (statePushes s) true ->
    forall (N : SmtModel),
      model_wf N ->
      model_agrees_on_globals M N ->
      AllInterpretedTrue N (premiseTermList s premises)
:=
by
  intro premises
  induction premises with
  | nil =>
      intro hM hs hStable hAss hPush N hN hAgree t ht
      cases ht
  | cons n premises ih =>
      intro hM hs hStable hAss hPush N hN hAgree t ht
      simp [premiseTermList] at ht
      rcases ht with rfl | ht
      · exact checkerLocalTruthInvariant_at_stable_var_model M hM hs hStable
          hAss hPush N hN hAgree n
      · exact ih hM hs hStable hAss hPush N hN hAgree t ht
/-- Builds the contextual premise evidence used by the richer rule-correctness template. -/
theorem premiseEvidence_of_localTruthInvariant
    (M N : SmtModel) (s : CState) (premises : CIndexList) :
  checkerLocalTruthInvariant M s ->
  checkerExtraInvariant M s ->
  model_wf N ->
  model_agrees_on_globals M N ->
  eo_interprets N (stateAssumes s) true ->
  eo_interprets N (statePushes s) true ->
  RulePremiseEvidence N
    (premiseTermList s premises) :=
by
  intro hs hStable hN hAgree hAss hPush
  refine ⟨?_, ?_⟩
  · exact premiseTermList_true_of_localTruthInvariant_var_model
      M s premises hs N hN hAgree hAss hPush
  · intro K hK hAgreeNK
    have hStableN : checkerExtraInvariant N s :=
      checkerAssumptionStabilityInvariant_rebase M N hStable
    have hAssK : eo_interprets K (stateAssumes s) true :=
      stateAssumes_true_in_var_model_of_assumptionStability N hN
        hStableN hAss K hK hAgreeNK
    have hPushK : eo_interprets K (statePushes s) true :=
      statePushes_true_in_var_model_of_assumptionStability N hN
        hStableN hPush K hK hAgreeNK
    exact premiseTermList_true_of_localTruthInvariant_var_model
      M s premises hs K hK
      (model_agrees_on_globals_trans hAgree hAgreeNK) hAssK hPushK
/-- Structure bundling the premise facts needed to justify a single checker step. -/
structure CmdStepFacts (M : SmtModel) (s : CState) (P : Term) : Prop where
  true_of_context :
    eo_interprets M (stateAssumes s) true ->
    eo_interprets M (statePushes s) true ->
    eo_interprets M P true
  true_in_var_model :
    ∀ N, model_wf N ->
      model_agrees_on_globals M N ->
      eo_interprets N (stateAssumes s) true ->
      eo_interprets N (statePushes s) true ->
      eo_interprets N P true
  has_smt_translation :
    RuleProofs.eo_has_smt_translation P
/-- Converts command-step facts into the local invariant payload for `push_proven`. -/
theorem CmdStepFacts.contextualTruth
    {M : SmtModel} {s : CState} {P : Term} :
  CmdStepFacts M s P ->
  ContextualTruth M (stateAssumes s) (statePushes s) P :=
by
  intro hFacts
  exact ⟨hFacts.true_of_context, hFacts.true_in_var_model⟩
/-- Packages rule-level step properties into the checker facts required for a single step. -/
theorem cmd_step_facts_of_rule_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (premises : CIndexList) {P : Term} :
  checkerLocalTruthInvariant M s ->
  checkerExtraInvariant M s ->
  (hProps : ∀ N, model_wf N ->
    model_agrees_on_globals M N ->
    StepRuleProperties N (premiseTermList s premises) P) ->
  CmdStepFacts M s P :=
by
  intro hs hAssumptionsStable hProps
  refine ⟨?_, ?_, ?_⟩
  · intro hAss hPush
    have hPM := hProps M hM (model_agrees_on_globals_refl M)
    exact hPM.facts_of_true
      (premiseEvidence_of_localTruthInvariant M M s premises hs hAssumptionsStable hM
        (model_agrees_on_globals_refl M) hAss hPush)
  · intro N hN hAgree hAss hPush
    have hPN := hProps N hN hAgree
    exact hPN.facts_of_true
      (premiseEvidence_of_localTruthInvariant M N s premises hs hAssumptionsStable
        hN hAgree hAss hPush)
  · exact (hProps M hM (model_agrees_on_globals_refl M)).has_smt_translation
/-- Packages rule-level step-pop properties into the checker facts required for a pop step. -/
theorem cmd_step_pop_facts_of_rule_properties
    (M : SmtModel) (hM : model_wf M)
    (root tail : CState) (A : Term) (premises : CIndexList) {P : Term} :
  checkerLocalTruthInvariant M root ->
  checkerExtraInvariant M root ->
  stateStepPopSuffix (CState.cons (CStateObj.assume_push A) tail) root ->
  (hProps : StepPopRuleProperties A (premiseTermList root premises) P) ->
  CmdStepFacts M tail P :=
by
  intro hsRoot hAssumptionsStableRoot hSuffix hProps
  rcases hProps with ⟨X, hXMem, hFactsOfImp, hPopTrans⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hAss hPush
    have hAssRoot : eo_interprets M (stateAssumes root) true := by
      rw [stateAssumes_eq_of_stateStepPopSuffix_assume_push hSuffix]
      exact hAss
    have hScoped :
        eo_interprets M A true -> eo_interprets M X true := by
      intro hATrue
      have hPushRoot : eo_interprets M (statePushes root) true := by
        rw [statePushes_eq_of_stateStepPopSuffix_assume_push hSuffix]
        exact eo_interprets_and_intro M A (statePushes tail) hATrue hPush
      exact (premiseTermList_true_of_localTruthInvariant_var_model
          M root premises hsRoot M hM (model_agrees_on_globals_refl M)
          hAssRoot hPushRoot)
        X hXMem
    exact hFactsOfImp M hM hScoped
  · intro N hN hAgree hAss hPush
    have hAssRoot : eo_interprets N (stateAssumes root) true := by
      rw [stateAssumes_eq_of_stateStepPopSuffix_assume_push hSuffix]
      exact hAss
    have hScoped :
        eo_interprets N A true -> eo_interprets N X true := by
      intro hATrue
      have hPushRoot : eo_interprets N (statePushes root) true := by
        rw [statePushes_eq_of_stateStepPopSuffix_assume_push hSuffix]
        exact eo_interprets_and_intro N A (statePushes tail) hATrue hPush
      exact (premiseTermList_true_of_localTruthInvariant_var_model
          M root premises hsRoot N hN hAgree hAssRoot hPushRoot)
        X hXMem
    exact hFactsOfImp N hN hScoped
  · exact hPopTrans
