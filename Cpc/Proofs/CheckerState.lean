module

public import Cpc.Spec
import all Cpc.Spec
public import Cpc.Logos
import all Cpc.Logos
public import Cpc.Proofs.Assumptions
import all Cpc.Proofs.Assumptions
public import Cpc.Proofs.RuleSupport.Contract
import all Cpc.Proofs.RuleSupport.Contract

/-!
# Checker state machine

The facts about `__eo_push_*`, `__eo_invoke_*`, `stateOk` and the shape of a
`CState` that hold whatever the calculus is.  Nothing here names a checker
invariant, so this layer is reusable by any Logos-like checker regardless of
what its rules require of the proof state.
-/

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 0
/-- Predicate asserting that a checker state is structurally well-formed and not `Stuck`. -/
def stateOk : CState -> Prop
  | CState.nil => True
  | CState.cons _ s => stateOk s
  | CState.Stuck => False

/-- Simplifies EO-to-SMT translation for `true_eq`. -/
private theorem eo_to_smt_true_eq :
    __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true := by
  rfl

/-- Simplifies EO-to-SMT translation for `false_eq`. -/
private theorem eo_to_smt_false_eq :
    __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false := by
  rfl

/-- Simplifies EO-to-SMT translation for `stuck_eq`. -/
private theorem eo_to_smt_stuck_eq :
    __eo_to_smt Term.Stuck = SmtTerm.None := by
  rfl

/-- Simplifies EO-to-SMT translation for `and_eq`. -/
private theorem eo_to_smt_and_eq (A B : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) =
      SmtTerm.and (__eo_to_smt A) (__eo_to_smt B) := by
  rfl

/-- Lemma about `eo_has_smt_translation_true`. -/
private theorem eo_has_smt_translation_true :
    RuleProofs.eo_has_smt_translation (Term.Boolean true) := by
  rw [RuleProofs.eo_has_smt_translation, eo_to_smt_true_eq, RuleProofs.typeof_boolean_eq _]
  decide
/-- Characterizes EO interpretation in terms of the translated SMT interpretation. -/
theorem eo_interprets_iff_smt_interprets (M : SmtModel) (t : Term) (b : Bool) :
  eo_interprets M t b ↔ smt_interprets M (__eo_to_smt t) b :=
by
  exact RuleProofs.eo_interprets_iff_smt_interprets M t b
/-- Shows that the EO term `true` is interpreted as `true` in every model. -/
theorem eo_interprets_true (M : SmtModel) :
  eo_interprets M (Term.Boolean true) true :=
by
  exact RuleProofs.eo_interprets_true M
/-- Lemma about `eo_interprets_false_true_absurd`. -/
theorem eo_interprets_false_true_absurd (M : SmtModel) :
  ¬ eo_interprets M (Term.Boolean false) true :=
by
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_false_eq]
  intro h
  cases h with
  | intro_true _ hEval =>
      simp [__smtx_model_eval] at hEval
/-- Lemma about `eo_interprets_stuck_false_absurd`. -/
theorem eo_interprets_stuck_false_absurd (M : SmtModel) :
  ¬ eo_interprets M Term.Stuck false :=
by
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_stuck_eq]
  intro h
  cases h with
  | intro_false hty _ =>
      rw [RuleProofs.typeof_none_eq] at hty
      cases hty
/-- Lemma about `eo_interprets_stuck_true_absurd`. -/
theorem eo_interprets_stuck_true_absurd (M : SmtModel) :
  ¬ eo_interprets M Term.Stuck true :=
by
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_stuck_eq]
  intro h
  cases h with
  | intro_true hty _ =>
      rw [RuleProofs.typeof_none_eq] at hty
      cases hty
/-- Lemma about `eo_interprets_true_not_false`. -/
theorem eo_interprets_true_not_false (M : SmtModel) (t : Term) :
  eo_interprets M t true ->
  ¬ eo_interprets M t false :=
by
  exact RuleProofs.eo_interprets_true_not_false M t
/-- Left-projection lemma for `eo_interprets_and`. -/
theorem eo_interprets_and_left (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) true ->
  eo_interprets M A true :=
by
  exact RuleProofs.eo_interprets_and_left M A B
/-- Right-projection lemma for `eo_interprets_and`. -/
theorem eo_interprets_and_right (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) true ->
  eo_interprets M B true :=
by
  exact RuleProofs.eo_interprets_and_right M A B
/-- Introduction lemma for `eo_interprets_and`. -/
theorem eo_interprets_and_intro (M : SmtModel) (A B : Term) :
  eo_interprets M A true ->
  eo_interprets M B true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) true :=
by
  exact RuleProofs.eo_interprets_and_intro M A B
/-- Derives `eo_interprets_and_false_left` from `right_not_false`. -/
theorem eo_interprets_and_false_left_of_right_not_false (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) false ->
  ¬ eo_interprets M B false ->
  eo_interprets M A false :=
by
  intro hAnd hBNotFalse
  rw [eo_interprets_iff_smt_interprets] at hAnd hBNotFalse ⊢
  rw [eo_to_smt_and_eq A B] at hAnd
  cases hAnd with
  | intro_false hty hEval =>
      have htyA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool := by
        have hNN : term_has_non_none_type
            (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) := by
          unfold term_has_non_none_type
          rw [hty]
          simp
        exact (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
          (typeof_and_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).1
      have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
        have hNN : term_has_non_none_type
            (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) := by
          unfold term_has_non_none_type
          rw [hty]
          simp
        exact (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
          (typeof_and_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).2
      have hEvalA : __smtx_model_eval M (__eo_to_smt A) = SmtValue.Boolean false := by
        rw [RuleProofs.model_eval_and_eq] at hEval
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [hAeval, hBeval, __smtx_model_eval_and] at hEval
        case Boolean.Boolean a b =>
          cases a <;> cases b
          · simp [SmtEval.native_and] at hEval
            have hBFalse : smt_interprets M (__eo_to_smt B) false :=
              smt_interprets.intro_false M (__eo_to_smt B) htyB hBeval
            exact False.elim (hBNotFalse hBFalse)
          · simp [SmtEval.native_and] at hEval
            simp
          · simp [SmtEval.native_and] at hEval
            have hBFalse : smt_interprets M (__eo_to_smt B) false :=
              smt_interprets.intro_false M (__eo_to_smt B) htyB hBeval
            exact False.elim (hBNotFalse hBFalse)
          · simp [SmtEval.native_and] at hEval
      exact smt_interprets.intro_false M (__eo_to_smt A) htyA hEvalA
/-- Derives `eo_interprets_and_false_right_true` from `left_false_and_right_not_false`. -/
theorem eo_interprets_and_false_right_true_of_left_false_and_right_not_false
    (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) false ->
  eo_interprets M A false ->
  ¬ eo_interprets M B false ->
  eo_interprets M B true :=
by
  intro hAnd hAFalse hBNotFalse
  rw [eo_interprets_iff_smt_interprets] at hAnd hAFalse hBNotFalse ⊢
  rw [eo_to_smt_and_eq A B] at hAnd
  cases hAnd with
  | intro_false htyAnd hEvalAnd =>
      cases hAFalse with
      | intro_false htyA hEvalA =>
          have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
            have hNN : term_has_non_none_type
                (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) := by
              unfold term_has_non_none_type
              rw [htyAnd]
              simp
            exact (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
              (typeof_and_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).2
          have hEvalB : __smtx_model_eval M (__eo_to_smt B) = SmtValue.Boolean true := by
            rw [RuleProofs.model_eval_and_eq] at hEvalAnd
            cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
              simp [hEvalA, hBeval, __smtx_model_eval_and] at hEvalAnd
            case Boolean b =>
              cases b with
              | false =>
                  have hBFalse : smt_interprets M (__eo_to_smt B) false :=
                    smt_interprets.intro_false M (__eo_to_smt B) htyB hBeval
                  exact False.elim (hBNotFalse hBFalse)
              | true =>
                  simp
          exact smt_interprets.intro_true M (__eo_to_smt B) htyB hEvalB
/-- Extracts the conjunction of active assumptions from a checker state. -/
def stateAssumes : CState -> Term
  | CState.nil => Term.Boolean true
  | CState.cons (CStateObj.assume F) s =>
      Term.Apply (Term.Apply (Term.UOp UserOp.and) F) (stateAssumes s)
  | CState.cons _ s => stateAssumes s
  | CState.Stuck => Term.Stuck
/-- Extracts the list of assumptions introduced by `assume_push` commands in a checker state. -/
def statePushes : CState -> Term
  | CState.nil => Term.Boolean true
  | CState.cons (CStateObj.assume_push F) s =>
      Term.Apply (Term.Apply (Term.UOp UserOp.and) F) (statePushes s)
  | CState.cons _ s => statePushes s
  | CState.Stuck => Term.Stuck
/-- Extracts the list of proven terms stored in a checker state. -/
def stateProvens : CState -> Term
  | CState.nil => Term.Boolean true
  | CState.cons (CStateObj.proven F) s =>
      Term.Apply (Term.Apply (Term.UOp UserOp.and) F) (stateProvens s)
  | CState.cons _ s => stateProvens s
  | CState.Stuck => Term.Stuck
/-
Because the checker pushes new entries at the head of the state, the initial
assumptions from `__eo_invoke_assume_list` live in a tail block of reachable
states. This is the structural fact that lets `step_pop` discard a prefix
without changing the assumption component.
-/
/-- Predicate asserting that a state appears as the tail of another checker state. -/
def stateAssumptionTail : CState -> Prop
  | CState.nil => True
  | CState.cons (CStateObj.assume _) s => stateAssumptionTail s
  | _ => False
/-- Predicate asserting that a state occurs as a suffix reached by repeatedly dropping assumptions. -/
def stateAssumptionSuffix : CState -> Prop
  | CState.nil => True
  | CState.cons (CStateObj.assume _) s => stateAssumptionTail s
  | CState.cons _ s => stateAssumptionSuffix s
  | CState.Stuck => False
/-- Derives `stateAssumptionSuffix` from `tail`. -/
theorem stateAssumptionSuffix_of_tail :
  forall {s : CState}, stateAssumptionTail s -> stateAssumptionSuffix s
:=
by
  intro s hTail
  cases s with
  | nil =>
      trivial
  | Stuck =>
      cases hTail
  | cons so s =>
      cases so <;> simp [stateAssumptionTail, stateAssumptionSuffix] at hTail ⊢
      exact hTail
/- `step_pop` traverses only across proved entries before it either finds the
   leading `assume_push` to discharge or falls into the assumption tail. This
   relation records the suffixes reachable by discarding only a proved prefix. -/
/-- Inductive relation describing suffix states reachable by repeated `step_pop` operations. -/
inductive stateStepPopSuffix : CState -> CState -> Prop
  | refl (s : CState) : stateStepPopSuffix s s
  | proven (P : Term) {cur root : CState} :
      stateStepPopSuffix cur root ->
      stateStepPopSuffix cur (CState.cons (CStateObj.proven P) root)
/-- Transitivity lemma for `stateStepPopSuffix`. -/
theorem stateStepPopSuffix_trans :
  forall {s t u : CState},
    stateStepPopSuffix s t ->
    stateStepPopSuffix t u ->
    stateStepPopSuffix s u
:=
by
  intro s t u hst htu
  induction htu generalizing s with
  | refl _ =>
      exact hst
  | proven P htu ih =>
      exact stateStepPopSuffix.proven P (ih hst)
/-- Derives `stateAssumes_eq` from `stateStepPopSuffix`. -/
theorem stateAssumes_eq_of_stateStepPopSuffix :
  forall {cur root : CState},
    stateStepPopSuffix cur root ->
    stateAssumes root = stateAssumes cur
:=
by
  intro cur root hSuffix
  induction hSuffix with
  | refl _ =>
      rfl
  | proven P hSuffix ih =>
      simpa [stateAssumes] using ih
/-- Derives `statePushes_eq` from `stateStepPopSuffix`. -/
theorem statePushes_eq_of_stateStepPopSuffix :
  forall {cur root : CState},
    stateStepPopSuffix cur root ->
    statePushes root = statePushes cur
:=
by
  intro cur root hSuffix
  induction hSuffix with
  | refl _ =>
      rfl
  | proven P hSuffix ih =>
      simpa [statePushes] using ih
/-- Derives `stateAssumes_eq` from `stateStepPopSuffix_assume_push`. -/
theorem stateAssumes_eq_of_stateStepPopSuffix_assume_push
    {root tail : CState} {A : Term} :
  stateStepPopSuffix (CState.cons (CStateObj.assume_push A) tail) root ->
  stateAssumes root = stateAssumes tail :=
by
  intro hSuffix
  simpa [stateAssumes] using stateAssumes_eq_of_stateStepPopSuffix hSuffix
/-- Derives `statePushes_eq` from `stateStepPopSuffix_assume_push`. -/
theorem statePushes_eq_of_stateStepPopSuffix_assume_push
    {root tail : CState} {A : Term} :
  stateStepPopSuffix (CState.cons (CStateObj.assume_push A) tail) root ->
  statePushes root = Term.Apply (Term.Apply (Term.UOp UserOp.and) A) (statePushes tail) :=
by
  intro hSuffix
  simpa [statePushes] using statePushes_eq_of_stateStepPopSuffix hSuffix
/-- Lemma about `stateOk_not_stuck`. -/
theorem stateOk_not_stuck {s : CState} :
  stateOk s -> s ≠ CState.Stuck :=
by
  intro hOk hStuck
  subst hStuck
  simp [stateOk] at hOk

/-- Establishes an equality relating `eo` and `bool_true_iff`. -/
@[simp] theorem eo_eq_bool_true_iff (t : Term) :
  __eo_eq t Term.Bool = Term.Boolean true ↔ t = Term.Bool :=
by
  cases t <;> simp [__eo_eq, native_teq]
/-- Lemma about `typeof_stuck_ne_bool`. -/
theorem typeof_stuck_ne_bool :
  __eo_typeof Term.Stuck ≠ Term.Bool :=
by
  native_decide

/-- Establishes an equality relating `eo_is_bool_type` and `true_iff`. -/
@[simp] theorem eo_is_bool_type_eq_true_iff (t : Term) :
  __eo_is_bool_type t = Term.Boolean true ↔ __eo_typeof t = Term.Bool :=
by
  by_cases hStuck : t = Term.Stuck
  · subst hStuck
    constructor
    · simp [__eo_is_bool_type]
    · exact False.elim ∘ typeof_stuck_ne_bool
  · simp [__eo_is_bool_type, eo_eq_bool_true_iff]

/-- Derives `eo_is_bool_type_eq_true` from `typeof_bool`. -/
@[simp] theorem eo_is_bool_type_eq_true_of_typeof_bool (t : Term) :
  __eo_typeof t = Term.Bool ->
  __eo_is_bool_type t = Term.Boolean true :=
by
  intro hTy
  exact (eo_is_bool_type_eq_true_iff t).2 hTy
/-- The combined guard used for assumptions and pushed assumptions. -/
def assumptionCheckGuard (A : Term) : Term :=
  __eo_and (__eo_is_bool_type A) (__eo_is_closed A)
/-!
The three projections of the generated `__eo_StateObj_proven`.  They are `rfl`,
but they are wanted as simp lemmas: `CheckerCore.lean` reasons about the term a
state object carries and would otherwise have to unfold the generated function
by name at every step.  `CStateObj` is part of the checker's state machine, so
its constructors are the same whatever the calculus is.
-/

@[simp] private theorem stateObjProven_assume (A : Term) :
    __eo_StateObj_proven (CStateObj.assume A) = A := rfl

@[simp] private theorem stateObjProven_assume_push (A : Term) :
    __eo_StateObj_proven (CStateObj.assume_push A) = A := rfl

@[simp] private theorem stateObjProven_proven (P : Term) :
    __eo_StateObj_proven (CStateObj.proven P) = P := rfl

/-- Splits a successful assumption guard. -/
theorem assumptionCheckGuard_eq_true_cases (A : Term) :
  assumptionCheckGuard A = Term.Boolean true ->
  __eo_is_bool_type A = Term.Boolean true ∧ __eo_is_closed A = Term.Boolean true :=
by
  intro h
  unfold assumptionCheckGuard at h
  cases hb : __eo_is_bool_type A <;> cases hc : __eo_is_closed A <;>
    simp [__eo_and, hb, hc, native_and, __eo_requires, native_ite, native_teq] at h
  case Binary.Binary =>
    split at h <;> contradiction
  case Boolean.Boolean b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp at h ⊢
/-- Simplifies the successful checked assume push. -/
theorem push_assume_check_true (A : Term) (s : CState) :
  __eo_push_assume_check (Term.Boolean true) A s =
    CState.cons (CStateObj.assume_push A) s :=
by
  simp [__eo_push_assume_check]
/-- Derives `push_assume_eq_cons` from a successful combined guard. -/
theorem push_assume_eq_cons_of_guard_true (A : Term) (s : CState) :
  assumptionCheckGuard A = Term.Boolean true ->
  __eo_push_assume_check (assumptionCheckGuard A) A s =
    CState.cons (CStateObj.assume_push A) s :=
by
  intro hGuard
  change __eo_push_assume_check (assumptionCheckGuard A) A s =
    CState.cons (CStateObj.assume_push A) s
  rw [hGuard]
  simp [__eo_push_assume_check]
/-- Derives `push_assume_eq_stuck` from `eq_stuck`. -/
theorem push_assume_eq_stuck_of_eq_stuck (s : CState) :
  __eo_push_assume_check (assumptionCheckGuard Term.Stuck) Term.Stuck s =
    CState.Stuck :=
by
  simp [assumptionCheckGuard, __eo_push_assume_check, __eo_is_bool_type, __eo_and]
/-- Derives `push_assume_eq_stuck` from an unsuccessful combined guard. -/
theorem push_assume_eq_stuck_of_guard_ne_true (A : Term) (s : CState) :
  assumptionCheckGuard A ≠ Term.Boolean true ->
  __eo_push_assume_check (assumptionCheckGuard A) A s = CState.Stuck :=
by
  intro hGuard
  cases hCheck : assumptionCheckGuard A <;>
    simp [__eo_push_assume_check]
  case Boolean b =>
    cases b <;> simp [hCheck] at hGuard ⊢
/-- Derives `push_assume_eq_stuck` from `typeof_ne_bool`. -/
theorem push_assume_eq_stuck_of_typeof_ne_bool (A : Term) (s : CState) :
  __eo_typeof A ≠ Term.Bool ->
  __eo_push_assume_check (assumptionCheckGuard A) A s = CState.Stuck :=
by
  intro hTy
  apply push_assume_eq_stuck_of_guard_ne_true
  intro hGuard
  exact hTy ((eo_is_bool_type_eq_true_iff A).1
    (assumptionCheckGuard_eq_true_cases A hGuard).1)
/-- Derives `assume_push_arg_ne_stuck` from `stateOk`. -/
theorem assume_push_arg_ne_stuck_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_assume_check (assumptionCheckGuard A) A s) -> A ≠ Term.Stuck :=
by
  intro hOk hA
  subst hA
  simp [push_assume_eq_stuck_of_eq_stuck, stateOk] at hOk
/-- Shows that `push_assume` reflects `stateOk`. -/
theorem push_assume_reflects_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_assume_check (assumptionCheckGuard A) A s) -> stateOk s :=
by
  intro hOk
  cases hCheck : assumptionCheckGuard A <;>
    simp [__eo_push_assume_check, hCheck, stateOk] at hOk
  case Boolean b =>
    cases b
    · simp [stateOk] at hOk
    · simpa [__eo_push_assume_check, hCheck, stateOk] using hOk
/-- Derives the successful combined guard from `stateOk`. -/
theorem push_assume_guard_true_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_assume_check (assumptionCheckGuard A) A s) ->
  assumptionCheckGuard A = Term.Boolean true :=
by
  intro hOk
  cases hCheck : assumptionCheckGuard A <;>
    simp [__eo_push_assume_check, hCheck, stateOk] at hOk
  case Boolean b =>
    cases b <;> simp [stateOk] at hOk ⊢
/-- Derives `push_assume_typeof_bool` from `stateOk`. -/
theorem push_assume_typeof_bool_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_assume_check (assumptionCheckGuard A) A s) -> __eo_typeof A = Term.Bool :=
by
  intro hOk
  have hGuard := push_assume_guard_true_of_stateOk A s hOk
  have hBool := (assumptionCheckGuard_eq_true_cases A hGuard).1
  exact (eo_is_bool_type_eq_true_iff A).1 hBool
/-- Derives `__eo_is_closed` from a successful checked assume push. -/
theorem push_assume_closed_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_assume_check (assumptionCheckGuard A) A s) ->
  __eo_is_closed A = Term.Boolean true :=
by
  intro hOk
  have hGuard := push_assume_guard_true_of_stateOk A s hOk
  exact (assumptionCheckGuard_eq_true_cases A hGuard).2
/-- Derives `push_assume_eq_cons` from `stateOk`. -/
theorem push_assume_eq_cons_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_assume_check (assumptionCheckGuard A) A s) ->
  __eo_push_assume_check (assumptionCheckGuard A) A s =
    CState.cons (CStateObj.assume_push A) s :=
by
  intro hOk
  exact push_assume_eq_cons_of_guard_true A s
    (push_assume_guard_true_of_stateOk A s hOk)
/-- Simplifies the successful checked input-assumption push. -/
theorem push_input_assume_check_true (A : Term) (s : CState) :
  __eo_push_input_assume_check (Term.Boolean true) A s =
    CState.cons (CStateObj.assume A) s :=
by
  simp [__eo_push_input_assume_check]
/-- Derives `push_input_assume_eq_cons` from a successful combined guard. -/
theorem push_input_assume_eq_cons_of_guard_true (A : Term) (s : CState) :
  assumptionCheckGuard A = Term.Boolean true ->
  __eo_push_input_assume_check (assumptionCheckGuard A) A s =
    CState.cons (CStateObj.assume A) s :=
by
  intro hGuard
  change __eo_push_input_assume_check (assumptionCheckGuard A) A s =
    CState.cons (CStateObj.assume A) s
  rw [hGuard]
  simp [__eo_push_input_assume_check]
/-- Derives `push_input_assume_eq_stuck` from `eq_stuck`. -/
theorem push_input_assume_eq_stuck_of_eq_stuck (s : CState) :
  __eo_push_input_assume_check (assumptionCheckGuard Term.Stuck) Term.Stuck s =
    CState.Stuck :=
by
  simp [assumptionCheckGuard, __eo_push_input_assume_check, __eo_is_bool_type, __eo_and]
/-- Derives `push_input_assume_eq_stuck` from an unsuccessful combined guard. -/
theorem push_input_assume_eq_stuck_of_guard_ne_true (A : Term) (s : CState) :
  assumptionCheckGuard A ≠ Term.Boolean true ->
  __eo_push_input_assume_check (assumptionCheckGuard A) A s = CState.Stuck :=
by
  intro hGuard
  cases hCheck : assumptionCheckGuard A <;>
    simp [__eo_push_input_assume_check]
  case Boolean b =>
    cases b <;> simp [hCheck] at hGuard ⊢
/-- Derives `push_input_assume_eq_stuck` from `typeof_ne_bool`. -/
theorem push_input_assume_eq_stuck_of_typeof_ne_bool (A : Term) (s : CState) :
  __eo_typeof A ≠ Term.Bool ->
  __eo_push_input_assume_check (assumptionCheckGuard A) A s = CState.Stuck :=
by
  intro hTy
  apply push_input_assume_eq_stuck_of_guard_ne_true
  intro hGuard
  exact hTy ((eo_is_bool_type_eq_true_iff A).1
    (assumptionCheckGuard_eq_true_cases A hGuard).1)
/-- Shows that `push_input_assume` reflects `stateOk`. -/
theorem push_input_assume_reflects_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A s) -> stateOk s :=
by
  intro hOk
  cases hCheck : assumptionCheckGuard A <;>
    simp [__eo_push_input_assume_check, hCheck, stateOk] at hOk
  case Boolean b =>
    cases b
    · simp [stateOk] at hOk
    · simpa [__eo_push_input_assume_check, hCheck, stateOk] using hOk
/-- Derives the successful combined guard from `stateOk`. -/
theorem push_input_assume_guard_true_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A s) ->
  assumptionCheckGuard A = Term.Boolean true :=
by
  intro hOk
  cases hCheck : assumptionCheckGuard A <;>
    simp [__eo_push_input_assume_check, hCheck, stateOk] at hOk
  case Boolean b =>
    cases b <;> simp [stateOk] at hOk ⊢
/-- Derives `push_input_assume_typeof_bool` from `stateOk`. -/
theorem push_input_assume_typeof_bool_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A s) ->
  __eo_typeof A = Term.Bool :=
by
  intro hOk
  have hGuard := push_input_assume_guard_true_of_stateOk A s hOk
  have hBool := (assumptionCheckGuard_eq_true_cases A hGuard).1
  exact (eo_is_bool_type_eq_true_iff A).1 hBool
/-- Derives `__eo_is_closed` from a successful checked input assumption. -/
theorem push_input_assume_closed_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A s) ->
  __eo_is_closed A = Term.Boolean true :=
by
  intro hOk
  have hGuard := push_input_assume_guard_true_of_stateOk A s hOk
  exact (assumptionCheckGuard_eq_true_cases A hGuard).2
/-- Derives `push_input_assume_eq_cons` from `stateOk`. -/
theorem push_input_assume_eq_cons_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A s) ->
  __eo_push_input_assume_check (assumptionCheckGuard A) A s =
    CState.cons (CStateObj.assume A) s :=
by
  intro hOk
  exact push_input_assume_eq_cons_of_guard_true A s
    (push_input_assume_guard_true_of_stateOk A s hOk)

/-- Derives `push_proven_eq_cons` from `typeof_bool`. -/
@[simp] theorem push_proven_eq_cons_of_typeof_bool (P : Term) (s : CState) :
  __eo_typeof P = Term.Bool ->
  __eo_push_proven P s = CState.cons (CStateObj.proven P) s :=
by
  intro hTy
  simp [__eo_push_proven, __eo_push_proven_check,
    eo_is_bool_type_eq_true_of_typeof_bool, hTy]

/-- Derives `push_proven_eq_stuck` from `eq_stuck`. -/
@[simp] theorem push_proven_eq_stuck_of_eq_stuck (s : CState) :
  __eo_push_proven Term.Stuck s = CState.Stuck :=
by
  simp [__eo_push_proven, __eo_push_proven_check, __eo_is_bool_type]

/-- Derives `push_proven_eq_stuck` from `typeof_ne_bool`. -/
@[simp] theorem push_proven_eq_stuck_of_typeof_ne_bool (P : Term) (s : CState) :
  __eo_typeof P ≠ Term.Bool ->
  __eo_push_proven P s = CState.Stuck :=
by
  intro hTy
  have hBool : __eo_is_bool_type P ≠ Term.Boolean true := by
    intro h
    exact hTy ((eo_is_bool_type_eq_true_iff P).1 h)
  cases hCheck : __eo_is_bool_type P <;> simp [__eo_push_proven, __eo_push_proven_check, hCheck]
  case Boolean b =>
    cases b <;> simp [hCheck] at hBool ⊢
/-- Derives `push_proven_typeof_bool` from `stateOk`. -/
theorem push_proven_typeof_bool_of_stateOk (P : Term) (s : CState) :
  stateOk (__eo_push_proven P s) -> __eo_typeof P = Term.Bool :=
by
  intro hOk
  have hBool : __eo_is_bool_type P = Term.Boolean true := by
    cases hCheck : __eo_is_bool_type P <;>
      simp [__eo_push_proven, __eo_push_proven_check, hCheck, stateOk] at hOk
    case Boolean b =>
      cases b <;> simp [stateOk] at hOk
      simp
  exact (eo_is_bool_type_eq_true_iff P).1 hBool
/-- Derives `push_proven_eq_cons` from `stateOk`. -/
theorem push_proven_eq_cons_of_stateOk (P : Term) (s : CState) :
  stateOk (__eo_push_proven P s) ->
  __eo_push_proven P s = CState.cons (CStateObj.proven P) s :=
by
  intro hOk
  exact push_proven_eq_cons_of_typeof_bool P s (push_proven_typeof_bool_of_stateOk P s hOk)
/-- Shows that `push_proven` reflects `stateOk`. -/
theorem push_proven_reflects_stateOk (P : Term) (s : CState) :
  stateOk (__eo_push_proven P s) -> stateOk s :=
by
  intro hOk
  have hTy := push_proven_typeof_bool_of_stateOk P s hOk
  simpa [push_proven_eq_cons_of_typeof_bool, hTy, stateOk] using hOk

/-- Establishes an equality relating `invoke_cmd_check_proven_proven` and `push_proven_check`. -/
@[simp] theorem invoke_cmd_check_proven_proven_eq_push_proven_check
    (F proven : Term) (s : CState) :
  __eo_invoke_cmd_check_proven (CState.cons (CStateObj.proven F) s) proven =
    __eo_push_proven_check (__eo_eq F proven) F s :=
by
  rw [__eo_invoke_cmd_check_proven]

/-- Establishes an equality relating `invoke_cmd_check_proven_proven` and `push_proven_check_cmd`. -/
@[simp] theorem invoke_cmd_check_proven_proven_eq_push_proven_check_cmd
    (F proven : Term) (s : CState) :
  __eo_invoke_cmd (CState.cons (CStateObj.proven F) s) (CCmd.check_proven proven) =
    __eo_push_proven_check (__eo_eq F proven) F s :=
by
  simp [__eo_invoke_cmd]
/-- Derives `invoke_step_eq` from `nonstuck`. -/
theorem invoke_step_eq_of_nonstuck
    (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  __eo_invoke_cmd s (CCmd.step r args premises) =
    __eo_push_proven (__eo_cmd_step_proven s r args premises) s :=
by
  cases s with
  | nil =>
      simp [__eo_invoke_cmd]
  | cons so s =>
      simp [__eo_invoke_cmd]
  | Stuck =>
      exact False.elim (hNotStuck rfl)
/-- Derives `invoke_step_eq_stuck` from `nonstuck`. -/
theorem invoke_step_eq_stuck_of_nonstuck
    (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  __eo_cmd_step_proven s r args premises = Term.Stuck ->
  __eo_invoke_cmd s (CCmd.step r args premises) = CState.Stuck :=
by
  intro hStep
  rw [invoke_step_eq_of_nonstuck s hNotStuck r args premises, hStep]
  simp [__eo_push_proven, __eo_push_proven_check, __eo_is_bool_type]
/-- Derives `invoke_step_eq_cons` from `nonstuck`. -/
theorem invoke_step_eq_cons_of_nonstuck
    (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) (P : Term) :
  __eo_cmd_step_proven s r args premises = P ->
  __eo_typeof P = Term.Bool ->
  __eo_invoke_cmd s (CCmd.step r args premises) = CState.cons (CStateObj.proven P) s :=
by
  intro hStep hTy
  rw [invoke_step_eq_of_nonstuck s hNotStuck r args premises, hStep]
  simp [push_proven_eq_cons_of_typeof_bool, hTy]
/-- Derives `invoke_step_eq_stuck` from `typeof_ne_bool`. -/
theorem invoke_step_eq_stuck_of_typeof_ne_bool
    (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) (P : Term) :
  __eo_cmd_step_proven s r args premises = P ->
  __eo_typeof P ≠ Term.Bool ->
  __eo_invoke_cmd s (CCmd.step r args premises) = CState.Stuck :=
by
  intro hStep hTy
  rw [invoke_step_eq_of_nonstuck s hNotStuck r args premises, hStep]
  simp [push_proven_eq_stuck_of_typeof_ne_bool, hTy]
/-- Derives `state_proven_nth_true` from `context`. -/
theorem state_proven_nth_true_of_context (M : SmtModel) :
  forall (s : CState) (n : native_Int),
    eo_interprets M (stateAssumes s) true ->
    eo_interprets M (statePushes s) true ->
    eo_interprets M (stateProvens s) true ->
    eo_interprets M (__eo_state_proven_nth s n) true
:=
by
  intro s
  induction s with
  | nil =>
      intro n hAss hPush hProv
      simpa [__eo_state_proven_nth] using eo_interprets_true M
  | Stuck =>
      intro n hAss hPush hProv
      exact False.elim (eo_interprets_stuck_true_absurd M (by simpa [stateAssumes] using hAss))
  | cons so s ih =>
      intro n hAss hPush hProv
      by_cases hZero : n = 0
      · subst hZero
        cases so with
        | assume A =>
            simpa [__eo_state_proven_nth, __eo_StateObj_proven] using eo_interprets_and_left M A (stateAssumes s) hAss
        | assume_push A =>
            simpa [__eo_state_proven_nth, __eo_StateObj_proven] using eo_interprets_and_left M A (statePushes s) hPush
        | proven A =>
            simpa [__eo_state_proven_nth, __eo_StateObj_proven] using eo_interprets_and_left M A (stateProvens s) hProv
      ·
        cases so with
        | assume A =>
            have hAssTail : eo_interprets M (stateAssumes s) true :=
              eo_interprets_and_right M A (stateAssumes s) hAss
            simpa [__eo_state_proven_nth, hZero] using
              ih (native_zplus n (native_zneg 1)) hAssTail hPush hProv
        | assume_push A =>
            have hPushTail : eo_interprets M (statePushes s) true :=
              eo_interprets_and_right M A (statePushes s) hPush
            simpa [__eo_state_proven_nth, hZero] using
              ih (native_zplus n (native_zneg 1)) hAss hPushTail hProv
        | proven A =>
            have hProvTail : eo_interprets M (stateProvens s) true :=
              eo_interprets_and_right M A (stateProvens s) hProv
            simpa [__eo_state_proven_nth, hZero] using
              ih (native_zplus n (native_zneg 1)) hAss hPush hProvTail
/-- Describes `stateAssumptionTail` after `invoke_assume_list`. -/
theorem stateAssumptionTail_invoke_assume_list :
  forall {F : CArgList},
    stateOk (__eo_invoke_assume_list CState.nil F) ->
    stateAssumptionTail (__eo_invoke_assume_list CState.nil F)
:=
by
  intro F hOk
  induction F with
  | nil =>
      simp [__eo_invoke_assume_list, stateAssumptionTail]
  | cons A rest ih =>
      have hPushOk :
          stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest)) := by
        simpa [__eo_invoke_assume_list, assumptionCheckGuard] using hOk
      have hRestOk :
          stateOk (__eo_invoke_assume_list CState.nil rest) :=
        push_input_assume_reflects_stateOk A
          (__eo_invoke_assume_list CState.nil rest) hPushOk
      have hPushEq := push_input_assume_eq_cons_of_stateOk A
        (__eo_invoke_assume_list CState.nil rest) hPushOk
      change stateAssumptionTail
        (__eo_push_input_assume_check (assumptionCheckGuard A) A
          (__eo_invoke_assume_list CState.nil rest))
      rw [hPushEq]
      simpa [stateAssumptionTail] using ih hRestOk
/-- Describes `stateAssumptionSuffix` after `invoke_assume_list`. -/
theorem stateAssumptionSuffix_invoke_assume_list :
  forall {F : CArgList},
    stateOk (__eo_invoke_assume_list CState.nil F) ->
    stateAssumptionSuffix (__eo_invoke_assume_list CState.nil F)
:=
by
  intro F hOk
  exact stateAssumptionSuffix_of_tail (stateAssumptionTail_invoke_assume_list hOk)
/-- Describes `stateAssumes` after `invoke_assume_list`. -/
theorem stateAssumes_invoke_assume_list :
  forall {F : CArgList},
    stateOk (__eo_invoke_assume_list CState.nil F) ->
    stateAssumes (__eo_invoke_assume_list CState.nil F) = argListAssumes F
:=
by
  intro F hOk
  induction F with
  | nil =>
      simp [__eo_invoke_assume_list, stateAssumes, argListAssumes]
  | cons A rest ih =>
      have hPushOk :
          stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest)) := by
        simpa [__eo_invoke_assume_list, assumptionCheckGuard] using hOk
      have hRestOk :
          stateOk (__eo_invoke_assume_list CState.nil rest) :=
        push_input_assume_reflects_stateOk A
          (__eo_invoke_assume_list CState.nil rest) hPushOk
      have hPushEq := push_input_assume_eq_cons_of_stateOk A
        (__eo_invoke_assume_list CState.nil rest) hPushOk
      change stateAssumes
          (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest)) =
        Term.Apply (Term.Apply (Term.UOp UserOp.and) A) (argListAssumes rest)
      rw [hPushEq]
      simpa [stateAssumes] using ih hRestOk
/-- Describes `statePushes` after `invoke_assume_list`. -/
theorem statePushes_invoke_assume_list :
  forall {F : CArgList},
    stateOk (__eo_invoke_assume_list CState.nil F) ->
    statePushes (__eo_invoke_assume_list CState.nil F) = Term.Boolean true
:=
by
  intro F hOk
  induction F with
  | nil =>
      simp [__eo_invoke_assume_list, statePushes]
  | cons A rest ih =>
      have hPushOk :
          stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest)) := by
        simpa [__eo_invoke_assume_list, assumptionCheckGuard] using hOk
      have hRestOk :
          stateOk (__eo_invoke_assume_list CState.nil rest) :=
        push_input_assume_reflects_stateOk A
          (__eo_invoke_assume_list CState.nil rest) hPushOk
      have hPushEq := push_input_assume_eq_cons_of_stateOk A
        (__eo_invoke_assume_list CState.nil rest) hPushOk
      change statePushes
          (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest)) =
        Term.Boolean true
      rw [hPushEq]
      simpa [statePushes] using ih hRestOk
/-- Describes `stateProvens` after `invoke_assume_list`. -/
theorem stateProvens_invoke_assume_list :
  forall {F : CArgList},
    stateOk (__eo_invoke_assume_list CState.nil F) ->
    stateProvens (__eo_invoke_assume_list CState.nil F) = Term.Boolean true
:=
by
  intro F hOk
  induction F with
  | nil =>
      simp [__eo_invoke_assume_list, stateProvens]
  | cons A rest ih =>
      have hPushOk :
          stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest)) := by
        simpa [__eo_invoke_assume_list, assumptionCheckGuard] using hOk
      have hRestOk :
          stateOk (__eo_invoke_assume_list CState.nil rest) :=
        push_input_assume_reflects_stateOk A
          (__eo_invoke_assume_list CState.nil rest) hPushOk
      have hPushEq := push_input_assume_eq_cons_of_stateOk A
        (__eo_invoke_assume_list CState.nil rest) hPushOk
      change stateProvens
          (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest)) =
        Term.Boolean true
      rw [hPushEq]
      simpa [stateProvens] using ih hRestOk
/-- Derives `stateOk` from `state_closed_true`. -/
theorem stateOk_of_state_closed_true :
  forall {s : CState}, __eo_state_is_closed s = true -> stateOk s
:=
by
  intro s hClosed
  induction s with
  | nil =>
      trivial
  | Stuck =>
      cases hClosed
  | cons so s ih =>
      cases so with
      | assume A =>
          exact ih hClosed
      | assume_push A =>
          cases hClosed
      | proven A =>
          exact ih hClosed
/-- Derives `statePushes` from `state_closed_true`. -/
theorem statePushes_of_state_closed_true :
  forall {s : CState}, __eo_state_is_closed s = true -> statePushes s = Term.Boolean true
:=
by
  intro s hClosed
  induction s with
  | nil =>
      simp [statePushes]
  | Stuck =>
      cases hClosed
  | cons so s ih =>
      cases so with
      | assume A =>
          simpa [__eo_state_is_closed, statePushes] using ih hClosed
      | assume_push A =>
          cases hClosed
      | proven A =>
          simpa [__eo_state_is_closed, statePushes] using ih hClosed
/-- Derives `invoke_cmd_step_pop` from `assumptionTail`. -/
theorem invoke_cmd_step_pop_of_assumptionTail :
  forall (s cur : CState) (r : CRule) (args : CArgList) (premises : CIndexList),
    stateAssumptionTail cur ->
    __eo_invoke_cmd_step_pop s cur r args premises = CState.Stuck
:=
by
  intro s cur
  induction cur with
  | nil =>
      intro r args premises hTail
      simp [__eo_invoke_cmd_step_pop]
  | Stuck =>
      intro r args premises hTail
      cases hTail
  | cons so cur ih =>
      intro r args premises hTail
      cases so with
      | assume A =>
          simpa [__eo_invoke_cmd_step_pop, stateAssumptionTail] using
            ih r args premises (by simpa [stateAssumptionTail] using hTail)
      | assume_push A =>
          cases hTail
      | proven A =>
          cases hTail
/-- Describes `stateAssumptionSuffix` after `invoke_cmd_step_pop`. -/
theorem stateAssumptionSuffix_invoke_cmd_step_pop :
  forall (s cur : CState) (r : CRule) (args : CArgList) (premises : CIndexList),
    stateAssumptionSuffix cur ->
    stateOk (__eo_invoke_cmd_step_pop s cur r args premises) ->
    stateAssumptionSuffix (__eo_invoke_cmd_step_pop s cur r args premises)
:=
by
  intro s cur
  induction cur with
  | nil =>
      intro r args premises hSuffix hOk
      simp [__eo_invoke_cmd_step_pop, stateOk] at hOk
  | Stuck =>
      intro r args premises hSuffix hOk
      cases hSuffix
  | cons so cur ih =>
      intro r args premises hSuffix hOk
      cases so with
      | assume_push A =>
          have hTailSuffix : stateAssumptionSuffix cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          have hPushOk :
              stateOk (__eo_push_proven (__eo_cmd_step_pop_proven s r args A premises) cur) := by
            simpa [__eo_invoke_cmd_step_pop] using hOk
          have hPushEq :
              __eo_push_proven (__eo_cmd_step_pop_proven s r args A premises) cur =
                CState.cons (CStateObj.proven (__eo_cmd_step_pop_proven s r args A premises)) cur :=
            push_proven_eq_cons_of_stateOk (__eo_cmd_step_pop_proven s r args A premises) cur hPushOk
          simpa [__eo_invoke_cmd_step_pop, hPushEq, stateAssumptionSuffix] using hTailSuffix
      | assume A =>
          have hTail : stateAssumptionTail cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          have hStuck : __eo_invoke_cmd_step_pop s cur r args premises = CState.Stuck :=
            invoke_cmd_step_pop_of_assumptionTail s cur r args premises hTail
          simp [__eo_invoke_cmd_step_pop, hStuck, stateOk] at hOk
      | proven A =>
          have hTailSuffix : stateAssumptionSuffix cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          exact ih r args premises hTailSuffix
            (by simpa [__eo_invoke_cmd_step_pop, stateOk] using hOk)
/-- Describes `stateAssumes` after `invoke_cmd_step_pop`. -/
theorem stateAssumes_invoke_cmd_step_pop :
  forall (s cur : CState) (r : CRule) (args : CArgList) (premises : CIndexList),
    stateAssumptionSuffix cur ->
    stateOk (__eo_invoke_cmd_step_pop s cur r args premises) ->
    stateAssumes (__eo_invoke_cmd_step_pop s cur r args premises) = stateAssumes cur
:=
by
  intro s cur
  induction cur with
  | nil =>
      intro r args premises hSuffix hOk
      simp [__eo_invoke_cmd_step_pop, stateOk] at hOk
  | Stuck =>
      intro r args premises hSuffix hOk
      cases hSuffix
  | cons so cur ih =>
      intro r args premises hSuffix hOk
      cases so with
      | assume_push A =>
          have hPushOk :
              stateOk (__eo_push_proven (__eo_cmd_step_pop_proven s r args A premises) cur) := by
            simpa [__eo_invoke_cmd_step_pop] using hOk
          have hPushEq :
              __eo_push_proven (__eo_cmd_step_pop_proven s r args A premises) cur =
                CState.cons (CStateObj.proven (__eo_cmd_step_pop_proven s r args A premises)) cur :=
            push_proven_eq_cons_of_stateOk (__eo_cmd_step_pop_proven s r args A premises) cur hPushOk
          simp [__eo_invoke_cmd_step_pop, hPushEq, stateAssumes]
      | assume A =>
          have hTail : stateAssumptionTail cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          have hStuck : __eo_invoke_cmd_step_pop s cur r args premises = CState.Stuck :=
            invoke_cmd_step_pop_of_assumptionTail s cur r args premises hTail
          simp [__eo_invoke_cmd_step_pop, hStuck, stateOk] at hOk
      | proven A =>
          have hTailSuffix : stateAssumptionSuffix cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          simpa [__eo_invoke_cmd_step_pop, stateAssumes] using
            ih r args premises hTailSuffix (by simpa [__eo_invoke_cmd_step_pop, stateOk] using hOk)
/-- Shows that `invoke_cmd_step_pop` reflects `stateOk`. -/
theorem invoke_cmd_step_pop_reflects_stateOk :
  forall (s cur : CState) (r : CRule) (args : CArgList) (premises : CIndexList),
    stateOk (__eo_invoke_cmd_step_pop s cur r args premises) -> stateOk cur
:=
by
  intro s cur
  induction cur with
  | nil =>
      intro r args premises
      simp [__eo_invoke_cmd_step_pop, stateOk]
  | Stuck =>
      intro r args premises
      simp [__eo_invoke_cmd_step_pop, stateOk]
  | cons so cur ih =>
      intro r args premises
      cases so with
      | assume_push A =>
          intro hOk
          have hPushOk :
              stateOk (__eo_push_proven (__eo_cmd_step_pop_proven s r args A premises) cur) := by
            simpa [__eo_invoke_cmd_step_pop] using hOk
          exact push_proven_reflects_stateOk (__eo_cmd_step_pop_proven s r args A premises) cur hPushOk
      | assume A =>
          intro hOk
          exact ih r args premises (by simpa [__eo_invoke_cmd_step_pop, stateOk] using hOk)
      | proven A =>
          intro hOk
          exact ih r args premises (by simpa [__eo_invoke_cmd_step_pop, stateOk] using hOk)
/-- Shows that `invoke_cmd` reflects `stateOk`. -/
theorem invoke_cmd_reflects_stateOk :
  forall (s : CState) (c : CCmd), stateOk (__eo_invoke_cmd s c) -> stateOk s
:=
by
  intro s c
  cases s with
  | nil =>
      cases c <;> simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, __eo_push_proven,
        __eo_push_proven_check, stateOk]
  | Stuck =>
      simp [__eo_invoke_cmd, stateOk]
  | cons so s =>
      cases c with
      | assume_push A =>
          intro hOk
          exact push_assume_reflects_stateOk A (CState.cons so s) (by
            simpa [__eo_invoke_cmd, assumptionCheckGuard] using hOk)
      | check_proven proven =>
          cases so with
          | assume A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, stateOk]
          | assume_push A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, stateOk]
          | proven F =>
              intro hOk
              cases hEq : __eo_eq F proven <;>
                simp [__eo_invoke_cmd, __eo_push_proven_check,
                  hEq, stateOk] at hOk ⊢
              case Boolean b =>
                cases b with
                | false =>
                    simp [stateOk] at hOk
                | true =>
                    exact hOk
      | step r args premises =>
          intro hOk
          have hPushOk :
              stateOk (__eo_push_proven (__eo_cmd_step_proven (CState.cons so s) r args premises)
                (CState.cons so s)) := by
            simpa [__eo_invoke_cmd] using hOk
          exact push_proven_reflects_stateOk
            (__eo_cmd_step_proven (CState.cons so s) r args premises) (CState.cons so s) hPushOk
      | step_pop r args premises =>
          intro hOk
          exact invoke_cmd_step_pop_reflects_stateOk (CState.cons so s) (CState.cons so s)
            r args premises (by simpa [__eo_invoke_cmd] using hOk)
/-- Describes `stateAssumptionSuffix` after `invoke_cmd`. -/
theorem stateAssumptionSuffix_invoke_cmd :
  forall (s : CState) (c : CCmd),
    stateAssumptionSuffix s ->
    stateOk (__eo_invoke_cmd s c) ->
    stateAssumptionSuffix (__eo_invoke_cmd s c)
:=
by
  intro s c
  cases c with
  | assume_push A =>
      intro hSuffix hOk
      cases s with
      | nil =>
          have hPushOk : stateOk (__eo_push_assume_check (assumptionCheckGuard A) A CState.nil) := by
            simpa [__eo_invoke_cmd, assumptionCheckGuard] using hOk
          have hPushEq := push_assume_eq_cons_of_stateOk A CState.nil hPushOk
          change stateAssumptionSuffix
            (__eo_push_assume_check (assumptionCheckGuard A) A CState.nil)
          rw [hPushEq]
          simp [stateAssumptionSuffix]
      | cons so s =>
          have hPushOk : stateOk (__eo_push_assume_check (assumptionCheckGuard A) A (CState.cons so s)) := by
            simpa [__eo_invoke_cmd, assumptionCheckGuard] using hOk
          have hPushEq := push_assume_eq_cons_of_stateOk A (CState.cons so s) hPushOk
          change stateAssumptionSuffix
            (__eo_push_assume_check (assumptionCheckGuard A) A (CState.cons so s))
          rw [hPushEq]
          simpa [stateAssumptionSuffix] using hSuffix
      | Stuck =>
          cases hSuffix
  | check_proven proven =>
      intro hSuffix hOk
      cases s with
      | nil =>
          simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, stateOk] at hOk
      | Stuck =>
          cases hSuffix
      | cons so s =>
          cases so with
          | assume A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, stateOk] at hOk
          | assume_push A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, stateOk] at hOk
          | proven F =>
              cases hEq : __eo_eq F proven <;>
                simp [__eo_invoke_cmd, __eo_push_proven_check,
                  hEq, stateOk] at hOk
              case Boolean b =>
                cases b with
                | false =>
                    contradiction
                | true =>
                    have hTailSuffix : stateAssumptionSuffix s := by
                      simpa [stateAssumptionSuffix] using hSuffix
                    simpa [__eo_invoke_cmd, __eo_push_proven_check,
                      hEq, stateAssumptionSuffix] using hTailSuffix
  | step r args premises =>
      intro hSuffix hOk
      cases s with
      | nil =>
          have hPushOk :
              stateOk (__eo_push_proven (__eo_cmd_step_proven CState.nil r args premises) CState.nil) := by
            simpa [__eo_invoke_cmd] using hOk
          have hPushEq := push_proven_eq_cons_of_stateOk
            (__eo_cmd_step_proven CState.nil r args premises) CState.nil hPushOk
          simp [__eo_invoke_cmd, hPushEq, stateAssumptionSuffix]
      | Stuck =>
          cases hSuffix
      | cons so s =>
          have hPushOk :
              stateOk (__eo_push_proven (__eo_cmd_step_proven (CState.cons so s) r args premises)
                (CState.cons so s)) := by
            simpa [__eo_invoke_cmd] using hOk
          have hPushEq := push_proven_eq_cons_of_stateOk
            (__eo_cmd_step_proven (CState.cons so s) r args premises) (CState.cons so s) hPushOk
          simpa [__eo_invoke_cmd, hPushEq, stateAssumptionSuffix] using hSuffix
  | step_pop r args premises =>
      intro hSuffix hOk
      cases s with
      | nil =>
          simpa [__eo_invoke_cmd] using
            stateAssumptionSuffix_invoke_cmd_step_pop CState.nil CState.nil r args premises hSuffix hOk
      | cons so s =>
          simpa [__eo_invoke_cmd] using
            stateAssumptionSuffix_invoke_cmd_step_pop (CState.cons so s) (CState.cons so s) r args premises hSuffix hOk
      | Stuck =>
          cases hSuffix
/-- Describes `stateAssumes` after `invoke_cmd`. -/
theorem stateAssumes_invoke_cmd :
  forall (s : CState) (c : CCmd),
    stateAssumptionSuffix s ->
    stateOk (__eo_invoke_cmd s c) ->
    stateAssumes (__eo_invoke_cmd s c) = stateAssumes s
:=
by
  intro s c
  cases c with
  | assume_push A =>
      intro hSuffix hOk
      cases s with
      | nil =>
          have hPushOk : stateOk (__eo_push_assume_check (assumptionCheckGuard A) A CState.nil) := by
            simpa [__eo_invoke_cmd, assumptionCheckGuard] using hOk
          have hPushEq := push_assume_eq_cons_of_stateOk A CState.nil hPushOk
          change stateAssumes
              (__eo_push_assume_check (assumptionCheckGuard A) A CState.nil) =
            stateAssumes CState.nil
          rw [hPushEq]
          simp [stateAssumes]
      | cons so s =>
          have hPushOk : stateOk (__eo_push_assume_check (assumptionCheckGuard A) A (CState.cons so s)) := by
            simpa [__eo_invoke_cmd, assumptionCheckGuard] using hOk
          have hPushEq := push_assume_eq_cons_of_stateOk A (CState.cons so s) hPushOk
          change stateAssumes
              (__eo_push_assume_check (assumptionCheckGuard A) A (CState.cons so s)) =
            stateAssumes (CState.cons so s)
          rw [hPushEq]
          simp [stateAssumes]
      | Stuck =>
          cases hSuffix
  | check_proven proven =>
      intro hSuffix hOk
      cases s with
      | nil =>
          simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, stateOk] at hOk
      | Stuck =>
          cases hSuffix
      | cons so s =>
          cases so with
          | assume A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, stateOk] at hOk
          | assume_push A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, stateOk] at hOk
          | proven F =>
              cases hEq : __eo_eq F proven <;>
                simp [__eo_invoke_cmd, __eo_push_proven_check,
                  hEq, stateOk] at hOk
              case Boolean b =>
                cases b with
                | false =>
                    contradiction
                | true =>
                    simp [__eo_invoke_cmd, __eo_push_proven_check,
                      hEq, stateAssumes]
  | step r args premises =>
      intro hSuffix hOk
      cases s with
      | nil =>
          have hPushOk :
              stateOk (__eo_push_proven (__eo_cmd_step_proven CState.nil r args premises) CState.nil) := by
            simpa [__eo_invoke_cmd] using hOk
          have hPushEq := push_proven_eq_cons_of_stateOk
            (__eo_cmd_step_proven CState.nil r args premises) CState.nil hPushOk
          simp [__eo_invoke_cmd, hPushEq, stateAssumes]
      | Stuck =>
          cases hSuffix
      | cons so s =>
          have hPushOk :
              stateOk (__eo_push_proven (__eo_cmd_step_proven (CState.cons so s) r args premises)
                (CState.cons so s)) := by
            simpa [__eo_invoke_cmd] using hOk
          have hPushEq := push_proven_eq_cons_of_stateOk
            (__eo_cmd_step_proven (CState.cons so s) r args premises) (CState.cons so s) hPushOk
          simp [__eo_invoke_cmd, hPushEq, stateAssumes]
  | step_pop r args premises =>
      intro hSuffix hOk
      cases s with
      | nil =>
          simpa [__eo_invoke_cmd] using
            stateAssumes_invoke_cmd_step_pop CState.nil CState.nil r args premises hSuffix hOk
      | cons so s =>
          simpa [__eo_invoke_cmd] using
            stateAssumes_invoke_cmd_step_pop (CState.cons so s) (CState.cons so s) r args premises hSuffix hOk
      | Stuck =>
          cases hSuffix
/-- Shows that `invoke_cmd_list` reflects `stateOk`. -/
theorem invoke_cmd_list_reflects_stateOk :
  forall (s : CState) (cs : CCmdList), stateOk (__eo_invoke_cmd_list s cs) -> stateOk s
:=
by
  intro s cs
  induction cs generalizing s with
  | nil =>
      simp [__eo_invoke_cmd_list]
  | cons c cs ih =>
      intro hOk
      have hTail : stateOk (__eo_invoke_cmd s c) := by
        exact ih (__eo_invoke_cmd s c) (by simpa [__eo_invoke_cmd_list] using hOk)
      exact invoke_cmd_reflects_stateOk s c hTail
/-- Describes `stateAssumptionSuffix` after `invoke_cmd_list`. -/
theorem stateAssumptionSuffix_invoke_cmd_list :
  forall (s : CState) (cs : CCmdList),
    stateAssumptionSuffix s ->
    stateOk (__eo_invoke_cmd_list s cs) ->
    stateAssumptionSuffix (__eo_invoke_cmd_list s cs)
:=
by
  intro s cs
  induction cs generalizing s with
  | nil =>
      intro hSuffix hOk
      simpa [__eo_invoke_cmd_list] using hSuffix
  | cons c cs ih =>
      intro hSuffix hOk
      have hStepOk : stateOk (__eo_invoke_cmd s c) := by
        exact invoke_cmd_list_reflects_stateOk (__eo_invoke_cmd s c) cs
          (by simpa [__eo_invoke_cmd_list] using hOk)
      have hStepSuffix : stateAssumptionSuffix (__eo_invoke_cmd s c) :=
        stateAssumptionSuffix_invoke_cmd s c hSuffix hStepOk
      exact ih (__eo_invoke_cmd s c) hStepSuffix
        (by simpa [__eo_invoke_cmd_list] using hOk)
/-- Describes `stateAssumes` after `invoke_cmd_list`. -/
theorem stateAssumes_invoke_cmd_list :
  forall (s : CState) (cs : CCmdList),
    stateAssumptionSuffix s ->
    stateOk (__eo_invoke_cmd_list s cs) ->
    stateAssumes (__eo_invoke_cmd_list s cs) = stateAssumes s
:=
by
  intro s cs
  induction cs generalizing s with
  | nil =>
      intro hSuffix hOk
      simp [__eo_invoke_cmd_list]
  | cons c cs ih =>
      intro hSuffix hOk
      have hStepOk : stateOk (__eo_invoke_cmd s c) := by
        exact invoke_cmd_list_reflects_stateOk (__eo_invoke_cmd s c) cs
          (by simpa [__eo_invoke_cmd_list] using hOk)
      have hStepSuffix : stateAssumptionSuffix (__eo_invoke_cmd s c) :=
        stateAssumptionSuffix_invoke_cmd s c hSuffix hStepOk
      have hStepAssumes :
          stateAssumes (__eo_invoke_cmd s c) = stateAssumes s :=
        stateAssumes_invoke_cmd s c hSuffix hStepOk
      calc
        stateAssumes (__eo_invoke_cmd_list s (CCmdList.cons c cs))
            = stateAssumes (__eo_invoke_cmd s c) := by
                simpa [__eo_invoke_cmd_list] using
                  ih (__eo_invoke_cmd s c) hStepSuffix
                    (by simpa [__eo_invoke_cmd_list] using hOk)
        _ = stateAssumes s := hStepAssumes
/-- Derives `final_stateOk` from `checker_true`. -/
theorem final_stateOk_of_checker_true (F : CArgList) (pf : CCmdList) :
  (__eo_checker_is_refutation F pf) = true ->
  stateOk (__eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf) :=
by
  intro hChecker
  let S1 := __eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf
  have hClosed : __eo_state_is_closed (__eo_invoke_cmd_check_proven S1 (Term.Boolean false)) = true := by
    simpa [__eo_checker_is_refutation, __eo_state_is_refutation, S1] using hChecker
  have hCheckedOk : stateOk (__eo_invoke_cmd_check_proven S1 (Term.Boolean false)) :=
    stateOk_of_state_closed_true hClosed
  have hCheckedOk' : stateOk (__eo_invoke_cmd S1 (CCmd.check_proven (Term.Boolean false))) := by
    cases hS1 : S1 <;> simpa [__eo_invoke_cmd, hS1, __eo_invoke_cmd_check_proven] using hCheckedOk
  simpa using invoke_cmd_reflects_stateOk S1 (CCmd.check_proven (Term.Boolean false)) hCheckedOk'
/-- Shows that `eo_eq_false_true` implies `eq_false`. -/
theorem eo_eq_false_true_implies_eq_false (t : Term) :
  __eo_eq t (Term.Boolean false) = Term.Boolean true ->
  t = Term.Boolean false :=
by
  intro hEq
  cases t <;> simp [__eo_eq, native_teq] at hEq ⊢ <;> assumption
/-- Derives `final_state_shape` from `checker_true`. -/
theorem final_state_shape_of_checker_true (F : CArgList) (pf : CCmdList) :
  (__eo_checker_is_refutation F pf) = true ->
  ∃ s : CState,
    __eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf =
      CState.cons (CStateObj.proven (Term.Boolean false)) s ∧
    __eo_state_is_closed s = true :=
by
  intro hChecker
  let S1 := __eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf
  have hClosed : __eo_state_is_closed (__eo_invoke_cmd_check_proven S1 (Term.Boolean false)) = true := by
    simpa [__eo_checker_is_refutation, __eo_state_is_refutation, S1] using hChecker
  cases hS1 : S1 with
  | nil =>
      simp [S1, hS1, __eo_invoke_cmd_check_proven, __eo_state_is_closed] at hClosed
  | Stuck =>
      simp [S1, hS1, __eo_invoke_cmd_check_proven, __eo_state_is_closed] at hClosed
  | cons so s =>
      cases so with
      | assume A =>
          simp [S1, hS1, __eo_invoke_cmd_check_proven, __eo_state_is_closed] at hClosed
      | assume_push A =>
          simp [S1, hS1, __eo_invoke_cmd_check_proven, __eo_state_is_closed] at hClosed
      | proven P =>
          cases hEq : __eo_eq P (Term.Boolean false) <;>
            simp [S1, hS1, __eo_push_proven_check,
              __eo_state_is_closed, hEq] at hClosed
          case Boolean b =>
            cases b with
            | false =>
                contradiction
            | true =>
                have hP : P = Term.Boolean false :=
                  eo_eq_false_true_implies_eq_false P hEq
                subst hP
                refine ⟨s, ?_, hClosed⟩
                simp [S1, hS1]
/-- Derives `stateAssumes` from `checker_true`. -/
theorem stateAssumes_of_checker_true (F : CArgList) (pf : CCmdList) :
  (__eo_checker_is_refutation F pf) = true ->
  stateAssumes (__eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf) =
    argListAssumes F :=
by
  intro hChecker
  let S0 := __eo_invoke_assume_list CState.nil F
  let S1 := __eo_invoke_cmd_list S0 pf
  have hS1Ok : stateOk S1 := by
    simpa [S1, S0] using final_stateOk_of_checker_true F pf hChecker
  have hS0Ok : stateOk S0 := by
    simpa [S1] using invoke_cmd_list_reflects_stateOk S0 pf hS1Ok
  have hShape0 : stateAssumptionSuffix S0 := by
    simpa [S0] using stateAssumptionSuffix_invoke_assume_list hS0Ok
  calc
    stateAssumes S1 = stateAssumes S0 := by
      simpa [S1] using stateAssumes_invoke_cmd_list S0 pf hShape0 hS1Ok
    _ = argListAssumes F := by
      simpa [S0] using stateAssumes_invoke_assume_list hS0Ok
