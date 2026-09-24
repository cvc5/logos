module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.StringSupport
import all Cpc.Proofs.RuleSupport.StringSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace CnfSupport

private theorem eo_requires_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [__eo_requires, hxy, SmtEval.native_ite] at h

/-- Shows that `false` is interpreted as `false` in every model. -/
theorem eo_interprets_false (M : SmtModel) :
    eo_interprets M (Term.Boolean false) false := by
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  rw [show __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false by
    rfl]
  refine smt_interprets.intro_false M (SmtTerm.Boolean false) ?_ ?_
  · rw [__smtx_typeof.eq_1]
  · rw [__smtx_model_eval.eq_1]

/-- Splits a Boolean EO term into the `true` and `false` cases. -/
theorem eo_interprets_bool_cases
    (M : SmtModel) (hM : model_wf M) (t : Term) :
    RuleProofs.eo_has_bool_type t ->
    eo_interprets M t true ∨ eo_interprets M t false := by
  intro hTy
  rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM t hTy with ⟨b, hEval⟩
  cases b with
  | true =>
      exact Or.inl (RuleProofs.eo_interprets_of_bool_eval M t true hTy hEval)
  | false =>
      exact Or.inr (RuleProofs.eo_interprets_of_bool_eval M t false hTy hEval)

/-- If `A ∨ B` is false, then `A` is false. -/
theorem eo_interprets_or_false_left
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) false ->
    eo_interprets M A false := by
  intro hOrFalse
  have hOrBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) :=
    RuleProofs.eo_has_bool_type_of_interprets_false M _ hOrFalse
  have hABool : RuleProofs.eo_has_bool_type A :=
    RuleProofs.eo_has_bool_type_or_left A B hOrBool
  have hBBool : RuleProofs.eo_has_bool_type B :=
    RuleProofs.eo_has_bool_type_or_right A B hOrBool
  rcases eo_interprets_bool_cases M hM A hABool with hATrue | hAFalse
  · have hOrTrue : eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) true :=
      RuleProofs.eo_interprets_or_left_intro M hM A B hATrue hBBool
    exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hOrTrue) hOrFalse)
  · exact hAFalse

/-- If `A ∨ B` is false, then `B` is false. -/
theorem eo_interprets_or_false_right
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) false ->
    eo_interprets M B false := by
  intro hOrFalse
  have hOrBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) :=
    RuleProofs.eo_has_bool_type_of_interprets_false M _ hOrFalse
  have hABool : RuleProofs.eo_has_bool_type A :=
    RuleProofs.eo_has_bool_type_or_left A B hOrBool
  have hBBool : RuleProofs.eo_has_bool_type B :=
    RuleProofs.eo_has_bool_type_or_right A B hOrBool
  rcases eo_interprets_bool_cases M hM B hBBool with hBTrue | hBFalse
  · have hOrTrue : eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) true :=
      RuleProofs.eo_interprets_or_right_intro M hM A B hABool hBTrue
    exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hOrTrue) hOrFalse)
  · exact hBFalse

/-- If `__eo_typeof_not t` is Boolean, then `t` is Boolean. -/
theorem typeof_not_eq_bool {t : Term} :
    __eo_typeof_not t = Term.Bool ->
    t = Term.Bool := by
  cases t <;> simp [__eo_typeof_not]

/-- If `__eo_typeof_or t1 t2` is Boolean, then `t1` is Boolean. -/
theorem typeof_or_eq_bool_left {t1 t2 : Term} :
    __eo_typeof_or t1 t2 = Term.Bool ->
    t1 = Term.Bool := by
  cases t1 <;> cases t2 <;> simp [__eo_typeof_or]

/-- If `__eo_typeof_or t1 t2` is Boolean, then `t2` is Boolean. -/
theorem typeof_or_eq_bool_right {t1 t2 : Term} :
    __eo_typeof_or t1 t2 = Term.Bool ->
    t2 = Term.Bool := by
  cases t1 <;> cases t2 <;> simp [__eo_typeof_or]

/-- The first literal of a right-associated two-literal Boolean clause is Boolean. -/
theorem typeof_clause2_left_eq_bool {A B : Term} :
    __eo_typeof_or A (__eo_typeof_or B Term.Bool) = Term.Bool ->
    A = Term.Bool := by
  intro hTy
  exact typeof_or_eq_bool_left hTy

/-- The second literal of a right-associated two-literal Boolean clause is Boolean. -/
theorem typeof_clause2_right_eq_bool {A B : Term} :
    __eo_typeof_or A (__eo_typeof_or B Term.Bool) = Term.Bool ->
    B = Term.Bool := by
  intro hTy
  exact typeof_or_eq_bool_left (typeof_or_eq_bool_right hTy)

/-- The first literal of a right-associated three-literal Boolean clause is Boolean. -/
theorem typeof_clause3_left_eq_bool {A B C : Term} :
    __eo_typeof_or A (__eo_typeof_or B (__eo_typeof_or C Term.Bool)) = Term.Bool ->
    A = Term.Bool := by
  intro hTy
  exact typeof_or_eq_bool_left hTy

/-- The second literal of a right-associated three-literal Boolean clause is Boolean. -/
theorem typeof_clause3_middle_eq_bool {A B C : Term} :
    __eo_typeof_or A (__eo_typeof_or B (__eo_typeof_or C Term.Bool)) = Term.Bool ->
    B = Term.Bool := by
  intro hTy
  exact typeof_or_eq_bool_left (typeof_or_eq_bool_right hTy)

/-- The third literal of a right-associated three-literal Boolean clause is Boolean. -/
theorem typeof_clause3_right_eq_bool {A B C : Term} :
    __eo_typeof_or A (__eo_typeof_or B (__eo_typeof_or C Term.Bool)) = Term.Bool ->
    C = Term.Bool := by
  intro hTy
  exact typeof_or_eq_bool_left
    (typeof_or_eq_bool_right (typeof_or_eq_bool_right hTy))


/-- A translated implication has Boolean translated arguments. -/
theorem imp_args_have_bool_type_of_translation (A B : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) ->
    RuleProofs.eo_has_bool_type A ∧ RuleProofs.eo_has_bool_type B := by
  intro hTrans
  rw [RuleProofs.eo_has_smt_translation] at hTrans
  have hNN : term_has_non_none_type (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) := by
    unfold term_has_non_none_type
    change
      __smtx_typeof (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) ≠
        SmtType.None at hTrans
    exact hTrans
  rcases bool_binop_args_bool_of_non_none
      (op := SmtTerm.imp) (t1 := __eo_to_smt A) (t2 := __eo_to_smt B)
      (typeof_imp_eq (__eo_to_smt A) (__eo_to_smt B)) hNN with ⟨hA, hB⟩
  exact ⟨by simpa [RuleProofs.eo_has_bool_type] using hA,
    by simpa [RuleProofs.eo_has_bool_type] using hB⟩

/-- A translated XOR has Boolean translated arguments. -/
theorem xor_args_have_bool_type_of_translation (A B : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) A) B) ->
    RuleProofs.eo_has_bool_type A ∧ RuleProofs.eo_has_bool_type B := by
  intro hTrans
  rw [RuleProofs.eo_has_smt_translation] at hTrans
  have hNN : term_has_non_none_type (SmtTerm.xor (__eo_to_smt A) (__eo_to_smt B)) := by
    unfold term_has_non_none_type
    change
      __smtx_typeof (SmtTerm.xor (__eo_to_smt A) (__eo_to_smt B)) ≠
        SmtType.None at hTrans
    exact hTrans
  rcases bool_binop_args_bool_of_non_none
      (op := SmtTerm.xor) (t1 := __eo_to_smt A) (t2 := __eo_to_smt B)
      (typeof_xor_eq (__eo_to_smt A) (__eo_to_smt B)) hNN with ⟨hA, hB⟩
  exact ⟨by simpa [RuleProofs.eo_has_bool_type] using hA,
    by simpa [RuleProofs.eo_has_bool_type] using hB⟩

/-- A translated equality has translated operands. -/
theorem eq_args_have_translation_of_translation (A B : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B) ->
    RuleProofs.eo_has_smt_translation A ∧ RuleProofs.eo_has_smt_translation B := by
  intro hTrans
  rw [RuleProofs.eo_has_smt_translation] at hTrans
  have hEqNN :
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt A)) (__smtx_typeof (__eo_to_smt B))
        ≠ SmtType.None := by
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B) =
        SmtTerm.eq (__eo_to_smt A) (__eo_to_smt B) by rfl] at hTrans
    rw [Smtm.typeof_eq_eq] at hTrans
    exact hTrans
  unfold __smtx_typeof_eq __smtx_typeof_guard at hEqNN
  unfold RuleProofs.eo_has_smt_translation
  constructor
  · intro hA
    exact hEqNN (by simp [hA, native_ite, native_Teq])
  · intro hB
    cases hA : __smtx_typeof (__eo_to_smt A)
    all_goals
      simp [hA, hB, native_ite, native_Teq] at hEqNN

/-- A translated Boolean `ite` has translated subterms. -/
theorem ite_args_have_translation_of_translation (C T E : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) ->
    RuleProofs.eo_has_smt_translation C ∧
      RuleProofs.eo_has_smt_translation T ∧
      RuleProofs.eo_has_smt_translation E := by
  intro hTrans
  rw [RuleProofs.eo_has_smt_translation] at hTrans
  have hIteNN :
      __smtx_typeof_ite
        (__smtx_typeof (__eo_to_smt C))
        (__smtx_typeof (__eo_to_smt T))
        (__smtx_typeof (__eo_to_smt E)) ≠ SmtType.None := by
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) =
        SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E) by rfl] at hTrans
    rw [Smtm.typeof_ite_eq] at hTrans
    exact hTrans
  unfold RuleProofs.eo_has_smt_translation
  cases hC : __smtx_typeof (__eo_to_smt C) <;>
    cases hT : __smtx_typeof (__eo_to_smt T) <;>
    cases hE : __smtx_typeof (__eo_to_smt E) <;>
    simp [__smtx_typeof_ite, hC, hT, hE, native_ite, native_Teq] at hIteNN ⊢
  all_goals assumption

/-- A translated EO `ite` has a Boolean condition. -/
theorem ite_cond_has_bool_type_of_translation (C T E : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) ->
    RuleProofs.eo_has_bool_type C := by
  intro hTrans
  rw [RuleProofs.eo_has_smt_translation] at hTrans
  have hIteNN :
      __smtx_typeof_ite
        (__smtx_typeof (__eo_to_smt C))
        (__smtx_typeof (__eo_to_smt T))
        (__smtx_typeof (__eo_to_smt E)) ≠ SmtType.None := by
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) =
        SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E) by rfl] at hTrans
    rw [Smtm.typeof_ite_eq] at hTrans
    exact hTrans
  unfold RuleProofs.eo_has_bool_type
  cases hC : __smtx_typeof (__eo_to_smt C) <;>
    cases hT : __smtx_typeof (__eo_to_smt T) <;>
    cases hE : __smtx_typeof (__eo_to_smt E) <;>
    simp [__smtx_typeof_ite, hC, hT, hE, native_ite, native_Teq] at hIteNN ⊢

/-- A translated EO `ite` has equal SMT types for its branches. -/
theorem ite_branches_same_smt_type_of_translation (C T E : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) ->
    __smtx_typeof (__eo_to_smt T) = __smtx_typeof (__eo_to_smt E) := by
  intro hTrans
  rw [RuleProofs.eo_has_smt_translation] at hTrans
  have hIteNN :
      __smtx_typeof_ite
        (__smtx_typeof (__eo_to_smt C))
        (__smtx_typeof (__eo_to_smt T))
        (__smtx_typeof (__eo_to_smt E)) ≠ SmtType.None := by
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) =
        SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E) by rfl] at hTrans
    rw [Smtm.typeof_ite_eq] at hTrans
    exact hTrans
  cases hC : __smtx_typeof (__eo_to_smt C) <;>
    cases hT : __smtx_typeof (__eo_to_smt T) <;>
    cases hE : __smtx_typeof (__eo_to_smt E) <;>
    simp [__smtx_typeof_ite, hC, hT, hE, native_ite, native_Teq] at hIteNN ⊢
  all_goals assumption

/-- In a translated `ite`, a Boolean then-branch makes the else-branch Boolean. -/
theorem ite_else_has_bool_type_of_then_bool (C T E : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) ->
    RuleProofs.eo_has_bool_type T ->
    RuleProofs.eo_has_bool_type E := by
  intro hTrans hTBool
  have hSame := ite_branches_same_smt_type_of_translation C T E hTrans
  unfold RuleProofs.eo_has_bool_type at hTBool ⊢
  simpa [← hSame] using hTBool

/-- In a translated `ite`, a Boolean else-branch makes the then-branch Boolean. -/
theorem ite_then_has_bool_type_of_else_bool (C T E : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) ->
    RuleProofs.eo_has_bool_type E ->
    RuleProofs.eo_has_bool_type T := by
  intro hTrans hEBool
  have hSame := ite_branches_same_smt_type_of_translation C T E hTrans
  unfold RuleProofs.eo_has_bool_type at hEBool ⊢
  simpa [hSame] using hEBool

/-- Builds translated Boolean type for EO implication from Boolean arguments. -/
theorem eo_has_bool_type_imp_of_bool_args (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) := by
  intro hA hB
  unfold RuleProofs.eo_has_bool_type at hA hB ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) =
      SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B) by rfl]
  rw [typeof_imp_eq]
  simp [hA, hB, native_ite, native_Teq]

/-- Builds translated Boolean type for EO XOR from Boolean arguments. -/
theorem eo_has_bool_type_xor_of_bool_args (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) A) B) := by
  intro hA hB
  unfold RuleProofs.eo_has_bool_type at hA hB ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.xor) A) B) =
      SmtTerm.xor (__eo_to_smt A) (__eo_to_smt B) by rfl]
  rw [typeof_xor_eq]
  simp [hA, hB, native_ite, native_Teq]

/-- Builds translated Boolean type for Boolean EO equality from Boolean arguments. -/
theorem eo_has_bool_type_eq_of_bool_args (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B) := by
  intro hA hB
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type A B
    (by simpa [RuleProofs.eo_has_bool_type] using hA.trans hB.symm)
    (by
      rw [RuleProofs.eo_has_bool_type] at hA
      rw [hA]
      simp)

/-- Builds translated Boolean type for Boolean EO `ite` from Boolean arguments. -/
theorem eo_has_bool_type_ite_of_bool_args (C T E : Term) :
    RuleProofs.eo_has_bool_type C ->
    RuleProofs.eo_has_bool_type T ->
    RuleProofs.eo_has_bool_type E ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) := by
  intro hC hT hE
  unfold RuleProofs.eo_has_bool_type at hC hT hE ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) =
      SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E) by rfl]
  rw [typeof_ite_eq]
  simp [__smtx_typeof_ite, hC, hT, hE, native_ite, native_Teq]

/-- If a Boolean term is true, its negation is false. -/
theorem eo_interprets_not_false_of_true (M : SmtModel) (t : Term) :
    eo_interprets M t true ->
    eo_interprets M (Term.Apply (Term.UOp UserOp.not) t) false := by
  intro hTrue
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hTrue ⊢
  rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.not) t) =
      SmtTerm.not (__eo_to_smt t) by rfl]
  cases hTrue with
  | intro_true hTy hEval =>
      refine smt_interprets.intro_false M (SmtTerm.not (__eo_to_smt t)) ?_ ?_
      · rw [typeof_not_eq]
        simp [hTy, native_Teq, native_ite]
      · rw [__smtx_model_eval.eq_7, hEval]
        simp [__smtx_model_eval_not, SmtEval.native_not]

/-- A false antecedent makes an implication true. -/
theorem eo_interprets_imp_true_of_left_false
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    eo_interprets M A false ->
    RuleProofs.eo_has_bool_type B ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) true := by
  intro hAFalse hBBool
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hAFalse ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) =
      SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B) by rfl]
  cases hAFalse with
  | intro_false hATy hAEval =>
      rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM B hBBool with ⟨b, hBEval⟩
      refine smt_interprets.intro_true M (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) ?_ ?_
      · rw [typeof_imp_eq]
        simpa [hATy, hBBool, RuleProofs.eo_has_bool_type, native_Teq, native_ite]
      · rw [__smtx_model_eval.eq_10, hAEval, hBEval]
        cases b <;> simp [__smtx_model_eval_imp, __smtx_model_eval_or,
          __smtx_model_eval_not, SmtEval.native_or, SmtEval.native_not]

/-- A true consequent makes an implication true. -/
theorem eo_interprets_imp_true_of_right_true
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    eo_interprets M B true ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) true := by
  intro hABool hBTrue
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hBTrue ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) =
      SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B) by rfl]
  cases hBTrue with
  | intro_true hBTy hBEval =>
      rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM A hABool with ⟨a, hAEval⟩
      refine smt_interprets.intro_true M (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) ?_ ?_
      · rw [typeof_imp_eq]
        simpa [hABool, hBTy, RuleProofs.eo_has_bool_type, native_Teq, native_ite]
      · rw [__smtx_model_eval.eq_10, hAEval, hBEval]
        cases a <;> simp [__smtx_model_eval_imp, __smtx_model_eval_or,
          __smtx_model_eval_not, SmtEval.native_or, SmtEval.native_not]

/-- Boolean equality is true when both sides are true. -/
theorem eo_interprets_eq_true_of_true_true (M : SmtModel) (A B : Term) :
    eo_interprets M A true ->
    eo_interprets M B true ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B) true := by
  intro hATrue hBTrue
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hATrue hBTrue ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B) =
      SmtTerm.eq (__eo_to_smt A) (__eo_to_smt B) by rfl]
  cases hATrue with
  | intro_true hATy hAEval =>
      cases hBTrue with
      | intro_true hBTy hBEval =>
          refine smt_interprets.intro_true M (SmtTerm.eq (__eo_to_smt A) (__eo_to_smt B)) ?_ ?_
          · rw [typeof_eq_eq]
            exact (RuleProofs.smtx_typeof_eq_bool_iff _ _).mpr
              ⟨by rw [hATy, hBTy], by rw [hATy]; simp⟩
          · rw [smtx_eval_eq_term_eq, hAEval, hBEval]
            simp [__smtx_model_eval_eq, native_veq]

/-- Boolean equality is true when both sides are false. -/
theorem eo_interprets_eq_true_of_false_false (M : SmtModel) (A B : Term) :
    eo_interprets M A false ->
    eo_interprets M B false ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B) true := by
  intro hAFalse hBFalse
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hAFalse hBFalse ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B) =
      SmtTerm.eq (__eo_to_smt A) (__eo_to_smt B) by rfl]
  cases hAFalse with
  | intro_false hATy hAEval =>
      cases hBFalse with
      | intro_false hBTy hBEval =>
          refine smt_interprets.intro_true M (SmtTerm.eq (__eo_to_smt A) (__eo_to_smt B)) ?_ ?_
          · rw [typeof_eq_eq]
            exact (RuleProofs.smtx_typeof_eq_bool_iff _ _).mpr
              ⟨by rw [hATy, hBTy], by rw [hATy]; simp⟩
          · rw [smtx_eval_eq_term_eq, hAEval, hBEval]
            simp [__smtx_model_eval_eq, native_veq]

/-- Boolean equality is false for true/false operands. -/
theorem eo_interprets_eq_false_of_true_false (M : SmtModel) (A B : Term) :
    eo_interprets M A true ->
    eo_interprets M B false ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B) false := by
  intro hATrue hBFalse
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hATrue hBFalse ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B) =
      SmtTerm.eq (__eo_to_smt A) (__eo_to_smt B) by rfl]
  cases hATrue with
  | intro_true hATy hAEval =>
      cases hBFalse with
      | intro_false hBTy hBEval =>
          refine smt_interprets.intro_false M (SmtTerm.eq (__eo_to_smt A) (__eo_to_smt B)) ?_ ?_
          · rw [typeof_eq_eq]
            exact (RuleProofs.smtx_typeof_eq_bool_iff _ _).mpr
              ⟨by rw [hATy, hBTy], by rw [hATy]; simp⟩
          · rw [smtx_eval_eq_term_eq, hAEval, hBEval]
            simp [__smtx_model_eval_eq, native_veq]

/-- Boolean equality is false for false/true operands. -/
theorem eo_interprets_eq_false_of_false_true (M : SmtModel) (A B : Term) :
    eo_interprets M A false ->
    eo_interprets M B true ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B) false := by
  intro hAFalse hBTrue
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hAFalse hBTrue ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B) =
      SmtTerm.eq (__eo_to_smt A) (__eo_to_smt B) by rfl]
  cases hAFalse with
  | intro_false hATy hAEval =>
      cases hBTrue with
      | intro_true hBTy hBEval =>
          refine smt_interprets.intro_false M (SmtTerm.eq (__eo_to_smt A) (__eo_to_smt B)) ?_ ?_
          · rw [typeof_eq_eq]
            exact (RuleProofs.smtx_typeof_eq_bool_iff _ _).mpr
              ⟨by rw [hATy, hBTy], by rw [hATy]; simp⟩
          · rw [smtx_eval_eq_term_eq, hAEval, hBEval]
            simp [__smtx_model_eval_eq, native_veq]

/-- Boolean XOR is true for true/false operands. -/
theorem eo_interprets_xor_true_of_true_false (M : SmtModel) (A B : Term) :
    eo_interprets M A true ->
    eo_interprets M B false ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.xor) A) B) true := by
  intro hATrue hBFalse
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hATrue hBFalse ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.xor) A) B) =
      SmtTerm.xor (__eo_to_smt A) (__eo_to_smt B) by rfl]
  cases hATrue with
  | intro_true hATy hAEval =>
      cases hBFalse with
      | intro_false hBTy hBEval =>
          refine smt_interprets.intro_true M (SmtTerm.xor (__eo_to_smt A) (__eo_to_smt B)) ?_ ?_
          · rw [typeof_xor_eq]
            simp [hATy, hBTy, native_Teq, native_ite]
          · rw [__smtx_model_eval.eq_11, hAEval, hBEval]
            simp [__smtx_model_eval_xor, __smtx_model_eval_not, __smtx_model_eval_eq,
              native_veq, SmtEval.native_not]

/-- Boolean XOR is true for false/true operands. -/
theorem eo_interprets_xor_true_of_false_true (M : SmtModel) (A B : Term) :
    eo_interprets M A false ->
    eo_interprets M B true ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.xor) A) B) true := by
  intro hAFalse hBTrue
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hAFalse hBTrue ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.xor) A) B) =
      SmtTerm.xor (__eo_to_smt A) (__eo_to_smt B) by rfl]
  cases hAFalse with
  | intro_false hATy hAEval =>
      cases hBTrue with
      | intro_true hBTy hBEval =>
          refine smt_interprets.intro_true M (SmtTerm.xor (__eo_to_smt A) (__eo_to_smt B)) ?_ ?_
          · rw [typeof_xor_eq]
            simp [hATy, hBTy, native_Teq, native_ite]
          · rw [__smtx_model_eval.eq_11, hAEval, hBEval]
            simp [__smtx_model_eval_xor, __smtx_model_eval_not, __smtx_model_eval_eq,
              native_veq, SmtEval.native_not]

/-- Boolean XOR is false when both operands are true. -/
theorem eo_interprets_xor_false_of_true_true (M : SmtModel) (A B : Term) :
    eo_interprets M A true ->
    eo_interprets M B true ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.xor) A) B) false := by
  intro hATrue hBTrue
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hATrue hBTrue ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.xor) A) B) =
      SmtTerm.xor (__eo_to_smt A) (__eo_to_smt B) by rfl]
  cases hATrue with
  | intro_true hATy hAEval =>
      cases hBTrue with
      | intro_true hBTy hBEval =>
          refine smt_interprets.intro_false M (SmtTerm.xor (__eo_to_smt A) (__eo_to_smt B)) ?_ ?_
          · rw [typeof_xor_eq]
            simp [hATy, hBTy, native_Teq, native_ite]
          · rw [__smtx_model_eval.eq_11, hAEval, hBEval]
            simp [__smtx_model_eval_xor, __smtx_model_eval_not, __smtx_model_eval_eq,
              native_veq, SmtEval.native_not]

/-- Boolean XOR is false when both operands are false. -/
theorem eo_interprets_xor_false_of_false_false (M : SmtModel) (A B : Term) :
    eo_interprets M A false ->
    eo_interprets M B false ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.xor) A) B) false := by
  intro hAFalse hBFalse
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hAFalse hBFalse ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.xor) A) B) =
      SmtTerm.xor (__eo_to_smt A) (__eo_to_smt B) by rfl]
  cases hAFalse with
  | intro_false hATy hAEval =>
      cases hBFalse with
      | intro_false hBTy hBEval =>
          refine smt_interprets.intro_false M (SmtTerm.xor (__eo_to_smt A) (__eo_to_smt B)) ?_ ?_
          · rw [typeof_xor_eq]
            simp [hATy, hBTy, native_Teq, native_ite]
          · rw [__smtx_model_eval.eq_11, hAEval, hBEval]
            simp [__smtx_model_eval_xor, __smtx_model_eval_not, __smtx_model_eval_eq,
              native_veq, SmtEval.native_not]

/-- A true condition and true then-branch make a Boolean `ite` true. -/
theorem eo_interprets_ite_true_of_cond_true
    (M : SmtModel) (C T E : Term) :
    eo_interprets M C true ->
    eo_interprets M T true ->
    RuleProofs.eo_has_bool_type E ->
    eo_interprets M (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) true := by
  intro hCTrue hTTrue hEBool
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hCTrue hTTrue ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) =
      SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E) by rfl]
  have hETyFromBool : __smtx_typeof (__eo_to_smt E) = SmtType.Bool := by
    simpa [RuleProofs.eo_has_bool_type] using hEBool
  cases hCTrue with
  | intro_true hCTy hCEval =>
      cases hTTrue with
      | intro_true hTTy hTEval =>
          refine smt_interprets.intro_true M
            (SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E)) ?_ ?_
          · rw [typeof_ite_eq]
            simp [__smtx_typeof_ite, hCTy, hTTy, hETyFromBool,
              native_Teq, native_ite]
          · rw [smtx_eval_ite_term_eq, hCEval, hTEval]
            simp [__smtx_model_eval_ite]

/-- A false condition and true else-branch make a Boolean `ite` true. -/
theorem eo_interprets_ite_true_of_cond_false
    (M : SmtModel) (C T E : Term) :
    eo_interprets M C false ->
    RuleProofs.eo_has_bool_type T ->
    eo_interprets M E true ->
    eo_interprets M (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) true := by
  intro hCFalse hTBool hETrue
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hCFalse hETrue ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) =
      SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E) by rfl]
  have hTTyFromBool : __smtx_typeof (__eo_to_smt T) = SmtType.Bool := by
    simpa [RuleProofs.eo_has_bool_type] using hTBool
  cases hCFalse with
  | intro_false hCTy hCEval =>
      cases hETrue with
      | intro_true hETy hEEval =>
          refine smt_interprets.intro_true M
            (SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E)) ?_ ?_
          · rw [typeof_ite_eq]
            simp [__smtx_typeof_ite, hCTy, hTTyFromBool, hETy,
              native_Teq, native_ite]
          · rw [smtx_eval_ite_term_eq, hCEval, hEEval]
            simp [__smtx_model_eval_ite]

/-- A true condition and false then-branch make a Boolean `ite` false. -/
theorem eo_interprets_ite_false_of_cond_true
    (M : SmtModel) (C T E : Term) :
    eo_interprets M C true ->
    eo_interprets M T false ->
    RuleProofs.eo_has_bool_type E ->
    eo_interprets M (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) false := by
  intro hCTrue hTFalse hEBool
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hCTrue hTFalse ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) =
      SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E) by rfl]
  have hETyFromBool : __smtx_typeof (__eo_to_smt E) = SmtType.Bool := by
    simpa [RuleProofs.eo_has_bool_type] using hEBool
  cases hCTrue with
  | intro_true hCTy hCEval =>
      cases hTFalse with
      | intro_false hTTy hTEval =>
          refine smt_interprets.intro_false M
            (SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E)) ?_ ?_
          · rw [typeof_ite_eq]
            simp [__smtx_typeof_ite, hCTy, hTTy, hETyFromBool,
              native_Teq, native_ite]
          · rw [smtx_eval_ite_term_eq, hCEval, hTEval]
            simp [__smtx_model_eval_ite]

/-- A false condition and false else-branch make a Boolean `ite` false. -/
theorem eo_interprets_ite_false_of_cond_false
    (M : SmtModel) (C T E : Term) :
    eo_interprets M C false ->
    RuleProofs.eo_has_bool_type T ->
    eo_interprets M E false ->
    eo_interprets M (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) false := by
  intro hCFalse hTBool hEFalse
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hCFalse hEFalse ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) =
      SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E) by rfl]
  have hTTyFromBool : __smtx_typeof (__eo_to_smt T) = SmtType.Bool := by
    simpa [RuleProofs.eo_has_bool_type] using hTBool
  cases hCFalse with
  | intro_false hCTy hCEval =>
      cases hEFalse with
      | intro_false hETy hEEval =>
          refine smt_interprets.intro_false M
            (SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E)) ?_ ?_
          · rw [typeof_ite_eq]
            simp [__smtx_typeof_ite, hCTy, hTTyFromBool, hETy,
              native_Teq, native_ite]
          · rw [smtx_eval_ite_term_eq, hCEval, hEEval]
            simp [__smtx_model_eval_ite]

/-- A right-associated two-literal clause is true when its first literal is true. -/
theorem clause2_left_true
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    eo_interprets M A true ->
    RuleProofs.eo_has_bool_type B ->
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) A)
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) B) (Term.Boolean false))) true := by
  intro hATrue hBBool
  have hInnerBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) B) (Term.Boolean false)) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args B (Term.Boolean false)
      hBBool RuleProofs.eo_has_bool_type_false
  exact RuleProofs.eo_interprets_or_left_intro M hM A
    (Term.Apply (Term.Apply (Term.UOp UserOp.or) B) (Term.Boolean false))
    hATrue hInnerBool

/-- A right-associated two-literal clause is true when its second literal is true. -/
theorem clause2_right_true
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    eo_interprets M B true ->
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) A)
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) B) (Term.Boolean false))) true := by
  intro hABool hBTrue
  have hInnerTrue : eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) B) (Term.Boolean false)) true :=
    RuleProofs.eo_interprets_or_left_intro M hM B (Term.Boolean false)
      hBTrue RuleProofs.eo_has_bool_type_false
  exact RuleProofs.eo_interprets_or_right_intro M hM A
    (Term.Apply (Term.Apply (Term.UOp UserOp.or) B) (Term.Boolean false))
    hABool hInnerTrue

/-- A right-associated three-literal clause is true when its first literal is true. -/
theorem clause3_left_true
    (M : SmtModel) (hM : model_wf M) (A B C : Term) :
    eo_interprets M A true ->
    RuleProofs.eo_has_bool_type B ->
    RuleProofs.eo_has_bool_type C ->
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) A)
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) B)
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) C) (Term.Boolean false)))) true := by
  intro hATrue hBBool hCBool
  have hTailBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) C) (Term.Boolean false)) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args C (Term.Boolean false)
      hCBool RuleProofs.eo_has_bool_type_false
  have hInnerBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) B)
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) C) (Term.Boolean false))) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args B
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) C) (Term.Boolean false))
      hBBool hTailBool
  exact RuleProofs.eo_interprets_or_left_intro M hM A
    (Term.Apply (Term.Apply (Term.UOp UserOp.or) B)
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) C) (Term.Boolean false)))
    hATrue hInnerBool

/-- A right-associated three-literal clause is true when its second literal is true. -/
theorem clause3_middle_true
    (M : SmtModel) (hM : model_wf M) (A B C : Term) :
    RuleProofs.eo_has_bool_type A ->
    eo_interprets M B true ->
    RuleProofs.eo_has_bool_type C ->
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) A)
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) B)
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) C) (Term.Boolean false)))) true := by
  intro hABool hBTrue hCBool
  have hInnerTrue : eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) B)
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) C) (Term.Boolean false))) true :=
    clause2_left_true M hM B C hBTrue hCBool
  exact RuleProofs.eo_interprets_or_right_intro M hM A
    (Term.Apply (Term.Apply (Term.UOp UserOp.or) B)
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) C) (Term.Boolean false)))
    hABool hInnerTrue

/-- A right-associated three-literal clause is true when its third literal is true. -/
theorem clause3_right_true
    (M : SmtModel) (hM : model_wf M) (A B C : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    eo_interprets M C true ->
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) A)
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) B)
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) C) (Term.Boolean false)))) true := by
  intro hABool hBBool hCTrue
  have hInnerTrue : eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) B)
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) C) (Term.Boolean false))) true :=
    clause2_right_true M hM B C hBBool hCTrue
  exact RuleProofs.eo_interprets_or_right_intro M hM A
    (Term.Apply (Term.Apply (Term.UOp UserOp.or) B)
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) C) (Term.Boolean false)))
    hABool hInnerTrue

private theorem is_ok_true_of_ne_stuck {x : Term} :
    x ≠ Term.Stuck ->
    __eo_is_ok x = Term.Boolean true := by
  intro hNe
  cases x <;> simp [__eo_is_ok, native_teq, native_not, SmtEval.native_not] at hNe ⊢

private theorem is_list_true_of_get_nil_rec_ne_stuck {f x : Term} :
    __eo_get_nil_rec f x ≠ Term.Stuck ->
    __eo_is_list f x = Term.Boolean true := by
  intro hRec
  have hF : f ≠ Term.Stuck := by
    intro hF
    subst hF
    simpa [__eo_get_nil_rec] using hRec
  have hX : x ≠ Term.Stuck := by
    intro hX
    subst hX
    simpa [__eo_get_nil_rec] using hRec
  simp [__eo_is_list, is_ok_true_of_ne_stuck hRec]

/-- Structural characterization of EO `and`-lists. -/
inductive AndList : Term -> Prop where
  | true : AndList (Term.Boolean true)
  | cons (x xs : Term) : AndList xs ->
      AndList (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs)

/-- Structural characterization of EO `or`-lists. -/
inductive OrList : Term -> Prop where
  | false : OrList (Term.Boolean false)
  | cons (x xs : Term) : OrList xs ->
      OrList (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs)

private theorem andList_of_is_list_true {c : Term} :
    __eo_is_list (Term.UOp UserOp.and) c = Term.Boolean true ->
    AndList c := by
  intro hList
  cases c with
  | Stuck =>
      simp [__eo_is_list
        ] at hList
  | Boolean b =>
      cases b with
      | true =>
          exact AndList.true
      | false =>
          simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
            __eo_is_list_nil, native_ite, native_teq, native_not,
            SmtEval.native_not] at hList
  | Apply f a =>
      cases f with
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | and =>
                  unfold __eo_is_list at hList
                  unfold __eo_is_ok at hList
                  unfold __eo_get_nil_rec at hList
                  unfold __eo_requires at hList
                  simp [native_ite, native_teq, native_not, SmtEval.native_not] at hList
                  exact AndList.cons x a
                    (andList_of_is_list_true (is_list_true_of_get_nil_rec_ne_stuck hList))
              | _ =>
                  simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
                    native_ite, native_teq, native_not,
                    SmtEval.native_not] at hList
          | _ =>
              simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
                native_ite, native_teq, native_not,
                SmtEval.native_not] at hList
      | _ =>
          simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
            __eo_is_list_nil, native_ite, native_teq, native_not,
            SmtEval.native_not] at hList
  | _ =>
      simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
        __eo_is_list_nil, native_ite, native_teq, native_not,
        SmtEval.native_not] at hList

private theorem andList_get_nil_rec_ne_stuck {c : Term} :
    AndList c ->
    __eo_get_nil_rec (Term.UOp UserOp.and) c ≠ Term.Stuck := by
  intro hList
  induction hList with
  | true =>
      simp [__eo_get_nil_rec, __eo_requires, __eo_is_list_nil, native_ite,
        native_teq, native_not, SmtEval.native_not]
  | cons x xs hXs ih =>
      simpa [__eo_get_nil_rec, __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] using ih

/-- Every structural EO `and`-list is accepted by `__eo_is_list`. -/
theorem andList_is_list_true {c : Term} :
    AndList c ->
    __eo_is_list (Term.UOp UserOp.and) c = Term.Boolean true := by
  intro hList
  exact is_list_true_of_get_nil_rec_ne_stuck (andList_get_nil_rec_ne_stuck hList)

/-- A structural EO `and`-list is never `Stuck`. -/
theorem andList_ne_stuck {c : Term} :
    AndList c ->
    c ≠ Term.Stuck := by
  intro hList
  cases hList <;> simp

/-- If a Boolean conjunction is false, one of its sides is false. -/
theorem eo_interprets_and_false_cases
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) false ->
    eo_interprets M A false ∨ eo_interprets M B false := by
  intro hABool hBBool hAndFalse
  rcases eo_interprets_bool_cases M hM A hABool with hATrue | hAFalse
  · rcases eo_interprets_bool_cases M hM B hBBool with hBTrue | hBFalse
    · have hAndTrue : eo_interprets M
          (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) true :=
        RuleProofs.eo_interprets_and_intro M A B hATrue hBTrue
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hAndTrue) hAndFalse)
    · exact Or.inr hBFalse
  · exact Or.inl hAFalse

/-- A non-stuck `lower_not_and` result implies a structural EO `and`-list. -/
theorem andList_of_lower_not_and_ne_stuck {c : Term} :
    __lower_not_and c ≠ Term.Stuck ->
    AndList c := by
  intro hLower
  cases c with
  | Boolean b =>
      cases b with
      | true => exact AndList.true
      | false => simp [__lower_not_and] at hLower
  | Apply f xs =>
      cases f with
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | and =>
                  have hTail : __lower_not_and xs ≠ Term.Stuck := by
                    intro hTail
                    apply hLower
                    simp [__lower_not_and, hTail, __eo_mk_apply]
                  exact AndList.cons x xs (andList_of_lower_not_and_ne_stuck hTail)
              | _ =>
                  simp [__lower_not_and] at hLower
          | _ =>
              simp [__lower_not_and] at hLower
      | _ =>
          simp [__lower_not_and] at hLower
  | _ =>
      simp [__lower_not_and] at hLower

/-- Lowering a negated structural conjunction preserves Boolean translated type. -/
theorem lower_not_and_has_bool_type {c : Term} :
    AndList c ->
    RuleProofs.eo_has_bool_type c ->
    RuleProofs.eo_has_bool_type (__lower_not_and c) := by
  intro hList hCBool
  induction hList with
  | true =>
      simpa [__lower_not_and] using RuleProofs.eo_has_bool_type_false
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_and_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_and_right x xs hCBool
      have hNotXBool : RuleProofs.eo_has_bool_type (Term.Apply (Term.UOp UserOp.not) x) :=
        RuleProofs.eo_has_bool_type_not_of_bool_arg x hXBool
      have hLowerBool : RuleProofs.eo_has_bool_type (__lower_not_and xs) :=
        ih hXsBool
      have hLowerNe : __lower_not_and xs ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type (__lower_not_and xs) hLowerBool
      simpa [__lower_not_and, __eo_mk_apply, hLowerNe] using
        RuleProofs.eo_has_bool_type_or_of_bool_args
          (Term.Apply (Term.UOp UserOp.not) x) (__lower_not_and xs)
          hNotXBool hLowerBool

/-- If a structural conjunction is false, its lowered negation is true. -/
theorem lower_not_and_true_of_false
    (M : SmtModel) (hM : model_wf M) {c : Term} :
    AndList c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c false ->
    eo_interprets M (__lower_not_and c) true := by
  intro hList hCBool hCFalse
  induction hList with
  | true =>
      exact False.elim
        ((RuleProofs.eo_interprets_true_not_false M (Term.Boolean true)
          (RuleProofs.eo_interprets_true M)) hCFalse)
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_and_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_and_right x xs hCBool
      have hLowerBool : RuleProofs.eo_has_bool_type (__lower_not_and xs) :=
        lower_not_and_has_bool_type hXs hXsBool
      have hLowerNe : __lower_not_and xs ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type (__lower_not_and xs) hLowerBool
      have hAndFalse : eo_interprets M
          (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs) false := by
        simpa using hCFalse
      rcases eo_interprets_and_false_cases M hM x xs hXBool hXsBool hAndFalse with
        hXFalse | hXsFalse
      · simpa [__lower_not_and, __eo_mk_apply, hLowerNe] using
          RuleProofs.eo_interprets_or_left_intro M hM
            (Term.Apply (Term.UOp UserOp.not) x) (__lower_not_and xs)
            (RuleProofs.eo_interprets_not_of_false M x hXFalse) hLowerBool
      · have hLowerTrue : eo_interprets M (__lower_not_and xs) true :=
          ih hXsBool hXsFalse
        simpa [__lower_not_and, __eo_mk_apply, hLowerNe] using
          RuleProofs.eo_interprets_or_right_intro M hM
            (Term.Apply (Term.UOp UserOp.not) x) (__lower_not_and xs)
            (RuleProofs.eo_has_bool_type_not_of_bool_arg x hXBool) hLowerTrue

private theorem orList_of_is_list_true {c : Term} :
    __eo_is_list (Term.UOp UserOp.or) c = Term.Boolean true ->
    OrList c := by
  intro hList
  cases c with
  | Stuck =>
      simp [__eo_is_list
        ] at hList
  | Boolean b =>
      cases b with
      | false =>
          exact OrList.false
      | true =>
          simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
            __eo_is_list_nil, native_ite, native_teq, native_not,
            SmtEval.native_not] at hList
  | Apply f a =>
      cases f with
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | or =>
                  unfold __eo_is_list at hList
                  unfold __eo_is_ok at hList
                  unfold __eo_get_nil_rec at hList
                  unfold __eo_requires at hList
                  simp [native_ite, native_teq, native_not, SmtEval.native_not] at hList
                  exact OrList.cons x a
                    (orList_of_is_list_true (is_list_true_of_get_nil_rec_ne_stuck hList))
              | _ =>
                  simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
                    native_ite, native_teq, native_not,
                    SmtEval.native_not] at hList
          | _ =>
              simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
                native_ite, native_teq, native_not,
                SmtEval.native_not] at hList
      | _ =>
          simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
            __eo_is_list_nil, native_ite, native_teq, native_not,
            SmtEval.native_not] at hList
  | _ =>
      simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
        __eo_is_list_nil, native_ite, native_teq, native_not,
        SmtEval.native_not] at hList

private theorem orList_get_nil_rec_ne_stuck {c : Term} :
    OrList c ->
    __eo_get_nil_rec (Term.UOp UserOp.or) c ≠ Term.Stuck := by
  intro hList
  induction hList with
  | false =>
      simp [__eo_get_nil_rec, __eo_requires, __eo_is_list_nil, native_ite,
        native_teq, native_not, SmtEval.native_not]
  | cons x xs hXs ih =>
      simpa [__eo_get_nil_rec, __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] using ih

/-- Every structural EO `or`-list is accepted by `__eo_is_list`. -/
theorem orList_is_list_true {c : Term} :
    OrList c ->
    __eo_is_list (Term.UOp UserOp.or) c = Term.Boolean true := by
  intro hList
  exact is_list_true_of_get_nil_rec_ne_stuck (orList_get_nil_rec_ne_stuck hList)

/-- A structural EO `or`-list is never `Stuck`. -/
theorem orList_ne_stuck {c : Term} :
    OrList c ->
    c ≠ Term.Stuck := by
  intro hList
  cases hList <;> simp

private theorem list_nth_nonstuck_is_list_true {f c i : Term} :
    __eo_list_nth f c i ≠ Term.Stuck ->
    __eo_is_list f c = Term.Boolean true := by
  intro hNth
  cases hIs : __eo_is_list f c with
  | Boolean b =>
      cases b with
      | true =>
          rfl
      | false =>
          simp [__eo_list_nth, __eo_requires, hIs, native_ite, native_teq
            ] at hNth
  | _ =>
      simp [__eo_list_nth, __eo_requires, hIs, native_ite, native_teq
        ] at hNth

/-- A non-stuck `and`-list selection implies the list structure is valid. -/
theorem andList_of_list_nth_ne_stuck {c i : Term} :
    __eo_list_nth (Term.UOp UserOp.and) c i ≠ Term.Stuck ->
    AndList c := by
  intro hNth
  exact andList_of_is_list_true (list_nth_nonstuck_is_list_true hNth)

/-- A non-stuck `or`-list selection implies the list structure is valid. -/
theorem orList_of_list_nth_ne_stuck {c i : Term} :
    __eo_list_nth (Term.UOp UserOp.or) c i ≠ Term.Stuck ->
    OrList c := by
  intro hNth
  exact orList_of_is_list_true (list_nth_nonstuck_is_list_true hNth)

private theorem list_nth_rec_cons_ne_zero
    (f x xs i : Term) :
    i ≠ Term.Stuck ->
    i ≠ Term.Numeral 0 ->
    __eo_list_nth_rec (Term.Apply (Term.Apply f x) xs) i =
      __eo_list_nth_rec xs (__eo_add i (Term.Numeral (-1 : native_Int))) := by
  intro hStuck hZero
  cases i with
  | Stuck =>
      exact False.elim (hStuck rfl)
  | Numeral n =>
      by_cases hN : n = 0
      · subst hN
        exact False.elim (hZero rfl)
      · simp [__eo_list_nth_rec]
  | _ =>
      simp [__eo_list_nth_rec]

private theorem list_nth_rec_cons_tail_ne_stuck
    (f x xs i : Term) :
    i ≠ Term.Stuck ->
    i ≠ Term.Numeral 0 ->
    __eo_list_nth_rec (Term.Apply (Term.Apply f x) xs) i ≠ Term.Stuck ->
    __eo_list_nth_rec xs (__eo_add i (Term.Numeral (-1 : native_Int))) ≠ Term.Stuck := by
  intro hStuck hZero hNth
  rw [← list_nth_rec_cons_ne_zero f x xs i hStuck hZero]
  exact hNth

private theorem andList_nth_rec_has_bool_type {c i : Term} :
    AndList c ->
    RuleProofs.eo_has_bool_type c ->
    __eo_list_nth_rec c i ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_list_nth_rec c i) := by
  intro hList hCBool hNth
  induction hList generalizing i with
  | true =>
      cases i <;> simp [__eo_list_nth_rec] at hNth
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_and_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_and_right x xs hCBool
      by_cases hStuck : i = Term.Stuck
      · subst hStuck
        simp [__eo_list_nth_rec] at hNth
      · by_cases hZero : i = Term.Numeral 0
        · subst hZero
          simpa [__eo_list_nth_rec] using hXBool
        · have hTail : __eo_list_nth_rec xs (__eo_add i (Term.Numeral (-1 : native_Int))) ≠
              Term.Stuck :=
            list_nth_rec_cons_tail_ne_stuck (Term.UOp UserOp.and) x xs i hStuck hZero hNth
          rw [list_nth_rec_cons_ne_zero (Term.UOp UserOp.and) x xs i hStuck hZero]
          exact ih hXsBool hTail

/-- A non-stuck selection from a typed EO `and`-list is Boolean. -/
theorem andList_nth_has_bool_type {c i : Term} :
    AndList c ->
    RuleProofs.eo_has_bool_type c ->
    __eo_list_nth (Term.UOp UserOp.and) c i ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_list_nth (Term.UOp UserOp.and) c i) := by
  intro hList hCBool hNth
  simp [__eo_list_nth, __eo_requires, andList_is_list_true hList, native_ite,
    native_teq, native_not, SmtEval.native_not] at hNth ⊢
  exact andList_nth_rec_has_bool_type hList hCBool hNth

private theorem andList_nth_rec_true_of_true
    (M : SmtModel) {c i : Term} :
    AndList c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c true ->
    __eo_list_nth_rec c i ≠ Term.Stuck ->
    eo_interprets M (__eo_list_nth_rec c i) true := by
  intro hList hCBool hCTrue hNth
  induction hList generalizing i with
  | true =>
      cases i <;> simp [__eo_list_nth_rec] at hNth
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_and_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_and_right x xs hCBool
      have hAndTrue : eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs) true := by
        simpa using hCTrue
      by_cases hStuck : i = Term.Stuck
      · subst hStuck
        simp [__eo_list_nth_rec] at hNth
      · by_cases hZero : i = Term.Numeral 0
        · subst hZero
          simpa [__eo_list_nth_rec] using RuleProofs.eo_interprets_and_left M x xs hAndTrue
        · have hTail : __eo_list_nth_rec xs (__eo_add i (Term.Numeral (-1 : native_Int))) ≠
              Term.Stuck :=
            list_nth_rec_cons_tail_ne_stuck (Term.UOp UserOp.and) x xs i hStuck hZero hNth
          have hXsTrue : eo_interprets M xs true :=
            RuleProofs.eo_interprets_and_right M x xs hAndTrue
          rw [list_nth_rec_cons_ne_zero (Term.UOp UserOp.and) x xs i hStuck hZero]
          exact ih hXsBool hXsTrue hTail

/-- Selecting from a true EO `and`-list yields a true conjunct. -/
theorem andList_nth_true_of_true
    (M : SmtModel) {c i : Term} :
    AndList c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c true ->
    __eo_list_nth (Term.UOp UserOp.and) c i ≠ Term.Stuck ->
    eo_interprets M (__eo_list_nth (Term.UOp UserOp.and) c i) true := by
  intro hList hCBool hCTrue hNth
  simp [__eo_list_nth, __eo_requires, andList_is_list_true hList, native_ite,
    native_teq, native_not, SmtEval.native_not] at hNth ⊢
  exact andList_nth_rec_true_of_true M hList hCBool hCTrue hNth

private theorem orList_nth_rec_has_bool_type {c i : Term} :
    OrList c ->
    RuleProofs.eo_has_bool_type c ->
    __eo_list_nth_rec c i ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_list_nth_rec c i) := by
  intro hList hCBool hNth
  induction hList generalizing i with
  | false =>
      cases i <;> simp [__eo_list_nth_rec] at hNth
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      by_cases hStuck : i = Term.Stuck
      · subst hStuck
        simp [__eo_list_nth_rec] at hNth
      · by_cases hZero : i = Term.Numeral 0
        · subst hZero
          simpa [__eo_list_nth_rec] using hXBool
        · have hTail : __eo_list_nth_rec xs (__eo_add i (Term.Numeral (-1 : native_Int))) ≠
              Term.Stuck :=
            list_nth_rec_cons_tail_ne_stuck (Term.UOp UserOp.or) x xs i hStuck hZero hNth
          rw [list_nth_rec_cons_ne_zero (Term.UOp UserOp.or) x xs i hStuck hZero]
          exact ih hXsBool hTail

/-- A non-stuck selection from a typed EO `or`-list is Boolean. -/
theorem orList_nth_has_bool_type {c i : Term} :
    OrList c ->
    RuleProofs.eo_has_bool_type c ->
    __eo_list_nth (Term.UOp UserOp.or) c i ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_list_nth (Term.UOp UserOp.or) c i) := by
  intro hList hCBool hNth
  simp [__eo_list_nth, __eo_requires, orList_is_list_true hList, native_ite,
    native_teq, native_not, SmtEval.native_not] at hNth ⊢
  exact orList_nth_rec_has_bool_type hList hCBool hNth

private theorem orList_nth_rec_false_of_false
    (M : SmtModel) (hM : model_wf M) {c i : Term} :
    OrList c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c false ->
    __eo_list_nth_rec c i ≠ Term.Stuck ->
    eo_interprets M (__eo_list_nth_rec c i) false := by
  intro hList hCBool hCFalse hNth
  induction hList generalizing i with
  | false =>
      cases i <;> simp [__eo_list_nth_rec] at hNth
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hOrFalse :
          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs) false := by
        simpa using hCFalse
      by_cases hStuck : i = Term.Stuck
      · subst hStuck
        simp [__eo_list_nth_rec] at hNth
      · by_cases hZero : i = Term.Numeral 0
        · subst hZero
          simpa [__eo_list_nth_rec] using eo_interprets_or_false_left M hM x xs hOrFalse
        · have hTail : __eo_list_nth_rec xs (__eo_add i (Term.Numeral (-1 : native_Int))) ≠
              Term.Stuck :=
            list_nth_rec_cons_tail_ne_stuck (Term.UOp UserOp.or) x xs i hStuck hZero hNth
          have hXsFalse : eo_interprets M xs false :=
            eo_interprets_or_false_right M hM x xs hOrFalse
          rw [list_nth_rec_cons_ne_zero (Term.UOp UserOp.or) x xs i hStuck hZero]
          exact ih hXsBool hXsFalse hTail

/-- Selecting from a false EO `or`-list yields a false disjunct. -/
theorem orList_nth_false_of_false
    (M : SmtModel) (hM : model_wf M) {c i : Term} :
    OrList c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c false ->
    __eo_list_nth (Term.UOp UserOp.or) c i ≠ Term.Stuck ->
    eo_interprets M (__eo_list_nth (Term.UOp UserOp.or) c i) false := by
  intro hList hCBool hCFalse hNth
  simp [__eo_list_nth, __eo_requires, orList_is_list_true hList, native_ite,
    native_teq, native_not, SmtEval.native_not] at hNth ⊢
  exact orList_nth_rec_false_of_false M hM hList hCBool hCFalse hNth

/-- A defined `mk_apply` has a defined function position. -/
theorem mk_apply_ne_stuck_left {f a : Term} :
    __eo_mk_apply f a ≠ Term.Stuck ->
    f ≠ Term.Stuck := by
  intro h
  cases f <;> cases a <;> simp [__eo_mk_apply] at h ⊢

/-- A defined `mk_apply` has a defined argument position. -/
theorem mk_apply_ne_stuck_right {f a : Term} :
    __eo_mk_apply f a ≠ Term.Stuck ->
    a ≠ Term.Stuck := by
  intro h
  cases f <;> cases a <;> simp [__eo_mk_apply] at h ⊢

/-- A defined `mk_apply` is ordinary application. -/
theorem mk_apply_eq_apply {f a : Term} :
    f ≠ Term.Stuck ->
    a ≠ Term.Stuck ->
    __eo_mk_apply f a = Term.Apply f a := by
  intro hF hA
  cases f <;> cases a <;> simp [__eo_mk_apply] at hF hA ⊢

/-- If a generated Boolean equality over a Boolean constant is well typed, its left side is Boolean. -/
theorem typeof_mk_eq_bool_left_const_bool {t : Term} {b : Bool} :
    t ≠ Term.Stuck ->
    __eo_typeof
        (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) t)
          (Term.Boolean b)) = Term.Bool ->
    __eo_typeof t = Term.Bool := by
  intro hT hTy
  rw [mk_apply_eq_apply (by simp) hT] at hTy
  rw [mk_apply_eq_apply (by simp) (by simp)] at hTy
  change __eo_typeof_eq (__eo_typeof t) Term.Bool = Term.Bool at hTy
  cases h : __eo_typeof t <;>
    simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
      native_not, h] at hTy ⊢

/-- A well-typed generated `and` application has a Boolean left argument. -/
theorem typeof_mk_apply_and_left_bool {x y : Term} :
    __eo_typeof (__eo_mk_apply (Term.Apply (Term.UOp UserOp.and) x) y) =
      Term.Bool ->
    __eo_typeof x = Term.Bool := by
  intro hTy
  by_cases hY : y = Term.Stuck
  · subst y
    have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hBad hTy)
  · rw [mk_apply_eq_apply (by simp) hY] at hTy
    change __eo_typeof_or (__eo_typeof x) (__eo_typeof y) = Term.Bool at hTy
    exact typeof_or_eq_bool_left hTy

/-- A well-typed generated `and` application has a Boolean right argument. -/
theorem typeof_mk_apply_and_right_bool {x y : Term} :
    __eo_typeof (__eo_mk_apply (Term.Apply (Term.UOp UserOp.and) x) y) =
      Term.Bool ->
    __eo_typeof y = Term.Bool := by
  intro hTy
  by_cases hY : y = Term.Stuck
  · subst y
    have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hBad hTy)
  · rw [mk_apply_eq_apply (by simp) hY] at hTy
    change __eo_typeof_or (__eo_typeof x) (__eo_typeof y) = Term.Bool at hTy
    exact typeof_or_eq_bool_right hTy

/-- A well-typed generated `or` application has a Boolean left argument. -/
theorem typeof_mk_apply_or_left_bool {x y : Term} :
    __eo_typeof (__eo_mk_apply (Term.Apply (Term.UOp UserOp.or) x) y) =
      Term.Bool ->
    __eo_typeof x = Term.Bool := by
  intro hTy
  by_cases hY : y = Term.Stuck
  · subst y
    have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hBad hTy)
  · rw [mk_apply_eq_apply (by simp) hY] at hTy
    change __eo_typeof_or (__eo_typeof x) (__eo_typeof y) = Term.Bool at hTy
    exact typeof_or_eq_bool_left hTy

/-- A well-typed generated `or` application has a Boolean right argument. -/
theorem typeof_mk_apply_or_right_bool {x y : Term} :
    __eo_typeof (__eo_mk_apply (Term.Apply (Term.UOp UserOp.or) x) y) =
      Term.Bool ->
    __eo_typeof y = Term.Bool := by
  intro hTy
  by_cases hY : y = Term.Stuck
  · subst y
    have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hBad hTy)
  · rw [mk_apply_eq_apply (by simp) hY] at hTy
    change __eo_typeof_or (__eo_typeof x) (__eo_typeof y) = Term.Bool at hTy
    exact typeof_or_eq_bool_right hTy

/-- A translated EO `and` application is Boolean. -/
theorem eo_has_bool_type_and_of_translation (A B : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) := by
  intro hTrans
  rw [RuleProofs.eo_has_smt_translation] at hTrans
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) =
    SmtType.Bool
  change __smtx_typeof (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) ≠
    SmtType.None at hTrans
  rw [typeof_and_eq] at hTrans ⊢
  cases hA : __smtx_typeof (__eo_to_smt A) <;>
    cases hB : __smtx_typeof (__eo_to_smt B) <;>
    simp [hA, hB, native_ite, native_Teq] at hTrans ⊢

/-- A translated EO `or` application is Boolean. -/
theorem eo_has_bool_type_or_of_translation (A B : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) := by
  intro hTrans
  rw [RuleProofs.eo_has_smt_translation] at hTrans
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) =
    SmtType.Bool
  change __smtx_typeof (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) ≠
    SmtType.None at hTrans
  rw [typeof_or_eq] at hTrans ⊢
  cases hA : __smtx_typeof (__eo_to_smt A) <;>
    cases hB : __smtx_typeof (__eo_to_smt B) <;>
    simp [hA, hB, native_ite, native_Teq] at hTrans ⊢

/-- A translated structural EO `and`-list is Boolean. -/
theorem andList_has_bool_type_of_translation {c : Term} :
    AndList c ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_bool_type c := by
  intro hList hTrans
  cases hList with
  | true =>
      exact RuleProofs.eo_has_bool_type_true
  | cons x xs hXs =>
      exact eo_has_bool_type_and_of_translation x xs hTrans

/-- A translated structural EO `or`-list is Boolean. -/
theorem orList_has_bool_type_of_translation {c : Term} :
    OrList c ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_bool_type c := by
  intro hList hTrans
  cases hList with
  | false =>
      exact RuleProofs.eo_has_bool_type_false
  | cons x xs hXs =>
      exact eo_has_bool_type_or_of_translation x xs hTrans

private theorem is_list_true_of_list_concat_ne_stuck_left {f a b : Term} :
    __eo_list_concat f a b ≠ Term.Stuck ->
    __eo_is_list f a = Term.Boolean true := by
  intro hConcat
  cases hA : __eo_is_list f a <;>
    simp [__eo_list_concat, __eo_requires, hA, native_ite, native_teq,
      native_not, SmtEval.native_not] at hConcat ⊢
  case Boolean b =>
    cases b <;>
      simp [__eo_list_concat, __eo_requires, hA, native_ite, native_teq,
        native_not, SmtEval.native_not] at hConcat ⊢

private theorem is_list_true_of_list_concat_ne_stuck_right {f a b : Term} :
    __eo_list_concat f a b ≠ Term.Stuck ->
    __eo_is_list f b = Term.Boolean true := by
  intro hConcat
  have hA := is_list_true_of_list_concat_ne_stuck_left hConcat
  cases hB : __eo_is_list f b <;>
    simp [__eo_list_concat, __eo_requires, hA, hB, native_ite, native_teq,
      native_not, SmtEval.native_not] at hConcat ⊢
  case Boolean b =>
    cases b <;>
      simp [__eo_list_concat, __eo_requires, hA, hB, native_ite, native_teq,
        native_not, SmtEval.native_not] at hConcat ⊢

/-- A non-stuck `and`-list concatenation has a structural left list. -/
theorem andList_of_concat_ne_stuck_left {a b : Term} :
    __eo_list_concat (Term.UOp UserOp.and) a b ≠ Term.Stuck ->
    AndList a := by
  intro hConcat
  exact andList_of_is_list_true (is_list_true_of_list_concat_ne_stuck_left hConcat)

/-- A non-stuck `and`-list concatenation has a structural right list. -/
theorem andList_of_concat_ne_stuck_right {a b : Term} :
    __eo_list_concat (Term.UOp UserOp.and) a b ≠ Term.Stuck ->
    AndList b := by
  intro hConcat
  exact andList_of_is_list_true (is_list_true_of_list_concat_ne_stuck_right hConcat)

/-- A non-stuck `or`-list concatenation has a structural left list. -/
theorem orList_of_concat_ne_stuck_left {a b : Term} :
    __eo_list_concat (Term.UOp UserOp.or) a b ≠ Term.Stuck ->
    OrList a := by
  intro hConcat
  exact orList_of_is_list_true (is_list_true_of_list_concat_ne_stuck_left hConcat)

/-- A non-stuck `or`-list concatenation has a structural right list. -/
theorem orList_of_concat_ne_stuck_right {a b : Term} :
    __eo_list_concat (Term.UOp UserOp.or) a b ≠ Term.Stuck ->
    OrList b := by
  intro hConcat
  exact orList_of_is_list_true (is_list_true_of_list_concat_ne_stuck_right hConcat)

/-- The tail of a generated structural `and` cons is a structural `and`-list. -/
theorem andList_tail_of_mk_apply_and {x xs : Term} :
    AndList (__eo_mk_apply (Term.Apply (Term.UOp UserOp.and) x) xs) ->
    AndList xs := by
  intro hList
  by_cases hXs : xs = Term.Stuck
  · subst xs
    simpa [__eo_mk_apply] using hList
  · rw [mk_apply_eq_apply (by simp) hXs] at hList
    cases hList
    assumption

/-- The tail of a structural `and` cons is a structural `and`-list. -/
theorem andList_tail_of_apply_and {x xs : Term} :
    AndList (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs) ->
    AndList xs := by
  intro hList
  cases hList
  assumption

/-- The tail of a generated structural `or` cons is a structural `or`-list. -/
theorem orList_tail_of_mk_apply_or {x xs : Term} :
    OrList (__eo_mk_apply (Term.Apply (Term.UOp UserOp.or) x) xs) ->
    OrList xs := by
  intro hList
  by_cases hXs : xs = Term.Stuck
  · subst xs
    simpa [__eo_mk_apply] using hList
  · rw [mk_apply_eq_apply (by simp) hXs] at hList
    cases hList
    assumption

/-- The tail of a structural `or` cons is a structural `or`-list. -/
theorem orList_tail_of_apply_or {x xs : Term} :
    OrList (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs) ->
    OrList xs := by
  intro hList
  cases hList
  assumption

private theorem andList_concat_rec_cons (x xs z : Term) :
    __eo_list_concat_rec xs z ≠ Term.Stuck ->
    __eo_list_concat_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs) z =
      Term.Apply (Term.Apply (Term.UOp UserOp.and) x)
        (__eo_list_concat_rec xs z) := by
  intro hTail
  cases z with
  | Stuck =>
      have hStuck : __eo_list_concat_rec xs Term.Stuck = Term.Stuck := by
        cases xs <;> simp [__eo_list_concat_rec]
      exact False.elim (hTail hStuck)
  | _ =>
      simp [__eo_list_concat_rec, __eo_mk_apply]

private theorem orList_concat_rec_cons (x xs z : Term) :
    __eo_list_concat_rec xs z ≠ Term.Stuck ->
    __eo_list_concat_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs) z =
      Term.Apply (Term.Apply (Term.UOp UserOp.or) x)
        (__eo_list_concat_rec xs z) := by
  intro hTail
  cases z with
  | Stuck =>
      have hStuck : __eo_list_concat_rec xs Term.Stuck = Term.Stuck := by
        cases xs <;> simp [__eo_list_concat_rec]
      exact False.elim (hTail hStuck)
  | _ =>
      simp [__eo_list_concat_rec, __eo_mk_apply]

private theorem andList_concat_rec_preserves_list {c1 c2 : Term} :
    AndList c1 ->
    AndList c2 ->
    AndList (__eo_list_concat_rec c1 c2) := by
  intro hC1 hC2
  have hConcatTrue (z : Term) :
      __eo_list_concat_rec (Term.Boolean true) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  induction hC1 generalizing c2 with
  | true =>
      rw [hConcatTrue c2]
      exact hC2
  | cons x xs hXs ih =>
      have hTail : AndList (__eo_list_concat_rec xs c2) := ih hC2
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        andList_ne_stuck hTail
      rw [andList_concat_rec_cons x xs c2 hTailNe]
      exact AndList.cons x (__eo_list_concat_rec xs c2) hTail

private theorem orList_concat_rec_preserves_list {c1 c2 : Term} :
    OrList c1 ->
    OrList c2 ->
    OrList (__eo_list_concat_rec c1 c2) := by
  intro hC1 hC2
  have hConcatFalse (z : Term) :
      __eo_list_concat_rec (Term.Boolean false) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  induction hC1 generalizing c2 with
  | false =>
      rw [hConcatFalse c2]
      exact hC2
  | cons x xs hXs ih =>
      have hTail : OrList (__eo_list_concat_rec xs c2) := ih hC2
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        orList_ne_stuck hTail
      rw [orList_concat_rec_cons x xs c2 hTailNe]
      exact OrList.cons x (__eo_list_concat_rec xs c2) hTail

/-- Concatenating structural EO `and`-lists preserves list structure. -/
theorem andList_concat_preserves_list {c1 c2 : Term} :
    AndList c1 ->
    AndList c2 ->
    AndList (__eo_list_concat (Term.UOp UserOp.and) c1 c2) := by
  intro hC1 hC2
  change AndList
    (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2)))
  rw [andList_is_list_true hC1, andList_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact andList_concat_rec_preserves_list hC1 hC2

/-- Concatenating structural EO `or`-lists preserves list structure. -/
theorem orList_concat_preserves_list {c1 c2 : Term} :
    OrList c1 ->
    OrList c2 ->
    OrList (__eo_list_concat (Term.UOp UserOp.or) c1 c2) := by
  intro hC1 hC2
  change OrList
    (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2)))
  rw [orList_is_list_true hC1, orList_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact orList_concat_rec_preserves_list hC1 hC2

private theorem andList_concat_rec_preserves_bool_type {c1 c2 : Term} :
    AndList c1 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    RuleProofs.eo_has_bool_type (__eo_list_concat_rec c1 c2) := by
  intro hC1 hC1Bool hC2Bool
  have hConcatTrue (z : Term) :
      __eo_list_concat_rec (Term.Boolean true) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  induction hC1 generalizing c2 with
  | true =>
      rw [hConcatTrue c2]
      exact hC2Bool
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_and_left x xs hC1Bool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_and_right x xs hC1Bool
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
        ih hXsBool hC2Bool
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
      rw [andList_concat_rec_cons x xs c2 hTailNe]
      exact RuleProofs.eo_has_bool_type_and_of_bool_args x
        (__eo_list_concat_rec xs c2) hXBool hTailBool

private theorem orList_concat_rec_preserves_bool_type {c1 c2 : Term} :
    OrList c1 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    RuleProofs.eo_has_bool_type (__eo_list_concat_rec c1 c2) := by
  intro hC1 hC1Bool hC2Bool
  have hConcatFalse (z : Term) :
      __eo_list_concat_rec (Term.Boolean false) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  induction hC1 generalizing c2 with
  | false =>
      rw [hConcatFalse c2]
      exact hC2Bool
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hC1Bool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hC1Bool
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
        ih hXsBool hC2Bool
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
      rw [orList_concat_rec_cons x xs c2 hTailNe]
      exact RuleProofs.eo_has_bool_type_or_of_bool_args x
        (__eo_list_concat_rec xs c2) hXBool hTailBool

/-- Concatenating typed structural EO `and`-lists preserves Boolean type. -/
theorem andList_concat_preserves_bool_type {c1 c2 : Term} :
    AndList c1 ->
    AndList c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    RuleProofs.eo_has_bool_type (__eo_list_concat (Term.UOp UserOp.and) c1 c2) := by
  intro hC1 hC2 hC1Bool hC2Bool
  change RuleProofs.eo_has_bool_type
    (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2)))
  rw [andList_is_list_true hC1, andList_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact andList_concat_rec_preserves_bool_type hC1 hC1Bool hC2Bool

/-- Concatenating typed structural EO `or`-lists preserves Boolean type. -/
theorem orList_concat_preserves_bool_type {c1 c2 : Term} :
    OrList c1 ->
    OrList c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    RuleProofs.eo_has_bool_type (__eo_list_concat (Term.UOp UserOp.or) c1 c2) := by
  intro hC1 hC2 hC1Bool hC2Bool
  change RuleProofs.eo_has_bool_type
    (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2)))
  rw [orList_is_list_true hC1, orList_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact orList_concat_rec_preserves_bool_type hC1 hC1Bool hC2Bool

private theorem andList_concat_rec_typeof_bool_right {c1 c2 : Term} :
    AndList c1 ->
    __eo_typeof (__eo_list_concat_rec c1 c2) = Term.Bool ->
    __eo_typeof c2 = Term.Bool := by
  intro hC1 hTy
  have hConcatTrue (z : Term) :
      __eo_list_concat_rec (Term.Boolean true) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  induction hC1 generalizing c2 with
  | true =>
      rw [hConcatTrue c2] at hTy
      exact hTy
  | cons x xs hXs ih =>
      have hRecNe :
          __eo_list_concat_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs) c2 ≠
            Term.Stuck :=
        term_ne_stuck_of_typeof_bool hTy
      have hC2Ne : c2 ≠ Term.Stuck := by
        intro hC2
        subst c2
        simp [__eo_list_concat_rec] at hRecNe
      have hRecEq :
          __eo_list_concat_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs) c2 =
            __eo_mk_apply (Term.Apply (Term.UOp UserOp.and) x)
              (__eo_list_concat_rec xs c2) := by
        cases c2 <;> simp [__eo_list_concat_rec] at hC2Ne ⊢
      rw [hRecEq] at hTy
      change __eo_typeof
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.and) x)
            (__eo_list_concat_rec xs c2)) = Term.Bool at hTy
      exact ih (typeof_mk_apply_and_right_bool hTy)

private theorem orList_concat_rec_typeof_bool_right {c1 c2 : Term} :
    OrList c1 ->
    __eo_typeof (__eo_list_concat_rec c1 c2) = Term.Bool ->
    __eo_typeof c2 = Term.Bool := by
  intro hC1 hTy
  have hConcatFalse (z : Term) :
      __eo_list_concat_rec (Term.Boolean false) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  induction hC1 generalizing c2 with
  | false =>
      rw [hConcatFalse c2] at hTy
      exact hTy
  | cons x xs hXs ih =>
      have hRecNe :
          __eo_list_concat_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs) c2 ≠
            Term.Stuck :=
        term_ne_stuck_of_typeof_bool hTy
      have hC2Ne : c2 ≠ Term.Stuck := by
        intro hC2
        subst c2
        simp [__eo_list_concat_rec] at hRecNe
      have hRecEq :
          __eo_list_concat_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs) c2 =
            __eo_mk_apply (Term.Apply (Term.UOp UserOp.or) x)
              (__eo_list_concat_rec xs c2) := by
        cases c2 <;> simp [__eo_list_concat_rec] at hC2Ne ⊢
      rw [hRecEq] at hTy
      change __eo_typeof
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.or) x)
            (__eo_list_concat_rec xs c2)) = Term.Bool at hTy
      exact ih (typeof_mk_apply_or_right_bool hTy)

/-- The right side of a well-typed structural `and`-list concatenation is well typed. -/
theorem andList_concat_typeof_bool_right {c1 c2 : Term} :
    AndList c1 ->
    AndList c2 ->
    __eo_typeof (__eo_list_concat (Term.UOp UserOp.and) c1 c2) = Term.Bool ->
    __eo_typeof c2 = Term.Bool := by
  intro hC1 hC2 hTy
  change __eo_typeof
    (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2))) = Term.Bool at hTy
  rw [andList_is_list_true hC1, andList_is_list_true hC2] at hTy
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hTy
  exact andList_concat_rec_typeof_bool_right hC1 hTy

/-- The right side of a well-typed structural `or`-list concatenation is well typed. -/
theorem orList_concat_typeof_bool_right {c1 c2 : Term} :
    OrList c1 ->
    OrList c2 ->
    __eo_typeof (__eo_list_concat (Term.UOp UserOp.or) c1 c2) = Term.Bool ->
    __eo_typeof c2 = Term.Bool := by
  intro hC1 hC2 hTy
  change __eo_typeof
    (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2))) = Term.Bool at hTy
  rw [orList_is_list_true hC1, orList_is_list_true hC2] at hTy
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hTy
  exact orList_concat_rec_typeof_bool_right hC1 hTy

/-- A false left side makes an EO conjunction false. -/
theorem eo_interprets_and_false_of_left_false
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    eo_interprets M A false ->
    RuleProofs.eo_has_bool_type B ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) false := by
  intro hAFalse hBBool
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hAFalse ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) =
      SmtTerm.and (__eo_to_smt A) (__eo_to_smt B) by rfl]
  rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM B hBBool with
    ⟨b, hBEval⟩
  cases hAFalse with
  | intro_false hATy hAEval =>
      refine smt_interprets.intro_false M
        (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) ?_ ?_
      · rw [typeof_and_eq]
        have hBTy : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
          simpa [RuleProofs.eo_has_bool_type] using hBBool
        simp [hATy, hBTy, native_Teq, native_ite]
      · rw [__smtx_model_eval.eq_9, hAEval, hBEval]
        cases b <;> simp [__smtx_model_eval_and, SmtEval.native_and]

/-- A false right side makes an EO conjunction false. -/
theorem eo_interprets_and_false_of_right_false
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    eo_interprets M B false ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) false := by
  intro hABool hBFalse
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hBFalse ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) =
      SmtTerm.and (__eo_to_smt A) (__eo_to_smt B) by rfl]
  rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM A hABool with
    ⟨a, hAEval⟩
  cases hBFalse with
  | intro_false hBTy hBEval =>
      refine smt_interprets.intro_false M
        (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) ?_ ?_
      · rw [typeof_and_eq]
        have hATy : __smtx_typeof (__eo_to_smt A) = SmtType.Bool := by
          simpa [RuleProofs.eo_has_bool_type] using hABool
        simp [hATy, hBTy, native_Teq, native_ite]
      · rw [__smtx_model_eval.eq_9, hAEval, hBEval]
        cases a <;> simp [__smtx_model_eval_and, SmtEval.native_and]

private theorem andList_concat_rec_false_of_right_false
    (M : SmtModel) (hM : model_wf M) {c1 c2 : Term} :
    AndList c1 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M c2 false ->
    eo_interprets M (__eo_list_concat_rec c1 c2) false := by
  intro hC1 hC1Bool hC2Bool hC2False
  have hConcatTrue (z : Term) :
      __eo_list_concat_rec (Term.Boolean true) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  induction hC1 generalizing c2 with
  | true =>
      rw [hConcatTrue c2]
      exact hC2False
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_and_left x xs hC1Bool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_and_right x xs hC1Bool
      have hTailFalse : eo_interprets M (__eo_list_concat_rec xs c2) false :=
        ih hXsBool hC2Bool hC2False
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
        andList_concat_rec_preserves_bool_type hXs hXsBool hC2Bool
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
      rw [andList_concat_rec_cons x xs c2 hTailNe]
      exact eo_interprets_and_false_of_right_false M hM x
        (__eo_list_concat_rec xs c2) hXBool hTailFalse

/-- If the right `and`-list is false, its concatenation is false. -/
theorem andList_concat_false_of_right_false
    (M : SmtModel) (hM : model_wf M) {c1 c2 : Term} :
    AndList c1 ->
    AndList c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M c2 false ->
    eo_interprets M (__eo_list_concat (Term.UOp UserOp.and) c1 c2) false := by
  intro hC1 hC2 hC1Bool hC2Bool hC2False
  change eo_interprets M
    (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2))) false
  rw [andList_is_list_true hC1, andList_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact andList_concat_rec_false_of_right_false M hM hC1 hC1Bool hC2Bool
    hC2False

/-- A defined `and` singleton-elimination input is a structural EO `and`-list. -/
theorem andList_of_singleton_elim_ne_stuck {c : Term} :
    __eo_list_singleton_elim (Term.UOp UserOp.and) c ≠ Term.Stuck ->
    AndList c := by
  intro hElim
  have hReq :
      __eo_requires (__eo_is_list (Term.UOp UserOp.and) c) (Term.Boolean true)
        (__eo_list_singleton_elim_2 c) ≠ Term.Stuck := by
    simpa [__eo_list_singleton_elim] using hElim
  have hList :
      __eo_is_list (Term.UOp UserOp.and) c = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck (__eo_is_list (Term.UOp UserOp.and) c)
      (Term.Boolean true) (__eo_list_singleton_elim_2 c) hReq
  exact andList_of_is_list_true hList

/-- Singleton elimination preserves translated Boolean type for structural EO `and`-lists. -/
theorem andList_singleton_elim_preserves_bool_type {c : Term} :
    AndList c ->
    RuleProofs.eo_has_bool_type c ->
    RuleProofs.eo_has_bool_type
      (__eo_list_singleton_elim (Term.UOp UserOp.and) c) := by
  intro hList hCBool
  change RuleProofs.eo_has_bool_type
    (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c) (Term.Boolean true)
      (__eo_list_singleton_elim_2 c))
  rw [andList_is_list_true hList]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases hList with
  | true =>
      simpa [__eo_list_singleton_elim_2] using hCBool
  | cons x xs hXs =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_and_left x xs hCBool
      cases hXs with
      | true =>
          simpa [__eo_list_singleton_elim_2, __eo_is_list_nil, __eo_ite,
            native_ite, native_teq] using hXBool
      | cons y ys hYs =>
          simpa [__eo_list_singleton_elim_2, __eo_is_list_nil, __eo_ite,
            native_ite, native_teq] using hCBool

/-- Singleton elimination preserves truth for structural EO `and`-lists. -/
theorem andList_singleton_elim_true_iff
    (M : SmtModel) {c : Term} :
    AndList c ->
    RuleProofs.eo_has_bool_type c ->
    (eo_interprets M (__eo_list_singleton_elim (Term.UOp UserOp.and) c) true ↔
      eo_interprets M c true) := by
  intro hList hCBool
  change
    (eo_interprets M
        (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c) (Term.Boolean true)
          (__eo_list_singleton_elim_2 c)) true ↔
      eo_interprets M c true)
  rw [andList_is_list_true hList]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases hList with
  | true =>
      simp [__eo_list_singleton_elim_2]
  | cons x xs hXs =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_and_left x xs hCBool
      cases hXs with
      | true =>
          have hIff :
              (eo_interprets M x true ↔
                eo_interprets M
                  (Term.Apply (Term.Apply (Term.UOp UserOp.and) x)
                    (Term.Boolean true)) true) := by
            constructor
            · intro hXTrue
              exact RuleProofs.eo_interprets_and_intro M x (Term.Boolean true)
                hXTrue (RuleProofs.eo_interprets_true M)
            · intro hAndTrue
              exact RuleProofs.eo_interprets_and_left M x (Term.Boolean true)
                hAndTrue
          simpa [__eo_list_singleton_elim_2, __eo_is_list_nil, __eo_ite,
            native_ite, native_teq] using hIff
      | cons y ys hYs =>
          simp [__eo_list_singleton_elim_2, __eo_is_list_nil, __eo_ite,
            native_ite, native_teq]

private theorem orList_concat_rec_true_of_right_true
    (M : SmtModel) (hM : model_wf M) {c1 c2 : Term} :
    OrList c1 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M c2 true ->
    eo_interprets M (__eo_list_concat_rec c1 c2) true := by
  intro hC1 hC1Bool hC2Bool hC2True
  have hConcatFalse (z : Term) :
      __eo_list_concat_rec (Term.Boolean false) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  induction hC1 generalizing c2 with
  | false =>
      rw [hConcatFalse c2]
      exact hC2True
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hC1Bool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hC1Bool
      have hTailTrue : eo_interprets M (__eo_list_concat_rec xs c2) true :=
        ih hXsBool hC2Bool hC2True
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
        orList_concat_rec_preserves_bool_type hXs hXsBool hC2Bool
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
      rw [orList_concat_rec_cons x xs c2 hTailNe]
      exact RuleProofs.eo_interprets_or_right_intro M hM x
        (__eo_list_concat_rec xs c2) hXBool hTailTrue

/-- If the right `or`-list is true, its concatenation is true. -/
theorem orList_concat_true_of_right_true
    (M : SmtModel) (hM : model_wf M) {c1 c2 : Term} :
    OrList c1 ->
    OrList c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M c2 true ->
    eo_interprets M (__eo_list_concat (Term.UOp UserOp.or) c1 c2) true := by
  intro hC1 hC2 hC1Bool hC2Bool hC2True
  change eo_interprets M
    (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2))) true
  rw [orList_is_list_true hC1, orList_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact orList_concat_rec_true_of_right_true M hM hC1 hC1Bool hC2Bool
    hC2True

/-- A defined `or` singleton-elimination input is a structural EO `or`-list. -/
theorem orList_of_singleton_elim_ne_stuck {c : Term} :
    __eo_list_singleton_elim (Term.UOp UserOp.or) c ≠ Term.Stuck ->
    OrList c := by
  intro hElim
  have hReq :
      __eo_requires (__eo_is_list (Term.UOp UserOp.or) c) (Term.Boolean true)
        (__eo_list_singleton_elim_2 c) ≠ Term.Stuck := by
    simpa [__eo_list_singleton_elim] using hElim
  have hList :
      __eo_is_list (Term.UOp UserOp.or) c = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck (__eo_is_list (Term.UOp UserOp.or) c)
      (Term.Boolean true) (__eo_list_singleton_elim_2 c) hReq
  exact orList_of_is_list_true hList

/-- Singleton elimination preserves translated Boolean type for structural EO `or`-lists. -/
theorem orList_singleton_elim_preserves_bool_type {c : Term} :
    OrList c ->
    RuleProofs.eo_has_bool_type c ->
    RuleProofs.eo_has_bool_type
      (__eo_list_singleton_elim (Term.UOp UserOp.or) c) := by
  intro hList hCBool
  change RuleProofs.eo_has_bool_type
    (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c) (Term.Boolean true)
      (__eo_list_singleton_elim_2 c))
  rw [orList_is_list_true hList]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases hList with
  | false =>
      simpa [__eo_list_singleton_elim_2] using hCBool
  | cons x xs hXs =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      cases hXs with
      | false =>
          simpa [__eo_list_singleton_elim_2, __eo_is_list_nil, __eo_ite,
            native_ite, native_teq] using hXBool
      | cons y ys hYs =>
          simpa [__eo_list_singleton_elim_2, __eo_is_list_nil, __eo_ite,
            native_ite, native_teq] using hCBool

/-- Singleton elimination preserves truth for structural EO `or`-lists. -/
theorem orList_singleton_elim_true_iff
    (M : SmtModel) (hM : model_wf M) {c : Term} :
    OrList c ->
    RuleProofs.eo_has_bool_type c ->
    (eo_interprets M (__eo_list_singleton_elim (Term.UOp UserOp.or) c) true ↔
      eo_interprets M c true) := by
  intro hList hCBool
  change
    (eo_interprets M
        (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c) (Term.Boolean true)
          (__eo_list_singleton_elim_2 c)) true ↔
      eo_interprets M c true)
  rw [orList_is_list_true hList]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases hList with
  | false =>
      simp [__eo_list_singleton_elim_2]
  | cons x xs hXs =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      cases hXs with
      | false =>
          have hIff :
              (eo_interprets M x true ↔
                eo_interprets M
                  (Term.Apply (Term.Apply (Term.UOp UserOp.or) x)
                    (Term.Boolean false)) true) := by
            constructor
            · intro hXTrue
              exact RuleProofs.eo_interprets_or_left_intro M hM x
                (Term.Boolean false) hXTrue RuleProofs.eo_has_bool_type_false
            · intro hOrTrue
              rcases eo_interprets_bool_cases M hM x hXBool with hXTrue | hXFalse
              · exact hXTrue
              · have hOrFalse :
                    eo_interprets M
                      (Term.Apply (Term.Apply (Term.UOp UserOp.or) x)
                        (Term.Boolean false)) false := by
                  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hXFalse ⊢
                  rw [show __eo_to_smt
                      (Term.Apply (Term.Apply (Term.UOp UserOp.or) x)
                        (Term.Boolean false)) =
                        SmtTerm.or (__eo_to_smt x) (SmtTerm.Boolean false) by rfl]
                  cases hXFalse with
                  | intro_false hTy hEval =>
                      refine smt_interprets.intro_false M
                        (SmtTerm.or (__eo_to_smt x) (SmtTerm.Boolean false)) ?_ ?_
                      · rw [typeof_or_eq]
                        rw [__smtx_typeof.eq_1]
                        simp [hTy, native_Teq, native_ite]
                      · rw [__smtx_model_eval.eq_8, hEval, __smtx_model_eval.eq_1]
                        simp [__smtx_model_eval_or, SmtEval.native_or]
                exact False.elim
                  ((RuleProofs.eo_interprets_true_not_false M _ hOrTrue) hOrFalse)
          simpa [__eo_list_singleton_elim_2, __eo_is_list_nil, __eo_ite,
            native_ite, native_teq] using hIff
      | cons y ys hYs =>
          simp [__eo_list_singleton_elim_2, __eo_is_list_nil, __eo_ite,
            native_ite, native_teq]

end CnfSupport
