module

public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace BooleanElimSupport

private theorem clause2_has_bool_type (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) A)
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) B) (Term.Boolean false))) := by
  intro hA hB
  exact RuleProofs.eo_has_bool_type_or_of_bool_args A
    (Term.Apply (Term.Apply (Term.UOp UserOp.or) B) (Term.Boolean false))
    hA
    (RuleProofs.eo_has_bool_type_or_of_bool_args B (Term.Boolean false)
      hB RuleProofs.eo_has_bool_type_false)

private theorem not_mk_apply_arg_ne_stuck {t : Term} :
    __eo_mk_apply (Term.UOp UserOp.not) t ≠ Term.Stuck ->
    t ≠ Term.Stuck := by
  intro hMk hT
  subst hT
  simp [__eo_mk_apply] at hMk

private theorem eq_true_bool_cases
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B) true ->
    (eo_interprets M A true ∧ eo_interprets M B true) ∨
      (eo_interprets M A false ∧ eo_interprets M B false) := by
  intro hABool hBBool hEqTrue
  rcases CnfSupport.eo_interprets_bool_cases M hM A hABool with hATrue | hAFalse
  · rcases CnfSupport.eo_interprets_bool_cases M hM B hBBool with hBTrue | hBFalse
    · exact Or.inl ⟨hATrue, hBTrue⟩
    · have hEqFalse :
          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B) false :=
        CnfSupport.eo_interprets_eq_false_of_true_false M A B hATrue hBFalse
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hEqTrue) hEqFalse)
  · rcases CnfSupport.eo_interprets_bool_cases M hM B hBBool with hBTrue | hBFalse
    · have hEqFalse :
          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B) false :=
        CnfSupport.eo_interprets_eq_false_of_false_true M A B hAFalse hBTrue
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hEqTrue) hEqFalse)
    · exact Or.inr ⟨hAFalse, hBFalse⟩

private theorem eq_false_bool_cases
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B) false ->
    (eo_interprets M A true ∧ eo_interprets M B false) ∨
      (eo_interprets M A false ∧ eo_interprets M B true) := by
  intro hABool hBBool hEqFalse
  rcases CnfSupport.eo_interprets_bool_cases M hM A hABool with hATrue | hAFalse
  · rcases CnfSupport.eo_interprets_bool_cases M hM B hBBool with hBTrue | hBFalse
    · have hEqTrue :
          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B) true :=
        CnfSupport.eo_interprets_eq_true_of_true_true M A B hATrue hBTrue
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hEqTrue) hEqFalse)
    · exact Or.inl ⟨hATrue, hBFalse⟩
  · rcases CnfSupport.eo_interprets_bool_cases M hM B hBBool with hBTrue | hBFalse
    · exact Or.inr ⟨hAFalse, hBTrue⟩
    · have hEqTrue :
          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B) true :=
        CnfSupport.eo_interprets_eq_true_of_false_false M A B hAFalse hBFalse
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hEqTrue) hEqFalse)

private theorem xor_true_bool_cases
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.xor) A) B) true ->
    (eo_interprets M A true ∧ eo_interprets M B false) ∨
      (eo_interprets M A false ∧ eo_interprets M B true) := by
  intro hABool hBBool hXorTrue
  rcases CnfSupport.eo_interprets_bool_cases M hM A hABool with hATrue | hAFalse
  · rcases CnfSupport.eo_interprets_bool_cases M hM B hBBool with hBTrue | hBFalse
    · have hXorFalse :
          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.xor) A) B) false :=
        CnfSupport.eo_interprets_xor_false_of_true_true M A B hATrue hBTrue
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hXorTrue) hXorFalse)
    · exact Or.inl ⟨hATrue, hBFalse⟩
  · rcases CnfSupport.eo_interprets_bool_cases M hM B hBBool with hBTrue | hBFalse
    · exact Or.inr ⟨hAFalse, hBTrue⟩
    · have hXorFalse :
          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.xor) A) B) false :=
        CnfSupport.eo_interprets_xor_false_of_false_false M A B hAFalse hBFalse
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hXorTrue) hXorFalse)

private theorem xor_false_bool_cases
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.xor) A) B) false ->
    (eo_interprets M A true ∧ eo_interprets M B true) ∨
      (eo_interprets M A false ∧ eo_interprets M B false) := by
  intro hABool hBBool hXorFalse
  rcases CnfSupport.eo_interprets_bool_cases M hM A hABool with hATrue | hAFalse
  · rcases CnfSupport.eo_interprets_bool_cases M hM B hBBool with hBTrue | hBFalse
    · exact Or.inl ⟨hATrue, hBTrue⟩
    · have hXorTrue :
          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.xor) A) B) true :=
        CnfSupport.eo_interprets_xor_true_of_true_false M A B hATrue hBFalse
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hXorTrue) hXorFalse)
  · rcases CnfSupport.eo_interprets_bool_cases M hM B hBBool with hBTrue | hBFalse
    · have hXorTrue :
          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.xor) A) B) true :=
        CnfSupport.eo_interprets_xor_true_of_false_true M A B hAFalse hBTrue
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hXorTrue) hXorFalse)
    · exact Or.inr ⟨hAFalse, hBFalse⟩

private theorem xor_args_bool_of_xor_bool (A B : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) A) B) ->
    RuleProofs.eo_has_bool_type A ∧ RuleProofs.eo_has_bool_type B := by
  intro hXorBool
  exact CnfSupport.xor_args_have_bool_type_of_translation A B
    (RuleProofs.eo_has_smt_translation_of_has_bool_type _ hXorBool)

private theorem ite_branches_bool_of_ite_bool (C T E : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) ->
    RuleProofs.eo_has_bool_type T ∧ RuleProofs.eo_has_bool_type E := by
  intro hIteBool
  have hIteTy :
      __smtx_typeof (SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E)) =
        SmtType.Bool := by
    simpa [RuleProofs.eo_has_bool_type] using hIteBool
  have hNN : term_has_non_none_type
      (SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E)) := by
    unfold term_has_non_none_type
    rw [hIteTy]
    simp
  rcases ite_args_of_non_none hNN with ⟨U, hC, hT, hE, _hUNN⟩
  have hUBool : U = SmtType.Bool := by
    rw [typeof_ite_eq, hC, hT, hE] at hIteTy
    simpa [__smtx_typeof_ite, native_ite, native_Teq] using hIteTy
  constructor
  · unfold RuleProofs.eo_has_bool_type
    rw [hT, hUBool]
  · unfold RuleProofs.eo_has_bool_type
    rw [hE, hUBool]

private theorem ite_args_bool_of_ite_bool (C T E : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) ->
    RuleProofs.eo_has_bool_type C ∧
      RuleProofs.eo_has_bool_type T ∧ RuleProofs.eo_has_bool_type E := by
  intro hIteBool
  have hIteTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type _ hIteBool
  rcases ite_branches_bool_of_ite_bool C T E hIteBool with ⟨hTBool, hEBool⟩
  exact ⟨CnfSupport.ite_cond_has_bool_type_of_translation C T E hIteTrans,
    hTBool, hEBool⟩

private theorem ite_true_bool_cases
    (M : SmtModel) (hM : model_wf M) (C T E : Term) :
    RuleProofs.eo_has_bool_type C ->
    RuleProofs.eo_has_bool_type T ->
    RuleProofs.eo_has_bool_type E ->
    eo_interprets M (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) true ->
    (eo_interprets M C true ∧ eo_interprets M T true) ∨
      (eo_interprets M C false ∧ eo_interprets M E true) := by
  intro hCBool hTBool hEBool hIteTrue
  rcases CnfSupport.eo_interprets_bool_cases M hM C hCBool with hCTrue | hCFalse
  · rcases CnfSupport.eo_interprets_bool_cases M hM T hTBool with hTTrue | hTFalse
    · exact Or.inl ⟨hCTrue, hTTrue⟩
    · have hIteFalse :
          eo_interprets M
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) false :=
        CnfSupport.eo_interprets_ite_false_of_cond_true M C T E hCTrue hTFalse hEBool
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hIteTrue) hIteFalse)
  · rcases CnfSupport.eo_interprets_bool_cases M hM E hEBool with hETrue | hEFalse
    · exact Or.inr ⟨hCFalse, hETrue⟩
    · have hIteFalse :
          eo_interprets M
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) false :=
        CnfSupport.eo_interprets_ite_false_of_cond_false M C T E hCFalse hTBool hEFalse
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hIteTrue) hIteFalse)

private theorem ite_false_bool_cases
    (M : SmtModel) (hM : model_wf M) (C T E : Term) :
    RuleProofs.eo_has_bool_type C ->
    RuleProofs.eo_has_bool_type T ->
    RuleProofs.eo_has_bool_type E ->
    eo_interprets M (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) false ->
    (eo_interprets M C true ∧ eo_interprets M T false) ∨
      (eo_interprets M C false ∧ eo_interprets M E false) := by
  intro hCBool hTBool hEBool hIteFalse
  rcases CnfSupport.eo_interprets_bool_cases M hM C hCBool with hCTrue | hCFalse
  · rcases CnfSupport.eo_interprets_bool_cases M hM T hTBool with hTTrue | hTFalse
    · have hIteTrue :
          eo_interprets M
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) true :=
        CnfSupport.eo_interprets_ite_true_of_cond_true M C T E hCTrue hTTrue hEBool
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hIteTrue) hIteFalse)
    · exact Or.inl ⟨hCTrue, hTFalse⟩
  · rcases CnfSupport.eo_interprets_bool_cases M hM E hEBool with hETrue | hEFalse
    · have hIteTrue :
          eo_interprets M
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) T) E) true :=
        CnfSupport.eo_interprets_ite_true_of_cond_false M C T E hCFalse hTBool hETrue
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hIteTrue) hIteFalse)
    · exact Or.inr ⟨hCFalse, hEFalse⟩

private theorem eq_args_bool_of_result_type
    (A B : Term)
    (hEqBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B))
    (hATypeof : __eo_typeof A = Term.Bool)
    (hBTypeof : __eo_typeof B = Term.Bool) :
    RuleProofs.eo_has_bool_type A ∧ RuleProofs.eo_has_bool_type B := by
  have hEqTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B) :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type _ hEqBool
  rcases CnfSupport.eq_args_have_translation_of_translation A B hEqTrans with
    ⟨hATrans, hBTrans⟩
  exact ⟨RuleProofs.eo_typeof_bool_implies_has_bool_type A hATrans hATypeof,
    RuleProofs.eo_typeof_bool_implies_has_bool_type B hBTrans hBTypeof⟩

private theorem typed_equiv_elim1_impl (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    __eo_typeof (__eo_prog_equiv_elim1 (Proof.pf x1)) = Term.Bool ->
    __eo_prog_equiv_elim1 (Proof.pf x1) ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_prog_equiv_elim1 (Proof.pf x1)) := by
  intro hX1Bool hResultTy hProg
  cases x1 with
  | Apply f F2 =>
      cases f with
      | Apply g F1 =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  have hTyData := hResultTy
                  simp [__eo_prog_equiv_elim1] at hTyData
                  change __eo_typeof_or (__eo_typeof_not (__eo_typeof F1))
                    (__eo_typeof_or (__eo_typeof F2) Term.Bool) = Term.Bool at hTyData
                  have hF1Typeof : __eo_typeof F1 = Term.Bool :=
                    CnfSupport.typeof_not_eq_bool
                      (CnfSupport.typeof_clause2_left_eq_bool hTyData)
                  have hF2Typeof : __eo_typeof F2 = Term.Bool :=
                    CnfSupport.typeof_clause2_right_eq_bool hTyData
                  rcases eq_args_bool_of_result_type F1 F2 hX1Bool hF1Typeof hF2Typeof with
                    ⟨hF1Bool, hF2Bool⟩
                  exact clause2_has_bool_type (Term.Apply (Term.UOp UserOp.not) F1) F2
                    (RuleProofs.eo_has_bool_type_not_of_bool_arg F1 hF1Bool) hF2Bool
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem facts_equiv_elim1_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    eo_interprets M x1 true ->
    __eo_typeof (__eo_prog_equiv_elim1 (Proof.pf x1)) = Term.Bool ->
    __eo_prog_equiv_elim1 (Proof.pf x1) ≠ Term.Stuck ->
    eo_interprets M (__eo_prog_equiv_elim1 (Proof.pf x1)) true := by
  intro hX1Bool hX1True hResultTy hProg
  cases x1 with
  | Apply f F2 =>
      cases f with
      | Apply g F1 =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  have hTyData := hResultTy
                  simp [__eo_prog_equiv_elim1] at hTyData
                  change __eo_typeof_or (__eo_typeof_not (__eo_typeof F1))
                    (__eo_typeof_or (__eo_typeof F2) Term.Bool) = Term.Bool at hTyData
                  have hF1Typeof : __eo_typeof F1 = Term.Bool :=
                    CnfSupport.typeof_not_eq_bool
                      (CnfSupport.typeof_clause2_left_eq_bool hTyData)
                  have hF2Typeof : __eo_typeof F2 = Term.Bool :=
                    CnfSupport.typeof_clause2_right_eq_bool hTyData
                  rcases eq_args_bool_of_result_type F1 F2 hX1Bool hF1Typeof hF2Typeof with
                    ⟨hF1Bool, hF2Bool⟩
                  rcases eq_true_bool_cases M hM F1 F2 hF1Bool hF2Bool hX1True with
                    hBothTrue | hBothFalse
                  · exact CnfSupport.clause2_right_true M hM
                      (Term.Apply (Term.UOp UserOp.not) F1) F2
                      (RuleProofs.eo_has_bool_type_not_of_bool_arg F1 hF1Bool)
                      hBothTrue.2
                  · exact CnfSupport.clause2_left_true M hM
                      (Term.Apply (Term.UOp UserOp.not) F1) F2
                      (RuleProofs.eo_interprets_not_of_false M F1 hBothFalse.1) hF2Bool
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem typed_equiv_elim2_impl (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    __eo_typeof (__eo_prog_equiv_elim2 (Proof.pf x1)) = Term.Bool ->
    __eo_prog_equiv_elim2 (Proof.pf x1) ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_prog_equiv_elim2 (Proof.pf x1)) := by
  intro hX1Bool hResultTy hProg
  cases x1 with
  | Apply f F2 =>
      cases f with
      | Apply g F1 =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  have hTyData := hResultTy
                  simp [__eo_prog_equiv_elim2] at hTyData
                  change __eo_typeof_or (__eo_typeof F1)
                    (__eo_typeof_or (__eo_typeof_not (__eo_typeof F2)) Term.Bool) =
                      Term.Bool at hTyData
                  have hF1Typeof : __eo_typeof F1 = Term.Bool :=
                    CnfSupport.typeof_clause2_left_eq_bool hTyData
                  have hF2Typeof : __eo_typeof F2 = Term.Bool :=
                    CnfSupport.typeof_not_eq_bool
                      (CnfSupport.typeof_clause2_right_eq_bool hTyData)
                  rcases eq_args_bool_of_result_type F1 F2 hX1Bool hF1Typeof hF2Typeof with
                    ⟨hF1Bool, hF2Bool⟩
                  exact clause2_has_bool_type F1 (Term.Apply (Term.UOp UserOp.not) F2)
                    hF1Bool (RuleProofs.eo_has_bool_type_not_of_bool_arg F2 hF2Bool)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem facts_equiv_elim2_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    eo_interprets M x1 true ->
    __eo_typeof (__eo_prog_equiv_elim2 (Proof.pf x1)) = Term.Bool ->
    __eo_prog_equiv_elim2 (Proof.pf x1) ≠ Term.Stuck ->
    eo_interprets M (__eo_prog_equiv_elim2 (Proof.pf x1)) true := by
  intro hX1Bool hX1True hResultTy hProg
  cases x1 with
  | Apply f F2 =>
      cases f with
      | Apply g F1 =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  have hTyData := hResultTy
                  simp [__eo_prog_equiv_elim2] at hTyData
                  change __eo_typeof_or (__eo_typeof F1)
                    (__eo_typeof_or (__eo_typeof_not (__eo_typeof F2)) Term.Bool) =
                      Term.Bool at hTyData
                  have hF1Typeof : __eo_typeof F1 = Term.Bool :=
                    CnfSupport.typeof_clause2_left_eq_bool hTyData
                  have hF2Typeof : __eo_typeof F2 = Term.Bool :=
                    CnfSupport.typeof_not_eq_bool
                      (CnfSupport.typeof_clause2_right_eq_bool hTyData)
                  rcases eq_args_bool_of_result_type F1 F2 hX1Bool hF1Typeof hF2Typeof with
                    ⟨hF1Bool, hF2Bool⟩
                  rcases eq_true_bool_cases M hM F1 F2 hF1Bool hF2Bool hX1True with
                    hBothTrue | hBothFalse
                  · exact CnfSupport.clause2_left_true M hM F1
                      (Term.Apply (Term.UOp UserOp.not) F2) hBothTrue.1
                      (RuleProofs.eo_has_bool_type_not_of_bool_arg F2 hF2Bool)
                  · exact CnfSupport.clause2_right_true M hM F1
                      (Term.Apply (Term.UOp UserOp.not) F2) hF1Bool
                      (RuleProofs.eo_interprets_not_of_false M F2 hBothFalse.2)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

theorem cmd_step_and_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.and_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.and_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.and_elim args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.and_elim args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons i args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n1 premises =>
              cases premises with
              | nil =>
                  let Fs := __eo_state_proven_nth s n1
                  change __eo_prog_and_elim i (Proof.pf (__eo_state_proven_nth s n1)) ≠
                    Term.Stuck at hProg
                  have hINe : i ≠ Term.Stuck := by
                    intro hI
                    subst hI
                    simp [__eo_prog_and_elim] at hProg
                  have hNthNe : __eo_list_nth (Term.UOp UserOp.and) Fs i ≠ Term.Stuck := by
                    intro hNth
                    apply hProg
                    simp [Fs, __eo_prog_and_elim, hNth]
                  have hFsList : CnfSupport.AndList Fs :=
                    CnfSupport.andList_of_list_nth_ne_stuck hNthNe
                  have hFsBool : RuleProofs.eo_has_bool_type Fs :=
                    hPremisesBool Fs (by simp [Fs, premiseTermList])
                  have hNthBool : RuleProofs.eo_has_bool_type
                      (__eo_list_nth (Term.UOp UserOp.and) Fs i) :=
                    CnfSupport.andList_nth_has_bool_type hFsList hFsBool hNthNe
                  refine ⟨?_, ?_⟩
                  · intro hTrue
                    change eo_interprets M (__eo_prog_and_elim i (Proof.pf Fs)) true
                    simpa [__eo_prog_and_elim, hINe, Fs] using
                      CnfSupport.andList_nth_true_of_true M hFsList hFsBool
                        (hTrue Fs (by simp [Fs, premiseTermList])) hNthNe
                  · change RuleProofs.eo_has_smt_translation
                      (__eo_prog_and_elim i (Proof.pf Fs))
                    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (by
                        simpa [__eo_prog_and_elim, hINe, Fs] using hNthBool)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)

theorem cmd_step_not_or_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_or_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.not_or_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_or_elim args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.not_or_elim args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons i args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n1 premises =>
              cases premises with
              | nil =>
                  change __eo_prog_not_or_elim i
                    (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                  have hINe : i ≠ Term.Stuck := by
                    intro hI
                    subst hI
                    simp [__eo_prog_not_or_elim] at hProg
                  cases hX1 : __eo_state_proven_nth s n1 with
                  | Apply f Fs =>
                      cases f with
                      | UOp op =>
                          cases op with
                          | not =>
                              have hProgNot :
                                  __eo_prog_not_or_elim i
                                    (Proof.pf (Term.Apply (Term.UOp UserOp.not) Fs)) ≠
                                      Term.Stuck := by
                                simpa [hX1] using hProg
                              have hMkNe :
                                  __eo_mk_apply (Term.UOp UserOp.not)
                                    (__eo_list_nth (Term.UOp UserOp.or) Fs i) ≠ Term.Stuck := by
                                simpa [__eo_prog_not_or_elim, hINe] using hProgNot
                              have hNthNe :
                                  __eo_list_nth (Term.UOp UserOp.or) Fs i ≠ Term.Stuck :=
                                not_mk_apply_arg_ne_stuck hMkNe
                              have hFsList : CnfSupport.OrList Fs :=
                                CnfSupport.orList_of_list_nth_ne_stuck hNthNe
                              have hX1Bool : RuleProofs.eo_has_bool_type
                                  (Term.Apply (Term.UOp UserOp.not) Fs) :=
                                hPremisesBool (Term.Apply (Term.UOp UserOp.not) Fs)
                                  (by simp [premiseTermList, hX1])
                              have hFsBool : RuleProofs.eo_has_bool_type Fs :=
                                RuleProofs.eo_has_bool_type_not_arg Fs hX1Bool
                              have hNthBool : RuleProofs.eo_has_bool_type
                                  (__eo_list_nth (Term.UOp UserOp.or) Fs i) :=
                                CnfSupport.orList_nth_has_bool_type hFsList hFsBool hNthNe
                              refine ⟨?_, ?_⟩
                              · intro hTrue
                                change eo_interprets M
                                  (__eo_prog_not_or_elim i
                                    (Proof.pf (__eo_state_proven_nth s n1))) true
                                rw [hX1]
                                have hFsFalse : eo_interprets M Fs false :=
                                  RuleProofs.eo_interprets_not_true_implies_false M Fs
                                    (hTrue (Term.Apply (Term.UOp UserOp.not) Fs)
                                      (by simp [premiseTermList, hX1]))
                                have hNthFalse :
                                    eo_interprets M
                                      (__eo_list_nth (Term.UOp UserOp.or) Fs i) false :=
                                  CnfSupport.orList_nth_false_of_false M hM hFsList hFsBool
                                    hFsFalse hNthNe
                                simpa [__eo_prog_not_or_elim, hINe, hNthNe, __eo_mk_apply] using
                                  RuleProofs.eo_interprets_not_of_false M
                                    (__eo_list_nth (Term.UOp UserOp.or) Fs i) hNthFalse
                              · change RuleProofs.eo_has_smt_translation
                                  (__eo_prog_not_or_elim i
                                    (Proof.pf (__eo_state_proven_nth s n1)))
                                rw [hX1]
                                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                  (by
                                    simpa [__eo_prog_not_or_elim, hINe, hNthNe, __eo_mk_apply] using
                                      RuleProofs.eo_has_bool_type_not_of_bool_arg
                                        (__eo_list_nth (Term.UOp UserOp.or) Fs i) hNthBool)
                          | _ =>
                              exact False.elim (by
                                apply hProg
                                simp [hX1, __eo_prog_not_or_elim])
                      | _ =>
                          exact False.elim (by
                            apply hProg
                            simp [hX1, __eo_prog_not_or_elim])
                  | _ =>
                      exact False.elim (by
                        apply hProg
                        simp [hX1, __eo_prog_not_or_elim])
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)

theorem cmd_step_not_and_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_and args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.not_and args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_and args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.not_and args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              change __eo_prog_not_and
                (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
              cases hX1 : __eo_state_proven_nth s n1 with
              | Apply f Fs =>
                  cases f with
                  | UOp op =>
                      cases op with
                      | not =>
                          have hProgNot :
                              __eo_prog_not_and
                                (Proof.pf (Term.Apply (Term.UOp UserOp.not) Fs)) ≠
                                  Term.Stuck := by
                            simpa [hX1] using hProg
                          have hLowerNe : __lower_not_and Fs ≠ Term.Stuck := by
                            simpa [__eo_prog_not_and] using hProgNot
                          have hFsList : CnfSupport.AndList Fs :=
                            CnfSupport.andList_of_lower_not_and_ne_stuck hLowerNe
                          have hX1Bool : RuleProofs.eo_has_bool_type
                              (Term.Apply (Term.UOp UserOp.not) Fs) :=
                            hPremisesBool (Term.Apply (Term.UOp UserOp.not) Fs)
                              (by simp [hX1, premiseTermList])
                          have hFsBool : RuleProofs.eo_has_bool_type Fs :=
                            RuleProofs.eo_has_bool_type_not_arg Fs hX1Bool
                          refine ⟨?_, ?_⟩
                          · intro hTrue
                            change eo_interprets M
                              (__eo_prog_not_and
                                (Proof.pf (__eo_state_proven_nth s n1))) true
                            rw [hX1]
                            have hFsFalse : eo_interprets M Fs false :=
                              RuleProofs.eo_interprets_not_true_implies_false M Fs
                                (hTrue (Term.Apply (Term.UOp UserOp.not) Fs)
                                  (by simp [hX1, premiseTermList]))
                            simpa [__eo_prog_not_and] using
                              CnfSupport.lower_not_and_true_of_false M hM hFsList
                                hFsBool hFsFalse
                          · change RuleProofs.eo_has_smt_translation
                              (__eo_prog_not_and
                                (Proof.pf (__eo_state_proven_nth s n1)))
                            rw [hX1]
                            exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (by
                                simpa [__eo_prog_not_and] using
                                  CnfSupport.lower_not_and_has_bool_type hFsList hFsBool)
                      | _ =>
                          exact False.elim (by
                            apply hProg
                            simp [hX1, __eo_prog_not_and])
                  | _ =>
                      exact False.elim (by
                        apply hProg
                        simp [hX1, __eo_prog_not_and])
              | _ =>
                  exact False.elim (by
                    apply hProg
                    simp [hX1, __eo_prog_not_and])
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

theorem cmd_step_equiv_elim1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.equiv_elim1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.equiv_elim1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.equiv_elim1 args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.equiv_elim1 args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              let X1 := __eo_state_proven_nth s n1
              have hProgRule : __eo_prog_equiv_elim1 (Proof.pf X1) ≠ Term.Stuck := by
                change __eo_prog_equiv_elim1 (Proof.pf (__eo_state_proven_nth s n1)) ≠
                  Term.Stuck at hProg
                simpa [X1] using hProg
              have hTyRule : __eo_typeof (__eo_prog_equiv_elim1 (Proof.pf X1)) = Term.Bool := by
                change __eo_typeof
                  (__eo_prog_equiv_elim1 (Proof.pf (__eo_state_proven_nth s n1))) =
                    Term.Bool at hResultTy
                simpa [X1] using hResultTy
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_equiv_elim1 (Proof.pf X1)) true
                exact facts_equiv_elim1_impl M hM X1
                  (hPremisesBool X1 (by simp [X1, premiseTermList]))
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hTyRule hProgRule
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed_equiv_elim1_impl X1
                    (hPremisesBool X1 (by simp [X1, premiseTermList]))
                    hTyRule hProgRule)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

theorem cmd_step_equiv_elim2_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.equiv_elim2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.equiv_elim2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.equiv_elim2 args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.equiv_elim2 args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              let X1 := __eo_state_proven_nth s n1
              have hProgRule : __eo_prog_equiv_elim2 (Proof.pf X1) ≠ Term.Stuck := by
                change __eo_prog_equiv_elim2 (Proof.pf (__eo_state_proven_nth s n1)) ≠
                  Term.Stuck at hProg
                simpa [X1] using hProg
              have hTyRule : __eo_typeof (__eo_prog_equiv_elim2 (Proof.pf X1)) = Term.Bool := by
                change __eo_typeof
                  (__eo_prog_equiv_elim2 (Proof.pf (__eo_state_proven_nth s n1))) =
                    Term.Bool at hResultTy
                simpa [X1] using hResultTy
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_equiv_elim2 (Proof.pf X1)) true
                exact facts_equiv_elim2_impl M hM X1
                  (hPremisesBool X1 (by simp [X1, premiseTermList]))
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hTyRule hProgRule
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed_equiv_elim2_impl X1
                    (hPremisesBool X1 (by simp [X1, premiseTermList]))
                    hTyRule hProgRule)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem typed_not_equiv_elim1_impl (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    __eo_typeof (__eo_prog_not_equiv_elim1 (Proof.pf x1)) = Term.Bool ->
    __eo_prog_not_equiv_elim1 (Proof.pf x1) ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_prog_not_equiv_elim1 (Proof.pf x1)) := by
  intro hX1Bool hResultTy hProg
  cases x1 with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases x with
              | Apply g F2 =>
                  cases g with
                  | Apply h F1 =>
                      cases h with
                      | UOp op' =>
                          cases op' with
                          | eq =>
                              have hEqBool : RuleProofs.eo_has_bool_type
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) F1) F2) :=
                                RuleProofs.eo_has_bool_type_not_arg _ hX1Bool
                              have hTyData := hResultTy
                              simp [__eo_prog_not_equiv_elim1] at hTyData
                              change __eo_typeof_or (__eo_typeof F1)
                                (__eo_typeof_or (__eo_typeof F2) Term.Bool) =
                                  Term.Bool at hTyData
                              have hF1Typeof : __eo_typeof F1 = Term.Bool :=
                                CnfSupport.typeof_clause2_left_eq_bool hTyData
                              have hF2Typeof : __eo_typeof F2 = Term.Bool :=
                                CnfSupport.typeof_clause2_right_eq_bool hTyData
                              rcases eq_args_bool_of_result_type F1 F2 hEqBool
                                  hF1Typeof hF2Typeof with
                                ⟨hF1Bool, hF2Bool⟩
                              exact clause2_has_bool_type F1 F2 hF1Bool hF2Bool
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem facts_not_equiv_elim1_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    eo_interprets M x1 true ->
    __eo_typeof (__eo_prog_not_equiv_elim1 (Proof.pf x1)) = Term.Bool ->
    __eo_prog_not_equiv_elim1 (Proof.pf x1) ≠ Term.Stuck ->
    eo_interprets M (__eo_prog_not_equiv_elim1 (Proof.pf x1)) true := by
  intro hX1Bool hX1True hResultTy hProg
  cases x1 with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases x with
              | Apply g F2 =>
                  cases g with
                  | Apply h F1 =>
                      cases h with
                      | UOp op' =>
                          cases op' with
                          | eq =>
                              have hEqBool : RuleProofs.eo_has_bool_type
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) F1) F2) :=
                                RuleProofs.eo_has_bool_type_not_arg _ hX1Bool
                              have hTyData := hResultTy
                              simp [__eo_prog_not_equiv_elim1] at hTyData
                              change __eo_typeof_or (__eo_typeof F1)
                                (__eo_typeof_or (__eo_typeof F2) Term.Bool) =
                                  Term.Bool at hTyData
                              have hF1Typeof : __eo_typeof F1 = Term.Bool :=
                                CnfSupport.typeof_clause2_left_eq_bool hTyData
                              have hF2Typeof : __eo_typeof F2 = Term.Bool :=
                                CnfSupport.typeof_clause2_right_eq_bool hTyData
                              rcases eq_args_bool_of_result_type F1 F2 hEqBool
                                  hF1Typeof hF2Typeof with
                                ⟨hF1Bool, hF2Bool⟩
                              have hEqFalse : eo_interprets M
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) F1) F2) false :=
                                RuleProofs.eo_interprets_not_true_implies_false M
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) F1) F2)
                                  hX1True
                              rcases eq_false_bool_cases M hM F1 F2 hF1Bool hF2Bool hEqFalse with
                                hTF | hFT
                              · exact CnfSupport.clause2_left_true M hM F1 F2 hTF.1 hF2Bool
                              · exact CnfSupport.clause2_right_true M hM F1 F2 hF1Bool hFT.2
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem typed_not_equiv_elim2_impl (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    __eo_typeof (__eo_prog_not_equiv_elim2 (Proof.pf x1)) = Term.Bool ->
    __eo_prog_not_equiv_elim2 (Proof.pf x1) ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_prog_not_equiv_elim2 (Proof.pf x1)) := by
  intro hX1Bool hResultTy hProg
  cases x1 with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases x with
              | Apply g F2 =>
                  cases g with
                  | Apply h F1 =>
                      cases h with
                      | UOp op' =>
                          cases op' with
                          | eq =>
                              have hEqBool : RuleProofs.eo_has_bool_type
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) F1) F2) :=
                                RuleProofs.eo_has_bool_type_not_arg _ hX1Bool
                              have hTyData := hResultTy
                              simp [__eo_prog_not_equiv_elim2] at hTyData
                              change __eo_typeof_or (__eo_typeof_not (__eo_typeof F1))
                                (__eo_typeof_or (__eo_typeof_not (__eo_typeof F2)) Term.Bool) =
                                  Term.Bool at hTyData
                              have hF1Typeof : __eo_typeof F1 = Term.Bool :=
                                CnfSupport.typeof_not_eq_bool
                                  (CnfSupport.typeof_clause2_left_eq_bool hTyData)
                              have hF2Typeof : __eo_typeof F2 = Term.Bool :=
                                CnfSupport.typeof_not_eq_bool
                                  (CnfSupport.typeof_clause2_right_eq_bool hTyData)
                              rcases eq_args_bool_of_result_type F1 F2 hEqBool
                                  hF1Typeof hF2Typeof with
                                ⟨hF1Bool, hF2Bool⟩
                              exact clause2_has_bool_type
                                (Term.Apply (Term.UOp UserOp.not) F1)
                                (Term.Apply (Term.UOp UserOp.not) F2)
                                (RuleProofs.eo_has_bool_type_not_of_bool_arg F1 hF1Bool)
                                (RuleProofs.eo_has_bool_type_not_of_bool_arg F2 hF2Bool)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem facts_not_equiv_elim2_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    eo_interprets M x1 true ->
    __eo_typeof (__eo_prog_not_equiv_elim2 (Proof.pf x1)) = Term.Bool ->
    __eo_prog_not_equiv_elim2 (Proof.pf x1) ≠ Term.Stuck ->
    eo_interprets M (__eo_prog_not_equiv_elim2 (Proof.pf x1)) true := by
  intro hX1Bool hX1True hResultTy hProg
  cases x1 with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases x with
              | Apply g F2 =>
                  cases g with
                  | Apply h F1 =>
                      cases h with
                      | UOp op' =>
                          cases op' with
                          | eq =>
                              have hEqBool : RuleProofs.eo_has_bool_type
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) F1) F2) :=
                                RuleProofs.eo_has_bool_type_not_arg _ hX1Bool
                              have hTyData := hResultTy
                              simp [__eo_prog_not_equiv_elim2] at hTyData
                              change __eo_typeof_or (__eo_typeof_not (__eo_typeof F1))
                                (__eo_typeof_or (__eo_typeof_not (__eo_typeof F2)) Term.Bool) =
                                  Term.Bool at hTyData
                              have hF1Typeof : __eo_typeof F1 = Term.Bool :=
                                CnfSupport.typeof_not_eq_bool
                                  (CnfSupport.typeof_clause2_left_eq_bool hTyData)
                              have hF2Typeof : __eo_typeof F2 = Term.Bool :=
                                CnfSupport.typeof_not_eq_bool
                                  (CnfSupport.typeof_clause2_right_eq_bool hTyData)
                              rcases eq_args_bool_of_result_type F1 F2 hEqBool
                                  hF1Typeof hF2Typeof with
                                ⟨hF1Bool, hF2Bool⟩
                              have hEqFalse : eo_interprets M
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) F1) F2) false :=
                                RuleProofs.eo_interprets_not_true_implies_false M
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) F1) F2)
                                  hX1True
                              rcases eq_false_bool_cases M hM F1 F2 hF1Bool hF2Bool hEqFalse with
                                hTF | hFT
                              · exact CnfSupport.clause2_right_true M hM
                                  (Term.Apply (Term.UOp UserOp.not) F1)
                                  (Term.Apply (Term.UOp UserOp.not) F2)
                                  (RuleProofs.eo_has_bool_type_not_of_bool_arg F1 hF1Bool)
                                  (RuleProofs.eo_interprets_not_of_false M F2 hTF.2)
                              · exact CnfSupport.clause2_left_true M hM
                                  (Term.Apply (Term.UOp UserOp.not) F1)
                                  (Term.Apply (Term.UOp UserOp.not) F2)
                                  (RuleProofs.eo_interprets_not_of_false M F1 hFT.1)
                                  (RuleProofs.eo_has_bool_type_not_of_bool_arg F2 hF2Bool)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

theorem cmd_step_not_equiv_elim1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_equiv_elim1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.not_equiv_elim1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_equiv_elim1 args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.not_equiv_elim1 args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              let X1 := __eo_state_proven_nth s n1
              have hProgRule : __eo_prog_not_equiv_elim1 (Proof.pf X1) ≠ Term.Stuck := by
                change __eo_prog_not_equiv_elim1
                  (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                simpa [X1] using hProg
              have hTyRule :
                  __eo_typeof (__eo_prog_not_equiv_elim1 (Proof.pf X1)) = Term.Bool := by
                change __eo_typeof
                  (__eo_prog_not_equiv_elim1 (Proof.pf (__eo_state_proven_nth s n1))) =
                    Term.Bool at hResultTy
                simpa [X1] using hResultTy
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_not_equiv_elim1 (Proof.pf X1)) true
                exact facts_not_equiv_elim1_impl M hM X1
                  (hPremisesBool X1 (by simp [X1, premiseTermList]))
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hTyRule hProgRule
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed_not_equiv_elim1_impl X1
                    (hPremisesBool X1 (by simp [X1, premiseTermList]))
                    hTyRule hProgRule)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

theorem cmd_step_not_equiv_elim2_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_equiv_elim2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.not_equiv_elim2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_equiv_elim2 args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.not_equiv_elim2 args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              let X1 := __eo_state_proven_nth s n1
              have hProgRule : __eo_prog_not_equiv_elim2 (Proof.pf X1) ≠ Term.Stuck := by
                change __eo_prog_not_equiv_elim2
                  (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                simpa [X1] using hProg
              have hTyRule :
                  __eo_typeof (__eo_prog_not_equiv_elim2 (Proof.pf X1)) = Term.Bool := by
                change __eo_typeof
                  (__eo_prog_not_equiv_elim2 (Proof.pf (__eo_state_proven_nth s n1))) =
                    Term.Bool at hResultTy
                simpa [X1] using hResultTy
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_not_equiv_elim2 (Proof.pf X1)) true
                exact facts_not_equiv_elim2_impl M hM X1
                  (hPremisesBool X1 (by simp [X1, premiseTermList]))
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hTyRule hProgRule
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed_not_equiv_elim2_impl X1
                    (hPremisesBool X1 (by simp [X1, premiseTermList]))
                    hTyRule hProgRule)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem typed_xor_elim1_impl (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    __eo_prog_xor_elim1 (Proof.pf x1) ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_prog_xor_elim1 (Proof.pf x1)) := by
  intro hX1Bool hProg
  cases x1 with
  | Apply f F2 =>
      cases f with
      | Apply g F1 =>
          cases g with
          | UOp op =>
              cases op with
              | xor =>
                  rcases xor_args_bool_of_xor_bool F1 F2 hX1Bool with ⟨hF1Bool, hF2Bool⟩
                  exact clause2_has_bool_type F1 F2 hF1Bool hF2Bool
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem facts_xor_elim1_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    eo_interprets M x1 true ->
    __eo_prog_xor_elim1 (Proof.pf x1) ≠ Term.Stuck ->
    eo_interprets M (__eo_prog_xor_elim1 (Proof.pf x1)) true := by
  intro hX1Bool hX1True hProg
  cases x1 with
  | Apply f F2 =>
      cases f with
      | Apply g F1 =>
          cases g with
          | UOp op =>
              cases op with
              | xor =>
                  rcases xor_args_bool_of_xor_bool F1 F2 hX1Bool with ⟨hF1Bool, hF2Bool⟩
                  rcases xor_true_bool_cases M hM F1 F2 hF1Bool hF2Bool hX1True with
                    hTF | hFT
                  · exact CnfSupport.clause2_left_true M hM F1 F2 hTF.1 hF2Bool
                  · exact CnfSupport.clause2_right_true M hM F1 F2 hF1Bool hFT.2
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem typed_xor_elim2_impl (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    __eo_prog_xor_elim2 (Proof.pf x1) ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_prog_xor_elim2 (Proof.pf x1)) := by
  intro hX1Bool hProg
  cases x1 with
  | Apply f F2 =>
      cases f with
      | Apply g F1 =>
          cases g with
          | UOp op =>
              cases op with
              | xor =>
                  rcases xor_args_bool_of_xor_bool F1 F2 hX1Bool with ⟨hF1Bool, hF2Bool⟩
                  exact clause2_has_bool_type
                    (Term.Apply (Term.UOp UserOp.not) F1)
                    (Term.Apply (Term.UOp UserOp.not) F2)
                    (RuleProofs.eo_has_bool_type_not_of_bool_arg F1 hF1Bool)
                    (RuleProofs.eo_has_bool_type_not_of_bool_arg F2 hF2Bool)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem facts_xor_elim2_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    eo_interprets M x1 true ->
    __eo_prog_xor_elim2 (Proof.pf x1) ≠ Term.Stuck ->
    eo_interprets M (__eo_prog_xor_elim2 (Proof.pf x1)) true := by
  intro hX1Bool hX1True hProg
  cases x1 with
  | Apply f F2 =>
      cases f with
      | Apply g F1 =>
          cases g with
          | UOp op =>
              cases op with
              | xor =>
                  rcases xor_args_bool_of_xor_bool F1 F2 hX1Bool with ⟨hF1Bool, hF2Bool⟩
                  rcases xor_true_bool_cases M hM F1 F2 hF1Bool hF2Bool hX1True with
                    hTF | hFT
                  · exact CnfSupport.clause2_right_true M hM
                      (Term.Apply (Term.UOp UserOp.not) F1)
                      (Term.Apply (Term.UOp UserOp.not) F2)
                      (RuleProofs.eo_has_bool_type_not_of_bool_arg F1 hF1Bool)
                      (RuleProofs.eo_interprets_not_of_false M F2 hTF.2)
                  · exact CnfSupport.clause2_left_true M hM
                      (Term.Apply (Term.UOp UserOp.not) F1)
                      (Term.Apply (Term.UOp UserOp.not) F2)
                      (RuleProofs.eo_interprets_not_of_false M F1 hFT.1)
                      (RuleProofs.eo_has_bool_type_not_of_bool_arg F2 hF2Bool)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem typed_not_xor_elim1_impl (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    __eo_prog_not_xor_elim1 (Proof.pf x1) ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_prog_not_xor_elim1 (Proof.pf x1)) := by
  intro hX1Bool hProg
  cases x1 with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases x with
              | Apply g F2 =>
                  cases g with
                  | Apply h F1 =>
                      cases h with
                      | UOp op' =>
                          cases op' with
                          | xor =>
                              have hXorBool : RuleProofs.eo_has_bool_type
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.xor) F1) F2) :=
                                RuleProofs.eo_has_bool_type_not_arg _ hX1Bool
                              rcases xor_args_bool_of_xor_bool F1 F2 hXorBool with
                                ⟨hF1Bool, hF2Bool⟩
                              exact clause2_has_bool_type F1
                                (Term.Apply (Term.UOp UserOp.not) F2) hF1Bool
                                (RuleProofs.eo_has_bool_type_not_of_bool_arg F2 hF2Bool)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem facts_not_xor_elim1_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    eo_interprets M x1 true ->
    __eo_prog_not_xor_elim1 (Proof.pf x1) ≠ Term.Stuck ->
    eo_interprets M (__eo_prog_not_xor_elim1 (Proof.pf x1)) true := by
  intro hX1Bool hX1True hProg
  cases x1 with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases x with
              | Apply g F2 =>
                  cases g with
                  | Apply h F1 =>
                      cases h with
                      | UOp op' =>
                          cases op' with
                          | xor =>
                              have hXorBool : RuleProofs.eo_has_bool_type
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.xor) F1) F2) :=
                                RuleProofs.eo_has_bool_type_not_arg _ hX1Bool
                              rcases xor_args_bool_of_xor_bool F1 F2 hXorBool with
                                ⟨hF1Bool, hF2Bool⟩
                              have hXorFalse : eo_interprets M
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.xor) F1) F2) false :=
                                RuleProofs.eo_interprets_not_true_implies_false M
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.xor) F1) F2) hX1True
                              rcases xor_false_bool_cases M hM F1 F2 hF1Bool hF2Bool hXorFalse with
                                hTT | hFF
                              · exact CnfSupport.clause2_left_true M hM F1
                                  (Term.Apply (Term.UOp UserOp.not) F2) hTT.1
                                  (RuleProofs.eo_has_bool_type_not_of_bool_arg F2 hF2Bool)
                              · exact CnfSupport.clause2_right_true M hM F1
                                  (Term.Apply (Term.UOp UserOp.not) F2) hF1Bool
                                  (RuleProofs.eo_interprets_not_of_false M F2 hFF.2)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem typed_not_xor_elim2_impl (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    __eo_prog_not_xor_elim2 (Proof.pf x1) ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_prog_not_xor_elim2 (Proof.pf x1)) := by
  intro hX1Bool hProg
  cases x1 with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases x with
              | Apply g F2 =>
                  cases g with
                  | Apply h F1 =>
                      cases h with
                      | UOp op' =>
                          cases op' with
                          | xor =>
                              have hXorBool : RuleProofs.eo_has_bool_type
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.xor) F1) F2) :=
                                RuleProofs.eo_has_bool_type_not_arg _ hX1Bool
                              rcases xor_args_bool_of_xor_bool F1 F2 hXorBool with
                                ⟨hF1Bool, hF2Bool⟩
                              exact clause2_has_bool_type
                                (Term.Apply (Term.UOp UserOp.not) F1) F2
                                (RuleProofs.eo_has_bool_type_not_of_bool_arg F1 hF1Bool)
                                hF2Bool
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem facts_not_xor_elim2_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    eo_interprets M x1 true ->
    __eo_prog_not_xor_elim2 (Proof.pf x1) ≠ Term.Stuck ->
    eo_interprets M (__eo_prog_not_xor_elim2 (Proof.pf x1)) true := by
  intro hX1Bool hX1True hProg
  cases x1 with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases x with
              | Apply g F2 =>
                  cases g with
                  | Apply h F1 =>
                      cases h with
                      | UOp op' =>
                          cases op' with
                          | xor =>
                              have hXorBool : RuleProofs.eo_has_bool_type
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.xor) F1) F2) :=
                                RuleProofs.eo_has_bool_type_not_arg _ hX1Bool
                              rcases xor_args_bool_of_xor_bool F1 F2 hXorBool with
                                ⟨hF1Bool, hF2Bool⟩
                              have hXorFalse : eo_interprets M
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.xor) F1) F2) false :=
                                RuleProofs.eo_interprets_not_true_implies_false M
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.xor) F1) F2) hX1True
                              rcases xor_false_bool_cases M hM F1 F2 hF1Bool hF2Bool hXorFalse with
                                hTT | hFF
                              · exact CnfSupport.clause2_right_true M hM
                                  (Term.Apply (Term.UOp UserOp.not) F1) F2
                                  (RuleProofs.eo_has_bool_type_not_of_bool_arg F1 hF1Bool)
                                  hTT.2
                              · exact CnfSupport.clause2_left_true M hM
                                  (Term.Apply (Term.UOp UserOp.not) F1) F2
                                  (RuleProofs.eo_interprets_not_of_false M F1 hFF.1)
                                  hF2Bool
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem typed_ite_elim1_impl (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    __eo_prog_ite_elim1 (Proof.pf x1) ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_prog_ite_elim1 (Proof.pf x1)) := by
  intro hX1Bool hProg
  cases x1 with
  | Apply f F2 =>
      cases f with
      | Apply g F1 =>
          cases g with
          | Apply h C =>
              cases h with
              | UOp op =>
                  cases op with
                  | ite =>
                      rcases ite_args_bool_of_ite_bool C F1 F2 hX1Bool with
                        ⟨hCBool, hF1Bool, _hF2Bool⟩
                      exact clause2_has_bool_type (Term.Apply (Term.UOp UserOp.not) C) F1
                        (RuleProofs.eo_has_bool_type_not_of_bool_arg C hCBool) hF1Bool
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem facts_ite_elim1_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    eo_interprets M x1 true ->
    __eo_prog_ite_elim1 (Proof.pf x1) ≠ Term.Stuck ->
    eo_interprets M (__eo_prog_ite_elim1 (Proof.pf x1)) true := by
  intro hX1Bool hX1True hProg
  cases x1 with
  | Apply f F2 =>
      cases f with
      | Apply g F1 =>
          cases g with
          | Apply h C =>
              cases h with
              | UOp op =>
                  cases op with
                  | ite =>
                      rcases ite_args_bool_of_ite_bool C F1 F2 hX1Bool with
                        ⟨hCBool, hF1Bool, hF2Bool⟩
                      rcases ite_true_bool_cases M hM C F1 F2 hCBool hF1Bool hF2Bool hX1True with
                        hCT | hCE
                      · exact CnfSupport.clause2_right_true M hM
                          (Term.Apply (Term.UOp UserOp.not) C) F1
                          (RuleProofs.eo_has_bool_type_not_of_bool_arg C hCBool) hCT.2
                      · exact CnfSupport.clause2_left_true M hM
                          (Term.Apply (Term.UOp UserOp.not) C) F1
                          (RuleProofs.eo_interprets_not_of_false M C hCE.1) hF1Bool
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem typed_ite_elim2_impl (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    __eo_prog_ite_elim2 (Proof.pf x1) ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_prog_ite_elim2 (Proof.pf x1)) := by
  intro hX1Bool hProg
  cases x1 with
  | Apply f F2 =>
      cases f with
      | Apply g F1 =>
          cases g with
          | Apply h C =>
              cases h with
              | UOp op =>
                  cases op with
                  | ite =>
                      rcases ite_args_bool_of_ite_bool C F1 F2 hX1Bool with
                        ⟨hCBool, _hF1Bool, hF2Bool⟩
                      exact clause2_has_bool_type C F2 hCBool hF2Bool
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem facts_ite_elim2_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    eo_interprets M x1 true ->
    __eo_prog_ite_elim2 (Proof.pf x1) ≠ Term.Stuck ->
    eo_interprets M (__eo_prog_ite_elim2 (Proof.pf x1)) true := by
  intro hX1Bool hX1True hProg
  cases x1 with
  | Apply f F2 =>
      cases f with
      | Apply g F1 =>
          cases g with
          | Apply h C =>
              cases h with
              | UOp op =>
                  cases op with
                  | ite =>
                      rcases ite_args_bool_of_ite_bool C F1 F2 hX1Bool with
                        ⟨hCBool, hF1Bool, hF2Bool⟩
                      rcases ite_true_bool_cases M hM C F1 F2 hCBool hF1Bool hF2Bool hX1True with
                        hCT | hCE
                      · exact CnfSupport.clause2_left_true M hM C F2 hCT.1 hF2Bool
                      · exact CnfSupport.clause2_right_true M hM C F2 hCBool hCE.2
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem typed_not_ite_elim1_impl (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    __eo_prog_not_ite_elim1 (Proof.pf x1) ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_prog_not_ite_elim1 (Proof.pf x1)) := by
  intro hX1Bool hProg
  cases x1 with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases x with
              | Apply g F2 =>
                  cases g with
                  | Apply h F1 =>
                      cases h with
                      | Apply k C =>
                          cases k with
                          | UOp op' =>
                              cases op' with
                              | ite =>
                                  have hIteBool : RuleProofs.eo_has_bool_type
                                      (Term.Apply
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) F1) F2) :=
                                    RuleProofs.eo_has_bool_type_not_arg _ hX1Bool
                                  rcases ite_args_bool_of_ite_bool C F1 F2 hIteBool with
                                    ⟨hCBool, hF1Bool, _hF2Bool⟩
                                  exact clause2_has_bool_type
                                    (Term.Apply (Term.UOp UserOp.not) C)
                                    (Term.Apply (Term.UOp UserOp.not) F1)
                                    (RuleProofs.eo_has_bool_type_not_of_bool_arg C hCBool)
                                    (RuleProofs.eo_has_bool_type_not_of_bool_arg F1 hF1Bool)
                              | _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem facts_not_ite_elim1_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    eo_interprets M x1 true ->
    __eo_prog_not_ite_elim1 (Proof.pf x1) ≠ Term.Stuck ->
    eo_interprets M (__eo_prog_not_ite_elim1 (Proof.pf x1)) true := by
  intro hX1Bool hX1True hProg
  cases x1 with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases x with
              | Apply g F2 =>
                  cases g with
                  | Apply h F1 =>
                      cases h with
                      | Apply k C =>
                          cases k with
                          | UOp op' =>
                              cases op' with
                              | ite =>
                                  have hIteBool : RuleProofs.eo_has_bool_type
                                      (Term.Apply
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) F1) F2) :=
                                    RuleProofs.eo_has_bool_type_not_arg _ hX1Bool
                                  rcases ite_args_bool_of_ite_bool C F1 F2 hIteBool with
                                    ⟨hCBool, hF1Bool, hF2Bool⟩
                                  have hIteFalse : eo_interprets M
                                      (Term.Apply
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) F1) F2)
                                      false :=
                                    RuleProofs.eo_interprets_not_true_implies_false M
                                      (Term.Apply
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) F1) F2)
                                      hX1True
                                  rcases ite_false_bool_cases M hM C F1 F2 hCBool hF1Bool hF2Bool
                                      hIteFalse with
                                    hCT | hCE
                                  · exact CnfSupport.clause2_right_true M hM
                                      (Term.Apply (Term.UOp UserOp.not) C)
                                      (Term.Apply (Term.UOp UserOp.not) F1)
                                      (RuleProofs.eo_has_bool_type_not_of_bool_arg C hCBool)
                                      (RuleProofs.eo_interprets_not_of_false M F1 hCT.2)
                                  · exact CnfSupport.clause2_left_true M hM
                                      (Term.Apply (Term.UOp UserOp.not) C)
                                      (Term.Apply (Term.UOp UserOp.not) F1)
                                      (RuleProofs.eo_interprets_not_of_false M C hCE.1)
                                      (RuleProofs.eo_has_bool_type_not_of_bool_arg F1 hF1Bool)
                              | _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem typed_not_ite_elim2_impl (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    __eo_prog_not_ite_elim2 (Proof.pf x1) ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_prog_not_ite_elim2 (Proof.pf x1)) := by
  intro hX1Bool hProg
  cases x1 with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases x with
              | Apply g F2 =>
                  cases g with
                  | Apply h F1 =>
                      cases h with
                      | Apply k C =>
                          cases k with
                          | UOp op' =>
                              cases op' with
                              | ite =>
                                  have hIteBool : RuleProofs.eo_has_bool_type
                                      (Term.Apply
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) F1) F2) :=
                                    RuleProofs.eo_has_bool_type_not_arg _ hX1Bool
                                  rcases ite_args_bool_of_ite_bool C F1 F2 hIteBool with
                                    ⟨hCBool, _hF1Bool, hF2Bool⟩
                                  exact clause2_has_bool_type C
                                    (Term.Apply (Term.UOp UserOp.not) F2) hCBool
                                    (RuleProofs.eo_has_bool_type_not_of_bool_arg F2 hF2Bool)
                              | _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem facts_not_ite_elim2_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    eo_interprets M x1 true ->
    __eo_prog_not_ite_elim2 (Proof.pf x1) ≠ Term.Stuck ->
    eo_interprets M (__eo_prog_not_ite_elim2 (Proof.pf x1)) true := by
  intro hX1Bool hX1True hProg
  cases x1 with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases x with
              | Apply g F2 =>
                  cases g with
                  | Apply h F1 =>
                      cases h with
                      | Apply k C =>
                          cases k with
                          | UOp op' =>
                              cases op' with
                              | ite =>
                                  have hIteBool : RuleProofs.eo_has_bool_type
                                      (Term.Apply
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) F1) F2) :=
                                    RuleProofs.eo_has_bool_type_not_arg _ hX1Bool
                                  rcases ite_args_bool_of_ite_bool C F1 F2 hIteBool with
                                    ⟨hCBool, hF1Bool, hF2Bool⟩
                                  have hIteFalse : eo_interprets M
                                      (Term.Apply
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) F1) F2)
                                      false :=
                                    RuleProofs.eo_interprets_not_true_implies_false M
                                      (Term.Apply
                                        (Term.Apply (Term.Apply (Term.UOp UserOp.ite) C) F1) F2)
                                      hX1True
                                  rcases ite_false_bool_cases M hM C F1 F2 hCBool hF1Bool hF2Bool
                                      hIteFalse with
                                    hCT | hCE
                                  · exact CnfSupport.clause2_left_true M hM C
                                      (Term.Apply (Term.UOp UserOp.not) F2) hCT.1
                                      (RuleProofs.eo_has_bool_type_not_of_bool_arg F2 hF2Bool)
                                  · exact CnfSupport.clause2_right_true M hM C
                                      (Term.Apply (Term.UOp UserOp.not) F2) hCBool
                                      (RuleProofs.eo_interprets_not_of_false M F2 hCE.2)
                              | _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

theorem cmd_step_xor_elim1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.xor_elim1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.xor_elim1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.xor_elim1 args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.xor_elim1 args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              let X1 := __eo_state_proven_nth s n1
              have hProgRule : __eo_prog_xor_elim1 (Proof.pf X1) ≠ Term.Stuck := by
                change __eo_prog_xor_elim1 (Proof.pf (__eo_state_proven_nth s n1)) ≠
                  Term.Stuck at hProg
                simpa [X1] using hProg
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_xor_elim1 (Proof.pf X1)) true
                exact facts_xor_elim1_impl M hM X1
                  (hPremisesBool X1 (by simp [X1, premiseTermList]))
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hProgRule
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed_xor_elim1_impl X1
                    (hPremisesBool X1 (by simp [X1, premiseTermList])) hProgRule)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

theorem cmd_step_xor_elim2_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.xor_elim2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.xor_elim2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.xor_elim2 args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.xor_elim2 args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              let X1 := __eo_state_proven_nth s n1
              have hProgRule : __eo_prog_xor_elim2 (Proof.pf X1) ≠ Term.Stuck := by
                change __eo_prog_xor_elim2 (Proof.pf (__eo_state_proven_nth s n1)) ≠
                  Term.Stuck at hProg
                simpa [X1] using hProg
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_xor_elim2 (Proof.pf X1)) true
                exact facts_xor_elim2_impl M hM X1
                  (hPremisesBool X1 (by simp [X1, premiseTermList]))
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hProgRule
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed_xor_elim2_impl X1
                    (hPremisesBool X1 (by simp [X1, premiseTermList])) hProgRule)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

theorem cmd_step_not_xor_elim1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_xor_elim1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.not_xor_elim1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_xor_elim1 args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.not_xor_elim1 args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              let X1 := __eo_state_proven_nth s n1
              have hProgRule : __eo_prog_not_xor_elim1 (Proof.pf X1) ≠ Term.Stuck := by
                change __eo_prog_not_xor_elim1
                  (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                simpa [X1] using hProg
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_not_xor_elim1 (Proof.pf X1)) true
                exact facts_not_xor_elim1_impl M hM X1
                  (hPremisesBool X1 (by simp [X1, premiseTermList]))
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hProgRule
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed_not_xor_elim1_impl X1
                    (hPremisesBool X1 (by simp [X1, premiseTermList])) hProgRule)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

theorem cmd_step_not_xor_elim2_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_xor_elim2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.not_xor_elim2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_xor_elim2 args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.not_xor_elim2 args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              let X1 := __eo_state_proven_nth s n1
              have hProgRule : __eo_prog_not_xor_elim2 (Proof.pf X1) ≠ Term.Stuck := by
                change __eo_prog_not_xor_elim2
                  (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                simpa [X1] using hProg
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_not_xor_elim2 (Proof.pf X1)) true
                exact facts_not_xor_elim2_impl M hM X1
                  (hPremisesBool X1 (by simp [X1, premiseTermList]))
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hProgRule
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed_not_xor_elim2_impl X1
                    (hPremisesBool X1 (by simp [X1, premiseTermList])) hProgRule)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

theorem cmd_step_ite_elim1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_elim1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.ite_elim1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_elim1 args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.ite_elim1 args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              let X1 := __eo_state_proven_nth s n1
              have hProgRule : __eo_prog_ite_elim1 (Proof.pf X1) ≠ Term.Stuck := by
                change __eo_prog_ite_elim1 (Proof.pf (__eo_state_proven_nth s n1)) ≠
                  Term.Stuck at hProg
                simpa [X1] using hProg
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_ite_elim1 (Proof.pf X1)) true
                exact facts_ite_elim1_impl M hM X1
                  (hPremisesBool X1 (by simp [X1, premiseTermList]))
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hProgRule
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed_ite_elim1_impl X1
                    (hPremisesBool X1 (by simp [X1, premiseTermList])) hProgRule)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

theorem cmd_step_ite_elim2_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_elim2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.ite_elim2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_elim2 args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.ite_elim2 args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              let X1 := __eo_state_proven_nth s n1
              have hProgRule : __eo_prog_ite_elim2 (Proof.pf X1) ≠ Term.Stuck := by
                change __eo_prog_ite_elim2 (Proof.pf (__eo_state_proven_nth s n1)) ≠
                  Term.Stuck at hProg
                simpa [X1] using hProg
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_ite_elim2 (Proof.pf X1)) true
                exact facts_ite_elim2_impl M hM X1
                  (hPremisesBool X1 (by simp [X1, premiseTermList]))
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hProgRule
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed_ite_elim2_impl X1
                    (hPremisesBool X1 (by simp [X1, premiseTermList])) hProgRule)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

theorem cmd_step_not_ite_elim1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_ite_elim1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.not_ite_elim1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_ite_elim1 args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.not_ite_elim1 args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              let X1 := __eo_state_proven_nth s n1
              have hProgRule : __eo_prog_not_ite_elim1 (Proof.pf X1) ≠ Term.Stuck := by
                change __eo_prog_not_ite_elim1
                  (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                simpa [X1] using hProg
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_not_ite_elim1 (Proof.pf X1)) true
                exact facts_not_ite_elim1_impl M hM X1
                  (hPremisesBool X1 (by simp [X1, premiseTermList]))
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hProgRule
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed_not_ite_elim1_impl X1
                    (hPremisesBool X1 (by simp [X1, premiseTermList])) hProgRule)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

theorem cmd_step_not_ite_elim2_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_ite_elim2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.not_ite_elim2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_ite_elim2 args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.not_ite_elim2 args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              let X1 := __eo_state_proven_nth s n1
              have hProgRule : __eo_prog_not_ite_elim2 (Proof.pf X1) ≠ Term.Stuck := by
                change __eo_prog_not_ite_elim2
                  (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                simpa [X1] using hProg
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_not_ite_elim2 (Proof.pf X1)) true
                exact facts_not_ite_elim2_impl M hM X1
                  (hPremisesBool X1 (by simp [X1, premiseTermList]))
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hProgRule
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed_not_ite_elim2_impl X1
                    (hPremisesBool X1 (by simp [X1, premiseTermList])) hProgRule)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

end BooleanElimSupport
