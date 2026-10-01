module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
import Cpc.Proofs.RuleSupport.CongSupport
import Cpc.Proofs.RuleSupport.StrEqReplSupport
import Cpc.Proofs.RuleSupport.StrReplaceAllSupport
public import Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Init.Data.Repr

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

theorem EvaluateProofInternal.smt_value_rel_model_eval_not_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_not a) (__smtx_model_eval_not b) := by
  intro hRel
  unfold RuleProofs.smt_value_rel at hRel ⊢
  cases a <;> cases b <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_not, native_veq] at hRel ⊢
  case Boolean b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp at hRel ⊢

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_to_lower_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_to_lower a) (__smtx_model_eval_str_to_lower b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_to_lower, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_to_upper_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_to_upper a) (__smtx_model_eval_str_to_upper b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_to_upper, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_rev_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_rev a) (__smtx_model_eval_str_rev b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_rev, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_leq_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_leq a b)
      (__smtx_model_eval_str_leq c d) := by
  intro hRelA hRelB
  by_cases hRegA :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ c = SmtValue.RegLan r2
  · rcases hRegA with ⟨r1, r2, rfl, rfl⟩
    cases b <;> cases d <;>
      simp [__smtx_model_eval_str_leq, __smtx_model_eval_str_lt,
        __smtx_model_eval_or, RuleProofs.smt_value_rel_refl]
  · have hAEq := (RuleProofs.smt_value_rel_iff_eq a c hRegA).mp hRelA
    subst c
    by_cases hRegB :
        ∃ r1 r2, b = SmtValue.RegLan r1 ∧ d = SmtValue.RegLan r2
    · rcases hRegB with ⟨r1, r2, rfl, rfl⟩
      cases a <;>
        simp [__smtx_model_eval_str_leq, __smtx_model_eval_str_lt,
          __smtx_model_eval_or, RuleProofs.smt_value_rel_refl]
    · have hBEq := (RuleProofs.smt_value_rel_iff_eq b d hRegB).mp hRelB
      subst d
      exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_replace_of_rel
    (a b c d e f : SmtValue) :
    RuleProofs.smt_value_rel a d ->
    RuleProofs.smt_value_rel b e ->
    RuleProofs.smt_value_rel c f ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_replace a b c)
      (__smtx_model_eval_str_replace d e f) := by
  intro hRelA hRelB hRelC
  by_cases hRegA :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ d = SmtValue.RegLan r2
  · rcases hRegA with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_replace, RuleProofs.smt_value_rel_refl]
  · have hAEq := (RuleProofs.smt_value_rel_iff_eq a d hRegA).mp hRelA
    subst d
    by_cases hRegB :
        ∃ r1 r2, b = SmtValue.RegLan r1 ∧ e = SmtValue.RegLan r2
    · rcases hRegB with ⟨r1, r2, rfl, rfl⟩
      cases a <;> simp [__smtx_model_eval_str_replace, RuleProofs.smt_value_rel_refl]
    · have hBEq := (RuleProofs.smt_value_rel_iff_eq b e hRegB).mp hRelB
      subst e
      by_cases hRegC :
          ∃ r1 r2, c = SmtValue.RegLan r1 ∧ f = SmtValue.RegLan r2
      · rcases hRegC with ⟨r1, r2, rfl, rfl⟩
        cases a <;> cases b <;>
          simp [__smtx_model_eval_str_replace, RuleProofs.smt_value_rel_refl]
      · have hCEq := (RuleProofs.smt_value_rel_iff_eq c f hRegC).mp hRelC
        subst f
        exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_indexof_of_rel
    (a b c d e f : SmtValue) :
    RuleProofs.smt_value_rel a d ->
    RuleProofs.smt_value_rel b e ->
    RuleProofs.smt_value_rel c f ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_indexof a b c)
      (__smtx_model_eval_str_indexof d e f) := by
  intro hRelA hRelB hRelC
  by_cases hRegA :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ d = SmtValue.RegLan r2
  · rcases hRegA with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_indexof, RuleProofs.smt_value_rel_refl]
  · have hAEq := (RuleProofs.smt_value_rel_iff_eq a d hRegA).mp hRelA
    subst d
    by_cases hRegB :
        ∃ r1 r2, b = SmtValue.RegLan r1 ∧ e = SmtValue.RegLan r2
    · rcases hRegB with ⟨r1, r2, rfl, rfl⟩
      cases a <;> simp [__smtx_model_eval_str_indexof, RuleProofs.smt_value_rel_refl]
    · have hBEq := (RuleProofs.smt_value_rel_iff_eq b e hRegB).mp hRelB
      subst e
      by_cases hRegC :
          ∃ r1 r2, c = SmtValue.RegLan r1 ∧ f = SmtValue.RegLan r2
      · rcases hRegC with ⟨r1, r2, rfl, rfl⟩
        cases a <;> cases b <;>
          simp [__smtx_model_eval_str_indexof, RuleProofs.smt_value_rel_refl]
      · have hCEq := (RuleProofs.smt_value_rel_iff_eq c f hRegC).mp hRelC
        subst f
        exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_update_of_rel
    (a b c d e f : SmtValue) :
    RuleProofs.smt_value_rel a d ->
    RuleProofs.smt_value_rel b e ->
    RuleProofs.smt_value_rel c f ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_update a b c)
      (__smtx_model_eval_str_update d e f) := by
  intro hRelA hRelB hRelC
  by_cases hRegA :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ d = SmtValue.RegLan r2
  · rcases hRegA with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_update, RuleProofs.smt_value_rel_refl]
  · have hAEq := (RuleProofs.smt_value_rel_iff_eq a d hRegA).mp hRelA
    subst d
    by_cases hRegB :
        ∃ r1 r2, b = SmtValue.RegLan r1 ∧ e = SmtValue.RegLan r2
    · rcases hRegB with ⟨r1, r2, rfl, rfl⟩
      cases a <;> simp [__smtx_model_eval_str_update, RuleProofs.smt_value_rel_refl]
    · have hBEq := (RuleProofs.smt_value_rel_iff_eq b e hRegB).mp hRelB
      subst e
      by_cases hRegC :
          ∃ r1 r2, c = SmtValue.RegLan r1 ∧ f = SmtValue.RegLan r2
      · rcases hRegC with ⟨r1, r2, rfl, rfl⟩
        cases a <;> cases b <;>
          simp [__smtx_model_eval_str_update, RuleProofs.smt_value_rel_refl]
      · have hCEq := (RuleProofs.smt_value_rel_iff_eq c f hRegC).mp hRelC
        subst f
        exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_replace_all_of_rel
    (a b c d e f : SmtValue) :
    RuleProofs.smt_value_rel a d ->
    RuleProofs.smt_value_rel b e ->
    RuleProofs.smt_value_rel c f ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_replace_all a b c)
      (__smtx_model_eval_str_replace_all d e f) := by
  intro hRelA hRelB hRelC
  by_cases hRegA :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ d = SmtValue.RegLan r2
  · rcases hRegA with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_replace_all, RuleProofs.smt_value_rel_refl]
  · have hAEq := (RuleProofs.smt_value_rel_iff_eq a d hRegA).mp hRelA
    subst d
    by_cases hRegB :
        ∃ r1 r2, b = SmtValue.RegLan r1 ∧ e = SmtValue.RegLan r2
    · rcases hRegB with ⟨r1, r2, rfl, rfl⟩
      cases a <;>
        simp [__smtx_model_eval_str_replace_all, RuleProofs.smt_value_rel_refl]
    · have hBEq := (RuleProofs.smt_value_rel_iff_eq b e hRegB).mp hRelB
      subst e
      by_cases hRegC :
          ∃ r1 r2, c = SmtValue.RegLan r1 ∧ f = SmtValue.RegLan r2
      · rcases hRegC with ⟨r1, r2, rfl, rfl⟩
        cases a <;> cases b <;>
          simp [__smtx_model_eval_str_replace_all,
            RuleProofs.smt_value_rel_refl]
      · have hCEq := (RuleProofs.smt_value_rel_iff_eq c f hRegC).mp hRelC
        subst f
        exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_len_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_len a) (__smtx_model_eval_str_len b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_len, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_to_code_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_to_code a) (__smtx_model_eval_str_to_code b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_to_code, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_to_int_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_to_int a) (__smtx_model_eval_str_to_int b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_to_int, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_from_code_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_from_code a) (__smtx_model_eval_str_from_code b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_from_code, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_from_int_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_from_int a) (__smtx_model_eval_str_from_int b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_from_int, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_sbv_to_int_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_sbv_to_int a) (__smtx_model_eval_sbv_to_int b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_sbv_to_int, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_bvashr_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_bvashr a b) (__smtx_model_eval_bvashr c d) := by
  intro hRelA hRelB
  by_cases hRegA :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ c = SmtValue.RegLan r2
  · rcases hRegA with ⟨r1, r2, rfl, rfl⟩
    cases b <;> cases d <;>
      simp [__smtx_model_eval_bvashr, __smtx_model_eval_bvlshr,
        __smtx_model_eval_bvnot, __smtx_model_eval_extract,
        __smtx_model_eval__, __smtx_model_eval_ite,
        RuleProofs.smt_value_rel_refl]
  · have hAEq := (RuleProofs.smt_value_rel_iff_eq a c hRegA).mp hRelA
    subst c
    by_cases hRegB :
        ∃ r1 r2, b = SmtValue.RegLan r1 ∧ d = SmtValue.RegLan r2
    · rcases hRegB with ⟨r1, r2, rfl, rfl⟩
      cases a <;>
        simp [__smtx_model_eval_bvashr, __smtx_model_eval_bvlshr,
          __smtx_model_eval_bvnot, __smtx_model_eval_extract,
          __smtx_model_eval__, __smtx_model_eval_ite,
          RuleProofs.smt_value_rel_refl]
    · have hBEq := (RuleProofs.smt_value_rel_iff_eq b d hRegB).mp hRelB
      subst d
      exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_and_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_and a b) (__smtx_model_eval_and c d) :=
  CongSupport.smt_value_rel_and_congr a b c d

theorem EvaluateProofInternal.smt_value_rel_model_eval_or_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_or a b) (__smtx_model_eval_or c d) :=
  CongSupport.smt_value_rel_or_congr a b c d

theorem EvaluateProofInternal.smt_value_rel_model_eval_imp_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_imp a b) (__smtx_model_eval_imp c d) := by
  intro hAC hBD
  unfold __smtx_model_eval_imp
  exact EvaluateProofInternal.smt_value_rel_model_eval_or_of_rel
    (__smtx_model_eval_not a) b (__smtx_model_eval_not c) d
    (EvaluateProofInternal.smt_value_rel_model_eval_not_of_rel a c hAC) hBD

theorem EvaluateProofInternal.smt_value_rel_model_eval_int_pow2_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_int_pow2 a) (__smtx_model_eval_int_pow2 b) := by
  intro hRel
  unfold RuleProofs.smt_value_rel at hRel ⊢
  cases a <;> cases b <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_int_pow2,
      native_veq] at hRel ⊢
  case Numeral n m =>
    subst m
    rfl

theorem EvaluateProofInternal.smt_value_rel_model_eval_int_log2_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_int_log2 a) (__smtx_model_eval_int_log2 b) := by
  intro hRel
  unfold RuleProofs.smt_value_rel at hRel ⊢
  cases a <;> cases b <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_int_log2,
      native_veq] at hRel ⊢
  case Numeral n m =>
    subst m
    rfl

theorem EvaluateProofInternal.smt_typeof_int_ispow2_formula_eq_bool
    (t : SmtTerm) :
    __smtx_typeof t = SmtType.Int ->
    __smtx_typeof
        (SmtTerm.and
          (SmtTerm.geq t (SmtTerm.Numeral 0))
          (SmtTerm.eq t
            (SmtTerm.int_pow2 (SmtTerm.int_log2 t)))) =
      SmtType.Bool := by
  intro hTy
  rw [typeof_and_eq, typeof_geq_eq, typeof_eq_eq,
    typeof_int_pow2_eq, typeof_int_log2_eq, hTy, __smtx_typeof.eq_2]
  simp [__smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq,
    __smtx_typeof_guard, native_ite, native_Teq]

theorem EvaluateProofInternal.smt_value_rel_boolean_eq
    (v : SmtValue) (b : Bool) :
    RuleProofs.smt_value_rel v (SmtValue.Boolean b) ->
    v = SmtValue.Boolean b := by
  intro hRel
  unfold RuleProofs.smt_value_rel at hRel
  cases v <;> simp [__smtx_model_eval_eq, native_veq] at hRel
  case Boolean b' =>
    cases b <;> cases b' <;> simp at hRel ⊢

theorem EvaluateProofInternal.smt_value_rel_numeral_eq
    (v : SmtValue) (n : native_Int) :
    RuleProofs.smt_value_rel v (SmtValue.Numeral n) ->
    v = SmtValue.Numeral n := by
  intro hRel
  exact (RuleProofs.smt_value_rel_iff_eq
    v (SmtValue.Numeral n) (by
      rintro ⟨r1, r2, _hv, hNum⟩
      cases hNum)).mp hRel

theorem EvaluateProofInternal.smt_value_rel_rational_eq
    (v : SmtValue) (q : native_Rat) :
    RuleProofs.smt_value_rel v (SmtValue.Rational q) ->
    v = SmtValue.Rational q := by
  intro hRel
  exact (RuleProofs.smt_value_rel_iff_eq
    v (SmtValue.Rational q) (by
      rintro ⟨r1, r2, _hv, hRat⟩
      cases hRat)).mp hRel

theorem EvaluateProofInternal.smt_value_rel_binary_eq
    (v : SmtValue) (w n : native_Int) :
    RuleProofs.smt_value_rel v (SmtValue.Binary w n) ->
    v = SmtValue.Binary w n := by
  intro hRel
  exact (RuleProofs.smt_value_rel_iff_eq
    v (SmtValue.Binary w n) (by
      rintro ⟨r1, r2, _hv, hBin⟩
      cases hBin)).mp hRel

theorem EvaluateProofInternal.smtx_typeof_binary_mod_nat_to_int
    (w : native_Nat) (n : native_Int) :
    __smtx_typeof
        (SmtTerm.Binary (native_nat_to_int w)
          (native_mod_total n (native_int_pow2 (native_nat_to_int w)))) =
      SmtType.BitVec w := by
  have hNN :
      __smtx_typeof
          (SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total n (native_int_pow2 (native_nat_to_int w)))) ≠
        SmtType.None := by
    unfold __smtx_typeof
    have hWidth :
        native_zleq 0 (native_nat_to_int w) = true := by
      simp [SmtEval.native_zleq, Smtm.native_nat_to_int]
    have hMod :
        native_zeq
            (native_mod_total n (native_int_pow2 (native_nat_to_int w)))
            (native_mod_total
              (native_mod_total n (native_int_pow2 (native_nat_to_int w)))
              (native_int_pow2 (native_nat_to_int w))) =
          true :=
      native_mod_total_canonical (native_nat_to_int w) n
    simp [SmtEval.native_and, hWidth, hMod, native_ite]
  simpa [SmtEval.native_int_to_nat, Smtm.native_nat_to_int]
    using
      TranslationProofs.smtx_typeof_binary_of_non_none
        (native_nat_to_int w)
        (native_mod_total n (native_int_pow2 (native_nat_to_int w))) hNN

theorem EvaluateProofInternal.smtx_typeof_binary_mod_of_nonneg
    (w n : native_Int)
    (hWidth : native_zleq 0 w = true) :
    __smtx_typeof
        (SmtTerm.Binary w
          (native_mod_total n (native_int_pow2 w))) =
      SmtType.BitVec (native_int_to_nat w) := by
  have hNN :
      __smtx_typeof
          (SmtTerm.Binary w
            (native_mod_total n (native_int_pow2 w))) ≠
        SmtType.None := by
    unfold __smtx_typeof
    have hMod :
        native_zeq
            (native_mod_total n (native_int_pow2 w))
            (native_mod_total
              (native_mod_total n (native_int_pow2 w))
              (native_int_pow2 w)) =
          true :=
      native_mod_total_canonical w n
    simp [SmtEval.native_and, hWidth, hMod, native_ite]
  exact
    TranslationProofs.smtx_typeof_binary_of_non_none
      w (native_mod_total n (native_int_pow2 w)) hNN

theorem EvaluateProofInternal.smtx_typeof_binary_of_nonneg_and_canonical
    (w n : native_Int)
    (hWidth : native_zleq 0 w = true)
    (hCanon :
      native_zeq n (native_mod_total n (native_int_pow2 w)) = true) :
    __smtx_typeof (SmtTerm.Binary w n) =
      SmtType.BitVec (native_int_to_nat w) := by
  have hNN :
      __smtx_typeof (SmtTerm.Binary w n) ≠ SmtType.None := by
    unfold __smtx_typeof
    simp [SmtEval.native_and, hWidth, hCanon, native_ite]
  exact TranslationProofs.smtx_typeof_binary_of_non_none w n hNN

theorem EvaluateProofInternal.smtx_typeof_binary_eq_bitvec_parts
    {w n : native_Int} {u : native_Nat}
    (hTy : __smtx_typeof (SmtTerm.Binary w n) = SmtType.BitVec u) :
    native_zleq 0 w = true ∧
      native_zeq n (native_mod_total n (native_int_pow2 w)) = true ∧
        native_int_to_nat w = u := by
  unfold __smtx_typeof at hTy
  cases hWidth : native_zleq 0 w <;>
    cases hCanon :
      native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
      simp [SmtEval.native_and, hWidth, hCanon, native_ite] at hTy
  all_goals
    try cases hTy
    simp

theorem EvaluateProofInternal.native_nat_to_int_of_int_to_nat_eq
    {w : native_Int} {u : native_Nat}
    (hWidth : native_zleq 0 w = true)
    (hNat : native_int_to_nat w = u) :
    w = native_nat_to_int u := by
  have hw0 : 0 <= w := by
    simpa [native_zleq, SmtEval.native_zleq] using hWidth
  have hToNat : Int.toNat w = u := by
    simpa [native_int_to_nat, SmtEval.native_int_to_nat] using hNat
  rw [← hToNat]
  simp [native_nat_to_int, Smtm.native_nat_to_int,
    Int.toNat_of_nonneg hw0]

theorem EvaluateProofInternal.model_eval_bitvec_term_binary
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (w : native_Nat)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w) :
    ∃ n : native_Int,
      __smtx_model_eval M (__eo_to_smt t) =
        SmtValue.Binary (native_nat_to_int w) n ∧
      0 <= n ∧ n < native_int_pow2 (native_nat_to_int w) := by
  have hNN : term_has_non_none_type (__eo_to_smt t) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.BitVec w := by
    simpa [hTy] using
      Smtm.smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt t) hNN
  rcases Smtm.bitvec_value_canonical hEvalTy with ⟨n, hv⟩
  have hWidth : native_zleq 0 (native_nat_to_int w) = true :=
    Smtm.bitvec_width_nonneg (by simpa [hv] using hEvalTy)
  have hMod :
      native_zeq n
          (native_mod_total n (native_int_pow2 (native_nat_to_int w))) =
        true :=
    Smtm.bitvec_payload_canonical (by simpa [hv] using hEvalTy)
  exact ⟨n, hv, Smtm.bitvec_payload_range_of_canonical hWidth hMod⟩

