module

public import Cpc.Proofs.RuleSupport.BvAbstractionMulMatcherSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionMulMatcherSupport

public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8000

open Eo SmtEval Smtm

namespace BvAbstraction
namespace Rule

def impTerm (a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b

def eqTerm (a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b

def bvBinTerm (op : UserOp) (a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp op) a) b

theorem imp_args_bool {a b : Term}
    (h : RuleProofs.eo_has_bool_type (impTerm a b)) :
    RuleProofs.eo_has_bool_type a ∧ RuleProofs.eo_has_bool_type b := by
  change __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at h
  have hNN : term_has_non_none_type
      (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [h]
    simp
  exact bool_binop_args_bool_of_non_none
    (typeof_imp_eq (__eo_to_smt a) (__eo_to_smt b)) hNN

theorem imp_bool_of_args {a b : Term}
    (ha : RuleProofs.eo_has_bool_type a)
    (hb : RuleProofs.eo_has_bool_type b) :
    RuleProofs.eo_has_bool_type (impTerm a b) := by
  change __smtx_typeof (__eo_to_smt a) = SmtType.Bool at ha
  change __smtx_typeof (__eo_to_smt b) = SmtType.Bool at hb
  change __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool
  rw [typeof_imp_eq]
  simp [ha, hb, native_ite, native_Teq]

theorem mul_operand_types (x s t : Term)
    (hEq : RuleProofs.eo_has_bool_type
      (eqTerm (bvBinTerm UserOp.bvmul x s) t)) :
    ∃ w : Nat,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type _ _ hEq with
    ⟨hSides, hOpNN⟩
  rcases bv_binop_args_of_non_none
      (show __smtx_typeof (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt s)) =
          __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt x))
            (__smtx_typeof (__eo_to_smt s)) by
        rw [__smtx_typeof.eq_def] <;> simp only)
      hOpNN with ⟨w, hxTy, hsTy⟩
  have hopTy : __smtx_typeof
      (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt s)) = SmtType.BitVec w := by
    rw [__smtx_typeof.eq_def]
    simp [__smtx_typeof_bv_op_2, hxTy, hsTy, native_ite, native_nateq]
  exact ⟨w, hxTy, hsTy, hSides.symm.trans hopTy⟩

theorem udiv_operand_types (x s t : Term)
    (hEq : RuleProofs.eo_has_bool_type
      (eqTerm (bvBinTerm UserOp.bvudiv x s) t)) :
    ∃ w : Nat,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type _ _ hEq with
    ⟨hSides, hOpNN⟩
  rcases bv_binop_args_of_non_none
      (show __smtx_typeof (SmtTerm.bvudiv (__eo_to_smt x) (__eo_to_smt s)) =
          __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt x))
            (__smtx_typeof (__eo_to_smt s)) by
        rw [__smtx_typeof.eq_def] <;> simp only)
      hOpNN with ⟨w, hxTy, hsTy⟩
  have hopTy : __smtx_typeof
      (SmtTerm.bvudiv (__eo_to_smt x) (__eo_to_smt s)) = SmtType.BitVec w := by
    rw [__smtx_typeof.eq_def]
    simp [__smtx_typeof_bv_op_2, hxTy, hsTy, native_ite, native_nateq]
  exact ⟨w, hxTy, hsTy, hSides.symm.trans hopTy⟩

theorem urem_operand_types (x s t : Term)
    (hEq : RuleProofs.eo_has_bool_type
      (eqTerm (bvBinTerm UserOp.bvurem x s) t)) :
    ∃ w : Nat,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type _ _ hEq with
    ⟨hSides, hOpNN⟩
  rcases bv_binop_args_of_non_none
      (show __smtx_typeof (SmtTerm.bvurem (__eo_to_smt x) (__eo_to_smt s)) =
          __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt x))
            (__smtx_typeof (__eo_to_smt s)) by
        rw [__smtx_typeof.eq_def] <;> simp only)
      hOpNN with ⟨w, hxTy, hsTy⟩
  have hopTy : __smtx_typeof
      (SmtTerm.bvurem (__eo_to_smt x) (__eo_to_smt s)) = SmtType.BitVec w := by
    rw [__smtx_typeof.eq_def]
    simp [__smtx_typeof_bv_op_2, hxTy, hsTy, native_ite, native_nateq]
  exact ⟨w, hxTy, hsTy, hSides.symm.trans hopTy⟩

theorem nested_mul_operand_types (x s ns t : Term)
    (hEq : RuleProofs.eo_has_bool_type
      (eqTerm (bvBinTerm UserOp.bvmul x
        (bvBinTerm UserOp.bvmul s ns)) t)) :
    ∃ w : Nat,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt ns) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w := by
  rcases mul_operand_types x (bvBinTerm UserOp.bvmul s ns) t hEq with
    ⟨w, hxTy, hInnerTy, htTy⟩
  change __smtx_typeof
    (SmtTerm.bvmul (__eo_to_smt s) (__eo_to_smt ns)) = SmtType.BitVec w at hInnerTy
  have hInnerNN : term_has_non_none_type
      (SmtTerm.bvmul (__eo_to_smt s) (__eo_to_smt ns)) := by
    unfold term_has_non_none_type
    rw [hInnerTy]
    simp
  rcases bv_binop_args_of_non_none
      (show __smtx_typeof (SmtTerm.bvmul (__eo_to_smt s) (__eo_to_smt ns)) =
          __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt s))
            (__smtx_typeof (__eo_to_smt ns)) by
        rw [__smtx_typeof.eq_def] <;> simp only)
      hInnerNN with ⟨v, hsTy, hnsTy⟩
  have hInnerTy' : __smtx_typeof
      (SmtTerm.bvmul (__eo_to_smt s) (__eo_to_smt ns)) = SmtType.BitVec v := by
    rw [__smtx_typeof.eq_def]
    simp [__smtx_typeof_bv_op_2, hsTy, hnsTy, native_ite, native_nateq]
  have hvw : v = w := by
    rw [hInnerTy] at hInnerTy'
    exact SmtType.BitVec.inj hInnerTy'.symm
  subst v
  exact ⟨w, hxTy, hsTy, hnsTy, htTy⟩

theorem simple_mul_bool (x s t l : Term) (w : Nat)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hl : RuleProofs.eo_has_bool_type l) :
    RuleProofs.eo_has_bool_type
      (impTerm (eqTerm (bvBinTerm UserOp.bvmul x s) t) l) := by
  have hopTy : __smtx_typeof
      (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt s)) = SmtType.BitVec w := by
    rw [__smtx_typeof.eq_def]
    simp [__smtx_typeof_bv_op_2, hxTy, hsTy, native_ite, native_nateq]
  have hEq := RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (bvBinTerm UserOp.bvmul x s) t (hopTy.trans htTy.symm) (by
      change __smtx_typeof
        (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt s)) ≠ SmtType.None
      rw [hopTy]
      simp)
  exact imp_bool_of_args hEq hl

theorem width_guard_sound (x : Term) (w : Nat)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hGuard : __eo_gt (__bv_bitwidth (__eo_typeof x)) (Term.Numeral 2) =
      Term.Boolean true) :
    3 ≤ w := by
  rw [Matcher.bitwidth_typeof_of_smt_type x w hxTy] at hGuard
  simp [__eo_gt, native_zlt, SmtEval.native_nat_to_int] at hGuard
  have hw : 2 < w := by exact_mod_cast hGuard
  omega

theorem nested_mul_interprets_of_simple (M : SmtModel)
    (x s ns t l : Term) {w : Nat} (xb sb tb : BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (hns : __smtx_model_eval M (__eo_to_smt ns) = bvValue (1#w))
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (hTargetBool : RuleProofs.eo_has_bool_type
      (impTerm (eqTerm (bvBinTerm UserOp.bvmul x
        (bvBinTerm UserOp.bvmul s ns)) t) l))
    (h : eo_interprets M
      (impTerm (eqTerm (bvBinTerm UserOp.bvmul x s) t) l) true) :
    eo_interprets M
      (impTerm (eqTerm (bvBinTerm UserOp.bvmul x
        (bvBinTerm UserOp.bvmul s ns)) t) l) true := by
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at h ⊢
  cases h with
  | intro_true _ hEval =>
      refine smt_interprets.intro_true M _ hTargetBool ?_
      change __smtx_model_eval_imp
        (__smtx_model_eval_eq
          (__smtx_model_eval_bvmul
            (__smtx_model_eval M (__eo_to_smt x))
            (__smtx_model_eval_bvmul
              (__smtx_model_eval M (__eo_to_smt s))
              (__smtx_model_eval M (__eo_to_smt ns))))
          (__smtx_model_eval M (__eo_to_smt t)))
        (__smtx_model_eval M (__eo_to_smt l)) = SmtValue.Boolean true
      change __smtx_model_eval_imp
        (__smtx_model_eval_eq
          (__smtx_model_eval_bvmul
            (__smtx_model_eval M (__eo_to_smt x))
            (__smtx_model_eval M (__eo_to_smt s)))
          (__smtx_model_eval M (__eo_to_smt t)))
        (__smtx_model_eval M (__eo_to_smt l)) = SmtValue.Boolean true at hEval
      rw [hx, hs, hns, ht, eval_bvmul_bvValue,
        eval_bvmul_bvValue, BitVec.mul_one]
      rw [hx, hs, ht, eval_bvmul_bvValue] at hEval
      exact hEval

theorem sound_udiv_match (M : SmtModel) (hM : model_total_typed M)
    (x s t l : Term)
    (hBool : RuleProofs.eo_has_bool_type
      (impTerm (eqTerm (bvBinTerm UserOp.bvudiv x s) t) l))
    (hGuard : __eo_gt (__bv_bitwidth (__eo_typeof x)) (Term.Numeral 2) =
      Term.Boolean true)
    (hMatch : __bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (impTerm (eqTerm (bvBinTerm UserOp.bvudiv x s) t) l) true := by
  have hEq := (imp_args_bool hBool).1
  rcases udiv_operand_types x s t hEq with ⟨w, hxTy, hsTy, htTy⟩
  obtain ⟨xb, hx⟩ := eval_as_bvValue M hM x w hxTy
  obtain ⟨sb, hs⟩ := eval_as_bvValue M hM s w hsTy
  obtain ⟨tb, ht⟩ := eval_as_bvValue M hM t w htTy
  have hw := width_guard_sound x w hxTy hGuard
  exact Matcher.matcher_udiv_sound M hM x s t l w xb sb tb hw
    hxTy hsTy htTy hx hs ht hBool hMatch

theorem sound_urem_match (M : SmtModel) (hM : model_total_typed M)
    (x s t l : Term)
    (hBool : RuleProofs.eo_has_bool_type
      (impTerm (eqTerm (bvBinTerm UserOp.bvurem x s) t) l))
    (hGuard : __eo_gt (__bv_bitwidth (__eo_typeof x)) (Term.Numeral 2) =
      Term.Boolean true)
    (hMatch : __bv_abstraction_lemma_urem x s t l = Term.Boolean true) :
    eo_interprets M
      (impTerm (eqTerm (bvBinTerm UserOp.bvurem x s) t) l) true := by
  have hEq := (imp_args_bool hBool).1
  rcases urem_operand_types x s t hEq with ⟨w, hxTy, hsTy, htTy⟩
  obtain ⟨xb, hx⟩ := eval_as_bvValue M hM x w hxTy
  obtain ⟨sb, hs⟩ := eval_as_bvValue M hM s w hsTy
  obtain ⟨tb, ht⟩ := eval_as_bvValue M hM t w htTy
  have hw := width_guard_sound x w hxTy hGuard
  exact Matcher.matcher_urem1_sound M hM x s t l w xb sb tb hw
    hxTy hsTy htTy hx hs ht hBool hMatch

theorem sound_nested_mul_match (M : SmtModel) (hM : model_total_typed M)
    (x s ns t l : Term)
    (hBool : RuleProofs.eo_has_bool_type
      (impTerm (eqTerm (bvBinTerm UserOp.bvmul x
        (bvBinTerm UserOp.bvmul s ns)) t) l))
    (hGuard : __eo_gt (__bv_bitwidth (__eo_typeof x)) (Term.Numeral 2) =
      Term.Boolean true)
    (hOne : __eo_eq ns
      (__eo_to_bin (__bv_bitwidth (__eo_typeof ns)) (Term.Numeral 1)) =
      Term.Boolean true)
    (hMatch : __bv_abstraction_lemma_mul x s t l = Term.Boolean true) :
    eo_interprets M
      (impTerm (eqTerm (bvBinTerm UserOp.bvmul x
        (bvBinTerm UserOp.bvmul s ns)) t) l) true := by
  rcases imp_args_bool hBool with ⟨hEq, hl⟩
  rcases nested_mul_operand_types x s ns t hEq with
    ⟨w, hxTy, hsTy, hnsTy, htTy⟩
  have hw := width_guard_sound x w hxTy hGuard
  have hnsEq := Matcher.validated_one (by omega) hnsTy hOne
  subst ns
  obtain ⟨xb, hx⟩ := eval_as_bvValue M hM x w hxTy
  obtain ⟨sb, hs⟩ := eval_as_bvValue M hM s w hsTy
  obtain ⟨tb, ht⟩ := eval_as_bvValue M hM t w htTy
  have hSimpleBool := simple_mul_bool x s t l w hxTy hsTy htTy hl
  have hSimple := Matcher.matcher_mul_sound M hM x s t l w xb sb tb hw
    hxTy hsTy htTy hx hs ht hSimpleBool hMatch
  exact nested_mul_interprets_of_simple M x s (Dsl.constTerm w 1) t l
    xb sb tb hx hs (Dsl.eval_constTerm_one M w (by omega)) ht hBool hSimple

theorem bv_abstraction_match_sound (M : SmtModel) (hM : model_total_typed M)
    (F : Term) (hBool : RuleProofs.eo_has_bool_type F)
    (hMatch : __bv_abstraction_lemma F = Term.Boolean true) :
    eo_interprets M F true := by
  fun_cases __bv_abstraction_lemma F
  all_goals simp only [__bv_abstraction_lemma] at hMatch
  case case1 => simp at hMatch
  case case2 x s ns t l =>
    rcases Matcher.eo_and_eq_true_args _ _ hMatch with ⟨hGuard, hRest⟩
    rcases Matcher.eo_and_eq_true_args _ _ hRest with ⟨hOne, hRule⟩
    exact sound_nested_mul_match M hM x s ns t l hBool hGuard hOne hRule
  case case3 x s t l =>
    rcases Matcher.eo_and_eq_true_args _ _ hMatch with ⟨hGuard, hRule⟩
    exact sound_udiv_match M hM x s t l hBool hGuard hRule
  case case4 x s t l =>
    rcases Matcher.eo_and_eq_true_args _ _ hMatch with ⟨hGuard, hRule⟩
    exact sound_urem_match M hM x s t l hBool hGuard hRule
  case case5 => simp at hMatch

theorem match_eq_true_of_program_ne_stuck (F : Term)
    (h : __eo_prog_bv_abstraction F ≠ Term.Stuck) :
    __bv_abstraction_lemma F = Term.Boolean true := by
  generalize hm : __bv_abstraction_lemma F = m at h ⊢
  cases m <;> cases F <;>
    simp [__eo_prog_bv_abstraction, __eo_requires, hm, native_ite,
      native_teq, native_not,
      SmtEval.native_not] at h ⊢
  all_goals assumption

theorem program_eq_input_of_match (F : Term)
    (h : __bv_abstraction_lemma F = Term.Boolean true) :
    __eo_prog_bv_abstraction F = F := by
  cases F <;> simp only [__eo_prog_bv_abstraction]
  all_goals rw [h]
  all_goals rfl

end Rule
end BvAbstraction
