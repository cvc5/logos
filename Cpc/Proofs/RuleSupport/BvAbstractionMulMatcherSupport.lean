module

public import Cpc.Proofs.RuleSupport.BvAbstractionUdivMatcherSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionUdivMatcherSupport

public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8000

open Eo SmtEval Smtm

namespace BvAbstraction
namespace Matcher

theorem typeof_extract00 {a : Term} {w : Nat} (hw : 0 < w)
    (ha : __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w) :
    __smtx_typeof (SmtTerm.extract (SmtTerm.Numeral 0) (SmtTerm.Numeral 0)
      (__eo_to_smt a)) = SmtType.BitVec 1 := by
  rw [typeof_extract_eq, ha]
  simp [__smtx_typeof_extract, native_ite, native_zleq, native_zlt,
    native_zplus, native_zneg, SmtEval.native_nat_to_int, native_int_to_nat, hw]

theorem eval_extract00_bvValue {w : Nat} (x : BitVec w) :
    __smtx_model_eval_extract (SmtValue.Numeral 0) (SmtValue.Numeral 0)
      (bvValue x) = bvValue (x.setWidth 1) := by
  simp [__smtx_model_eval_extract, bvValue, native_zplus, native_zneg,
    native_mod_total, native_binary_extract, native_div_total,
    native_int_pow2, native_zexp_total, SmtEval.native_nat_to_int,
    BitVec.toNat_setWidth]

theorem to_smt_type_tuple_ne_bitvec (U V : SmtType) (w : Nat) :
    __eo_to_smt_type_tuple U V ≠ SmtType.BitVec w := by
  cases V <;> simp [__eo_to_smt_type_tuple, native_ite]
  case Datatype s dd =>
    cases dd with
    | nil => simp [__eo_to_smt_type_tuple]
    | cons s2 d rest =>
      cases d with
      | null => simp [__eo_to_smt_type_tuple]
      | sum c tail =>
        cases tail <;> cases rest <;>
          simp [__eo_to_smt_type_tuple, native_ite]
        split <;> simp_all

theorem bitwidth_typeof_of_smt_type (x : Term) (w : Nat)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __bv_bitwidth (__eo_typeof x) = Term.Numeral w := by
  have hType := TranslationProofs.eo_to_smt_type_typeof_of_smt_type x hx (by simp)
  generalize hT : __eo_typeof x = T at hType ⊢
  fun_cases __eo_to_smt_type T
  all_goals simp only [__eo_to_smt_type] at hType
  all_goals simp [__bv_bitwidth, __smtx_typeof_guard, native_ite, native_Teq,
    native_zleq, SmtEval.native_nat_to_int, native_int_to_nat] at hType ⊢
  all_goals try { split at hType <;> simp_all }
  case case4 =>
    split at hType <;> try simp_all
    split at hType <;> simp_all
  case case6 =>
    split at hType <;> try simp_all
    split at hType <;> simp_all
  case case9 n =>
    by_cases hn : 0 ≤ n
    · simp [hn] at hType
      have hnNat : Int.toNat n = w := hType
      calc
        n = (Int.toNat n : Int) := (Int.toNat_of_nonneg hn).symm
        _ = (w : Int) := congrArg Int.ofNat hnNat
    · simp [hn] at hType
  case case12 =>
    split at hType <;> try simp_all
    split at hType <;> simp_all
  case case15 =>
    split at hType
    · exact to_smt_type_tuple_ne_bitvec _ _ _ hType
    · simp_all

section

variable (M : SmtModel) (hM : model_total_typed M)
variable (x s t l : Term) (w : Nat) (xb sb tb : BitVec w)
variable (hw : 3 ≤ w)
variable (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
variable (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
variable (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
variable (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
variable (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
variable (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
variable (hBool : RuleProofs.eo_has_bool_type
  (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l))

include hM hw hxTy hsTy htTy hx hs ht hBool

theorem matcher_mul19_sound
    (hmatch : __eo_l_18___bv_abstraction_lemma_mul x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l) true := by
  fun_cases __eo_l_18___bv_abstraction_lemma_mul x s t l
  all_goals simp only [__eo_l_18___bv_abstraction_lemma_mul] at hmatch
  all_goals try { simp [__eo_l_19___bv_abstraction_lemma_mul] at hmatch }
  case case5 px px2 ps pt zero hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hZero⟩
      rcases aliases4 hAliases with ⟨hpx, hpx2, hps, hpt⟩
      subst px; subst px2; subst ps; subst pt
      let p : Raw.Pred := .not (.eq .x
        (.not (.shl .x (.add .s (.add .t (.lit zero))))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_mul_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hzTy := hLits zero (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have ez := validated_zero hzTy hZero
      subst zero
      change eo_interprets M
        ((Dsl.mulPred (.not (.eq .x
          (.not (.shl .x (.add .s (.add .t .zero))))))).term w x s t) true
      apply Dsl.sound_mul_pred
        (q := .not (.eq .x (.not (.shl .x (.add .s (.add .t .zero))))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      simpa [hAnte] using mul19 hw xb sb
    · exact False.elim (by simp [__eo_l_19___bv_abstraction_lemma_mul] at hFallback)

theorem matcher_mul18_sound
    (hmatch : __eo_l_17___bv_abstraction_lemma_mul x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l) true := by
  fun_cases __eo_l_17___bv_abstraction_lemma_mul x s t l
  all_goals simp only [__eo_l_17___bv_abstraction_lemma_mul] at hmatch
  all_goals try { simp [__eo_l_18___bv_abstraction_lemma_mul,
    __eo_l_19___bv_abstraction_lemma_mul] at hmatch }
  case case5 pt one px ps zero1 zero2 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases3 hAliases with ⟨hpt, hpx, hps⟩
      subst pt; subst px; subst ps
      rcases eo_and_eq_true_args _ _ hVals with ⟨hOne, hZeros⟩
      rcases eo_and_eq_true_args _ _ hZeros with ⟨hZero1, hZero2⟩
      let p : Raw.Pred := .not (.eq .t
        (.or (.lit one) (.or (.add .x (.add .s (.lit zero1))) (.lit zero2))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_mul_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hOneTy := hLits one (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hZero1Ty := hLits zero1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hZero2Ty := hLits zero2 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have eOne := validated_one (by omega) hOneTy hOne
      have eZero1 := validated_zero hZero1Ty hZero1
      have eZero2 := validated_zero hZero2Ty hZero2
      subst one; subst zero1; subst zero2
      change eo_interprets M
        ((Dsl.mulPred (.not (.eq .t
          (.or .one (.or (.add .x (.add .s .zero)) .zero))))).term w x s t) true
      apply Dsl.sound_mul_pred
        (q := .not (.eq .t (.or .one (.or (.add .x (.add .s .zero)) .zero))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      simpa [hAnte] using mul18 hw xb sb
    · exact matcher_mul19_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_mul19_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_mul17_sound
    (hmatch : __eo_l_16___bv_abstraction_lemma_mul x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l) true := by
  fun_cases __eo_l_16___bv_abstraction_lemma_mul x s t l
  all_goals simp only [__eo_l_16___bv_abstraction_lemma_mul] at hmatch
  all_goals try { simp [__eo_l_17___bv_abstraction_lemma_mul,
    __eo_l_18___bv_abstraction_lemma_mul, __eo_l_19___bv_abstraction_lemma_mul] at hmatch }
  case case5 ps one ps2 px pt zero hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases4 hAliases with ⟨hps, hps2, hpx, hpt⟩
      subst ps; subst ps2; subst px; subst pt
      rcases eo_and_eq_true_args _ _ hVals with ⟨hOne, hZero⟩
      let p : Raw.Pred := .not (.eq .s
        (.add (.lit one) (.add (.shl .s (.sub .x .t)) (.lit zero))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_mul_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hOneTy := hLits one (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hZeroTy := hLits zero (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have eOne := validated_one (by omega) hOneTy hOne
      have eZero := validated_zero hZeroTy hZero
      subst one; subst zero
      change eo_interprets M
        ((Dsl.mulPred (.not (.eq .s
          (.add .one (.add (.shl .s (.sub .x .t)) .zero))))).term w x s t) true
      apply Dsl.sound_mul_pred
        (q := .not (.eq .s (.add .one (.add (.shl .s (.sub .x .t)) .zero))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      simpa [hAnte] using mul17 hw xb sb
    · exact matcher_mul18_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_mul18_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_mul16_sound
    (hmatch : __eo_l_15___bv_abstraction_lemma_mul x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l) true := by
  fun_cases __eo_l_15___bv_abstraction_lemma_mul x s t l
  all_goals simp only [__eo_l_15___bv_abstraction_lemma_mul] at hmatch
  all_goals try { simp at hmatch }
  case case5 ps one ps2 pt px hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hOne⟩
      rcases aliases4 hAliases with ⟨hps, hps2, hpt, hpx⟩
      subst ps; subst ps2; subst pt; subst px
      let p : Raw.Pred := .not (.eq .s (.sub (.lit one) (.shl .s (.sub .t .x))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_mul_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hOneTy := hLits one (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have eOne := validated_one (by omega) hOneTy hOne
      subst one
      change eo_interprets M
        ((Dsl.mulPred (.not (.eq .s (.sub .one (.shl .s (.sub .t .x)))))).term
          w x s t) true
      apply Dsl.sound_mul_pred
        (q := .not (.eq .s (.sub .one (.shl .s (.sub .t .x)))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      simpa [hAnte] using mul16 hw xb sb
    · exact matcher_mul17_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_mul17_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_mul15_sound
    (hmatch : __eo_l_14___bv_abstraction_lemma_mul x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l) true := by
  fun_cases __eo_l_14___bv_abstraction_lemma_mul x s t l
  all_goals simp only [__eo_l_14___bv_abstraction_lemma_mul] at hmatch
  all_goals try { simp at hmatch }
  case case5 ps one ps2 pt px zero hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases4 hAliases with ⟨hps, hps2, hpt, hpx⟩
      subst ps; subst ps2; subst pt; subst px
      rcases eo_and_eq_true_args _ _ hVals with ⟨hOne, hZero⟩
      let p : Raw.Pred := .not (.eq .s
        (.add (.lit one) (.add (.shl .s (.sub .t .x)) (.lit zero))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_mul_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hOneTy := hLits one (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hZeroTy := hLits zero (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have eOne := validated_one (by omega) hOneTy hOne
      have eZero := validated_zero hZeroTy hZero
      subst one; subst zero
      change eo_interprets M
        ((Dsl.mulPred (.not (.eq .s
          (.add .one (.add (.shl .s (.sub .t .x)) .zero))))).term w x s t) true
      apply Dsl.sound_mul_pred
        (q := .not (.eq .s (.add .one (.add (.shl .s (.sub .t .x)) .zero))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      simpa [hAnte] using mul15 hw xb sb
    · exact matcher_mul16_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_mul16_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_mul14_sound
    (hmatch : __eo_l_13___bv_abstraction_lemma_mul x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l) true := by
  fun_cases __eo_l_13___bv_abstraction_lemma_mul x s t l
  all_goals simp only [__eo_l_13___bv_abstraction_lemma_mul] at hmatch
  all_goals try { simp at hmatch }
  case case5 px one px2 ps pt hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hOne⟩
      rcases aliases4 hAliases with ⟨hpx, hpx2, hps, hpt⟩
      subst px; subst px2; subst ps; subst pt
      let p : Raw.Pred := .not (.eq .x (.sub (.lit one) (.shl .x (.sub .s .t))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_mul_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hOneTy := hLits one (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have eOne := validated_one (by omega) hOneTy hOne
      subst one
      change eo_interprets M
        ((Dsl.mulPred (.not (.eq .x (.sub .one (.shl .x (.sub .s .t)))))).term
          w x s t) true
      apply Dsl.sound_mul_pred
        (q := .not (.eq .x (.sub .one (.shl .x (.sub .s .t)))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      simpa [hAnte] using mul14 hw xb sb
    · exact matcher_mul15_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_mul15_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_mul13_sound
    (hmatch : __eo_l_12___bv_abstraction_lemma_mul x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l) true := by
  fun_cases __eo_l_12___bv_abstraction_lemma_mul x s t l
  all_goals simp only [__eo_l_12___bv_abstraction_lemma_mul] at hmatch
  all_goals try { simp at hmatch }
  case case5 px px2 ps pt zero one hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases4 hAliases with ⟨hpx, hpx2, hps, hpt⟩
      subst px; subst px2; subst ps; subst pt
      rcases eo_and_eq_true_args _ _ hVals with ⟨hZero, hOne⟩
      let p : Raw.Pred := .not (.eq .x
        (.sub (.shl .x (.add .s (.add .t (.lit zero)))) (.lit one)))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_mul_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hZeroTy := hLits zero (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hOneTy := hLits one (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have eZero := validated_zero hZeroTy hZero
      have eOne := validated_one (by omega) hOneTy hOne
      subst zero; subst one
      change eo_interprets M
        ((Dsl.mulPred (.not (.eq .x
          (.sub (.shl .x (.add .s (.add .t .zero))) .one)))).term w x s t) true
      apply Dsl.sound_mul_pred
        (q := .not (.eq .x (.sub (.shl .x (.add .s (.add .t .zero))) .one)))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      simpa [hAnte] using mul13 hw xb sb
    · exact matcher_mul14_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_mul14_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_mul12_sound
    (hmatch : __eo_l_11___bv_abstraction_lemma_mul x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l) true := by
  fun_cases __eo_l_11___bv_abstraction_lemma_mul x s t l
  all_goals simp only [__eo_l_11___bv_abstraction_lemma_mul] at hmatch
  all_goals try { simp at hmatch }
  case case5 pt one px ps zero1 zero2 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases3 hAliases with ⟨hpt, hpx, hps⟩
      subst pt; subst px; subst ps
      rcases eo_and_eq_true_args _ _ hVals with ⟨hOne, hZeros⟩
      rcases eo_and_eq_true_args _ _ hZeros with ⟨hZero1, hZero2⟩
      let p : Raw.Pred := .not (.eq .t
        (.or (.not (.lit one)) (.or (.xor .x (.xor .s (.lit zero1))) (.lit zero2))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_mul_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hOneTy := hLits one (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hZero1Ty := hLits zero1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hZero2Ty := hLits zero2 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have eOne := validated_one (by omega) hOneTy hOne
      have eZero1 := validated_zero hZero1Ty hZero1
      have eZero2 := validated_zero hZero2Ty hZero2
      subst one; subst zero1; subst zero2
      change eo_interprets M
        ((Dsl.mulPred (.not (.eq .t
          (.or (.not .one) (.or (.xor .x (.xor .s .zero)) .zero))))).term w x s t) true
      apply Dsl.sound_mul_pred
        (q := .not (.eq .t (.or (.not .one) (.or (.xor .x (.xor .s .zero)) .zero))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      simpa [hAnte] using mul12 hw xb sb
    · exact matcher_mul13_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_mul13_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_mul11_sound
    (hmatch : __eo_l_10___bv_abstraction_lemma_mul x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l) true := by
  fun_cases __eo_l_10___bv_abstraction_lemma_mul x s t l
  all_goals simp only [__eo_l_10___bv_abstraction_lemma_mul] at hmatch
  all_goals try { simp at hmatch }
  case case5 pt one px ps zero1 zero2 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases3 hAliases with ⟨hpt, hpx, hps⟩
      subst pt; subst px; subst ps
      rcases eo_and_eq_true_args _ _ hVals with ⟨hOne, hZeros⟩
      rcases eo_and_eq_true_args _ _ hZeros with ⟨hZero1, hZero2⟩
      let p : Raw.Pred := .not (.eq .t
        (.or (.lit one) (.or (.not (.xor .x (.xor .s (.lit zero1)))) (.lit zero2))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_mul_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hOneTy := hLits one (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hZero1Ty := hLits zero1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hZero2Ty := hLits zero2 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have eOne := validated_one (by omega) hOneTy hOne
      have eZero1 := validated_zero hZero1Ty hZero1
      have eZero2 := validated_zero hZero2Ty hZero2
      subst one; subst zero1; subst zero2
      change eo_interprets M
        ((Dsl.mulPred (.not (.eq .t
          (.or .one (.or (.not (.xor .x (.xor .s .zero))) .zero))))).term w x s t) true
      apply Dsl.sound_mul_pred
        (q := .not (.eq .t (.or .one (.or (.not (.xor .x (.xor .s .zero))) .zero))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      simpa [hAnte] using mul11 hw xb sb
    · exact matcher_mul12_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_mul12_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_mul10_sound
    (hmatch : __eo_l_9___bv_abstraction_lemma_mul x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l) true := by
  fun_cases __eo_l_9___bv_abstraction_lemma_mul x s t l
  all_goals simp only [__eo_l_9___bv_abstraction_lemma_mul] at hmatch
  all_goals try { simp at hmatch }
  case case5 px one px2 ps pt zero1 zero2 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases4 hAliases with ⟨hpx, hpx2, hps, hpt⟩
      subst px; subst px2; subst ps; subst pt
      rcases eo_and_eq_true_args _ _ hVals with ⟨hOne, hZeros⟩
      rcases eo_and_eq_true_args _ _ hZeros with ⟨hZero1, hZero2⟩
      let p : Raw.Pred := .not (.eq .x
        (.xor (.lit one)
          (.xor (.shl .x (.xor .s (.xor .t (.lit zero1)))) (.lit zero2))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_mul_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hOneTy := hLits one (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hZero1Ty := hLits zero1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hZero2Ty := hLits zero2 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have eOne := validated_one (by omega) hOneTy hOne
      have eZero1 := validated_zero hZero1Ty hZero1
      have eZero2 := validated_zero hZero2Ty hZero2
      subst one; subst zero1; subst zero2
      change eo_interprets M
        ((Dsl.mulPred (.not (.eq .x
          (.xor .one (.xor (.shl .x (.xor .s (.xor .t .zero))) .zero))))).term
          w x s t) true
      apply Dsl.sound_mul_pred
        (q := .not (.eq .x
          (.xor .one (.xor (.shl .x (.xor .s (.xor .t .zero))) .zero))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      simpa [hAnte] using mul10 hw xb sb
    · exact matcher_mul11_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_mul11_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_mul9_sound
    (hmatch : __eo_l_8___bv_abstraction_lemma_mul x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l) true := by
  fun_cases __eo_l_8___bv_abstraction_lemma_mul x s t l
  all_goals simp only [__eo_l_8___bv_abstraction_lemma_mul] at hmatch
  all_goals try { simp at hmatch }
  case case5 pt one px ps one2 ones1 ones2 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases4 hAliases with ⟨hpt, hpx, hps, hOne2⟩
      rw [hpt] at hBool ⊢
      subst pt; subst one
      rw [← hOne2] at hBool hVals ⊢
      rcases eo_and_eq_true_args _ _ hVals with ⟨hOne, hOnesVals⟩
      rcases eo_and_eq_true_args _ _ hOnesVals with ⟨hOnes1, hOnes2⟩
      let p : Raw.Pred := .uge .t
        (.and (.lit ps)
          (.and (.lshr (.and .x (.and .s (.lit px))) (.lit ps)) (.lit one2)))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_mul_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hOneTy := hLits ps (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hOnes1Ty := hLits px (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hOnes2Ty := hLits one2 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have eOne := validated_one (by omega) hOneTy hOne
      have eOnes1 := validated_ones hOnes1Ty hOnes1
      have eOnes2 := validated_ones hOnes2Ty hOnes2
      rw [eOne] at hBool ⊢
      subst px; subst one2
      change eo_interprets M
        ((Dsl.mulPred (.uge .t
          (.and .one (.and (.lshr (.and .x (.and .s .ones)) .one) .ones)))).term
          w x s t) true
      apply Dsl.sound_mul_pred
        (q := .uge .t
          (.and .one (.and (.lshr (.and .x (.and .s .ones)) .one) .ones)))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply decide_eq_true
      rw [← hAnte, BitVec.neg_one_eq_allOnes, BitVec.and_allOnes,
        BitVec.and_allOnes]
      have honeNat : (1#w).toNat = 1 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        exact Nat.one_lt_two_pow (by omega)
      rw [honeNat]
      exact mul9' hw xb sb
    · exact matcher_mul10_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_mul10_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_mul8_sound
    (hmatch : __eo_l_7___bv_abstraction_lemma_mul x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l) true := by
  fun_cases __eo_l_7___bv_abstraction_lemma_mul x s t l
  all_goals simp only [__eo_l_7___bv_abstraction_lemma_mul] at hmatch
  all_goals try { simp at hmatch }
  case case5 ps ps2 px one pt ones hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases4 hAliases with ⟨hps, hps2, hpx, hpt⟩
      rw [hps] at hBool ⊢
      subst ps; subst ps2; subst one
      rcases eo_and_eq_true_args _ _ hVals with ⟨hOne, hOnes⟩
      let p : Raw.Pred := .eq .s
        (.shl .s (.and .x (.and (.lshr (.lit px) .t) (.lit pt))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_mul_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hOneTy := hLits px (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hOnesTy := hLits pt (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have eOne := validated_one (by omega) hOneTy hOne
      have eOnes := validated_ones hOnesTy hOnes
      subst px; subst pt
      change eo_interprets M
        ((Dsl.mulPred (.eq .s
          (.shl .s (.and .x (.and (.lshr .one .t) .ones))))).term w x s t) true
      apply Dsl.sound_mul_pred
        (q := .eq .s (.shl .s (.and .x (.and (.lshr .one .t) .ones))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply decide_eq_true
      rw [BitVec.neg_one_eq_allOnes, BitVec.and_allOnes]
      simpa [hAnte] using mul8 (by omega) xb sb
    · exact matcher_mul9_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_mul9_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_mul7_sound
    (hmatch : __eo_l_6___bv_abstraction_lemma_mul x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l) true := by
  fun_cases __eo_l_6___bv_abstraction_lemma_mul x s t l
  all_goals simp only [__eo_l_6___bv_abstraction_lemma_mul] at hmatch
  all_goals try { simp at hmatch }
  case case5 pt ps one zero pt2 px hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases4 hAliases with ⟨hpt, hps, hpt2, hpx⟩
      subst pt; subst ps; subst pt2; subst px
      rcases eo_and_eq_true_args _ _ hVals with ⟨hOne, hZero⟩
      let p : Raw.Pred := .not (.eq .t
        (.shl (.or .s (.or (.lit one) (.lit zero))) (.shl .t .x)))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_mul_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hOneTy := hLits one (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hZeroTy := hLits zero (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have eOne := validated_one (by omega) hOneTy hOne
      have eZero := validated_zero hZeroTy hZero
      subst one; subst zero
      change eo_interprets M
        ((Dsl.mulPred (.not (.eq .t
          (.shl (.or .s (.or .one .zero)) (.shl .t .x))))).term w x s t) true
      apply Dsl.sound_mul_pred
        (q := .not (.eq .t (.shl (.or .s (.or .one .zero)) (.shl .t .x))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      simpa [hAnte] using mul7 hw xb sb
    · exact matcher_mul8_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_mul8_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_mul6_sound
    (hmatch : __eo_l_5___bv_abstraction_lemma_mul x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l) true := by
  fun_cases __eo_l_5___bv_abstraction_lemma_mul x s t l
  all_goals simp only [__eo_l_5___bv_abstraction_lemma_mul] at hmatch
  all_goals try { simp at hmatch }
  case case5 px pt ones ps pt2 zero w1 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases4 hAliases with ⟨hpx, hpt, hps, hpt2⟩
      subst px; subst pt; subst ps; subst pt2
      rcases eo_and_eq_true_args _ _ hVals with ⟨hOnes, hZero⟩
      let p : Raw.Pred := .not (.eq
        (.and .x (.and .t (.lit ones)))
        (.or .s (.or (.not .t) (.lit zero))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_mul_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hOnesTy := hLits ones (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hZeroTy := hLits zero (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have eOnes := validated_ones hOnesTy hOnes
      have eZero := validated_zero hZeroTy hZero
      subst ones; subst zero
      change eo_interprets M
        ((Dsl.mulPred (.not (.eq (.and .x (.and .t .ones))
          (.or .s (.or (.not .t) .zero))))).term w x s t) true
      apply Dsl.sound_mul_pred
        (q := .not (.eq (.and .x (.and .t .ones))
          (.or .s (.or (.not .t) .zero))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      rw [BitVec.neg_one_eq_allOnes, BitVec.and_allOnes, BitVec.or_zero]
      simpa [hAnte] using mul6 hw xb sb
    · exact matcher_mul7_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_mul7_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_mul5_sound
    (hmatch : __eo_l_4___bv_abstraction_lemma_mul x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l) true := by
  fun_cases __eo_l_4___bv_abstraction_lemma_mul x s t l
  all_goals simp only [__eo_l_4___bv_abstraction_lemma_mul] at hmatch
  all_goals try { simp at hmatch }
  case case5 ps pt one px ps2 zero1 ones zero2 w1 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases4 hAliases with ⟨hps, hpt, hpx, hps2⟩
      subst ps; subst pt; subst px; subst ps2
      rcases eo_and_eq_true_args _ _ hVals with ⟨hOne, hRest⟩
      rcases eo_and_eq_true_args _ _ hRest with ⟨hZero1, hRest2⟩
      rcases eo_and_eq_true_args _ _ hRest2 with ⟨hOnes, hZero2⟩
      let p : Raw.Pred := .not (.eq .s
        (.not (.or .t
          (.or (.and (.lit one)
            (.and (.or .x (.or .s (.lit zero1))) (.lit ones))) (.lit zero2)))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_mul_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hOneTy := hLits one (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hZero1Ty := hLits zero1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hOnesTy := hLits ones (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hZero2Ty := hLits zero2 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have eOne := validated_one (by omega) hOneTy hOne
      have eZero1 := validated_zero hZero1Ty hZero1
      have eOnes := validated_ones hOnesTy hOnes
      have eZero2 := validated_zero hZero2Ty hZero2
      subst one; subst zero1; subst ones; subst zero2
      change eo_interprets M
        ((Dsl.mulPred (.not (.eq .s
          (.not (.or .t (.or (.and .one
            (.and (.or .x (.or .s .zero)) .ones)) .zero)))))).term w x s t) true
      apply Dsl.sound_mul_pred
        (q := .not (.eq .s
          (.not (.or .t (.or (.and .one
            (.and (.or .x (.or .s .zero)) .ones)) .zero)))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      rw [BitVec.or_zero, BitVec.neg_one_eq_allOnes, BitVec.and_allOnes,
        BitVec.or_zero]
      simpa [hAnte, BitVec.or_assoc] using mul5 hw xb sb
    · exact matcher_mul6_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_mul6_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_mul4_sound
    (hmatch : __eo_l_3___bv_abstraction_lemma_mul x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l) true := by
  fun_cases __eo_l_3___bv_abstraction_lemma_mul x s t l
  all_goals simp only [__eo_l_3___bv_abstraction_lemma_mul] at hmatch
  all_goals try { simp at hmatch }
  case case5 pt px ps ones extractOp w1 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hOnes⟩
      rcases aliases3 hAliases with ⟨hpt, hpx, hps⟩
      subst pt; subst px; subst ps
      let et : Term :=
        Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral 0) (Term.Numeral 0)) t
      let ex : Term :=
        Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral 0) (Term.Numeral 0)) x
      let es : Term :=
        Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral 0) (Term.Numeral 0)) s
      let rhs : Term := Term.Apply (Term.Apply (Term.UOp UserOp.bvand) ex)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) es) ones)
      have hpBool : RuleProofs.eo_has_bool_type
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) et) rhs) := by
        simpa [et, ex, es, rhs] using raw_mul_result_bool x s t _ hBool
      have hSides :=
        RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type et rhs hpBool
      have hetTy : __smtx_typeof (__eo_to_smt et) = SmtType.BitVec 1 := by
        change __smtx_typeof
          (SmtTerm.extract (SmtTerm.Numeral 0) (SmtTerm.Numeral 0)
            (__eo_to_smt t)) = SmtType.BitVec 1
        exact typeof_extract00 (by omega) htTy
      have hrhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.BitVec 1 := by
        rw [← hSides.1]
        exact hetTy
      have hOuter := bv_op2_args_of_result
        (a := __eo_to_smt ex)
        (b := __eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) es) ones))
        (by rfl) hrhsTy
      have hInner := bv_op2_args_of_result
        (a := __eo_to_smt es) (b := __eo_to_smt ones) (by rfl) hOuter.2
      have eOnes := validated_ones hInner.2 hOnes
      subst ones
      rw [RuleProofs.eo_interprets_iff_smt_interprets]
      refine smt_interprets.intro_true M _ hBool ?_
      change __smtx_model_eval_imp
        (__smtx_model_eval_eq
          (__smtx_model_eval_bvmul
            (__smtx_model_eval M (__eo_to_smt x))
            (__smtx_model_eval M (__eo_to_smt s)))
          (__smtx_model_eval M (__eo_to_smt t)))
        (__smtx_model_eval_eq
          (__smtx_model_eval M (SmtTerm.extract (SmtTerm.Numeral 0)
            (SmtTerm.Numeral 0) (__eo_to_smt t)))
          (__smtx_model_eval_bvand
            (__smtx_model_eval M (SmtTerm.extract (SmtTerm.Numeral 0)
              (SmtTerm.Numeral 0) (__eo_to_smt x)))
            (__smtx_model_eval_bvand
              (__smtx_model_eval M (SmtTerm.extract (SmtTerm.Numeral 0)
                (SmtTerm.Numeral 0) (__eo_to_smt s)))
              (__smtx_model_eval M (__eo_to_smt (Dsl.constTerm 1 1)))))) =
          SmtValue.Boolean true
      rw [hx, hs, ht, eval_bvmul_bvValue,
        smtx_eval_extract_term_eq, smtx_eval_extract_term_eq,
        smtx_eval_extract_term_eq]
      have hzeroEval : __smtx_model_eval M (SmtTerm.Numeral 0) =
          SmtValue.Numeral 0 := by rfl
      rw [hzeroEval, hx, hs, ht, eval_extract00_bvValue,
        eval_extract00_bvValue, eval_extract00_bvValue,
        Dsl.eval_constTerm_one M 1 (by omega),
        eval_bvand_bvValue (by omega), eval_bvand_bvValue (by omega),
        eval_eq_bvValue, eval_eq_bvValue]
      simp only [__smtx_model_eval_imp, __smtx_model_eval_not,
        __smtx_model_eval_or, native_not, native_or]
      congr 1
      change (!decide (xb * sb = tb) ||
        decide (tb.setWidth 1 = xb.setWidth 1 &&& (sb.setWidth 1 &&& 1#1))) = true
      apply Dsl.bool_imp_true_of
      intro hAnte
      apply decide_eq_true
      rw [← hAnte, show (1#1 : BitVec 1) = -1#1 by decide,
        BitVec.neg_one_eq_allOnes, BitVec.and_allOnes,
        BitVec.setWidth_mul xb sb (by omega), BitVec.mul_eq_and]
    · exact matcher_mul5_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_mul5_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_mul3_sound
    (hmatch : __eo_l_2___bv_abstraction_lemma_mul x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l) true := by
  fun_cases __eo_l_2___bv_abstraction_lemma_mul x s t l
  all_goals simp only [__eo_l_2___bv_abstraction_lemma_mul] at hmatch
  all_goals try { simp at hmatch }
  case case5 ps ps2 zero pt ones pt2 w1 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases4 hAliases with ⟨hps, hps2, hpt, hpt2⟩
      subst ps; subst ps2; subst pt; subst pt2
      rcases eo_and_eq_true_args _ _ hVals with ⟨hZero, hOnes⟩
      let p : Raw.Pred := .eq
        (.and (.or (.neg .s) (.or .s (.lit zero))) (.and .t (.lit ones))) .t
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_mul_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hZeroTy := hLits zero (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hOnesTy := hLits ones (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have eZero := validated_zero hZeroTy hZero
      have eOnes := validated_ones hOnesTy hOnes
      subst zero; subst ones
      change eo_interprets M
        ((Dsl.mulPred (.eq
          (.and (.or (.neg .s) (.or .s .zero)) (.and .t .ones)) .t)).term
          w x s t) true
      apply Dsl.sound_mul_pred
        (q := .eq (.and (.or (.neg .s) (.or .s .zero)) (.and .t .ones)) .t)
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply decide_eq_true
      rw [BitVec.or_zero, BitVec.neg_one_eq_allOnes, BitVec.and_allOnes,
        ← hAnte]
      exact mul3 xb sb
    · exact matcher_mul4_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_mul4_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_mul2_sound
    (hmatch : __eo_l_1___bv_abstraction_lemma_mul x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l) true := by
  fun_cases __eo_l_1___bv_abstraction_lemma_mul x s t l
  all_goals simp only [__eo_l_1___bv_abstraction_lemma_mul] at hmatch
  all_goals try { simp at hmatch }
  case case5 px c pt ps d widthTerm exponentTerm hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hPower⟩
      rcases aliases3 hAliases with ⟨hpx, hpt, hps⟩
      subst px; subst pt; subst ps
      let p : Raw.Pred := .imp (.eq .x (.lit c))
        (.eq .t (.shl (.neg .s) (.lit d)))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_mul_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hcTy := hLits c (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hdTy := hLits d (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      obtain ⟨cb, hcEval⟩ := eval_as_bvValue M hM c w hcTy
      obtain ⟨db, hdEval⟩ := eval_as_bvValue M hM d w hdTy
      have hwidth : __bv_bitwidth (__eo_typeof x) = Term.Numeral w :=
        bitwidth_typeof_of_smt_type x w hxTy
      rcases to_z_numeral_or_stuck d with hNumeral | hStuck
      · obtain ⟨i, hdz⟩ := hNumeral
        have hdi : (db.toNat : Int) = i :=
          to_z_numeral_eval M d w db i hdz hdEval
        have hi0 : 0 ≤ i := by
          rw [← hdi]
          exact Int.natCast_nonneg _
        have hini : ¬ i < 0 := Int.not_lt.mpr hi0
        have hwNonneg : ¬((w : Int) < 0) :=
          Int.not_lt_of_ge (Int.natCast_nonneg w)
        rw [hwidth, hdz] at hPower
        have hPower' : __eo_to_z c =
            Term.Numeral ((2 : Int) ^ w - (2 : Int) ^ i.toNat) := by
          have hEq := support_eq_of_eo_eq_true (__eo_to_z c)
            (Term.Numeral ((2 : Int) ^ w - (2 : Int) ^ i.toNat))
          apply (hEq ?_).symm
          simpa [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_pow,
            __eo_mk_apply, __eo_add, __eo_neg, native_ite, native_teq,
            native_zlt, native_and, native_not, hini, native_zexp_total,
            native_zplus, native_zneg, SmtEval.native_nat_to_int, hwNonneg,
            Int.sub_eq_add_neg] using hPower
        have hcNatInt : (cb.toNat : Int) =
            (2 : Int) ^ w - (2 : Int) ^ i.toNat :=
          to_z_numeral_eval M c w cb
            ((2 : Int) ^ w - (2 : Int) ^ i.toNat) hPower' hcEval
        have hpowLeInt : (2 : Int) ^ i.toNat ≤ (2 : Int) ^ w := by
          have hcb0 : (0 : Int) ≤ cb.toNat := Int.natCast_nonneg _
          omega
        have hpowLe : 2 ^ i.toNat ≤ 2 ^ w := by exact_mod_cast hpowLeInt
        have hiLe : i.toNat ≤ w :=
          (Nat.pow_le_pow_iff_right (by omega)).mp hpowLe
        have hcNat : cb.toNat = 2 ^ w - 2 ^ i.toNat := by
          exact_mod_cast hcNatInt
        have hcb : cb = -BitVec.twoPow w i.toNat := by
          apply BitVec.eq_of_toNat_eq
          rw [hcNat, BitVec.toNat_neg, BitVec.toNat_twoPow]
          by_cases hiw : i.toNat < w
          · rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hiw)]
            rw [Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos w)
              (Nat.two_pow_pos i.toNat))]
          · have hiEq : i.toNat = w := by omega
            rw [hiEq]
            simp
        rw [RuleProofs.eo_interprets_iff_smt_interprets]
        refine smt_interprets.intro_true M _ hBool ?_
        change __smtx_model_eval_imp
          (__smtx_model_eval_eq
            (__smtx_model_eval_bvmul
              (__smtx_model_eval M (__eo_to_smt x))
              (__smtx_model_eval M (__eo_to_smt s)))
            (__smtx_model_eval M (__eo_to_smt t)))
          (__smtx_model_eval_imp
            (__smtx_model_eval_eq
              (__smtx_model_eval M (__eo_to_smt x))
              (__smtx_model_eval M (__eo_to_smt c)))
            (__smtx_model_eval_eq
              (__smtx_model_eval M (__eo_to_smt t))
              (__smtx_model_eval_bvshl
                (__smtx_model_eval_bvneg
                  (__smtx_model_eval M (__eo_to_smt s)))
                (__smtx_model_eval M (__eo_to_smt d))))) = SmtValue.Boolean true
        rw [hx, hs, ht, hcEval, hdEval, eval_bvmul_bvValue,
          eval_bvneg_bvValue, eval_bvshl_bvValue,
          eval_eq_bvValue, eval_eq_bvValue, eval_eq_bvValue]
        simp only [__smtx_model_eval_imp, __smtx_model_eval_not,
          __smtx_model_eval_or, native_not, native_or]
        congr 1
        change (!decide (xb * sb = tb) ||
          (!decide (xb = cb) || decide (tb = (-sb) <<< db.toNat))) = true
        apply Dsl.bool_imp_true_of
        intro hAnte
        apply Dsl.bool_imp_true_of
        intro hxc
        have hxPow : xb = -BitVec.twoPow w i.toNat := hxc.trans hcb
        have hq := mul2 sb xb tb i.toNat hxPow (by simpa [BitVec.mul_comm] using hAnte)
        have hdb : db.toNat = i.toNat := by omega
        exact decide_eq_true (by simpa [hdb] using hq)
      · rw [hwidth, hStuck] at hPower
        generalize hc : __eo_to_z c = z at hPower
        cases z <;>
          simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_pow,
            __eo_mk_apply, __eo_add, __eo_neg, __eo_eq, native_ite,
            native_teq, native_zlt, native_and, native_not,
            native_zexp_total, native_zplus, native_zneg,
            SmtEval.native_nat_to_int] at hPower
    · exact matcher_mul3_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_mul3_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_mul_sound
    (hmatch : __bv_abstraction_lemma_mul x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l) true := by
  fun_cases __bv_abstraction_lemma_mul x s t l
  all_goals simp only [__bv_abstraction_lemma_mul] at hmatch
  all_goals try { simp [__eo_l_1___bv_abstraction_lemma_mul] at hmatch }
  case case5 px c pt ps d exponentTerm hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hPower⟩
      rcases aliases3 hAliases with ⟨hpx, hpt, hps⟩
      subst px; subst pt; subst ps
      let p : Raw.Pred := .imp (.eq .x (.lit c))
        (.eq .t (.shl .s (.lit d)))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_mul_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hcTy := hLits c (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hdTy := hLits d (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      obtain ⟨cb, hcEval⟩ := eval_as_bvValue M hM c w hcTy
      obtain ⟨db, hdEval⟩ := eval_as_bvValue M hM d w hdTy
      obtain ⟨i, hdz⟩ := power_match_arg_numeral c d hPower
      have hdi : (db.toNat : Int) = i :=
        to_z_numeral_eval M d w db i hdz hdEval
      have hi0 : 0 ≤ i := by
        rw [← hdi]
        exact Int.natCast_nonneg _
      have hini : ¬ i < 0 := Int.not_lt.mpr hi0
      have hPower' : __eo_to_z c = Term.Numeral ((2 : Int) ^ i.toNat) := by
        have hEq := support_eq_of_eo_eq_true (__eo_to_z c)
          (Term.Numeral ((2 : Int) ^ i.toNat))
        apply (hEq ?_).symm
        rw [hdz] at hPower
        simpa [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_pow,
          __eo_mk_apply, native_ite, native_teq, native_zlt,
          native_and, native_not, hi0, hini,
          native_zexp_total] using hPower
      have hcNatInt : (cb.toNat : Int) = (2 : Int) ^ i.toNat :=
        to_z_numeral_eval M c w cb ((2 : Int) ^ i.toNat) hPower' hcEval
      have hcNat : cb.toNat = 2 ^ i.toNat := by exact_mod_cast hcNatInt
      have hiw : i.toNat < w := by
        by_cases hiw : i.toNat < w
        · exact hiw
        · have hwle : w ≤ i.toNat := Nat.le_of_not_gt hiw
          have hpLe : 2 ^ w ≤ 2 ^ i.toNat :=
            Nat.pow_le_pow_right (by omega) hwle
          have hcbLt := cb.isLt
          rw [hcNat] at hcbLt
          omega
      have hcb : cb = BitVec.twoPow w i.toNat := by
        apply BitVec.eq_of_toNat_eq
        rw [hcNat, BitVec.toNat_twoPow_of_lt hiw]
      rw [RuleProofs.eo_interprets_iff_smt_interprets]
      refine smt_interprets.intro_true M _ hBool ?_
      change __smtx_model_eval_imp
        (__smtx_model_eval_eq
          (__smtx_model_eval_bvmul
            (__smtx_model_eval M (__eo_to_smt x))
            (__smtx_model_eval M (__eo_to_smt s)))
          (__smtx_model_eval M (__eo_to_smt t)))
        (__smtx_model_eval_imp
          (__smtx_model_eval_eq
            (__smtx_model_eval M (__eo_to_smt x))
            (__smtx_model_eval M (__eo_to_smt c)))
          (__smtx_model_eval_eq
            (__smtx_model_eval M (__eo_to_smt t))
            (__smtx_model_eval_bvshl
              (__smtx_model_eval M (__eo_to_smt s))
              (__smtx_model_eval M (__eo_to_smt d))))) = SmtValue.Boolean true
      rw [hx, hs, ht, hcEval, hdEval, eval_bvmul_bvValue,
        eval_bvshl_bvValue, eval_eq_bvValue, eval_eq_bvValue, eval_eq_bvValue]
      simp only [__smtx_model_eval_imp, __smtx_model_eval_not,
        __smtx_model_eval_or, native_not, native_or]
      congr 1
      change (!decide (xb * sb = tb) ||
        (!decide (xb = cb) || decide (tb = sb <<< db.toNat))) = true
      apply Dsl.bool_imp_true_of
      intro hAnte
      apply Dsl.bool_imp_true_of
      intro hxc
      have hxPow : xb = BitVec.twoPow w i.toNat := hxc.trans hcb
      have hq := mul1 sb xb tb i.toNat hxPow
        (by simpa [BitVec.mul_comm] using hAnte)
      have hdb : db.toNat = i.toNat := by omega
      exact decide_eq_true (by simpa [hdb] using hq)
    · exact matcher_mul2_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_mul2_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

end

end Matcher
end BvAbstraction
