module

public import Cpc.Proofs.RuleSupport.BvAbstractionMatcherSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionMatcherSupport

public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8000

open Eo SmtEval Smtm

namespace BvAbstraction
namespace Matcher

theorem to_z_numeral_or_stuck (d : Term) :
    (∃ i, __eo_to_z d = Term.Numeral i) ∨ __eo_to_z d = Term.Stuck := by
  cases d <;> simp [__eo_to_z, native_ite]
  case String str =>
    by_cases hlen : native_zeq 1 (native_str_len str) = true
    · exact Or.inl ⟨native_str_to_code str, by simp [__eo_to_z, native_ite, hlen]⟩
    · exact Or.inr (by simp [__eo_to_z, native_ite, hlen])

theorem power_match_arg_numeral (c d : Term)
    (h : __eo_eq (__eo_to_z c)
      (__eo_ite (__eo_is_z (__eo_to_z d))
        (__eo_ite (__eo_is_neg (__eo_to_z d)) (Term.Numeral 0)
          (__eo_pow (Term.Numeral 2) (__eo_to_z d)))
        (__eo_mk_apply (Term.UOp UserOp.int_pow2) (__eo_to_z d))) =
      Term.Boolean true) :
    ∃ i, __eo_to_z d = Term.Numeral i := by
  rcases to_z_numeral_or_stuck d with hNumeral | hStuck
  · exact hNumeral
  · rw [hStuck] at h
    generalize hc : __eo_to_z c = z at h
    cases z <;>
      simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_pow,
        __eo_mk_apply, __eo_eq, native_ite, native_teq, native_and,
        native_not] at h

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
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l))

include hM hw hxTy hsTy htTy hx hs ht hBool

theorem matcher_udiv35_sound
    (hmatch : __eo_l_35___bv_abstraction_lemma_udiv x s t l =
      Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l)
      true := by
  fun_cases __eo_l_35___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_35___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_36___bv_abstraction_lemma_udiv,
    __eo_l_37___bv_abstraction_lemma_udiv] at hmatch }
  case case5 ps cone px pt hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hOne⟩
      rcases aliases3 hAliases with ⟨hps, hpx, hpt⟩
      subst ps; subst px; subst pt
      let p : Raw.Pred := .uge (.sub .s (.lit cone)) (.lshr .x .t)
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using
          raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hcTy : __smtx_typeof (__eo_to_smt cone) = SmtType.BitVec w :=
        hLits cone (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hc := validated_one (by omega) hcTy hOne
      subst cone
      change eo_interprets M
        ((Dsl.udivPred (.uge (.sub .s .one) (.lshr .x .t))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .uge (.sub .s .one) (.lshr .x .t))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      exact decide_eq_true (by simpa [hAnte] using UdivShiftCases.udiv35 hw xb sb)
    · exact matcher_udiv36_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv36_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv34_sound
    (hmatch : __eo_l_34___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_34___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_34___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_35___bv_abstraction_lemma_udiv,
    __eo_l_36___bv_abstraction_lemma_udiv, __eo_l_37___bv_abstraction_lemma_udiv] at hmatch }
  case case5 pt px ps cone hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hOne⟩
      rcases aliases3 hAliases with ⟨hpt, hpx, hps⟩
      subst pt; subst px; subst ps
      let p : Raw.Pred := .uge .t (.lshr .x (.sub .s (.lit cone)))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hcTy := hLits cone (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hc := validated_one (by omega) hcTy hOne
      subst cone
      change eo_interprets M
        ((Dsl.udivPred (.uge .t (.lshr .x (.sub .s .one)))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .uge .t (.lshr .x (.sub .s .one)))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      exact decide_eq_true (by simpa [hAnte] using UdivShiftCases.udiv34 hw xb sb)
    · exact matcher_udiv35_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv35_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv33_sound
    (hmatch : __eo_l_33___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_33___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_33___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_34___bv_abstraction_lemma_udiv,
    __eo_l_35___bv_abstraction_lemma_udiv, __eo_l_36___bv_abstraction_lemma_udiv,
    __eo_l_37___bv_abstraction_lemma_udiv] at hmatch }
  case case5 ps px pt ln1 ln2 pt2 cone ln3 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases4 hAliases with ⟨hps, hpx, hpt, hpt2⟩
      subst ps; subst px; subst pt; subst pt2
      rcases and_true4r _ _ _ _ hVals with ⟨hz1, hz2, hOne, hz3⟩
      let p : Raw.Pred := .uge
        (.xor .s (.xor (.or .x (.or .t (.lit ln1))) (.lit ln2)))
        (.xor .t (.xor (.lit cone) (.lit ln3)))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have h1Ty := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have h2Ty := hLits ln2 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hcTy := hLits cone (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have h3Ty := hLits ln3 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have e1 := validated_zero h1Ty hz1
      have e2 := validated_zero h2Ty hz2
      have ec := validated_one (by omega) hcTy hOne
      have e3 := validated_zero h3Ty hz3
      subst ln1; subst ln2; subst cone; subst ln3
      change eo_interprets M ((Dsl.udivPred (.uge
        (.xor .s (.xor (.or .x (.or .t .zero)) .zero))
        (.xor .t (.xor .one .zero)))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .uge
        (.xor .s (.xor (.or .x (.or .t .zero)) .zero))
        (.xor .t (.xor .one .zero))) M (by omega)
        x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      exact decide_eq_true (by simpa [hAnte] using Udiv33Case.udiv33 hw xb sb)
    · exact matcher_udiv34_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv34_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv32_sound
    (hmatch : __eo_l_32___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_32___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_32___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_33___bv_abstraction_lemma_udiv,
    __eo_l_34___bv_abstraction_lemma_udiv, __eo_l_35___bv_abstraction_lemma_udiv,
    __eo_l_36___bv_abstraction_lemma_udiv, __eo_l_37___bv_abstraction_lemma_udiv] at hmatch }
  case case5 px pt pt2 px2 ps ln1 ln2 ln3 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases5 hAliases with ⟨hpx, hpt, hpt2, hpx2, hps⟩
      subst px; subst pt; subst pt2; subst px2; subst ps
      rcases and_true3r _ _ _ hVals with ⟨hz1, hz2, hz3⟩
      let p : Raw.Pred := .not (.eq .x
        (.add .t (.add (.add .t (.add (.or .x (.or .s (.lit ln1)))
          (.lit ln2))) (.lit ln3))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have h1Ty := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have h2Ty := hLits ln2 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have h3Ty := hLits ln3 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have e1 := validated_zero h1Ty hz1
      have e2 := validated_zero h2Ty hz2
      have e3 := validated_zero h3Ty hz3
      subst ln1; subst ln2; subst ln3
      change eo_interprets M ((Dsl.udivPred (.not (.eq .x
        (.add .t (.add (.add .t (.add (.or .x (.or .s .zero)) .zero)) .zero))))).term
          w x s t) true
      apply Dsl.sound_udiv_pred (q := .not (.eq .x
        (.add .t (.add (.add .t (.add (.or .x (.or .s .zero)) .zero)) .zero))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      simpa [hAnte, BitVec.add_assoc] using Udiv32Case.udiv32 hw xb sb
    · exact matcher_udiv33_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv33_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv31_sound
    (hmatch : __eo_l_31___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_31___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_31___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_32___bv_abstraction_lemma_udiv,
    __eo_l_33___bv_abstraction_lemma_udiv, __eo_l_34___bv_abstraction_lemma_udiv,
    __eo_l_35___bv_abstraction_lemma_udiv, __eo_l_36___bv_abstraction_lemma_udiv,
    __eo_l_37___bv_abstraction_lemma_udiv] at hmatch }
  case case5 ps px pt ln1 pt2 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hZero⟩
      rcases aliases4 hAliases with ⟨hps, hpx, hpt, hpt2⟩
      subst ps; subst px; subst pt; subst pt2
      let p : Raw.Pred := .uge .s (.lshr (.add .x (.add .t (.lit ln1))) .t)
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have h1Ty := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have e1 := validated_zero h1Ty hZero
      subst ln1
      change eo_interprets M
        ((Dsl.udivPred (.uge .s (.lshr (.add .x (.add .t .zero)) .t))).term w x s t) true
      apply Dsl.sound_udiv_pred
        (q := .uge .s (.lshr (.add .x (.add .t .zero)) .t))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      exact decide_eq_true (by simpa [hAnte] using UdivMoreShiftCases.udiv31 hw xb sb)
    · exact matcher_udiv32_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv32_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv30_sound
    (hmatch : __eo_l_30___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_30___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_30___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_31___bv_abstraction_lemma_udiv] at hmatch }
  case case5 px pt cone pcone px2 ln1 ln2 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases4 hAliases with ⟨hpx, hpt, hpc, hpx2⟩
      subst px; subst pt; subst pcone; subst px2
      rcases and_true3r _ _ _ hVals with ⟨hOne, hz1, hz2⟩
      let p : Raw.Pred := .not (.eq .x (.add .t
        (.add (.add (.lit cone) (.add (.shl (.lit cone) .x) (.lit ln1)))
          (.lit ln2))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hcTy := hLits cone (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have h1Ty := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have h2Ty := hLits ln2 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have ec := validated_one (by omega) hcTy hOne
      have e1 := validated_zero h1Ty hz1
      have e2 := validated_zero h2Ty hz2
      subst cone; subst ln1; subst ln2
      change eo_interprets M ((Dsl.udivPred (.not (.eq .x (.add .t
        (.add (.add .one (.add (.shl .one .x) .zero)) .zero))))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .not (.eq .x (.add .t
        (.add (.add .one (.add (.shl .one .x) .zero)) .zero))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      simpa [hAnte, BitVec.add_assoc] using Udiv30Case.udiv30 hw xb sb
    · exact matcher_udiv31_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv31_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv29_sound
    (hmatch : __eo_l_29___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_29___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_29___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_30___bv_abstraction_lemma_udiv] at hmatch }
  case case5 px pt ps px2 ps2 ln1 ln2 ln3 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases5 hAliases with ⟨hpx, hpt, hps, hpx2, hps2⟩
      subst px; subst pt; subst ps; subst px2; subst ps2
      rcases and_true3r _ _ _ hVals with ⟨hz1, hz2, hz3⟩
      let p : Raw.Pred := .not (.eq .x (.add .t
        (.add (.or .s (.or (.add .x (.add .s (.lit ln1))) (.lit ln2)))
          (.lit ln3))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have h1Ty := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have h2Ty := hLits ln2 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have h3Ty := hLits ln3 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have e1 := validated_zero h1Ty hz1
      have e2 := validated_zero h2Ty hz2
      have e3 := validated_zero h3Ty hz3
      subst ln1; subst ln2; subst ln3
      change eo_interprets M ((Dsl.udivPred (.not (.eq .x (.add .t
        (.add (.or .s (.or (.add .x (.add .s .zero)) .zero)) .zero))))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .not (.eq .x (.add .t
        (.add (.or .s (.or (.add .x (.add .s .zero)) .zero)) .zero))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      simpa [hAnte, BitVec.add_assoc] using Udiv29Case.udiv29 hw xb sb
    · exact matcher_udiv30_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv30_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv28_sound
    (hmatch : __eo_l_28___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_28___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_28___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_29___bv_abstraction_lemma_udiv] at hmatch }
  case case5 px pt px2 ps ln1 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hZero⟩
      rcases aliases4 hAliases with ⟨hpx, hpt, hpx2, hps⟩
      subst px; subst pt; subst px2; subst ps
      let p : Raw.Pred := .uge .x
        (.shl .t (.not (.xor .x (.xor .s (.lit ln1)))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have h1Ty := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have e1 := validated_zero h1Ty hZero
      subst ln1
      change eo_interprets M ((Dsl.udivPred (.uge .x
        (.shl .t (.not (.xor .x (.xor .s .zero)))))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .uge .x
        (.shl .t (.not (.xor .x (.xor .s .zero)))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      exact decide_eq_true (by simpa [hAnte] using
        UdivComplementShiftCases.udiv28 hw xb sb)
    · exact matcher_udiv29_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv29_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv27_sound
    (hmatch : __eo_l_27___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_27___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_27___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_28___bv_abstraction_lemma_udiv] at hmatch }
  case case5 px ps px2 pt ln1 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hZero⟩
      rcases aliases4 hAliases with ⟨hpx, hps, hpx2, hpt⟩
      subst px; subst ps; subst px2; subst pt
      let p : Raw.Pred := .uge .x
        (.shl .s (.not (.xor .x (.xor .t (.lit ln1)))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have h1Ty := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have e1 := validated_zero h1Ty hZero
      subst ln1
      change eo_interprets M ((Dsl.udivPred (.uge .x
        (.shl .s (.not (.xor .x (.xor .t .zero)))))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .uge .x
        (.shl .s (.not (.xor .x (.xor .t .zero)))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      exact decide_eq_true (by simpa [hAnte] using
        UdivComplementShiftCases.udiv27 hw xb sb)
    · exact matcher_udiv28_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv28_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv26_sound
    (hmatch : __eo_l_26___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_26___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_26___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_27___bv_abstraction_lemma_udiv] at hmatch }
  case case5 px ps ps2 pt cone ln1 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases4 hAliases with ⟨hpx, hps, hps2, hpt⟩
      subst px; subst ps; subst ps2; subst pt
      rcases eo_and_eq_true_args _ _ hVals with ⟨hOne, hZero⟩
      let p : Raw.Pred := .uge .x
        (.xor .s (.xor (.lshr .s (.lshr .t (.lit cone))) (.lit ln1)))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hcTy := hLits cone (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have h1Ty := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have ec := validated_one (by omega) hcTy hOne
      have e1 := validated_zero h1Ty hZero
      subst cone; subst ln1
      change eo_interprets M ((Dsl.udivPred (.uge .x
        (.xor .s (.xor (.lshr .s (.lshr .t .one)) .zero)))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .uge .x
        (.xor .s (.xor (.lshr .s (.lshr .t .one)) .zero)))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      have hone : (1#w).toNat = 1 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        exact Nat.one_lt_two_pow (by omega)
      exact decide_eq_true (by simpa [hAnte, hone] using UdivXorCases.udiv26 xb sb)
    · exact matcher_udiv27_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv27_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv25_sound
    (hmatch : __eo_l_25___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_25___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_25___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_26___bv_abstraction_lemma_udiv] at hmatch }
  case case5 px pt pt2 ps cone ln1 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases4 hAliases with ⟨hpx, hpt, hpt2, hps⟩
      subst px; subst pt; subst pt2; subst ps
      rcases eo_and_eq_true_args _ _ hVals with ⟨hOne, hZero⟩
      let p : Raw.Pred := .uge .x
        (.xor .t (.xor (.lshr .t (.lshr .s (.lit cone))) (.lit ln1)))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hcTy := hLits cone (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have h1Ty := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have ec := validated_one (by omega) hcTy hOne
      have e1 := validated_zero h1Ty hZero
      subst cone; subst ln1
      change eo_interprets M ((Dsl.udivPred (.uge .x
        (.xor .t (.xor (.lshr .t (.lshr .s .one)) .zero)))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .uge .x
        (.xor .t (.xor (.lshr .t (.lshr .s .one)) .zero)))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      have hone : (1#w).toNat = 1 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        exact Nat.one_lt_two_pow (by omega)
      exact decide_eq_true (by simpa [hAnte, hone] using UdivXorCases.udiv25 xb sb)
    · exact matcher_udiv26_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv26_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv24_sound
    (hmatch : __eo_l_24___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_24___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_24___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_25___bv_abstraction_lemma_udiv] at hmatch }
  case case5 px pt px2 ps ln1 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hZero⟩
      rcases aliases4 hAliases with ⟨hpx, hpt, hpx2, hps⟩
      subst px; subst pt; subst px2; subst ps
      let p : Raw.Pred := .uge .x
        (.shl .t (.not (.or .x (.or .s (.lit ln1)))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have h1Ty := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have e1 := validated_zero h1Ty hZero
      subst ln1
      change eo_interprets M ((Dsl.udivPred (.uge .x
        (.shl .t (.not (.or .x (.or .s .zero)))))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .uge .x
        (.shl .t (.not (.or .x (.or .s .zero)))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      exact decide_eq_true (by simpa [hAnte] using
        UdivComplementShiftCases.udiv24 hw xb sb)
    · exact matcher_udiv25_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv25_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv23_sound
    (hmatch : __eo_l_23___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_23___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_23___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_24___bv_abstraction_lemma_udiv] at hmatch }
  case case5 px ps px2 pt ln1 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hZero⟩
      rcases aliases4 hAliases with ⟨hpx, hps, hpx2, hpt⟩
      subst px; subst ps; subst px2; subst pt
      let p : Raw.Pred := .uge .x
        (.shl .s (.not (.or .x (.or .t (.lit ln1)))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have h1Ty := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have e1 := validated_zero h1Ty hZero
      subst ln1
      change eo_interprets M ((Dsl.udivPred (.uge .x
        (.shl .s (.not (.or .x (.or .t .zero)))))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .uge .x
        (.shl .s (.not (.or .x (.or .t .zero)))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      exact decide_eq_true (by simpa [hAnte] using
        UdivComplementShiftCases.udiv23 hw xb sb)
    · exact matcher_udiv24_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv24_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv22_sound
    (hmatch : __eo_l_22___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_22___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_22___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_23___bv_abstraction_lemma_udiv] at hmatch }
  case case5 pt px cone ps hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hOne⟩
      rcases aliases3 hAliases with ⟨hpt, hpx, hps⟩
      subst pt; subst px; subst ps
      let p : Raw.Pred := .uge .t (.lshr (.shl .x (.lit cone)) .s)
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hcTy := hLits cone (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have ec := validated_one (by omega) hcTy hOne
      subst cone
      change eo_interprets M
        ((Dsl.udivPred (.uge .t (.lshr (.shl .x .one) .s))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .uge .t (.lshr (.shl .x .one) .s))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      have hone : (1#w).toNat = 1 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        exact Nat.one_lt_two_pow (by omega)
      exact decide_eq_true (by simpa [hAnte, hone] using UdivShiftCases.udiv22 hw xb sb)
    · exact matcher_udiv23_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv23_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv21_sound
    (hmatch : __eo_l_21___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_21___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_21___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_22___bv_abstraction_lemma_udiv] at hmatch }
  case case5 px px2 pt cone ln1 widthTerm hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases3 hAliases with ⟨hpx, hpx2, hpt⟩
      subst px; subst px2; subst pt
      rcases eo_and_eq_true_args _ _ hVals with ⟨hOne, hOnes⟩
      let p : Raw.Pred := .not (.eq .x
        (.not (.and .x (.and (.shl .t (.lit cone)) (.lit ln1)))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hcTy := hLits cone (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have h1Ty := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have ec := validated_one (by omega) hcTy hOne
      have e1 := validated_ones h1Ty hOnes
      subst cone; subst ln1
      change eo_interprets M ((Dsl.udivPred (.not (.eq .x
        (.not (.and .x (.and (.shl .t .one) .ones)))))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .not (.eq .x
        (.not (.and .x (.and (.shl .t .one) .ones)))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      have hone : (1#w).toNat = 1 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        exact Nat.one_lt_two_pow (by omega)
      apply bool_not_decide_true_of
      simpa [hAnte, hone, BitVec.neg_one_eq_allOnes, BitVec.and_allOnes,
        BitVec.and_comm] using Udiv21Case.udiv21 hw xb sb
    · exact matcher_udiv22_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv22_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv20_sound
    (hmatch : __eo_l_20___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_20___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_20___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_21___bv_abstraction_lemma_udiv] at hmatch }
  case case5 ps ps2 pt cone hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hOne⟩
      rcases aliases3 hAliases with ⟨hps, hps2, hpt⟩
      subst ps; subst ps2; subst pt
      let p : Raw.Pred := .not (.eq .s
        (.not (.lshr .s (.lshr .t (.lit cone)))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hcTy := hLits cone (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have ec := validated_one (by omega) hcTy hOne
      subst cone
      change eo_interprets M ((Dsl.udivPred (.not (.eq .s
        (.not (.lshr .s (.lshr .t .one)))))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .not (.eq .s
        (.not (.lshr .s (.lshr .t .one)))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      have hone : (1#w).toNat = 1 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        exact Nat.one_lt_two_pow (by omega)
      apply bool_not_decide_true_of
      simpa [hAnte, hone] using Udiv20Case.udiv20 hw xb sb
    · exact matcher_udiv21_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv21_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv19_sound
    (hmatch : __eo_l_19___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_19___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_19___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_20___bv_abstraction_lemma_udiv] at hmatch }
  case case5 px pt ps pt2 ln1 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hZero⟩
      rcases aliases4 hAliases with ⟨hpx, hpt, hps, hpt2⟩
      subst px; subst pt; subst ps; subst pt2
      let p : Raw.Pred := .not (.eq (.lshr .x .t)
        (.or .s (.or .t (.lit ln1))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have h1Ty := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have e1 := validated_zero h1Ty hZero
      subst ln1
      change eo_interprets M ((Dsl.udivPred (.not (.eq (.lshr .x .t)
        (.or .s (.or .t .zero))))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .not (.eq (.lshr .x .t)
        (.or .s (.or .t .zero))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      simpa [hAnte] using UdivMoreShiftCases.udiv19 hw xb sb
    · exact matcher_udiv20_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv20_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv18_sound
    (hmatch : __eo_l_18___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_18___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_18___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_19___bv_abstraction_lemma_udiv] at hmatch }
  case case5 px px2 ps ln1 pt cone ln2 widthTerm hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases4 hAliases with ⟨hpx, hpx2, hps, hpt⟩
      subst px; subst px2; subst ps; subst pt
      rcases and_true3r _ _ _ hVals with ⟨hZero, hOne, hOnes⟩
      let p : Raw.Pred := .uge .x (.and (.or .x (.or .s (.lit ln1)))
        (.and (.shl .t (.lit cone)) (.lit ln2)))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have h0Ty := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hcTy := hLits cone (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hoTy := hLits ln2 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have e0 := validated_zero h0Ty hZero
      have ec := validated_one (by omega) hcTy hOne
      have eo := validated_ones hoTy hOnes
      subst ln1; subst cone; subst ln2
      change eo_interprets M ((Dsl.udivPred (.uge .x (.and (.or .x (.or .s .zero))
        (.and (.shl .t .one) .ones)))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .uge .x (.and (.or .x (.or .s .zero))
        (.and (.shl .t .one) .ones))) M (by omega)
        x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      have hone : (1#w).toNat = 1 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        exact Nat.one_lt_two_pow (by omega)
      exact decide_eq_true (by simpa [hAnte, hone, BitVec.neg_one_eq_allOnes,
        BitVec.and_allOnes, BitVec.and_comm] using UdivMaskCases.udiv18 hw xb sb)
    · exact matcher_udiv19_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv19_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv17_sound
    (hmatch : __eo_l_17___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_17___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_17___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_18___bv_abstraction_lemma_udiv] at hmatch }
  case case5 px px2 pt ln1 ps cone ln2 widthTerm hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases4 hAliases with ⟨hpx, hpx2, hpt, hps⟩
      subst px; subst px2; subst pt; subst ps
      rcases and_true3r _ _ _ hVals with ⟨hZero, hOne, hOnes⟩
      let p : Raw.Pred := .uge .x (.and (.or .x (.or .t (.lit ln1)))
        (.and (.shl .s (.lit cone)) (.lit ln2)))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have h0Ty := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hcTy := hLits cone (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hoTy := hLits ln2 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have e0 := validated_zero h0Ty hZero
      have ec := validated_one (by omega) hcTy hOne
      have eo := validated_ones hoTy hOnes
      subst ln1; subst cone; subst ln2
      change eo_interprets M ((Dsl.udivPred (.uge .x (.and (.or .x (.or .t .zero))
        (.and (.shl .s .one) .ones)))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .uge .x (.and (.or .x (.or .t .zero))
        (.and (.shl .s .one) .ones))) M (by omega)
        x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      have hone : (1#w).toNat = 1 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        exact Nat.one_lt_two_pow (by omega)
      exact decide_eq_true (by simpa [hAnte, hone, BitVec.neg_one_eq_allOnes,
        BitVec.and_allOnes, BitVec.and_comm] using UdivMaskCases.udiv17 hw xb sb)
    · exact matcher_udiv18_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv18_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv16_sound
    (hmatch : __eo_l_16___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_16___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_16___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_17___bv_abstraction_lemma_udiv] at hmatch }
  case case5 pt px ps cone hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hOne⟩
      rcases aliases3 hAliases with ⟨hpt, hpx, hps⟩
      subst pt; subst px; subst ps
      let p : Raw.Pred := .uge .t (.shl (.lshr .x .s) (.lit cone))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hcTy := hLits cone (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have ec := validated_one (by omega) hcTy hOne
      subst cone
      change eo_interprets M
        ((Dsl.udivPred (.uge .t (.shl (.lshr .x .s) .one))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .uge .t (.shl (.lshr .x .s) .one))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      have hone : (1#w).toNat = 1 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        exact Nat.one_lt_two_pow (by omega)
      exact decide_eq_true (by simpa [hAnte, hone] using UdivShiftCases.udiv16 hw xb sb)
    · exact matcher_udiv17_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv17_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv15_sound
    (hmatch : __eo_l_15___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_15___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_15___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_16___bv_abstraction_lemma_udiv] at hmatch }
  case case5 px pt cone pt2 ps hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hOne⟩
      rcases aliases4 hAliases with ⟨hpx, hpt, hpt2, hps⟩
      subst px; subst pt; subst pt2; subst ps
      let p : Raw.Pred := .uge .x
        (.lshr (.shl .t (.lit cone)) (.shl .t .s))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hcTy := hLits cone (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have ec := validated_one (by omega) hcTy hOne
      subst cone
      change eo_interprets M ((Dsl.udivPred (.uge .x
        (.lshr (.shl .t .one) (.shl .t .s)))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .uge .x
        (.lshr (.shl .t .one) (.shl .t .s)))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      have hone : (1#w).toNat = 1 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        exact Nat.one_lt_two_pow (by omega)
      exact decide_eq_true (by simpa [hAnte, hone] using
        UdivNestedShiftCases.udiv15 hw xb sb)
    · exact matcher_udiv16_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv16_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv14_sound
    (hmatch : __eo_l_14___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_14___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_14___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_15___bv_abstraction_lemma_udiv] at hmatch }
  case case5 px ps ps2 pt cone hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hOne⟩
      rcases aliases4 hAliases with ⟨hpx, hps, hps2, hpt⟩
      subst px; subst ps; subst ps2; subst pt
      let p : Raw.Pred := .uge .x
        (.shl (.lshr .s (.shl .s .t)) (.lit cone))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hcTy := hLits cone (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have ec := validated_one (by omega) hcTy hOne
      subst cone
      change eo_interprets M ((Dsl.udivPred (.uge .x
        (.shl (.lshr .s (.shl .s .t)) .one))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .uge .x
        (.shl (.lshr .s (.shl .s .t)) .one))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      have hone : (1#w).toNat = 1 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
        exact Nat.one_lt_two_pow (by omega)
      exact decide_eq_true (by simpa [hAnte, hone] using
        UdivNestedShiftCases.udiv14 hw xb sb)
    · exact matcher_udiv15_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv15_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv13_sound
    (hmatch : __eo_l_13___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_13___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_13___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_14___bv_abstraction_lemma_udiv] at hmatch }
  case case5 ps px pt hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hTrue⟩
      rcases aliases3 hAliases with ⟨hps, hpx, hpt⟩
      subst ps; subst px; subst pt
      change eo_interprets M
        ((Dsl.udivPred (.uge .s (.lshr .x .t))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .uge .s (.lshr .x .t))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      exact decide_eq_true (by simpa [hAnte] using UdivShiftCases.udiv13 xb sb)
    · exact matcher_udiv14_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv14_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv12_sound
    (hmatch : __eo_l_12___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_12___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_12___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_13___bv_abstraction_lemma_udiv] at hmatch }
  case case5 px pt ln1 ps pt2 ln2 width2 width1 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases4 hAliases with ⟨hpx, hpt, hps, hpt2⟩
      subst px; subst pt; subst ps; subst pt2
      rcases eo_and_eq_true_args _ _ hVals with ⟨hOnes1, hOnes2⟩
      let p : Raw.Pred := .uge
        (.and .x (.and (.neg .t) (.lit ln1)))
        (.and .s (.and .t (.lit ln2)))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have h1Ty := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have h2Ty := hLits ln2 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have e1 := validated_ones h1Ty hOnes1
      have e2 := validated_ones h2Ty hOnes2
      subst ln1; subst ln2
      change eo_interprets M ((Dsl.udivPred (.uge
        (.and .x (.and (.neg .t) .ones))
        (.and .s (.and .t .ones)))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .uge
        (.and .x (.and (.neg .t) .ones))
        (.and .s (.and .t .ones))) M (by omega)
        x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      exact decide_eq_true (by simpa [hAnte, BitVec.neg_one_eq_allOnes,
        BitVec.and_allOnes, BitVec.and_comm] using Udiv12Case.udiv12 xb sb)
    · exact matcher_udiv13_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv13_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv11_sound
    (hmatch : __eo_l_11___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_11___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_11___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_12___bv_abstraction_lemma_udiv] at hmatch }
  case case5 ps cone ln1 px pt ln2 widthTerm hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases3 hAliases with ⟨hps, hpx, hpt⟩
      subst ps; subst px; subst pt
      rcases and_true3r _ _ _ hVals with ⟨hOne, hZero, hOnes⟩
      let p : Raw.Pred := .not (.eq
        (.or .s (.or (.lit cone) (.lit ln1)))
        (.and .x (.and (.not .t) (.lit ln2))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hcTy := hLits cone (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have h0Ty := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hoTy := hLits ln2 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have ec := validated_one (by omega) hcTy hOne
      have e0 := validated_zero h0Ty hZero
      have eo := validated_ones hoTy hOnes
      subst cone; subst ln1; subst ln2
      change eo_interprets M ((Dsl.udivPred (.not (.eq
        (.or .s (.or .one .zero)) (.and .x (.and (.not .t) .ones))))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .not (.eq
        (.or .s (.or .one .zero)) (.and .x (.and (.not .t) .ones))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      simpa [hAnte, BitVec.neg_one_eq_allOnes, BitVec.and_allOnes,
        BitVec.and_comm] using BvAbstraction.udiv11 hw xb sb
    · exact matcher_udiv12_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv12_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv10_sound
    (hmatch : __eo_l_10___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_10___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_10___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_11___bv_abstraction_lemma_udiv] at hmatch }
  case case5 ps pt ln1 px cone ln2 widthTerm hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases3 hAliases with ⟨hps, hpt, hpx⟩
      subst ps; subst pt; subst px
      rcases and_true3r _ _ _ hVals with ⟨hZero, hOne, hOnes⟩
      let p : Raw.Pred := .not (.eq
        (.or .s (.or .t (.lit ln1)))
        (.and .x (.and (.not (.lit cone)) (.lit ln2))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have h0Ty := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hcTy := hLits cone (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hoTy := hLits ln2 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have e0 := validated_zero h0Ty hZero
      have ec := validated_one (by omega) hcTy hOne
      have eo := validated_ones hoTy hOnes
      subst ln1; subst cone; subst ln2
      change eo_interprets M ((Dsl.udivPred (.not (.eq
        (.or .s (.or .t .zero)) (.and .x (.and (.not .one) .ones))))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .not (.eq
        (.or .s (.or .t .zero)) (.and .x (.and (.not .one) .ones))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      simpa [hAnte, BitVec.neg_one_eq_allOnes, BitVec.and_allOnes,
        BitVec.and_comm] using BvAbstraction.udiv10 hw xb sb
    · exact matcher_udiv11_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv11_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv9_sound
    (hmatch : __eo_l_9___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_9___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_9___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_10___bv_abstraction_lemma_udiv] at hmatch }
  case case5 pt ps px ln1 widthTerm hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hOnes⟩
      rcases aliases3 hAliases with ⟨hpt, hps, hpx⟩
      subst pt; subst ps; subst px
      let p : Raw.Pred := .not (.eq .t
        (.neg (.and .s (.and (.not .x) (.lit ln1)))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hoTy := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have eo := validated_ones hoTy hOnes
      subst ln1
      change eo_interprets M ((Dsl.udivPred (.not (.eq .t
        (.neg (.and .s (.and (.not .x) .ones)))))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .not (.eq .t
        (.neg (.and .s (.and (.not .x) .ones)))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      simpa [hAnte, BitVec.neg_one_eq_allOnes, BitVec.and_allOnes,
        BitVec.and_comm] using BvAbstraction.udiv9 hw xb sb
    · exact matcher_udiv10_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv10_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv8_sound
    (hmatch : __eo_l_8___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_8___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_8___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_9___bv_abstraction_lemma_udiv] at hmatch }
  case case5 ps cone ln1 pt hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases2 hAliases with ⟨hps, hpt⟩
      subst ps; subst pt
      rcases eo_and_eq_true_args _ _ hVals with ⟨hOne, hZero⟩
      let p : Raw.Pred := .uge (.neg (.or .s (.or (.lit cone) (.lit ln1)))) .t
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hcTy := hLits cone (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have h0Ty := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have ec := validated_one (by omega) hcTy hOne
      have e0 := validated_zero h0Ty hZero
      subst cone; subst ln1
      change eo_interprets M ((Dsl.udivPred (.uge (.neg (.or .s (.or .one .zero))) .t)).term
        w x s t) true
      apply Dsl.sound_udiv_pred (q := .uge (.neg (.or .s (.or .one .zero))) .t)
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      exact decide_eq_true (by simpa [hAnte] using BvAbstraction.udiv8 hw xb sb)
    · exact matcher_udiv9_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv9_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv7_sound
    (hmatch : __eo_l_7___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_7___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_7___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_8___bv_abstraction_lemma_udiv] at hmatch }
  case case5 px ps pt ln1 widthTerm hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hOnes⟩
      rcases aliases3 hAliases with ⟨hpx, hps, hpt⟩
      subst px; subst ps; subst pt
      let p : Raw.Pred := .uge .x
        (.neg (.and (.neg .s) (.and (.neg .t) (.lit ln1))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hoTy := hLits ln1 (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have eo := validated_ones hoTy hOnes
      subst ln1
      change eo_interprets M ((Dsl.udivPred (.uge .x
        (.neg (.and (.neg .s) (.and (.neg .t) .ones))))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .uge .x
        (.neg (.and (.neg .s) (.and (.neg .t) .ones))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      exact decide_eq_true (by simpa [hAnte, BitVec.neg_one_eq_allOnes,
        BitVec.and_allOnes, BitVec.and_comm] using BvAbstraction.udiv7 hw xb sb)
    · exact matcher_udiv8_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv8_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv6_sound
    (hmatch : __eo_l_6___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_6___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_6___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_7___bv_abstraction_lemma_udiv] at hmatch }
  case case5 ps cones px pcones pt czero widthTerm hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases4 hAliases with ⟨hps, hpx, hpcones, hpt⟩
      subst ps; subst px; subst pcones; subst pt
      rcases eo_and_eq_true_args _ _ hVals with ⟨hOnes, hZero⟩
      let p : Raw.Pred := .imp
        (.and (.eq .s (.lit cones))
          (.and (.not (.eq .x (.lit cones))) .true))
        (.eq .t (.lit czero))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hoTy := hLits cones (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hzTy := hLits czero (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have eo := validated_ones hoTy hOnes
      have ez := validated_zero hzTy hZero
      subst cones; subst czero
      change eo_interprets M ((Dsl.udivPred (.imp
        (.and (.eq .s .ones) (.and (.not (.eq .x .ones)) .true))
        (.eq .t .zero))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .imp
        (.and (.eq .s .ones) (.and (.not (.eq .x .ones)) .true))
        (.eq .t .zero)) M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      by_cases hsOnes : sb = -1#w
      · by_cases hxOnes : xb = -1#w
        · simp [hsOnes, hxOnes]
        · have hq := BvAbstraction.udiv6 xb sb
              (by simpa [BitVec.neg_one_eq_allOnes] using hsOnes)
              (by simpa [BitVec.neg_one_eq_allOnes] using hxOnes)
          have htb : tb = 0#w := hAnte.symm.trans hq
          simp [hsOnes, hxOnes, htb]
      · simp [hsOnes]
    · exact matcher_udiv7_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv7_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv5_sound
    (hmatch : __eo_l_5___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_5___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_5___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_6___bv_abstraction_lemma_udiv] at hmatch }
  case case5 ps czero pt px hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hZero⟩
      rcases aliases3 hAliases with ⟨hps, hpt, hpx⟩
      subst ps; subst pt; subst px
      let p : Raw.Pred := .imp (.not (.eq .s (.lit czero))) (.ule .t .x)
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hzTy := hLits czero (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have ez := validated_zero hzTy hZero
      subst czero
      change eo_interprets M
        ((Dsl.udivPred (.imp (.not (.eq .s .zero)) (.ule .t .x))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .imp (.not (.eq .s .zero)) (.ule .t .x))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      by_cases hs0 : sb = 0#w
      · simp [hs0]
      · have hq := BvAbstraction.udiv5 xb sb hs0
        have htb : tb ≤ xb := by simpa [hAnte] using hq
        simp [hs0, htb]
    · exact matcher_udiv6_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv6_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv4_sound
    (hmatch : __eo_l_4___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_4___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_4___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_5___bv_abstraction_lemma_udiv] at hmatch }
  case case5 px czero ps pzero pt pzero2 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hZero⟩
      rcases aliases5 hAliases with ⟨hpx, hps, hpz, hpt, hpz2⟩
      subst px; subst ps; subst pzero; subst pt; subst pzero2
      let p : Raw.Pred := .imp
        (.and (.eq .x (.lit czero))
          (.and (.not (.eq .s (.lit czero))) .true))
        (.eq .t (.lit czero))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hzTy := hLits czero (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have ez := validated_zero hzTy hZero
      subst czero
      change eo_interprets M ((Dsl.udivPred (.imp
        (.and (.eq .x .zero) (.and (.not (.eq .s .zero)) .true))
        (.eq .t .zero))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .imp
        (.and (.eq .x .zero) (.and (.not (.eq .s .zero)) .true))
        (.eq .t .zero)) M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      by_cases hx0 : xb = 0#w
      · by_cases hs0 : sb = 0#w
        · simp [hx0, hs0]
        · have hq := BvAbstraction.udiv4 xb sb hx0 hs0
          have htb : tb = 0#w := hAnte.symm.trans hq
          simp [hx0, hs0, htb]
      · simp [hx0]
    · exact matcher_udiv5_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv5_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv3_sound
    (hmatch : __eo_l_3___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_3___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_3___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_4___bv_abstraction_lemma_udiv] at hmatch }
  case case5 ps czero pt cones widthTerm hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases2 hAliases with ⟨hps, hpt⟩
      subst ps; subst pt
      rcases eo_and_eq_true_args _ _ hVals with ⟨hZero, hOnes⟩
      let p : Raw.Pred := .imp (.eq .s (.lit czero)) (.eq .t (.lit cones))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hzTy := hLits czero (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hoTy := hLits cones (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have ez := validated_zero hzTy hZero
      have eo := validated_ones hoTy hOnes
      subst czero; subst cones
      change eo_interprets M
        ((Dsl.udivPred (.imp (.eq .s .zero) (.eq .t .ones))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .imp (.eq .s .zero) (.eq .t .ones))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      by_cases hs0 : sb = 0#w
      · have hq := BvAbstraction.udiv3 xb sb hs0
        have htbAll : tb = BitVec.allOnes w := hAnte.symm.trans hq
        have htb : tb = -1#w := by
          simpa [BitVec.neg_one_eq_allOnes] using htbAll
        simp [hs0, htb]
      · simp [hs0]
    · exact matcher_udiv4_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv4_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv2_sound
    (hmatch : __eo_l_2___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_2___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_2___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_3___bv_abstraction_lemma_udiv] at hmatch }
  case case5 ps px ps2 czero pt cone hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases aliases4 hAliases with ⟨hps, hpx, hps2, hpt⟩
      subst ps; subst px; subst ps2; subst pt
      rcases eo_and_eq_true_args _ _ hVals with ⟨hZero, hOne⟩
      let p : Raw.Pred := .imp
        (.and (.eq .s .x) (.and (.not (.eq .s (.lit czero))) .true))
        (.eq .t (.lit cone))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hzTy := hLits czero (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hcTy := hLits cone (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have ez := validated_zero hzTy hZero
      have ec := validated_one (by omega) hcTy hOne
      subst czero; subst cone
      change eo_interprets M ((Dsl.udivPred (.imp
        (.and (.eq .s .x) (.and (.not (.eq .s .zero)) .true))
        (.eq .t .one))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .imp
        (.and (.eq .s .x) (.and (.not (.eq .s .zero)) .true))
        (.eq .t .one)) M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      by_cases hsx : sb = xb
      · by_cases hs0 : sb = 0#w
        · have hx0 : xb = 0#w := hsx.symm.trans hs0
          simp [hsx, hs0, hx0]
        · have hq := BvAbstraction.udiv2 xb sb hsx hs0
          have htb : tb = 1#w := hAnte.symm.trans hq
          simp [hsx, hs0, htb]
      · simp [hsx]
    · exact matcher_udiv3_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv3_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv1_sound
    (hmatch : __eo_l_1___bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __eo_l_1___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_1___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_2___bv_abstraction_lemma_udiv] at hmatch }
  case case5 ps cone pt px hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hOne⟩
      rcases aliases3 hAliases with ⟨hps, hpt, hpx⟩
      subst ps; subst pt; subst px
      let p : Raw.Pred := .imp (.eq .s (.lit cone)) (.eq .t .x)
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hcTy := hLits cone (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have ec := validated_one (by omega) hcTy hOne
      subst cone
      change eo_interprets M
        ((Dsl.udivPred (.imp (.eq .s .one) (.eq .t .x))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .imp (.eq .s .one) (.eq .t .x))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      by_cases hs1 : sb = 1#w
      · have hq := BvAbstraction.udiv37 xb sb tb hs1 hAnte
        simp [hs1, hq]
      · simp [hs1]
    · exact matcher_udiv2_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv2_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv_sound
    (hmatch : __bv_abstraction_lemma_udiv x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) true := by
  fun_cases __bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_1___bv_abstraction_lemma_udiv] at hmatch }
  case case5 ps c pt px d powerTerm hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hPower⟩
      rcases aliases3 hAliases with ⟨hps, hpt, hpx⟩
      subst ps; subst pt; subst px
      let p : Raw.Pred := .imp (.eq .s (.lit c))
        (.eq .t (.lshr .x (.lit d)))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy rfl hpBool
      have hcTy := hLits c (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hdTy := hLits d (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      obtain ⟨cb, hcEval⟩ := eval_as_bvValue M hM c w hcTy
      obtain ⟨db, hdEval⟩ := eval_as_bvValue M hM d w hdTy
      obtain ⟨i, hdz⟩ := power_match_arg_numeral c d hPower
      have hi0 : 0 ≤ i := by
        have hdi : (db.toNat : Int) = i :=
          to_z_numeral_eval M d w db i hdz hdEval
        rw [← hdi]
        exact Int.natCast_nonneg _
      have hdi : (db.toNat : Int) = i :=
        to_z_numeral_eval M d w db i hdz hdEval
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
          (__smtx_model_eval_bvudiv
            (__smtx_model_eval M (__eo_to_smt x))
            (__smtx_model_eval M (__eo_to_smt s)))
          (__smtx_model_eval M (__eo_to_smt t)))
        (__smtx_model_eval_imp
          (__smtx_model_eval_eq
            (__smtx_model_eval M (__eo_to_smt s))
            (__smtx_model_eval M (__eo_to_smt c)))
          (__smtx_model_eval_eq
            (__smtx_model_eval M (__eo_to_smt t))
            (__smtx_model_eval_bvlshr
              (__smtx_model_eval M (__eo_to_smt x))
              (__smtx_model_eval M (__eo_to_smt d))))) = SmtValue.Boolean true
      rw [hx, hs, ht, hcEval, hdEval, eval_bvudiv_bvValue (by omega),
        eval_bvlshr_bvValue, eval_eq_bvValue, eval_eq_bvValue, eval_eq_bvValue]
      simp only [__smtx_model_eval_imp, __smtx_model_eval_not,
        __smtx_model_eval_or, native_not, native_or]
      congr 1
      change (!decide (xb.smtUDiv sb = tb) ||
        (!decide (sb = cb) || decide (tb = xb >>> db.toNat))) = true
      apply Dsl.bool_imp_true_of
      intro hAnte
      apply Dsl.bool_imp_true_of
      intro hsc
      have hsPow : sb = BitVec.twoPow w i.toNat := hsc.trans hcb
      have hq := BvAbstraction.udiv1 xb sb tb i.toNat hsPow hiw hAnte
      have hdb : db.toNat = i.toNat := by omega
      exact decide_eq_true (by simpa [hdb] using hq)
    · exact matcher_udiv1_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_udiv1_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

end

end Matcher
end BvAbstraction
