module

public import Cpc.Proofs.RuleSupport.StrInReConsume.Normalization
import all Cpc.Proofs.RuleSupport.StrInReConsume.Normalization

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace RuleProofs

theorem str_re_consume_model_rel
    (M : SmtModel) (hM : model_wf M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hSide : side = __str_re_consume s r)
    (hSideNe : side ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  rcases str_re_consume_translation_facts s r side hEqTrans with
    ⟨_hStrInTrans, _hSideTrans, _hSTy, _hRTy, _hEqBool⟩
  rcases str_re_consume_input_eval M hM s r side hEqTrans with
    ⟨_ss, _rv, _hSEval, _hREval, _hStrInEval⟩
  rcases str_re_consume_side_eval_bool M hM s r side hEqTrans with
    ⟨_sideBool, _hSideEval⟩
  rcases str_re_consume_terms_ne_stuck s r side hEqTrans with
    ⟨hSNe, hRNe, _hSideTransNe⟩
  have hRecSemantic :
      ∀ s0 r0 fuel0,
        StrInReConsumeInternal.str_re_consume_rec_semantic_motive M s0 r0 fuel0 := by
    intro s0 r0 fuel0
    refine __str_re_consume_rec.induct
      (StrInReConsumeInternal.str_re_consume_inter_semantic_motive M)
      (StrInReConsumeInternal.str_re_consume_rec_semantic_motive M)
      (StrInReConsumeInternal.str_re_consume_union_semantic_motive M)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ s0 r0 fuel0
    rotate_left 5
    · intro r fuel
      constructor
      · intro side hSTy _hRTy _hSide _hFalse
        rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
          TranslationProofs.smtx_typeof_none] at hSTy
        cases hSTy
      · intro side hSTy _hRTy _hSide _hMemEq
        rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
          TranslationProofs.smtx_typeof_none] at hSTy
        cases hSTy
    · intro s fuel hS
      constructor
      · intro side _hSTy hRTy _hSide _hFalse
        rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
          TranslationProofs.smtx_typeof_none] at hRTy
        cases hRTy
      · intro side _hSTy hRTy _hSide _hMemEq
        rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
          TranslationProofs.smtx_typeof_none] at hRTy
        cases hRTy
    · intro s r hS hR
      constructor
      · intro side _hSTy _hRTy hSide hFalse
        exfalso
        subst side
        cases s <;> cases r <;> simp [__str_re_consume_rec] at hS hR hFalse
      · intro side _hSTy _hRTy hSide hMemEq
        exfalso
        subst side
        cases s <;> cases r <;> simp [__str_re_consume_rec,
          __str_membership_re, StrInReConsumeInternal.consume_elim_unflat_stuck_early_local] at hS hR hMemEq
    · intro s1 s2 r2 fuel hFuel ih
      exact str_re_consume_rec_re_concat_empty_left_semantic_from_ih M hM
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        r2 fuel (by simp) hFuel ih
    · intro s1 s2 s3 r2 fuel hFuel hS3Ne ih
      exact str_re_consume_rec_str_concat_str_to_re_semantic_from_ih
        M hM s1 s2 s3 r2 fuel hFuel hS3Ne ih
    · intro s1 s2 s3 s5 r2 fuel hFuel ih
      exact str_re_consume_rec_str_concat_re_range_semantic_from_ih
        M hM s1 s2 s3 s5 r2 fuel hFuel ih
    · intro s1 s2 r2 fuel hFuel ih
      exact str_re_consume_rec_str_concat_re_allchar_semantic_from_ih
        M hM s1 s2 r2 fuel hFuel ih
    · intro s1 s2 r3 r2 fc fr _v0 _v1 _v3 _v4 _v5 ihLeft ihRight
        _ihLeftAgain ihResidual
      exact str_re_consume_rec_str_concat_re_mult_concat_fuel_semantic_from_ih
        M hM s1 s2 r3 r2 fc fr ihLeft ihRight ihResidual
    · intro s1 s2 r3 r2 fuel hFuel hNotFuelConcat
      exact str_re_consume_rec_semantic_of_side_eq_str_in_re_local M hM
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.re_mult) r3))
          r2)
        fuel
        (str_re_consume_rec_str_concat_re_mult_non_concat_fuel_eq
          s1 s2 r3 r2 fuel hFuel hNotFuelConcat)
    rotate_left
    · intro s r fuel hS hFuel _hNotConcat ih
      exact str_re_consume_rec_re_concat_empty_left_semantic_from_ih
        M hM s r fuel hS hFuel ih
    · intro s r1 r2 fuel hS hFuel ih
      constructor
      · intro side hSTy hRTy hSide hFalse
        exact ih.1 side hSTy hRTy (by
          rw [hSide, str_re_consume_rec_re_inter_eq s r1 r2 fuel hS
            hFuel]) hFalse
      · intro side hSTy hRTy hSide hMemEq
        exact ih.2 side hSTy hRTy (by
          rw [hSide, str_re_consume_rec_re_inter_eq s r1 r2 fuel hS
            hFuel]) hMemEq
    · intro s r1 r2 fuel hS hFuel ih
      constructor
      · intro side hSTy hRTy hSide hFalse
        exact ih.1 side hSTy hRTy (by
          rw [hSide, str_re_consume_rec_re_union_eq s r1 r2 fuel hS
            hFuel]) hFalse
      · intro side hSTy hRTy hSide hMemEq
        exact ih.2 side hSTy hRTy (by
          rw [hSide, str_re_consume_rec_re_union_eq s r1 r2 fuel hS
            hFuel]) hMemEq
    · intro s r fuel hS hR hFuel hNotStrConcatEmpty
        hNotStrConcatStrToRe hNotStrConcatRange hNotStrConcatAllchar
        hNotStrConcatMultFuel hNotStrConcatMult hNotStrConcatConcat
        hNotRConcatEmpty hNotRInter hNotRUnion
      exact str_re_consume_rec_semantic_of_side_eq_str_in_re_local M hM
        s r fuel
        (str_re_consume_rec_default_eq s r fuel hS hR hFuel
          hNotRConcatEmpty hNotRInter hNotRUnion hNotStrConcatEmpty
          hNotStrConcatStrToRe hNotStrConcatRange hNotStrConcatAllchar
          hNotStrConcatMult hNotStrConcatConcat hNotStrConcatMultFuel)
    · intro r fuel
      constructor
      · intro side hSTy _hRTy _hSide _hFalse
        rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
          TranslationProofs.smtx_typeof_none] at hSTy
        cases hSTy
      · intro side hSTy _hRTy _hSide _hMemEq
        rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
          TranslationProofs.smtx_typeof_none] at hSTy
        cases hSTy
    · intro s r hS
      constructor
      · intro side _hSTy _hRTy hSide hFalse
        exfalso
        subst side
        cases s <;> simp [__str_re_consume_union] at hS hFalse
      · intro side _hSTy _hRTy hSide hMemEq
        exfalso
        subst side
        cases s <;> simp [__str_re_consume_union,
          __str_membership_re, StrInReConsumeInternal.consume_elim_unflat_stuck_early_local] at hS hMemEq
    rotate_left
    rotate_left
    · intro s r fuel hS hFuel hNotNone hNotUnion
      constructor
      · intro side _hSTy _hRTy hSide hFalse
        have hSideStuck : side = Term.Stuck := by
          rw [hSide, str_re_consume_union_default_eq s r fuel hS hFuel
            hNotNone hNotUnion]
        rw [hSideStuck] at hFalse
        cases hFalse
      · intro side _hSTy _hRTy hSide hMemEq
        have hSideStuck : side = Term.Stuck := by
          rw [hSide, str_re_consume_union_default_eq s r fuel hS hFuel
            hNotNone hNotUnion]
        rw [hSideStuck] at hMemEq
        simp [__str_membership_re, StrInReConsumeInternal.consume_elim_unflat_stuck_early_local] at hMemEq
    · intro r fuel
      constructor
      · intro side hSTy _hRTy _hSide _hFalse
        rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
          TranslationProofs.smtx_typeof_none] at hSTy
        cases hSTy
      · intro side hSTy _hRTy _hSide _hMemEq
        rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
          TranslationProofs.smtx_typeof_none] at hSTy
        cases hSTy
    · intro s r hS
      constructor
      · intro side _hSTy _hRTy hSide hFalse
        exfalso
        subst side
        cases s <;> simp [__str_re_consume_inter] at hS hFalse
      · intro side _hSTy _hRTy hSide hMemEq
        exfalso
        subst side
        cases s <;> simp [__str_re_consume_inter,
          __str_membership_re, StrInReConsumeInternal.consume_elim_unflat_stuck_early_local] at hS hMemEq
    rotate_left
    rotate_left
    · intro s r fuel hS hFuel hNotAll hNotInter
      constructor
      · intro side _hSTy _hRTy hSide hFalse
        have hSideStuck : side = Term.Stuck := by
          rw [hSide, str_re_consume_inter_default_eq s r fuel hS hFuel
            hNotAll hNotInter]
        rw [hSideStuck] at hFalse
        cases hFalse
      · intro side _hSTy _hRTy hSide hMemEq
        have hSideStuck : side = Term.Stuck := by
          rw [hSide, str_re_consume_inter_default_eq s r fuel hS hFuel
            hNotAll hNotInter]
        rw [hSideStuck] at hMemEq
        simp [__str_membership_re, StrInReConsumeInternal.consume_elim_unflat_stuck_early_local] at hMemEq
    rotate_left
    · intro s r fuel hS hFuel ih
      exact str_re_consume_union_re_none_semantic_from_ih
        M hM s r fuel hS hFuel ih
    rotate_left
    · intro s r fuel hS hFuel ih
      exact str_re_consume_inter_re_all_semantic_from_ih
        M hM s r fuel hS hFuel ih
    rotate_left
    · intro s1 s2 r1 r2 fuel hFuel hR1Empty hR1StrToRe hR1Range
        hR1Allchar hFuelMult hR1Mult _v0 _v1 ihLeft _ihLeftAgain
        ihResidual
      exact str_re_consume_rec_str_concat_re_concat_semantic_from_ih
        M hM s1 s2 r1 r2 fuel hFuel hR1Empty hR1StrToRe hR1Range
        hR1Allchar hFuelMult hR1Mult ihLeft ihResidual
    · intro s c1 c2 fuel hS hFuel hC2Ne ihLeft ihRight
      exact str_re_consume_union_semantic_from_ih M hM s c1 c2 fuel
        hS hFuel hC2Ne ihLeft ihRight
    · intro s c1 c2 fuel hS hFuel hC2Ne ihLeft ihRight
      exact str_re_consume_inter_semantic_from_ih M hM s c1 c2 fuel
        hS hFuel hC2Ne ihRight ihLeft
  have hRecNoPrefix :
      ∀ s0 r0 fuel0,
        StrInReConsumeInternal.str_re_consume_rec_no_prefix_motive M s0 r0 fuel0 :=
    fun s0 r0 fuel0 => (hRecSemantic s0 r0 fuel0).1
  have hRecResidual :
      ∀ s0 r0 fuel0,
        StrInReConsumeInternal.str_re_consume_rec_residual_motive M s0 r0 fuel0 :=
    fun s0 r0 fuel0 => (hRecSemantic s0 r0 fuel0).2
  have hRecFalseWholeNativeProgress :
      ∀ s0 r0 fuel0 side0,
        __smtx_typeof (__eo_to_smt s0) = SmtType.Seq SmtType.Char ->
        __smtx_typeof (__eo_to_smt r0) = SmtType.RegLan ->
        side0 = __str_re_consume_rec s0 r0 fuel0 ->
        side0 = Term.Boolean false ->
        ∀ ss rv,
          __smtx_model_eval M (__eo_to_smt s0) = SmtValue.Seq ss ->
          __smtx_model_eval M (__eo_to_smt r0) = SmtValue.RegLan rv ->
            native_str_in_re (native_unpack_string ss) rv = false := by
    intro s0 r0 fuel0 side0 hSTy hRTy hSide0 hFalse ss rv hSEval hREval
    have hNoPrefix :=
      hRecNoPrefix s0 r0 fuel0 side0 hSTy hRTy hSide0 hFalse ss rv
        hSEval hREval
    exact hNoPrefix (native_unpack_string ss) [] (by simp)
  have hOriginalFalseOfInputNativeEqAndRecFalseProgress :
      ∀ nextS nextR side0,
        __smtx_typeof (__eo_to_smt nextS) = SmtType.Seq SmtType.Char ->
        __smtx_typeof (__eo_to_smt nextR) = SmtType.RegLan ->
        side0 = __str_re_consume_rec nextS nextR nextS ->
        side0 = Term.Boolean false ->
        (∀ ss rv nextSs nextRv,
          __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
          __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
          __smtx_model_eval M (__eo_to_smt nextS) =
            SmtValue.Seq nextSs ->
          __smtx_model_eval M (__eo_to_smt nextR) =
            SmtValue.RegLan nextRv ->
            native_str_in_re (native_unpack_string ss) rv =
              native_str_in_re (native_unpack_string nextSs) nextRv) ->
        ∀ ss rv,
          __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
          __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
            native_str_in_re (native_unpack_string ss) rv = false := by
    intro nextS nextR side0 hNextSTy hNextRTy hSide0 hFalse
      hInputNativeEq ss rv hSEval hREval
    rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM
        (__eo_to_smt nextS) hNextSTy with
      ⟨nextSs, hNextSEval⟩
    rcases smt_model_eval_reglan_of_type M hM nextR hNextRTy with
      ⟨nextRv, hNextREval⟩
    have hNextFalse :
        native_str_in_re (native_unpack_string nextSs) nextRv = false :=
      hRecFalseWholeNativeProgress nextS nextR nextS side0 hNextSTy
        hNextRTy hSide0 hFalse nextSs nextRv hNextSEval hNextREval
    rw [hInputNativeEq ss rv nextSs nextRv hSEval hREval hNextSEval
      hNextREval]
    exact hNextFalse
  have hRecType :
      ∀ s0 r0 fuel0,
        StrInReConsumeInternal.str_re_consume_rec_type_motive s0 r0 fuel0 := by
    intro s0 r0 fuel0
    refine __str_re_consume_rec.induct
      (StrInReConsumeInternal.str_re_consume_inter_type_motive)
      (StrInReConsumeInternal.str_re_consume_rec_type_motive)
      (StrInReConsumeInternal.str_re_consume_union_type_motive)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ s0 r0 fuel0
    rotate_left 5
    · intro r fuel hSTy _hRTy _hNe
      rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
        TranslationProofs.smtx_typeof_none] at hSTy
      cases hSTy
    · intro s fuel hS _hSTy hRTy _hNe
      rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
        TranslationProofs.smtx_typeof_none] at hRTy
      cases hRTy
    · intro s r hS hR _hSTy _hRTy hNe
      exfalso
      exact str_re_consume_rec_stuck_fuel_absurd s r
        (__str_re_consume_rec s r Term.Stuck) hS hR rfl hNe
    · intro s1 s2 r2 fuel hFuel ih hSTy hRTy hNe
      let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
      let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
      let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) eps) r2
      have hR2Ty : __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan :=
        (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local eps r2
          (by simpa [eps, rConcat] using hRTy)).2
      have hEq :
          __str_re_consume_rec sConcat rConcat fuel =
            __str_re_consume_rec sConcat r2 fuel := by
        simpa [sConcat, eps, rConcat] using
          str_re_consume_rec_re_concat_empty_left_eq sConcat r2 fuel
            (by simp [sConcat]) hFuel
      have hReducedNe : __str_re_consume_rec sConcat r2 fuel ≠ Term.Stuck := by
        intro hBad
        apply hNe
        rw [hEq, hBad]
      rw [hEq]
      exact ih (by simpa [sConcat] using hSTy) hR2Ty hReducedNe
    · intro s1 s2 s3 r2 fuel hFuel hS3Ne ih hSTy hRTy hNe
      let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
      let head := Term.Apply (Term.UOp UserOp.str_to_re) s3
      let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) head) r2
      let reduced := __str_re_consume_rec s2 r2 fuel
      let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) sConcat) rConcat
      let condEq := __eo_eq s1 s3
      let condLen :=
        __eo_and (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
          (__eo_is_eq (__eo_len s3) (Term.Numeral 1))
      let lenIte := __eo_ite condLen (Term.Boolean false) fallback
      have hS2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq SmtType.Char :=
        (str_concat_args_of_seq_type s1 s2 SmtType.Char
          (by simpa [sConcat] using hSTy)).2
      have hR2Ty : __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan :=
        (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local head r2
          (by simpa [head, rConcat] using hRTy)).2
      rw [__str_re_consume_rec.eq_5 fuel s1 s2 s3 r2 hS3Ne hFuel]
      have hWholeNe :
          __eo_ite condEq reduced lenIte ≠ Term.Stuck := by
        simpa [sConcat, head, rConcat, reduced, fallback, condEq, condLen,
          lenIte, __str_re_consume_rec.eq_5 fuel s1 s2 s3 r2 hS3Ne
            hFuel] using hNe
      exact StrInReConsumeInternal.smt_typeof_eo_ite_of_selected_local condEq reduced lenIte
        (fun hReducedNe => ih hS2Ty hR2Ty
          (by simpa [reduced] using hReducedNe))
        (fun hLenIteNe =>
          StrInReConsumeInternal.smt_typeof_eo_ite_of_branches_local condLen (Term.Boolean false)
            fallback StrInReConsumeInternal.smt_typeof_boolean_false_local
            (StrInReConsumeInternal.smt_typeof_str_in_re_of_types_local sConcat rConcat
              (by simpa [sConcat] using hSTy)
              (by simpa [rConcat] using hRTy))
            (by simpa [lenIte] using hLenIteNe))
        hWholeNe
    · intro s1 s2 s3 s5 r2 fuel hFuel ih hSTy hRTy hNe
      let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
      let range := Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s5
      let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) range) r2
      let reduced := __str_re_consume_rec s2 r2 fuel
      let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) sConcat) rConcat
      let condLen :=
        __eo_and (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
          (__eo_and (__eo_is_eq (__eo_len s3) (Term.Numeral 1))
            (__eo_is_eq (__eo_len s5) (Term.Numeral 1)))
      let condMatch :=
        __eo_requires (__eo_is_str s1) (Term.Boolean true)
          (__str_eval_str_in_re_rec
            (__str_flatten
              (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s1))
            range)
      let matchIte := __eo_ite condMatch reduced (Term.Boolean false)
      have hS2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq SmtType.Char :=
        (str_concat_args_of_seq_type s1 s2 SmtType.Char
          (by simpa [sConcat] using hSTy)).2
      have hR2Ty : __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan :=
        (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local range r2
          (by simpa [range, rConcat] using hRTy)).2
      rw [__str_re_consume_rec.eq_6 fuel s1 s2 s3 s5 r2 hFuel]
      have hWholeNe :
          __eo_ite condLen matchIte fallback ≠ Term.Stuck := by
        simpa [sConcat, range, rConcat, reduced, fallback, condLen,
          condMatch, matchIte,
          __str_re_consume_rec.eq_6 fuel s1 s2 s3 s5 r2 hFuel] using hNe
      exact StrInReConsumeInternal.smt_typeof_eo_ite_of_selected_local condLen matchIte fallback
        (fun hMatchIteNe =>
          StrInReConsumeInternal.smt_typeof_eo_ite_of_selected_local condMatch reduced
            (Term.Boolean false)
            (fun hReducedNe => ih hS2Ty hR2Ty
              (by simpa [reduced] using hReducedNe))
            (fun _hFalseNe => StrInReConsumeInternal.smt_typeof_boolean_false_local)
            (by simpa [matchIte] using hMatchIteNe))
        (fun _hFallbackNe =>
          StrInReConsumeInternal.smt_typeof_str_in_re_of_types_local sConcat rConcat
            (by simpa [sConcat] using hSTy)
            (by simpa [rConcat] using hRTy))
        hWholeNe
    · intro s1 s2 r2 fuel hFuel ih hSTy hRTy hNe
      let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
      let allchar := Term.UOp UserOp.re_allchar
      let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) allchar) r2
      let reduced := __str_re_consume_rec s2 r2 fuel
      let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) sConcat) rConcat
      let cond := __eo_is_eq (__eo_len s1) (Term.Numeral 1)
      have hS2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq SmtType.Char :=
        (str_concat_args_of_seq_type s1 s2 SmtType.Char
          (by simpa [sConcat] using hSTy)).2
      have hR2Ty : __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan :=
        (StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local allchar r2
          (by simpa [allchar, rConcat] using hRTy)).2
      rw [__str_re_consume_rec.eq_7 fuel s1 s2 r2 hFuel]
      have hWholeNe : __eo_ite cond reduced fallback ≠ Term.Stuck := by
        simpa [sConcat, allchar, rConcat, reduced, fallback, cond,
          __str_re_consume_rec.eq_7 fuel s1 s2 r2 hFuel] using hNe
      exact StrInReConsumeInternal.smt_typeof_eo_ite_of_selected_local cond reduced fallback
        (fun hReducedNe => ih hS2Ty hR2Ty
          (by simpa [reduced] using hReducedNe))
        (fun _hFallbackNe =>
          StrInReConsumeInternal.smt_typeof_str_in_re_of_types_local sConcat rConcat
            (by simpa [sConcat] using hSTy)
            (by have hsimpa := hRTy; (try simp [rConcat] at hsimpa ⊢); exact hsimpa))
        hWholeNe
    · intro s1 s2 r3 r2 fc fr _v0 _v1 _v3 _v4 _v5
        ihLeft ihRight _ihLeftAgain ihResidual hSTy hRTy hNe
      let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
      let fuelConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr
      let rConcat :=
        Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.re_mult) r3))
          r2
      let left := __str_re_consume_rec sConcat r3 fuelConcat
      let right := __str_re_consume_rec sConcat r2 fuelConcat
      let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re)
        sConcat) rConcat
      let condLeftFalse := __eo_eq left (Term.Boolean false)
      let condMem :=
        __eo_eq (__str_membership_re left)
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
      let condRightFalse := __eo_is_eq right (Term.Boolean false)
      let condSame := __eo_eq sConcat (__str_membership_str left)
      let residual := __str_re_consume_rec (__str_membership_str left)
        rConcat fr
      let sameIte := __eo_ite condSame fallback residual
      let rightFalseIte := __eo_ite condRightFalse sameIte fallback
      let memIte := __eo_ite condMem rightFalseIte fallback
      let whole := __eo_ite condLeftFalse right memIte
      have hRConcatArgs :
          __smtx_typeof
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r3)) =
            SmtType.RegLan ∧
          __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan :=
        StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local
          (Term.Apply (Term.UOp UserOp.re_mult) r3) r2
          (by simpa [rConcat] using hRTy)
      have hR3Ty : __smtx_typeof (__eo_to_smt r3) = SmtType.RegLan :=
        StrInReConsumeInternal.re_mult_arg_type_of_reglan_consume_local r3 hRConcatArgs.1
      have hRecEq :
          __str_re_consume_rec sConcat rConcat fuelConcat = whole := by
        simpa [sConcat, fuelConcat, rConcat, left, right, fallback,
          condLeftFalse, condMem, condRightFalse, condSame, residual,
          sameIte, rightFalseIte, memIte, whole] using
          __str_re_consume_rec.eq_8 s1 s2 r3 r2 fc fr
      have hWholeNe : whole ≠ Term.Stuck := by
        intro hBad
        exact hNe (by rw [hRecEq, hBad])
      rw [hRecEq]
      rcases eo_ite_cases_of_ne_stuck condLeftFalse right memIte
          hWholeNe with hLeftFalse | hLeftNotFalse
      · have hRightNe : right ≠ Term.Stuck := by
          intro hBad
          apply hWholeNe
          simpa [whole, hLeftFalse, eo_ite_true] using hBad
        simpa [whole, hLeftFalse, eo_ite_true, right] using
          ihRight (by have hsimpa := hSTy; (try simp at hsimpa ⊢); exact hsimpa) hRConcatArgs.2 (by simpa [right] using hRightNe)
      · have hMemIteNe : memIte ≠ Term.Stuck := by
          intro hBad
          apply hWholeNe
          simpa [whole, hLeftNotFalse, eo_ite_false] using hBad
        rcases eo_ite_cases_of_ne_stuck condMem rightFalseIte fallback
            hMemIteNe with hMemEps | hMemNotEps
        · have hRightFalseIteNe : rightFalseIte ≠ Term.Stuck := by
            intro hBad
            apply hMemIteNe
            simpa [memIte, hMemEps, eo_ite_true] using hBad
          rcases eo_ite_cases_of_ne_stuck condRightFalse sameIte fallback
              hRightFalseIteNe with hRightFalse | hRightNotFalse
          · have hSameIteNe : sameIte ≠ Term.Stuck := by
              intro hBad
              apply hRightFalseIteNe
              simpa [rightFalseIte, hRightFalse, eo_ite_true] using hBad
            rcases eo_ite_cases_of_ne_stuck condSame fallback residual
                hSameIteNe with hSame | hDifferent
            · simpa [whole, hLeftNotFalse, eo_ite_false, memIte,
                hMemEps, eo_ite_true, rightFalseIte, hRightFalse,
                sameIte, hSame, fallback] using
                StrInReConsumeInternal.smt_typeof_str_in_re_of_types_local sConcat rConcat
                  (by simpa [sConcat] using hSTy)
                  (by simpa [rConcat] using hRTy)
            · have hResidualNe : residual ≠ Term.Stuck := by
                intro hBad
                apply hSameIteNe
                simpa [sameIte, hDifferent, eo_ite_false] using hBad
              have hLeftMemEq :
                  __str_membership_re left =
                    Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String []) :=
                (eq_of_eo_eq_true (__str_membership_re left)
                  (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
                  (by simpa [left, condMem] using hMemEps)).symm
              have hTailTy :
                  __smtx_typeof (__eo_to_smt (__str_membership_str left)) =
                    SmtType.Seq SmtType.Char :=
                (hRecResidual sConcat r3 fuelConcat left
                  (by simpa [sConcat] using hSTy) hR3Ty rfl
                  (StrInReConsumeInternal.consume_elim_unflat_eps_of_mem_eps_early_local
                    hLeftMemEq)).1
              simpa [whole, hLeftNotFalse, eo_ite_false, memIte,
                hMemEps, eo_ite_true, rightFalseIte, hRightFalse,
                sameIte, hDifferent, residual] using
                ihResidual hTailTy (by have hsimpa := hRTy; (try simp at hsimpa ⊢); exact hsimpa) (by simpa [residual] using hResidualNe)
          · simpa [whole, hLeftNotFalse, eo_ite_false, memIte,
              hMemEps, eo_ite_true, rightFalseIte, hRightNotFalse,
              eo_ite_false, fallback] using
              StrInReConsumeInternal.smt_typeof_str_in_re_of_types_local sConcat rConcat
                (by simpa [sConcat] using hSTy)
                (by simpa [rConcat] using hRTy)
        · simpa [whole, hLeftNotFalse, eo_ite_false, memIte, hMemNotEps,
            eo_ite_false, fallback] using
            StrInReConsumeInternal.smt_typeof_str_in_re_of_types_local sConcat rConcat
              (by simpa [sConcat] using hSTy)
              (by simpa [rConcat] using hRTy)
    · intro s1 s2 r3 r2 fuel hFuel hNotFuelConcat hSTy hRTy _hNe
      let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
      let rConcat :=
        Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.re_mult) r3))
          r2
      have hEq :=
        str_re_consume_rec_str_concat_re_mult_non_concat_fuel_eq
          s1 s2 r3 r2 fuel hFuel hNotFuelConcat
      rw [hEq]
      exact StrInReConsumeInternal.smt_typeof_str_in_re_of_types_local sConcat rConcat
        (by simpa [sConcat] using hSTy)
        (by simpa [rConcat] using hRTy)
    rotate_left
    · intro s r fuel hS hFuel _hNotConcat ih hSTy hRTy hNe
      let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
      let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) eps) r
      have hArgs :=
        StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local eps r
          (by simpa [eps, rConcat] using hRTy)
      have hEq :=
        str_re_consume_rec_re_concat_empty_left_eq s r fuel hS hFuel
      have hReducedNe : __str_re_consume_rec s r fuel ≠ Term.Stuck := by
        intro hBad
        apply hNe
        rw [hEq, hBad]
      rw [hEq]
      exact ih hSTy hArgs.2 hReducedNe
    · intro s r1 r2 fuel hS hFuel ih hSTy hRTy hNe
      have hEq := str_re_consume_rec_re_inter_eq s r1 r2 fuel hS hFuel
      have hReducedNe :
          __str_re_consume_inter s
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r1) r2)
              fuel ≠ Term.Stuck := by
        intro hBad
        apply hNe
        rw [hEq, hBad]
      rw [hEq]
      exact ih hSTy hRTy hReducedNe
    · intro s r1 r2 fuel hS hFuel ih hSTy hRTy hNe
      have hEq := str_re_consume_rec_re_union_eq s r1 r2 fuel hS hFuel
      have hReducedNe :
          __str_re_consume_union s
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r1) r2)
              fuel ≠ Term.Stuck := by
        intro hBad
        apply hNe
        rw [hEq, hBad]
      rw [hEq]
      exact ih hSTy hRTy hReducedNe
    · intro s r fuel hS hR hFuel hNotStrConcatEmpty
        hNotStrConcatStrToRe hNotStrConcatRange hNotStrConcatAllchar
        hNotStrConcatMultFuel hNotStrConcatMult hNotStrConcatConcat
        hNotRConcatEmpty hNotRInter hNotRUnion hSTy hRTy _hNe
      have hEq :=
        str_re_consume_rec_default_eq s r fuel hS hR hFuel
          hNotRConcatEmpty hNotRInter hNotRUnion hNotStrConcatEmpty
          hNotStrConcatStrToRe hNotStrConcatRange hNotStrConcatAllchar
          hNotStrConcatMult hNotStrConcatConcat hNotStrConcatMultFuel
      rw [hEq]
      exact StrInReConsumeInternal.smt_typeof_str_in_re_of_types_local s r hSTy hRTy
    · intro r fuel hSTy _hRTy _hNe
      rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
        TranslationProofs.smtx_typeof_none] at hSTy
      cases hSTy
    · intro s r hS _hSTy _hRTy hNe
      exfalso
      exact str_re_consume_union_stuck_fuel_absurd s r
        (__str_re_consume_union s r Term.Stuck) hS rfl hNe
    rotate_left
    rotate_left
    · intro s r fuel hS hFuel hNotNone hNotUnion _hSTy _hRTy hNe
      exfalso
      apply hNe
      exact str_re_consume_union_default_eq s r fuel hS hFuel
        hNotNone hNotUnion
    · intro r fuel hSTy _hRTy _hNe
      rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
        TranslationProofs.smtx_typeof_none] at hSTy
      cases hSTy
    · intro s r hS _hSTy _hRTy hNe
      exfalso
      exact str_re_consume_inter_stuck_fuel_absurd s r
        (__str_re_consume_inter s r Term.Stuck) hS rfl hNe
    rotate_left
    rotate_left
    · intro s r fuel hS hFuel hNotAll hNotInter _hSTy _hRTy hNe
      exfalso
      apply hNe
      exact str_re_consume_inter_default_eq s r fuel hS hFuel
        hNotAll hNotInter
    rotate_left
    · intro s r fuel hS hFuel ih hSTy hRTy hNe
      let none := Term.UOp UserOp.re_none
      let union := Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) none
      have hArgs := StrInReConsumeInternal.re_union_arg_types_of_reglan_consume_local r none
        (by simpa [none, union] using hRTy)
      have hEq := str_re_consume_union_re_none_eq s r fuel hS hFuel
      have hReducedNe : __str_re_consume_rec s r fuel ≠ Term.Stuck := by
        intro hBad
        apply hNe
        rw [hEq, hBad]
      rw [hEq]
      exact ih hSTy hArgs.1 hReducedNe
    rotate_left
    · intro s r fuel hS hFuel ih hSTy hRTy hNe
      let all := Term.UOp UserOp.re_all
      let inter := Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) all
      have hArgs := StrInReConsumeInternal.re_inter_arg_types_of_reglan_consume_local r all
        (by simpa [all, inter] using hRTy)
      have hEq := str_re_consume_inter_re_all_eq s r fuel hS hFuel
      have hReducedNe : __str_re_consume_rec s r fuel ≠ Term.Stuck := by
        intro hBad
        apply hNe
        rw [hEq, hBad]
      rw [hEq]
      exact ih hSTy hArgs.1 hReducedNe
    rotate_left
    · intro s1 s2 r1 r2 fuel hFuel hR1Empty hR1StrToRe hR1Range
        hR1Allchar hFuelMult hR1Mult _v0 _v1 ihLeft _ihLeftAgain
        ihResidual hSTy hRTy hNe
      let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
      let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2
      let left := __str_re_consume_rec sConcat r1 fuel
      let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re)
        sConcat) rConcat
      let condLeftFalse := __eo_is_eq left (Term.Boolean false)
      let condMem :=
        __eo_is_eq (__str_membership_re left)
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
      let residual := __str_re_consume_rec (__str_membership_str left) r2 fuel
      let memIte := __eo_ite condMem residual fallback
      let whole := __eo_ite condLeftFalse (Term.Boolean false) memIte
      have hArgs := StrInReConsumeInternal.re_concat_arg_types_of_reglan_consume_local r1 r2
        (by simpa [rConcat] using hRTy)
      have hRecEq :
          __str_re_consume_rec sConcat rConcat fuel = whole := by
        simpa [sConcat, rConcat, left, fallback, condLeftFalse, condMem,
          residual, memIte, whole] using
          __str_re_consume_rec.eq_10 fuel s1 s2 r1 r2 hR1Empty
            hR1StrToRe hR1Range hR1Allchar hR1Mult hFuel hFuelMult
      have hWholeNe : whole ≠ Term.Stuck := by
        intro hBad
        exact hNe (by rw [hRecEq, hBad])
      rw [hRecEq]
      rcases eo_ite_cases_of_ne_stuck condLeftFalse (Term.Boolean false)
          memIte hWholeNe with hLeftFalse | hLeftNotFalse
      · simpa [whole, hLeftFalse, eo_ite_true] using
          StrInReConsumeInternal.smt_typeof_boolean_false_local
      · have hMemIteNe : memIte ≠ Term.Stuck := by
          intro hBad
          apply hWholeNe
          simpa [whole, hLeftNotFalse, eo_ite_false] using hBad
        rcases eo_ite_cases_of_ne_stuck condMem residual fallback
            hMemIteNe with hMemEps | hMemNotEps
        · have hResidualNe : residual ≠ Term.Stuck := by
            intro hBad
            apply hMemIteNe
            simpa [memIte, hMemEps, eo_ite_true] using hBad
          have hLeftMemEq :
              __str_membership_re left =
                Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) :=
            eq_of_eo_is_eq_true_consume_local (__str_membership_re left)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
              (by simpa [left, condMem] using hMemEps)
          have hTailTy :
              __smtx_typeof (__eo_to_smt (__str_membership_str left)) =
                SmtType.Seq SmtType.Char :=
            (hRecResidual sConcat r1 fuel left
              (by simpa [sConcat] using hSTy) hArgs.1 rfl
              (StrInReConsumeInternal.consume_elim_unflat_eps_of_mem_eps_early_local
                hLeftMemEq)).1
          simpa [whole, hLeftNotFalse, eo_ite_false, memIte, hMemEps,
            eo_ite_true, residual] using
            ihResidual hTailTy hArgs.2 (by simpa [residual] using hResidualNe)
        · simpa [whole, hLeftNotFalse, eo_ite_false, memIte, hMemNotEps,
            eo_ite_false, fallback] using
            StrInReConsumeInternal.smt_typeof_str_in_re_of_types_local sConcat rConcat
              (by simpa [sConcat] using hSTy)
              (by simpa [rConcat] using hRTy)
    · intro s c1 c2 fuel hS hFuel hC2Ne ihLeft ihRight hSTy hRTy hNe
      let union := Term.Apply (Term.Apply (Term.UOp UserOp.re_union) c1) c2
      let left := __str_re_consume_rec s c1 fuel
      let right := __str_re_consume_union s c2 fuel
      let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
      let condLeftFalse := __eo_is_eq left (Term.Boolean false)
      let condMem := __eo_eq (__str_membership_re left) eps
      let condRightFalse := __eo_is_eq right (Term.Boolean false)
      let condSame := __eo_eq left right
      let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
        union
      let sameIte := __eo_ite condSame left fallback
      let rightIte := __eo_ite condRightFalse left sameIte
      let memIte := __eo_ite condMem rightIte fallback
      let whole := __eo_ite condLeftFalse right memIte
      have hArgs := StrInReConsumeInternal.re_union_arg_types_of_reglan_consume_local c1 c2
        (by simpa [union] using hRTy)
      have hUnionEq :
          __str_re_consume_union s union fuel = whole := by
        simpa [union, left, right, eps, condLeftFalse, condMem,
          condRightFalse, condSame, fallback, sameIte, rightIte, memIte,
          whole] using
          __str_re_consume_union.eq_4 s fuel c1 c2 hC2Ne hS hFuel
      have hWholeNe : whole ≠ Term.Stuck := by
        intro hBad
        exact hNe (by rw [hUnionEq, hBad])
      rw [hUnionEq]
      exact StrInReConsumeInternal.smt_typeof_eo_ite_of_selected_local condLeftFalse right memIte
        (fun hRightNe => ihRight hSTy hArgs.2
          (by simpa [right] using hRightNe))
        (fun hMemIteNe =>
          StrInReConsumeInternal.smt_typeof_eo_ite_of_selected_local condMem rightIte fallback
            (fun hRightIteNe =>
              StrInReConsumeInternal.smt_typeof_eo_ite_of_selected_local condRightFalse left sameIte
                (fun hLeftNe => ihLeft hSTy hArgs.1
                  (by simpa [left] using hLeftNe))
                (fun hSameIteNe =>
                  StrInReConsumeInternal.smt_typeof_eo_ite_of_selected_local condSame left fallback
                    (fun hLeftNe => ihLeft hSTy hArgs.1
                      (by simpa [left] using hLeftNe))
                    (fun _hFallbackNe =>
                      StrInReConsumeInternal.smt_typeof_str_in_re_of_types_local s union hSTy
                        (by simpa [union] using hRTy))
                    (by simpa [sameIte] using hSameIteNe))
                (by simpa [rightIte] using hRightIteNe))
            (fun _hFallbackNe =>
              StrInReConsumeInternal.smt_typeof_str_in_re_of_types_local s union hSTy
                (by simpa [union] using hRTy))
            (by simpa [memIte] using hMemIteNe))
        hWholeNe
    · intro s c1 c2 fuel hS hFuel hC2Ne ihLeft ihRight hSTy hRTy hNe
      let inter := Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) c1) c2
      let left := __str_re_consume_rec s c1 fuel
      let right := __str_re_consume_inter s c2 fuel
      let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
      let condLeftFalse := __eo_is_eq left (Term.Boolean false)
      let condMem := __eo_eq (__str_membership_re left) eps
      let condRightFalse := __eo_is_eq right (Term.Boolean false)
      let condSame := __eo_eq left right
      let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
        inter
      let sameIte := __eo_ite condSame left fallback
      let rightIte := __eo_ite condRightFalse (Term.Boolean false) sameIte
      let rightFallbackIte := __eo_ite condRightFalse (Term.Boolean false)
        fallback
      let memIte := __eo_ite condMem rightIte rightFallbackIte
      let whole := __eo_ite condLeftFalse (Term.Boolean false) memIte
      have hArgs := StrInReConsumeInternal.re_inter_arg_types_of_reglan_consume_local c1 c2
        (by simpa [inter] using hRTy)
      have hInterEq :
          __str_re_consume_inter s inter fuel = whole := by
        simpa [inter, left, right, eps, condLeftFalse, condMem,
          condRightFalse, condSame, fallback, sameIte, rightIte,
          rightFallbackIte, memIte, whole] using
          __str_re_consume_inter.eq_4 s fuel c1 c2 hC2Ne hS hFuel
      have hWholeNe : whole ≠ Term.Stuck := by
        intro hBad
        exact hNe (by rw [hInterEq, hBad])
      rw [hInterEq]
      exact StrInReConsumeInternal.smt_typeof_eo_ite_of_selected_local condLeftFalse
        (Term.Boolean false) memIte
        (fun _hFalseNe => StrInReConsumeInternal.smt_typeof_boolean_false_local)
        (fun hMemIteNe =>
          StrInReConsumeInternal.smt_typeof_eo_ite_of_selected_local condMem rightIte
            rightFallbackIte
            (fun hRightIteNe =>
              StrInReConsumeInternal.smt_typeof_eo_ite_of_selected_local condRightFalse
                (Term.Boolean false) sameIte
                (fun _hFalseNe => StrInReConsumeInternal.smt_typeof_boolean_false_local)
                (fun hSameIteNe =>
                  StrInReConsumeInternal.smt_typeof_eo_ite_of_selected_local condSame left fallback
                    (fun hLeftNe => ihRight hSTy hArgs.1
                      (by simpa [left] using hLeftNe))
                    (fun _hFallbackNe =>
                      StrInReConsumeInternal.smt_typeof_str_in_re_of_types_local s inter hSTy
                        (by simpa [inter] using hRTy))
                    (by simpa [sameIte] using hSameIteNe))
                (by simpa [rightIte] using hRightIteNe))
            (fun hRightFallbackIteNe =>
              StrInReConsumeInternal.smt_typeof_eo_ite_of_selected_local condRightFalse
                (Term.Boolean false) fallback
                (fun _hFalseNe => StrInReConsumeInternal.smt_typeof_boolean_false_local)
                (fun _hFallbackNe =>
                  StrInReConsumeInternal.smt_typeof_str_in_re_of_types_local s inter hSTy
                    (by simpa [inter] using hRTy))
                (by simpa [rightFallbackIte] using hRightFallbackIteNe))
            (by simpa [memIte] using hMemIteNe))
        hWholeNe
  have hRecModelRel :
      ∀ s0 r0 fuel0,
        StrInReConsumeInternal.str_re_consume_rec_model_rel_motive M s0 r0 fuel0 := by
    intro s0 r0 fuel0
    refine __str_re_consume_rec.induct
      (StrInReConsumeInternal.str_re_consume_inter_model_rel_motive M)
      (StrInReConsumeInternal.str_re_consume_rec_model_rel_motive M)
      (StrInReConsumeInternal.str_re_consume_union_model_rel_motive M)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ s0 r0 fuel0
    rotate_left 5
    · intro r fuel side _hEqTrans hSide hSideNe
      exfalso
      exact str_re_consume_rec_stuck_left_absurd r fuel side hSide hSideNe
    · intro s fuel hS side _hEqTrans hSide hSideNe
      exfalso
      exact str_re_consume_rec_stuck_right_absurd s fuel side hS hSide
        hSideNe
    · intro s r hS hR side _hEqTrans hSide hSideNe
      exfalso
      exact str_re_consume_rec_stuck_fuel_absurd s r side hS hR hSide
        hSideNe
    · intro s1 s2 r2 fuel hFuel ih side hEqTrans hSide hSideNe
      exact str_re_consume_rec_re_concat_empty_left_model_rel_from_ih
        M hM
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        r2 fuel side hEqTrans hSide hSideNe (by simp) hFuel ih
    · intro s1 s2 s3 r2 fuel hFuel hS3Ne ih side hEqTrans hSide
        hSideNe
      exact str_re_consume_rec_str_concat_str_to_re_model_rel_from_ih
        M hM s1 s2 s3 r2 fuel side hEqTrans hSide hSideNe hFuel
        hS3Ne ih
    · intro s1 s2 s3 s5 r2 fuel hFuel ih side hEqTrans hSide
        hSideNe
      exact str_re_consume_rec_str_concat_re_range_model_rel_from_ih
        M hM s1 s2 s3 s5 r2 fuel side hEqTrans hSide hSideNe
        hFuel ih
    · intro s1 s2 r2 fuel hFuel ih side hEqTrans hSide hSideNe
      exact str_re_consume_rec_str_concat_re_allchar_model_rel_from_ih
        M hM s1 s2 r2 fuel side hEqTrans hSide hSideNe hFuel ih
    · intro s1 s2 r3 r2 fc fr _v0 _v1 _v3 _v4 _v5
        ihLeft ihRight _ihLeftAgain ihResidual side hEqTrans hSide
        hSideNe
      let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
      let fuelConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) fc) fr
      let rConcat :=
        Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.re_mult) r3))
          r2
      let left := __str_re_consume_rec sConcat r3 fuelConcat
      let right := __str_re_consume_rec sConcat r2 fuelConcat
      let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re)
        sConcat) rConcat
      let condLeftFalse := __eo_eq left (Term.Boolean false)
      let condMem :=
        __eo_eq (__str_membership_re left)
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
      let condRightFalse := __eo_is_eq right (Term.Boolean false)
      let condSame := __eo_eq sConcat (__str_membership_str left)
      let residual := __str_re_consume_rec (__str_membership_str left)
        rConcat fr
      let sameIte := __eo_ite condSame fallback residual
      let rightFalseIte := __eo_ite condRightFalse sameIte fallback
      let memIte := __eo_ite condMem rightFalseIte fallback
      let whole := __eo_ite condLeftFalse right memIte
      have hSideWhole : side = whole := by
        rw [hSide, __str_re_consume_rec.eq_8 s1 s2 r3 r2 fc fr]
      have hWholeNe : whole ≠ Term.Stuck := by
        intro hBad
        apply hSideNe
        rw [hSideWhole, hBad]
      rcases eo_ite_cases_of_ne_stuck condLeftFalse right memIte hWholeNe with
        hLeftFalse | hLeftNotFalse
      · have hRightRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_in_re) sConcat)
                    rConcat)))
              (__smtx_model_eval M (__eo_to_smt right)) := by
          rcases str_re_consume_translation_facts sConcat rConcat side (by
              simpa [sConcat, rConcat] using hEqTrans) with
            ⟨_hStrInTrans, _hSideTrans, hSTy, hRConcatTy, _hEqBool⟩
          rcases smt_eval_reglan_of_smt_type_reglan_consume_local M hM
              (__eo_to_smt rConcat) hRConcatTy with
            ⟨rvConcat, hRConcatEval⟩
          rcases eval_re_concat_parts_consume_local M hM
              (Term.Apply (Term.UOp UserOp.re_mult) r3) r2
              rvConcat
              (by simpa [sConcat, rConcat] using hRConcatTy)
              (by simpa [sConcat, rConcat] using hRConcatEval) with
            ⟨_rvStar, _rv2, hStarTy, hR2Ty, _hStarEval, _hR2Eval, _hRv⟩
          have hR3Ty :
              __smtx_typeof (__eo_to_smt r3) = SmtType.RegLan :=
            RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_mult_arg_of_reglan
              r3 (by simpa using hStarTy)
          have hSideRight : side = right := by
            rw [hSideWhole]
            simp [whole, hLeftFalse, eo_ite_true]
          have hRightTy :
              __smtx_typeof (__eo_to_smt right) = SmtType.Bool := by
            have hSideTy := str_re_consume_side_smt_type sConcat rConcat
              side (by simpa [sConcat, rConcat] using hEqTrans)
            simpa [hSideRight, right] using hSideTy
          have hRightNe : right ≠ Term.Stuck := by
            intro hBad
            apply hSideNe
            rw [hSideRight, hBad]
          have hRightTailRel :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_in_re) sConcat)
                      r2)))
                (__smtx_model_eval M (__eo_to_smt right)) :=
            str_re_consume_rec_model_rel_from_ih_of_types M sConcat r2
              fuelConcat ihRight hSTy hR2Ty
              (by simpa [right] using hRightTy)
              (by simpa [right] using hRightNe)
          have hLeftEqFalse : left = Term.Boolean false :=
            (eq_of_eo_eq_true left (Term.Boolean false)
              (by simpa [condLeftFalse] using hLeftFalse)).symm
          have hNoNonemptyPrefix :
              ∀ ss rv3,
                __smtx_model_eval M (__eo_to_smt sConcat) =
                  SmtValue.Seq ss ->
                __smtx_model_eval M (__eo_to_smt r3) =
                  SmtValue.RegLan rv3 ->
                  ∀ pre suf : native_String,
                    pre ++ suf = native_unpack_string ss ->
                      pre ≠ [] ->
                        native_str_in_re pre rv3 = false := by
            intro ss rv3 hSEval hR3Eval pre suf hAppend _hPreNe
            exact hRecNoPrefix sConcat r3 fuelConcat left hSTy hR3Ty rfl
              hLeftEqFalse ss rv3 hSEval hR3Eval pre suf hAppend
          exact str_in_re_re_mult_concat_rel_of_no_nonempty_prefix_consume_local
            M hM sConcat r3 r2 side right
            (by simpa [sConcat, rConcat] using hEqTrans)
            (by simpa [right] using hRightTailRel)
            hNoNonemptyPrefix
        exact
          str_re_consume_rec_str_concat_re_mult_concat_fuel_left_false_model_rel_of_right_rel
            M s1 s2 r3 r2 fc fr side
            (by simpa [sConcat, fuelConcat, rConcat] using hSide)
            (by simpa [left, condLeftFalse] using hLeftFalse)
            (by simpa [sConcat, fuelConcat, rConcat, right] using hRightRel)
      · have hMemIteNe : memIte ≠ Term.Stuck := by
          intro hBad
          apply hWholeNe
          simpa [whole, hLeftNotFalse, eo_ite_false] using hBad
        rcases eo_ite_cases_of_ne_stuck condMem rightFalseIte fallback
            hMemIteNe with hMemEps | hMemNotEps
        · have hRightFalseIteNe : rightFalseIte ≠ Term.Stuck := by
            intro hBad
            apply hMemIteNe
            simpa [memIte, hMemEps, eo_ite_true] using hBad
          rcases eo_ite_cases_of_ne_stuck condRightFalse sameIte fallback
              hRightFalseIteNe with hRightFalse | hRightNotFalse
          · have hSameIteNe : sameIte ≠ Term.Stuck := by
              intro hBad
              apply hRightFalseIteNe
              simpa [rightFalseIte, hRightFalse, eo_ite_true] using hBad
            rcases eo_ite_cases_of_ne_stuck condSame fallback residual
                hSameIteNe with hSame | hDifferent
            · exact
                str_re_consume_rec_str_concat_re_mult_concat_fuel_same_residual_model_rel
                  M s1 s2 r3 r2 fc fr side
                  (by simpa [sConcat, fuelConcat, rConcat] using hSide)
                  (by simpa [left, condLeftFalse] using hLeftNotFalse)
                  (by simpa [left, condMem] using hMemEps)
                  (by simpa [right, condRightFalse] using hRightFalse)
                  (by simpa [sConcat, left, condSame] using hSame)
            · have hResidualRel :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M
                      (__eo_to_smt
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.str_in_re) sConcat)
                          rConcat)))
                    (__smtx_model_eval M (__eo_to_smt residual)) := by
                rcases str_re_consume_translation_facts sConcat rConcat
                    side (by simpa [sConcat, rConcat] using hEqTrans) with
                  ⟨_hStrInTrans, _hSideTrans, hSTy, hRConcatTy,
                    _hEqBool⟩
                have hRConcatArgs :
                    __smtx_typeof
                        (__eo_to_smt
                          (Term.Apply (Term.UOp UserOp.re_mult) r3)) =
                      SmtType.RegLan ∧
                    __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan := by
                  have hNN : term_has_non_none_type
                      (SmtTerm.re_concat
                        (__eo_to_smt
                          (Term.Apply (Term.UOp UserOp.re_mult) r3))
                        (__eo_to_smt r2)) := by
                    unfold term_has_non_none_type
                    change __smtx_typeof (__eo_to_smt rConcat) ≠
                      SmtType.None
                    rw [hRConcatTy]
                    simp
                  exact reglan_binop_args_of_non_none
                    (op := SmtTerm.re_concat)
                    (typeof_re_concat_eq
                      (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r3))
                      (__eo_to_smt r2)) hNN
                have hR3Ty :
                    __smtx_typeof (__eo_to_smt r3) = SmtType.RegLan :=
                  RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_mult_arg_of_reglan
                    r3 hRConcatArgs.1
                have hSideResidual : side = residual := by
                  rw [hSideWhole]
                  simp [whole, hLeftNotFalse, eo_ite_false, memIte,
                    hMemEps, eo_ite_true, rightFalseIte, hRightFalse,
                    sameIte, hDifferent, residual]
                have hResidualTy :
                    __smtx_typeof (__eo_to_smt residual) =
                      SmtType.Bool := by
                  have hSideTy := str_re_consume_side_smt_type sConcat
                    rConcat side (by
                      simpa [sConcat, rConcat] using hEqTrans)
                  simpa [hSideResidual, residual] using hSideTy
                have hResidualNe : residual ≠ Term.Stuck := by
                  intro hBad
                  apply hSideNe
                  rw [hSideResidual, hBad]
                have hLeftMemEq :
                    __str_membership_re left =
                      Term.Apply (Term.UOp UserOp.str_to_re)
                        (Term.String []) :=
                  (eq_of_eo_eq_true (__str_membership_re left)
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String []))
                    (by simpa [left, condMem] using hMemEps)).symm
                have hLeftResidual :=
                  hRecResidual sConcat r3 fuelConcat left hSTy hR3Ty rfl
                    (StrInReConsumeInternal.consume_elim_unflat_eps_of_mem_eps_early_local
                      hLeftMemEq)
                have hTailTy :
                    __smtx_typeof (__eo_to_smt (__str_membership_str left)) =
                      SmtType.Seq SmtType.Char := by
                  exact hLeftResidual.1
                have hResidualTailRel :
                    RuleProofs.smt_value_rel
                      (__smtx_model_eval M
                        (__eo_to_smt
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_in_re)
                              (__str_membership_str left))
                            rConcat)))
                      (__smtx_model_eval M (__eo_to_smt residual)) :=
                  str_re_consume_rec_model_rel_from_ih_of_types M
                    (__str_membership_str left) rConcat fr ihResidual
                    hTailTy hRConcatTy
                    (by simpa [residual] using hResidualTy)
                    (by simpa [residual] using hResidualNe)
                have hNativeEq :
                    ∀ ss rv ss' rv',
                      __smtx_model_eval M (__eo_to_smt sConcat) =
                        SmtValue.Seq ss ->
                      __smtx_model_eval M (__eo_to_smt rConcat) =
                        SmtValue.RegLan rv ->
                      __smtx_model_eval M
                          (__eo_to_smt (__str_membership_str left)) =
                        SmtValue.Seq ss' ->
                      __smtx_model_eval M (__eo_to_smt rConcat) =
                        SmtValue.RegLan rv' ->
                        native_str_in_re (native_unpack_string ss) rv =
                          native_str_in_re (native_unpack_string ss') rv' := by
                  intro ss rv ss' rv' hSEval hRConcatEval hTailEval
                    hRConcatEval'
                  have hRvEq : rv = rv' := by
                    rw [hRConcatEval] at hRConcatEval'
                    cases hRConcatEval'
                    rfl
                  subst rv'
                  rcases eval_re_concat_parts_consume_local M hM
                      (Term.Apply (Term.UOp UserOp.re_mult) r3) r2 rv
                      hRConcatTy hRConcatEval with
                    ⟨starRv, rv2, _hStarTy, _hR2Ty, hStarEval,
                      hR2Eval, hRv⟩
                  subst rv
                  rcases smt_eval_reglan_of_smt_type_reglan_consume_local
                      M hM (__eo_to_smt r3) hR3Ty with
                    ⟨rv3, hR3Eval⟩
                  have hStarNative :
                      SmtValue.RegLan (native_re_mult rv3) =
                        SmtValue.RegLan starRv := by
                    change __smtx_model_eval M
                        (SmtTerm.re_mult (__eo_to_smt r3)) =
                      SmtValue.RegLan starRv at hStarEval
                    simpa [__smtx_model_eval, __smtx_model_eval_re_mult,
                      hR3Eval] using hStarEval
                  cases hStarNative
                  have hRightEqFalse : right = Term.Boolean false :=
                    eq_of_eo_is_eq_true_consume_local right
                      (Term.Boolean false)
                      (by simpa [right, condRightFalse] using hRightFalse)
                  have hTailFalse :
                      native_str_in_re (native_unpack_string ss) rv2 =
                        false :=
                    hRecNoPrefix sConcat r2 fuelConcat right hSTy
                      hRConcatArgs.2 rfl hRightEqFalse ss rv2 hSEval
                      hR2Eval (native_unpack_string ss) [] (by simp)
                  have hRConcatEvalNative :
                      __smtx_model_eval M (__eo_to_smt rConcat) =
                        SmtValue.RegLan
                          (native_re_concat (native_re_mult rv3) rv2) := by
                    simpa [rConcat] using hRConcatEval
                  have hResidualNative :
                      native_str_in_re (native_unpack_string ss)
                          (native_re_concat rv3
                            (native_re_concat (native_re_mult rv3) rv2)) =
                        native_str_in_re (native_unpack_string ss')
                          (native_re_concat (native_re_mult rv3) rv2) :=
                    hLeftResidual.2 rConcat ss rv3 ss'
                      (native_re_concat (native_re_mult rv3) rv2)
                      hSEval hR3Eval hTailEval hRConcatEvalNative
                  exact
                    native_str_in_re_re_mult_concat_residual_eq_local
                      (native_unpack_string ss) (native_unpack_string ss')
                      rv3 rv2 hTailFalse hResidualNative
                exact str_in_re_residual_rel_of_native_eq_consume_local
                  M hM sConcat rConcat side (__str_membership_str left)
                  rConcat residual
                  (by simpa [sConcat, rConcat] using hEqTrans)
                  hTailTy hRConcatTy hResidualTailRel hNativeEq
              exact
                str_re_consume_rec_str_concat_re_mult_concat_fuel_residual_model_rel_of_residual_rel
                  M s1 s2 r3 r2 fc fr side
                  (by simpa [sConcat, fuelConcat, rConcat] using hSide)
                  (by simpa [left, condLeftFalse] using hLeftNotFalse)
                  (by simpa [left, condMem] using hMemEps)
                  (by simpa [right, condRightFalse] using hRightFalse)
                  (by simpa [sConcat, left, condSame] using hDifferent)
                  (by simpa [sConcat, rConcat, left, residual] using
                    hResidualRel)
          · exact
              str_re_consume_rec_str_concat_re_mult_concat_fuel_right_not_false_model_rel
                M s1 s2 r3 r2 fc fr side
                (by simpa [sConcat, fuelConcat, rConcat] using hSide)
                (by simpa [left, condLeftFalse] using hLeftNotFalse)
                (by simpa [left, condMem] using hMemEps)
                (by simpa [right, condRightFalse] using hRightNotFalse)
        · exact
            str_re_consume_rec_str_concat_re_mult_concat_fuel_mem_not_epsilon_model_rel
              M s1 s2 r3 r2 fc fr side
              (by simpa [sConcat, fuelConcat, rConcat] using hSide)
              (by simpa [left, condLeftFalse] using hLeftNotFalse)
              (by simpa [left, condMem] using hMemNotEps)
    · intro s1 s2 r3 r2 fuel hFuel hNotFuelConcat side _hEqTrans
        hSide _hSideNe
      exact str_re_consume_rec_str_concat_re_mult_non_concat_fuel_model_rel
        M s1 s2 r3 r2 fuel side hSide hFuel hNotFuelConcat
    · intro s1 s2 r1 r2 fuel hFuel hR1Empty hR1StrToRe hR1Range
        hR1Allchar hFuelMult hR1Mult _v0 _v1 ihLeft _ihLeftAgain
        ihResidual side hEqTrans hSide hSideNe
      let sConcat := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
      let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2
      let left := __str_re_consume_rec sConcat r1 fuel
      let fallback := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re)
        sConcat) rConcat
      let condLeftFalse := __eo_is_eq left (Term.Boolean false)
      let condMem :=
        __eo_is_eq (__str_membership_re left)
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
      let residual := __str_re_consume_rec (__str_membership_str left) r2 fuel
      let memIte := __eo_ite condMem residual fallback
      let whole := __eo_ite condLeftFalse (Term.Boolean false) memIte
      have hSideWhole : side = whole := by
        rw [hSide, __str_re_consume_rec.eq_10 fuel s1 s2 r1 r2
          hR1Empty hR1StrToRe hR1Range hR1Allchar hR1Mult hFuel
          hFuelMult]
      have hWholeNe : whole ≠ Term.Stuck := by
        intro hBad
        apply hSideNe
        rw [hSideWhole, hBad]
      rcases eo_ite_cases_of_ne_stuck condLeftFalse (Term.Boolean false)
          memIte hWholeNe with hLeftFalse | hLeftNotFalse
      · have hFalseRel :
            RuleProofs.smt_value_rel
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_in_re) sConcat)
                    rConcat)))
              (__smtx_model_eval M (__eo_to_smt (Term.Boolean false))) := by
          rcases str_re_consume_translation_facts sConcat rConcat side (by
              simpa [sConcat, rConcat] using hEqTrans) with
            ⟨_hStrInTrans, _hSideTrans, hSTy, hRConcatTy, _hEqBool⟩
          have hRConcatArgs :
              __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan ∧
                __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan := by
            have hNN : term_has_non_none_type
                (SmtTerm.re_concat (__eo_to_smt r1) (__eo_to_smt r2)) := by
              unfold term_has_non_none_type
              change __smtx_typeof (__eo_to_smt rConcat) ≠ SmtType.None
              rw [hRConcatTy]
              simp
            exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
              (typeof_re_concat_eq (__eo_to_smt r1) (__eo_to_smt r2))
              hNN
          have hLeftEqFalse : left = Term.Boolean false :=
            eq_of_eo_is_eq_true_consume_local left (Term.Boolean false)
              (by simpa [condLeftFalse] using hLeftFalse)
          have hNoSplit :
              ∀ ss rv1,
                __smtx_model_eval M (__eo_to_smt sConcat) =
                  SmtValue.Seq ss ->
                __smtx_model_eval M (__eo_to_smt r1) =
                  SmtValue.RegLan rv1 ->
                  ∀ pre suf : native_String,
                    pre ++ suf = native_unpack_string ss ->
                      native_str_in_re pre rv1 = false := by
            intro ss rv1 hSEval hR1Eval pre suf hAppend
            exact hRecNoPrefix sConcat r1 fuel left hSTy hRConcatArgs.1
              rfl hLeftEqFalse ss rv1 hSEval hR1Eval pre suf hAppend
          exact str_in_re_re_concat_false_rel_of_no_split_consume_local
            M hM sConcat r1 r2 side
            (by simpa [sConcat, rConcat] using hEqTrans)
            hNoSplit
        exact
          str_re_consume_rec_str_concat_re_concat_left_false_model_rel_of_false_rel
            M s1 s2 r1 r2 fuel side
            (by simpa [sConcat, rConcat] using hSide)
            hFuel hR1Empty hR1StrToRe hR1Range hR1Allchar hR1Mult
            hFuelMult
            (by simpa [left, condLeftFalse] using hLeftFalse)
            (by simpa [sConcat, rConcat] using hFalseRel)
      · have hMemIteNe : memIte ≠ Term.Stuck := by
          intro hBad
          apply hWholeNe
          simpa [whole, hLeftNotFalse, eo_ite_false] using hBad
        rcases eo_ite_cases_of_ne_stuck condMem residual fallback
            hMemIteNe with hMemEps | hMemNotEps
        · have hResidualRel :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_in_re) sConcat)
                      rConcat)))
                (__smtx_model_eval M (__eo_to_smt residual)) := by
            rcases str_re_consume_translation_facts sConcat rConcat side (by
                simpa [sConcat, rConcat] using hEqTrans) with
              ⟨_hStrInTrans, _hSideTrans, hSTy, hRConcatTy, _hEqBool⟩
            have hRConcatArgs :
                __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan ∧
                  __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan := by
              have hNN : term_has_non_none_type
                  (SmtTerm.re_concat (__eo_to_smt r1) (__eo_to_smt r2)) := by
                unfold term_has_non_none_type
                change __smtx_typeof (__eo_to_smt rConcat) ≠ SmtType.None
                rw [hRConcatTy]
                simp
              exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
                (typeof_re_concat_eq (__eo_to_smt r1) (__eo_to_smt r2))
                hNN
            have hSideResidual : side = residual := by
              rw [hSideWhole]
              simp [whole, hLeftNotFalse, eo_ite_false, memIte, hMemEps,
                eo_ite_true, residual]
            have hResidualTy :
                __smtx_typeof (__eo_to_smt residual) = SmtType.Bool := by
              have hSideTy := str_re_consume_side_smt_type sConcat
                rConcat side (by simpa [sConcat, rConcat] using hEqTrans)
              simpa [hSideResidual, residual] using hSideTy
            have hResidualNe : residual ≠ Term.Stuck := by
              intro hBad
              apply hSideNe
              rw [hSideResidual, hBad]
            have hLeftMemEq :
                __str_membership_re left =
                  Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) :=
              eq_of_eo_is_eq_true_consume_local (__str_membership_re left)
                (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
                (by simpa [left, condMem] using hMemEps)
            have hLeftResidual :=
              hRecResidual sConcat r1 fuel left hSTy hRConcatArgs.1 rfl
                (StrInReConsumeInternal.consume_elim_unflat_eps_of_mem_eps_early_local
                  hLeftMemEq)
            have hTailTy :
                __smtx_typeof (__eo_to_smt (__str_membership_str left)) =
                  SmtType.Seq SmtType.Char := by
              exact hLeftResidual.1
            have hResidualTailRel :
                RuleProofs.smt_value_rel
                  (__smtx_model_eval M
                    (__eo_to_smt
                      (Term.Apply
                        (Term.Apply (Term.UOp UserOp.str_in_re)
                          (__str_membership_str left))
                        r2)))
                  (__smtx_model_eval M (__eo_to_smt residual)) :=
              str_re_consume_rec_model_rel_from_ih_of_types M
                (__str_membership_str left) r2 fuel ihResidual
                hTailTy hRConcatArgs.2
                (by simpa [residual] using hResidualTy)
                (by simpa [residual] using hResidualNe)
            have hNativeEq :
                ∀ ss rv ss' rv',
                  __smtx_model_eval M (__eo_to_smt sConcat) =
                    SmtValue.Seq ss ->
                  __smtx_model_eval M (__eo_to_smt rConcat) =
                    SmtValue.RegLan rv ->
                  __smtx_model_eval M
                      (__eo_to_smt (__str_membership_str left)) =
                    SmtValue.Seq ss' ->
                  __smtx_model_eval M (__eo_to_smt r2) =
                    SmtValue.RegLan rv' ->
                    native_str_in_re (native_unpack_string ss) rv =
                      native_str_in_re (native_unpack_string ss') rv' := by
              intro ss rv ss' rv' hSEval hRConcatEval hTailEval hR2Eval
              rcases eval_re_concat_parts_consume_local M hM r1 r2 rv
                  hRConcatTy hRConcatEval with
                ⟨rv1, rv2, _hR1Ty, _hR2Ty, hR1Eval, hR2Eval0, hRv⟩
              subst rv
              have hRv2 : rv2 = rv' := by
                rw [hR2Eval] at hR2Eval0
                cases hR2Eval0
                rfl
              subst rv2
              exact hLeftResidual.2 r2 ss rv1 ss' rv' hSEval hR1Eval
                hTailEval hR2Eval
            exact str_in_re_residual_rel_of_native_eq_consume_local M hM
              sConcat rConcat side (__str_membership_str left) r2
              residual (by simpa [sConcat, rConcat] using hEqTrans)
              hTailTy hRConcatArgs.2 hResidualTailRel hNativeEq
          exact
            str_re_consume_rec_str_concat_re_concat_mem_epsilon_model_rel_of_residual_rel
              M s1 s2 r1 r2 fuel side
              (by simpa [sConcat, rConcat] using hSide)
              hFuel hR1Empty hR1StrToRe hR1Range hR1Allchar hR1Mult
              hFuelMult
              (by simpa [left, condLeftFalse] using hLeftNotFalse)
              (by simpa [left, condMem] using hMemEps)
              (by simpa [sConcat, rConcat, left, residual] using
                hResidualRel)
        · exact
            str_re_consume_rec_str_concat_re_concat_fallback_model_rel
              M s1 s2 r1 r2 fuel side
              (by simpa [sConcat, rConcat] using hSide)
              hFuel hR1Empty hR1StrToRe hR1Range hR1Allchar hR1Mult
              hFuelMult
              (by simpa [left, condLeftFalse] using hLeftNotFalse)
              (by simpa [left, condMem] using hMemNotEps)
    · intro s r fuel hS hFuel _hNotConcat ih side hEqTrans hSide hSideNe
      exact str_re_consume_rec_re_concat_empty_left_model_rel_from_ih
        M hM s r fuel side hEqTrans hSide hSideNe hS hFuel ih
    · intro s r1 r2 fuel hS hFuel ih side hEqTrans hSide hSideNe
      apply ih side hEqTrans
      · rw [hSide, str_re_consume_rec_re_inter_eq s r1 r2 fuel hS hFuel]
      · exact hSideNe
    · intro s r1 r2 fuel hS hFuel ih side hEqTrans hSide hSideNe
      apply ih side hEqTrans
      · rw [hSide, str_re_consume_rec_re_union_eq s r1 r2 fuel hS hFuel]
      · exact hSideNe
    · intro s r fuel hS hR hFuel hNotStrConcatEmpty
        hNotStrConcatStrToRe hNotStrConcatRange hNotStrConcatAllchar
        hNotStrConcatMultFuel hNotStrConcatMult hNotStrConcatConcat
        hNotRConcatEmpty hNotRInter hNotRUnion side hEqTrans hSide
        _hSideNe
      exact str_re_consume_rec_default_model_rel M s r fuel side hEqTrans
        hSide hS hR hFuel hNotRConcatEmpty hNotRInter hNotRUnion
        hNotStrConcatEmpty hNotStrConcatStrToRe hNotStrConcatRange
        hNotStrConcatAllchar hNotStrConcatMult hNotStrConcatConcat
        hNotStrConcatMultFuel
    · intro r fuel side _hEqTrans hSide hSideNe
      exfalso
      exact str_re_consume_union_stuck_left_absurd r fuel side hSide
        hSideNe
    · intro s r hS side _hEqTrans hSide hSideNe
      exfalso
      exact str_re_consume_union_stuck_fuel_absurd s r side hS hSide
        hSideNe
    · intro s c1 fuel hS hFuel ih side hEqTrans hSide hSideNe
      exact str_re_consume_union_re_none_model_rel_from_ih M hM s c1 fuel
        side hEqTrans hSide hSideNe hS hFuel ih
    · intro s c1 c2 fuel hS hFuel hC2Ne ihLeft ihRight side hEqTrans
        hSide hSideNe
      exact str_re_consume_union_model_rel_from_ih M hM s c1 c2 fuel
        side hEqTrans hSide hSideNe hS hFuel hC2Ne ihLeft ihRight
    · intro s r fuel hS hFuel hNotNone hNotUnion side _hEqTrans hSide
        hSideNe
      exfalso
      exact str_re_consume_union_default_absurd s r fuel side hSide hSideNe
        hS hFuel hNotNone hNotUnion
    · intro r fuel side _hEqTrans hSide hSideNe
      exfalso
      exact str_re_consume_inter_stuck_left_absurd r fuel side hSide
        hSideNe
    · intro s r hS side _hEqTrans hSide hSideNe
      exfalso
      exact str_re_consume_inter_stuck_fuel_absurd s r side hS hSide
        hSideNe
    · intro s c1 fuel hS hFuel ih side hEqTrans hSide hSideNe
      exact str_re_consume_inter_re_all_model_rel_from_ih M hM s c1 fuel
        side hEqTrans hSide hSideNe hS hFuel ih
    · intro s c1 c2 fuel hS hFuel hC2Ne ihLeft ihRight side hEqTrans
        hSide hSideNe
      exact str_re_consume_inter_model_rel_from_ih M hM s c1 c2 fuel
        side hEqTrans hSide hSideNe hS hFuel hC2Ne ihRight ihLeft
    · intro s r fuel hS hFuel hNotAll hNotInter side _hEqTrans hSide
        hSideNe
      exfalso
      exact str_re_consume_inter_default_absurd s r fuel side hSide hSideNe
        hS hFuel hNotAll hNotInter
  have hNonMultFalseProgress :=
    fun (hSideFalse : side = Term.Boolean false)
        (hNotMult :
          ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) =>
      StrInReConsumeInternal.str_re_consume_non_mult_false_rec_cases_local s r side hSNe hRNe
        hNotMult hSide hSideNe hSideFalse
  have hNonMultFinalProgress :=
    fun (hSideNotFalse : side ≠ Term.Boolean false)
        (hNotMult :
          ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) =>
      StrInReConsumeInternal.str_re_consume_non_mult_final_subterms_ne_stuck_local s r side hSNe
        hRNe hNotMult hSide hSideNe hSideNotFalse
  have hNonMultFinalArgTypeProgress :
      ∀ (hSideNotFalse : side ≠ Term.Boolean false),
        (∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) ->
          let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s))
          let rFlat :=
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          let first := __str_re_consume_rec sFlat rFlat sFlat
          let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          let carry :=
            __eo_and (Term.Boolean false)
              (__eo_not (__eo_eq (__str_membership_re first) eps))
          let nextS :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_ite carry sFlat (__str_membership_str first))
          let nextR :=
            __re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__eo_ite carry rFlat (__str_membership_re first))) eps
          let second := __str_re_consume_rec nextS nextR nextS
          let strPart :=
            __eo_list_singleton_elim (Term.UOp UserOp.str_concat)
              (__str_collect (__str_membership_str second))
          let rePart :=
            __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
              (__re_unflatten (Term.Boolean true)
                (__str_membership_re second))
          __smtx_typeof (__eo_to_smt strPart) =
              SmtType.Seq SmtType.Char ∧
            __smtx_typeof (__eo_to_smt rePart) = SmtType.RegLan ∧
            __str_collect (__str_membership_str second) ≠ Term.Stuck ∧
            rePart ≠ Term.Stuck := by
    intro hSideNotFalse hNotMult
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    let strPart :=
      __eo_list_singleton_elim (Term.UOp UserOp.str_concat)
        (__str_collect (__str_membership_str second))
    let rePart :=
      __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true)
          (__str_membership_re second))
    let final :=
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_in_re) strPart)
        rePart
    rcases hNonMultFinalProgress hSideNotFalse hNotMult with
      ⟨hSideFinal, hCollectNe, hRePartNe⟩
    have hSideTy := str_re_consume_side_smt_type s r side hEqTrans
    rcases StrInReConsumeInternal.str_re_consume_final_args_type_of_side_local side strPart
        rePart hSideTy (by
          simpa [sFlat, rFlat, first, eps, carry, nextS, nextR,
            second, strPart, rePart, final] using hSideFinal)
        hSideNe with
      ⟨hStrPartTy, hRePartTy⟩
    exact ⟨hStrPartTy, hRePartTy,
      by simpa [second] using hCollectNe,
      by simpa [rePart, second] using hRePartNe⟩
  have hNonMultFinalRawProjectionProgress :
      ∀ (hSideNotFalse : side ≠ Term.Boolean false),
        (∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) ->
          let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s))
          let rFlat :=
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          let first := __str_re_consume_rec sFlat rFlat sFlat
          let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          let carry :=
            __eo_and (Term.Boolean false)
              (__eo_not (__eo_eq (__str_membership_re first) eps))
          let nextS :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_ite carry sFlat (__str_membership_str first))
          let nextR :=
            __re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__eo_ite carry rFlat (__str_membership_re first))) eps
          let second := __str_re_consume_rec nextS nextR nextS
          __str_membership_str second ≠ Term.Stuck ∧
            __str_membership_re second ≠ Term.Stuck := by
    intro hSideNotFalse hNotMult
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    rcases hNonMultFinalArgTypeProgress hSideNotFalse hNotMult with
      ⟨_hStrPartTy, _hRePartTy, hCollectNe, hRePartNe⟩
    have hMemStrNe : __str_membership_str second ≠ Term.Stuck :=
      StrInReConsumeInternal.str_collect_arg_ne_stuck_of_ne_stuck_local
        (__str_membership_str second)
        (by simpa [second] using hCollectNe)
    have hUnflatNe :
        __re_unflatten (Term.Boolean true)
            (__str_membership_re second) ≠
          Term.Stuck :=
      StrInReConsumeInternal.eo_list_singleton_elim_arg_ne_stuck_of_ne_stuck_local
        (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true)
          (__str_membership_re second))
        (by simpa [second] using hRePartNe)
    have hMemReNe : __str_membership_re second ≠ Term.Stuck :=
      StrInReConsumeInternal.re_unflatten_tree_ne_stuck_of_ne_stuck_local
        (Term.Boolean true) (__str_membership_re second)
        (by simpa [second] using hUnflatNe)
    exact ⟨hMemStrNe, hMemReNe⟩
  have hNonMultFinalPartsListProgress :
      ∀ (hSideNotFalse : side ≠ Term.Boolean false),
        (∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) ->
          let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s))
          let rFlat :=
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          let first := __str_re_consume_rec sFlat rFlat sFlat
          let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          let carry :=
            __eo_and (Term.Boolean false)
              (__eo_not (__eo_eq (__str_membership_re first) eps))
          let nextS :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_ite carry sFlat (__str_membership_str first))
          let nextR :=
            __re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__eo_ite carry rFlat (__str_membership_re first))) eps
          let second := __str_re_consume_rec nextS nextR nextS
          __eo_is_list (Term.UOp UserOp.str_concat)
              (__str_membership_str second) =
            Term.Boolean true := by
    intro hSideNotFalse hNotMult
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    rcases hNonMultFinalArgTypeProgress hSideNotFalse hNotMult with
      ⟨_hStrPartTy, _hRePartTy, hCollectNe, _hRePartNe⟩
    exact StrInReConsumeInternal.str_collect_arg_is_list_true_of_ne_stuck_local
      (__str_membership_str second) (by simpa [second] using hCollectNe)
  have hNonMultFinalSecondRebuildProgress :
      ∀ (hSideNotFalse : side ≠ Term.Boolean false),
        (∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) ->
          let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s))
          let rFlat :=
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          let first := __str_re_consume_rec sFlat rFlat sFlat
          let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          let carry :=
            __eo_and (Term.Boolean false)
              (__eo_not (__eo_eq (__str_membership_re first) eps))
          let nextS :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_ite carry sFlat (__str_membership_str first))
          let nextR :=
            __re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__eo_ite carry rFlat (__str_membership_re first))) eps
          let second := __str_re_consume_rec nextS nextR nextS
          second =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (__str_membership_str second))
              (__str_membership_re second) := by
    intro hSideNotFalse hNotMult
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    rcases hNonMultFinalRawProjectionProgress hSideNotFalse hNotMult with
      ⟨_hMemStrNe, hMemReNe⟩
    exact str_membership_re_eq_rebuild second
      (__str_membership_re second) rfl
      (by simpa [second] using hMemReNe)
  have hNonMultCarryProgress :=
    fun (hSideNotFalse : side ≠ Term.Boolean false)
        (hNotMult :
          ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) =>
      StrInReConsumeInternal.str_re_consume_non_mult_final_carry_false_local s r side hSNe hRNe
        hNotMult hSide hSideNe hSideNotFalse
  have hNonMultSecondInputNeProgress :=
    fun (hSideNotFalse : side ≠ Term.Boolean false)
        (hNotMult :
          ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) =>
      StrInReConsumeInternal.str_re_consume_non_mult_second_input_ne_stuck_facts_local s r side
        hSNe hRNe hNotMult hSide hSideNe hSideNotFalse
  have hNonMultFirstInputProgress :=
    fun (hSideNotFalse : side ≠ Term.Boolean false)
        (hNotMult :
          ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) =>
      StrInReConsumeInternal.str_re_consume_non_mult_first_input_type_facts_local M hM s r side
        hEqTrans hSNe hRNe hNotMult hSide hSideNe hSideNotFalse
  have hNonMultFinalNotFalseProgress :
      ∀ (hSideNotFalse : side ≠ Term.Boolean false),
        (∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) ->
          let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s))
          let rFlat :=
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          let first := __str_re_consume_rec sFlat rFlat sFlat
          let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          let carry :=
            __eo_and (Term.Boolean false)
              (__eo_not (__eo_eq (__str_membership_re first) eps))
          let nextS :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_ite carry sFlat (__str_membership_str first))
          let nextR :=
            __re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__eo_ite carry rFlat (__str_membership_re first))) eps
          let second := __str_re_consume_rec nextS nextR nextS
          first ≠ Term.Boolean false ∧
            second ≠ Term.Boolean false ∧
            first ≠ Term.Stuck ∧
            second ≠ Term.Stuck := by
    intro hSideNotFalse hNotMult
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    rcases hNonMultCarryProgress hSideNotFalse hNotMult with
      ⟨_hCarryFalse, hSecondNe, hFirstEqFalse, hSecondEqFalse⟩
    rcases hNonMultFirstInputProgress hSideNotFalse hNotMult with
      ⟨_hSFlatTy, _hRFlatTy, _hSFlatList, _hRFlatList, hFirstNe,
        _hSFlatNe, _hRFlatNe⟩
    exact ⟨
      StrInReConsumeInternal.ne_of_eo_eq_false_local first (Term.Boolean false)
        (by simpa [first] using hFirstEqFalse),
      StrInReConsumeInternal.ne_of_eo_eq_false_local second (Term.Boolean false)
        (by simpa [second] using hSecondEqFalse),
      by simpa [first] using hFirstNe,
      by simpa [second] using hSecondNe⟩
  have hNonMultFirstNativeEqProgress :
      ∀ (hSideNotFalse : side ≠ Term.Boolean false),
        (∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) ->
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        ∀ sFlatSs rFlatRv firstSs firstRv,
          __smtx_model_eval M (__eo_to_smt sFlat) =
            SmtValue.Seq sFlatSs ->
          __smtx_model_eval M (__eo_to_smt rFlat) =
            SmtValue.RegLan rFlatRv ->
          __smtx_model_eval M
              (__eo_to_smt (__str_membership_str first)) =
            SmtValue.Seq firstSs ->
          __smtx_model_eval M
              (__eo_to_smt (__str_membership_re first)) =
            SmtValue.RegLan firstRv ->
            native_str_in_re (native_unpack_string sFlatSs) rFlatRv =
              native_str_in_re (native_unpack_string firstSs) firstRv) := by
    intro hSideNotFalse hNotMult
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    rcases hNonMultFirstInputProgress hSideNotFalse hNotMult with
      ⟨hSFlatTy, hRFlatTy, _hSFlatList, _hRFlatList, hFirstNe,
        _hSFlatNe, _hRFlatNe⟩
    rcases hNonMultSecondInputNeProgress hSideNotFalse hNotMult with
      ⟨_hMemStrNe, hMemReNe, _hNextSNe, _hNextRNe, _hSecondNe⟩
    have hFirstTy :
        __smtx_typeof (__eo_to_smt first) = SmtType.Bool :=
      hRecType sFlat rFlat sFlat
        (by simpa [sFlat] using hSFlatTy)
        (by simpa [rFlat] using hRFlatTy)
        (by simpa [first] using hFirstNe)
    have hFirstRebuild :
        first =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (__str_membership_str first))
            (__str_membership_re first) :=
      str_membership_re_eq_rebuild first (__str_membership_re first) rfl
        (by simpa [first] using hMemReNe)
    exact StrInReConsumeInternal.str_re_consume_rec_native_eq_of_rebuilt_result_local M hM
      sFlat rFlat sFlat first (hRecModelRel sFlat rFlat sFlat) rfl
      hFirstRebuild
      (by simpa [first] using hFirstNe)
      (by simpa [sFlat] using hSFlatTy)
      (by simpa [rFlat] using hRFlatTy)
      hFirstTy
  have hNonMultFirstInputEvalProgress :=
    fun (hSideNotFalse : side ≠ Term.Boolean false)
        (hNotMult :
          ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) => by
      let sFlatSource := __str_flatten (__str_nary_intro s)
      let sFlat := __eo_list_rev (Term.UOp UserOp.str_concat) sFlatSource
      let rFlatSource :=
        __re_flatten (Term.Boolean true) r
      let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
      let rFlat := __re_rev_map_rev rFlatSource eps
      rcases hNonMultFirstInputProgress hSideNotFalse hNotMult with
        ⟨_hSFlatTy, _hRFlatTy, _hSFlatList, _hRFlatList, _hFirstNe,
          hSFlatNe, hRFlatNe⟩
      rcases str_re_consume_translation_facts s r side hEqTrans with
        ⟨_hStrInTrans, _hSideTrans, _hSTy, hRTy, _hEqBool⟩
      exact StrInReConsumeInternal.str_re_consume_first_input_eval_context_local M hM s r side r
        hEqTrans hRTy
        (by simpa [sFlatSource, sFlat, __str_nary_intro] using hSFlatNe)
        (by simpa [rFlatSource, eps, rFlat] using hRFlatNe)
  have hNonMultFirstInputEvalForValuesProgress :
      ∀ (hSideNotFalse : side ≠ Term.Boolean false)
        (hNotMult :
          ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False)
        (ss : SmtSeq) (rv : SmtRegLan),
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
          ∃ flatSs sFlatSs flatRv rFlatRv,
            __smtx_model_eval M
                (__eo_to_smt (__str_flatten (__str_nary_intro s))) =
              SmtValue.Seq flatSs ∧
            __smtx_model_eval M
                (__eo_to_smt
                  (__eo_list_rev (Term.UOp UserOp.str_concat)
                    (__str_flatten (__str_nary_intro s)))) =
              SmtValue.Seq sFlatSs ∧
            __smtx_model_eval M
                (__eo_to_smt
                  (__re_flatten (Term.Boolean true) r)) =
              SmtValue.RegLan flatRv ∧
            __smtx_model_eval M
                (__eo_to_smt
                  (__re_rev_map_rev
                    (__re_flatten (Term.Boolean true) r)
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String [])))) =
              SmtValue.RegLan rFlatRv ∧
            __smtx_typeof
                (__eo_to_smt (__str_flatten (__str_nary_intro s))) =
              SmtType.Seq SmtType.Char ∧
            __smtx_typeof
                (__eo_to_smt
                  (__eo_list_rev (Term.UOp UserOp.str_concat)
                    (__str_flatten (__str_nary_intro s)))) =
              SmtType.Seq SmtType.Char ∧
            __smtx_typeof
                (__eo_to_smt
                  (__re_flatten (Term.Boolean true) r)) =
              SmtType.RegLan ∧
            __smtx_typeof
                (__eo_to_smt
                  (__re_rev_map_rev
                    (__re_flatten (Term.Boolean true) r)
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String [])))) =
              SmtType.RegLan ∧
            __eo_is_list (Term.UOp UserOp.str_concat)
                (__str_flatten (__str_nary_intro s)) =
              Term.Boolean true ∧
            __eo_is_list (Term.UOp UserOp.str_concat)
                (__eo_list_rev (Term.UOp UserOp.str_concat)
                  (__str_flatten (__str_nary_intro s))) =
              Term.Boolean true ∧
            __eo_is_list (Term.UOp UserOp.re_concat)
                (__re_flatten (Term.Boolean true) r) =
              Term.Boolean true ∧
            __eo_is_list (Term.UOp UserOp.re_concat)
                (__re_rev_map_rev
                  (__re_flatten (Term.Boolean true) r)
                  (Term.Apply (Term.UOp UserOp.str_to_re)
                    (Term.String []))) =
              Term.Boolean true ∧
            RuleProofs.smt_value_rel (SmtValue.Seq flatSs)
              (SmtValue.Seq ss) := by
    intro hSideNotFalse hNotMult ss rv hSEval hREval
    rcases hNonMultFirstInputEvalProgress hSideNotFalse hNotMult with
      ⟨ss0, flatSs, sFlatSs, rv0, flatRv, rFlatRv, hSEval0,
        hSFlatSourceEval, hSFlatEval, hREval0, hRFlatSourceEval,
        hRFlatEval, hSFlatSourceTy, hSFlatTy, hRFlatSourceTy,
        hRFlatTy, hSFlatSourceList, hSFlatList, hRFlatSourceList,
        hRFlatList, hSFlatSourceRel⟩
    have hSs : ss0 = ss := by
      rw [hSEval] at hSEval0
      cases hSEval0
      rfl
    have hRv : rv0 = rv := by
      rw [hREval] at hREval0
      cases hREval0
      rfl
    subst ss0
    subst rv0
    exact ⟨flatSs, sFlatSs, flatRv, rFlatRv, hSFlatSourceEval,
      hSFlatEval, hRFlatSourceEval, hRFlatEval, hSFlatSourceTy,
      hSFlatTy, hRFlatSourceTy, hRFlatTy, hSFlatSourceList,
      hSFlatList, hRFlatSourceList, hRFlatList, hSFlatSourceRel⟩
  have hNonMultSecondInputTypeProgress :
      ∀ (hSideNotFalse : side ≠ Term.Boolean false),
        (∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) ->
          let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s))
          let rFlat :=
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          let first := __str_re_consume_rec sFlat rFlat sFlat
          let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          let carry :=
            __eo_and (Term.Boolean false)
              (__eo_not (__eo_eq (__str_membership_re first) eps))
          let nextS :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_ite carry sFlat (__str_membership_str first))
          let nextR :=
            __re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__eo_ite carry rFlat (__str_membership_re first))) eps
          __smtx_typeof (__eo_to_smt nextS) =
              SmtType.Seq SmtType.Char ∧
            __smtx_typeof (__eo_to_smt nextR) = SmtType.RegLan := by
    intro hSideNotFalse hNotMult
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    rcases hNonMultFirstInputProgress hSideNotFalse hNotMult with
      ⟨hSFlatTy, hRFlatTy, _hSFlatList, _hRFlatList, hFirstNe,
        _hSFlatNe, _hRFlatNe⟩
    rcases hNonMultSecondInputNeProgress hSideNotFalse hNotMult with
      ⟨_hMemStrNe, hMemReNe, hNextSNe, hNextRNe, _hSecondNe⟩
    rcases hNonMultCarryProgress hSideNotFalse hNotMult with
      ⟨hCarryFalse, _hSecondNe, _hFirstEqFalse, _hSecondEqFalse⟩
    have hFirstTy :
        __smtx_typeof (__eo_to_smt first) = SmtType.Bool :=
      hRecType sFlat rFlat sFlat
        (by simpa [sFlat] using hSFlatTy)
        (by simpa [rFlat] using hRFlatTy)
        (by simpa [first] using hFirstNe)
    rcases StrInReConsumeInternal.str_re_consume_rec_projection_types_of_bool_local first
        hFirstTy (by simpa [first] using hMemReNe) with
      ⟨hMemStrTy, hMemReTy⟩
    have hCarryFalseLocal : carry = Term.Boolean false := by
      simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
        hCarryFalse
    have hIteSTy :
        __smtx_typeof
            (__eo_to_smt
              (__eo_ite carry sFlat (__str_membership_str first))) =
          SmtType.Seq SmtType.Char := by
      simpa [hCarryFalseLocal, eo_ite_false] using hMemStrTy
    have hIteSList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first)) =
          Term.Boolean true :=
      eo_list_rev_is_list_true_of_ne_stuck
        (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
        (by simpa [nextS] using hNextSNe)
    have hNextSTy :
        __smtx_typeof (__eo_to_smt nextS) =
          SmtType.Seq SmtType.Char := by
      simpa [nextS] using
        smt_typeof_list_rev_str_concat_of_seq
          (__eo_ite carry sFlat (__str_membership_str first))
          SmtType.Char hIteSList hIteSTy
          (by simpa [nextS] using hNextSNe)
    have hIteRTy :
        __smtx_typeof
            (__eo_to_smt
              (__eo_ite carry rFlat (__str_membership_re first))) =
          SmtType.RegLan := by
      simpa [hCarryFalseLocal, eo_ite_false] using hMemReTy
    have hNextRTy :
        __smtx_typeof (__eo_to_smt nextR) = SmtType.RegLan := by
      rcases StrInReConsumeInternal.str_re_consume_rflat_type_facts_local M hM
          (__eo_ite carry rFlat (__str_membership_re first)) hIteRTy
          (by simpa [nextR] using hNextRNe) with
        ⟨hTy, _hList, _hFlatNe, _hFlatList, _hFlatTy⟩
      simpa [nextR] using hTy
    exact ⟨hNextSTy, hNextRTy⟩
  have hNonMultFinalRelOfSecondEvalProgress :
      ∀ (hSideNotFalse : side ≠ Term.Boolean false),
        (∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) ->
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean false)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextS :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first))
        let nextR :=
          __re_rev_map_rev
            (__re_flatten (Term.Boolean true)
              (__eo_ite carry rFlat (__str_membership_re first))) eps
        let second := __str_re_consume_rec nextS nextR nextS
        (∀ ss,
          __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
            ∃ partsSs,
              __smtx_model_eval M
                  (__eo_to_smt (__str_membership_str second)) =
                SmtValue.Seq partsSs ∧
              RuleProofs.smt_value_rel (SmtValue.Seq partsSs)
                (SmtValue.Seq ss)) ->
        (∀ rv,
          __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
            ∃ reRv,
              __smtx_model_eval M
                  (__eo_to_smt (__str_membership_re second)) =
                SmtValue.RegLan reRv ∧
              RuleProofs.smt_value_rel (SmtValue.RegLan reRv)
                (SmtValue.RegLan rv)) ->
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
          (__smtx_model_eval M (__eo_to_smt side))) := by
    intro hSideNotFalse hNotMult
    exact StrInReConsumeInternal.str_re_consume_non_mult_model_rel_of_final_second_eval_rels_local
      M hM hRecType s r side hEqTrans hSNe hRNe hNotMult hSide hSideNe
      hSideNotFalse
  have hNonMultFinalRelOfSecondNativeEqProgress :
      ∀ (hSideNotFalse : side ≠ Term.Boolean false),
        (∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) ->
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean false)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextS :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first))
        let nextR :=
          __re_rev_map_rev
            (__re_flatten (Term.Boolean true)
              (__eo_ite carry rFlat (__str_membership_re first))) eps
        let second := __str_re_consume_rec nextS nextR nextS
        ∀ ss rv partsSs reRv,
          __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
          __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
          __smtx_model_eval M
              (__eo_to_smt (__str_membership_str second)) =
            SmtValue.Seq partsSs ->
          __smtx_model_eval M
              (__eo_to_smt (__str_membership_re second)) =
            SmtValue.RegLan reRv ->
            native_str_in_re (native_unpack_string ss) rv =
              native_str_in_re (native_unpack_string partsSs) reRv) ->
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
          (__smtx_model_eval M (__eo_to_smt side)) := by
    intro hSideNotFalse hNotMult hNativeEq
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    rcases hNonMultFinalProgress hSideNotFalse hNotMult with
      ⟨hSideFinal, hCollectNe, hUnflatElimNe⟩
    have hSecondTy :
        __smtx_typeof (__eo_to_smt second) = SmtType.Bool := by
      simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
        StrInReConsumeInternal.str_re_consume_non_mult_second_type_from_rec_type_local M hM
          hRecType s r side hEqTrans hSNe hRNe hNotMult hSide hSideNe
          hSideNotFalse
    have hPartsList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (__str_membership_str second) =
          Term.Boolean true := by
      simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
        hNonMultFinalPartsListProgress hSideNotFalse hNotMult
    exact StrInReConsumeInternal.str_re_consume_model_rel_of_final_second_native_eq_local M hM
      s r side second hEqTrans
      (by
        simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
          hSideFinal)
      hSideNe hPartsList hSecondTy
      (by simpa [second] using hCollectNe)
      (by simpa [second] using hUnflatElimNe)
      (by
        simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
          hNativeEq)
  have hNonMultFinalRelOfSecondInputNativeEqProgress :
      ∀ (hSideNotFalse : side ≠ Term.Boolean false),
        (∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) ->
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean false)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextS :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first))
        __smtx_typeof (__eo_to_smt nextS) = SmtType.Seq SmtType.Char) ->
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean false)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextR :=
          __re_rev_map_rev
            (__re_flatten (Term.Boolean true)
              (__eo_ite carry rFlat (__str_membership_re first))) eps
        __smtx_typeof (__eo_to_smt nextR) = SmtType.RegLan) ->
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean false)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextS :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first))
        let nextR :=
          __re_rev_map_rev
            (__re_flatten (Term.Boolean true)
              (__eo_ite carry rFlat (__str_membership_re first))) eps
        ∀ ss rv nextSs nextRv,
          __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
          __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
          __smtx_model_eval M (__eo_to_smt nextS) =
            SmtValue.Seq nextSs ->
          __smtx_model_eval M (__eo_to_smt nextR) =
            SmtValue.RegLan nextRv ->
            native_str_in_re (native_unpack_string ss) rv =
              native_str_in_re (native_unpack_string nextSs) nextRv) ->
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
          (__smtx_model_eval M (__eo_to_smt side)) := by
    intro hSideNotFalse hNotMult hNextSTy hNextRTy hInputNativeEq
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    rcases hNonMultFinalProgress hSideNotFalse hNotMult with
      ⟨hSideFinal, hCollectNe, hUnflatElimNe⟩
    rcases hNonMultFinalNotFalseProgress hSideNotFalse hNotMult with
      ⟨_hFirstNotFalse, _hSecondNotFalse, _hFirstNe, hSecondNe⟩
    have hPartsList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (__str_membership_str second) =
          Term.Boolean true := by
      simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
        hNonMultFinalPartsListProgress hSideNotFalse hNotMult
    have hSecondTy :
        __smtx_typeof (__eo_to_smt second) = SmtType.Bool := by
      simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
        StrInReConsumeInternal.str_re_consume_non_mult_second_type_from_rec_type_local M hM
          hRecType s r side hEqTrans hSNe hRNe hNotMult hSide hSideNe
          hSideNotFalse
    have hSecondRebuild :
        second =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (__str_membership_str second))
            (__str_membership_re second) := by
      simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
        hNonMultFinalSecondRebuildProgress hSideNotFalse hNotMult
    have hSecondNativeEq :
        ∀ nextSs nextRv partsSs reRv,
          __smtx_model_eval M (__eo_to_smt nextS) =
            SmtValue.Seq nextSs ->
          __smtx_model_eval M (__eo_to_smt nextR) =
            SmtValue.RegLan nextRv ->
          __smtx_model_eval M
              (__eo_to_smt (__str_membership_str second)) =
            SmtValue.Seq partsSs ->
          __smtx_model_eval M
              (__eo_to_smt (__str_membership_re second)) =
            SmtValue.RegLan reRv ->
            native_str_in_re (native_unpack_string nextSs) nextRv =
              native_str_in_re (native_unpack_string partsSs) reRv :=
      StrInReConsumeInternal.str_re_consume_rec_native_eq_of_rebuilt_result_local M hM nextS nextR
        nextS second (hRecModelRel nextS nextR nextS) rfl
        hSecondRebuild (by simpa [second] using hSecondNe)
        (by simpa [sFlat, rFlat, first, eps, carry, nextS] using
          hNextSTy)
        (by simpa [sFlat, rFlat, first, eps, carry, nextR] using
          hNextRTy)
        hSecondTy
    exact StrInReConsumeInternal.str_re_consume_model_rel_of_final_second_input_native_eq_local M
      hM s r side nextS nextR second hEqTrans
      (by
        simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
          hSideFinal)
      hSideNe
      (by simpa [sFlat, rFlat, first, eps, carry, nextS] using
        hNextSTy)
      (by simpa [sFlat, rFlat, first, eps, carry, nextR] using
        hNextRTy)
      hPartsList hSecondTy
      (by simpa [second] using hCollectNe)
      (by simpa [second] using hUnflatElimNe)
      (by
        simpa [sFlat, rFlat, first, eps, carry, nextS, nextR] using
          hInputNativeEq)
      hSecondNativeEq
  have hNonMultFinalRelOfInputNativeEqProgress :
      ∀ (hSideNotFalse : side ≠ Term.Boolean false),
        (∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) ->
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean false)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextS :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first))
        let nextR :=
          __re_rev_map_rev
            (__re_flatten (Term.Boolean true)
              (__eo_ite carry rFlat (__str_membership_re first))) eps
        ∀ ss rv nextSs nextRv,
          __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
          __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
          __smtx_model_eval M (__eo_to_smt nextS) =
            SmtValue.Seq nextSs ->
          __smtx_model_eval M (__eo_to_smt nextR) =
            SmtValue.RegLan nextRv ->
            native_str_in_re (native_unpack_string ss) rv =
              native_str_in_re (native_unpack_string nextSs) nextRv) ->
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
          (__smtx_model_eval M (__eo_to_smt side)) := by
    intro hSideNotFalse hNotMult hInputNativeEq
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    rcases hNonMultSecondInputTypeProgress hSideNotFalse hNotMult with
      ⟨hNextSTy, hNextRTy⟩
    exact hNonMultFinalRelOfSecondInputNativeEqProgress hSideNotFalse
      hNotMult
      (by simpa [sFlat, rFlat, first, eps, carry, nextS] using hNextSTy)
      (by simpa [sFlat, rFlat, first, eps, carry, nextR] using hNextRTy)
      (by
        simpa [sFlat, rFlat, first, eps, carry, nextS, nextR] using
          hInputNativeEq)
  have hNonMultSecondNativeEqProgress :
      ∀ (hSideNotFalse : side ≠ Term.Boolean false),
        (∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) ->
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean false)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextS :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first))
        let nextR :=
          __re_rev_map_rev
            (__re_flatten (Term.Boolean true)
              (__eo_ite carry rFlat (__str_membership_re first))) eps
        let second := __str_re_consume_rec nextS nextR nextS
        ∀ nextSs nextRv partsSs reRv,
          __smtx_model_eval M (__eo_to_smt nextS) =
            SmtValue.Seq nextSs ->
          __smtx_model_eval M (__eo_to_smt nextR) =
            SmtValue.RegLan nextRv ->
          __smtx_model_eval M
              (__eo_to_smt (__str_membership_str second)) =
            SmtValue.Seq partsSs ->
          __smtx_model_eval M
              (__eo_to_smt (__str_membership_re second)) =
            SmtValue.RegLan reRv ->
            native_str_in_re (native_unpack_string nextSs) nextRv =
              native_str_in_re (native_unpack_string partsSs) reRv) := by
    intro hSideNotFalse hNotMult
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    rcases hNonMultSecondInputTypeProgress hSideNotFalse hNotMult with
      ⟨hNextSTy, hNextRTy⟩
    rcases hNonMultFinalNotFalseProgress hSideNotFalse hNotMult with
      ⟨_hFirstNotFalse, _hSecondNotFalse, _hFirstNe, hSecondNe⟩
    have hSecondTy :
        __smtx_typeof (__eo_to_smt second) = SmtType.Bool := by
      simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
        StrInReConsumeInternal.str_re_consume_non_mult_second_type_from_rec_type_local M hM
          hRecType s r side hEqTrans hSNe hRNe hNotMult hSide hSideNe
          hSideNotFalse
    have hSecondRebuild :
        second =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (__str_membership_str second))
            (__str_membership_re second) := by
      simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
        hNonMultFinalSecondRebuildProgress hSideNotFalse hNotMult
    exact StrInReConsumeInternal.str_re_consume_rec_native_eq_of_rebuilt_result_local M hM
      nextS nextR nextS second (hRecModelRel nextS nextR nextS) rfl
      hSecondRebuild
      (by simpa [second] using hSecondNe)
      (by simpa [sFlat, rFlat, first, eps, carry, nextS] using hNextSTy)
      (by simpa [sFlat, rFlat, first, eps, carry, nextR] using hNextRTy)
      hSecondTy
  have hMultFalseProgress :
      ∀ r0,
        r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
        side = Term.Boolean false ->
          let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s))
          let rFlat :=
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          let first := __str_re_consume_rec sFlat rFlat sFlat
          let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          let carry :=
            __eo_and (Term.Boolean true)
              (__eo_not (__eo_eq (__str_membership_re first) eps))
          let nextS :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_ite carry sFlat (__str_membership_str first))
          let nextR :=
            __re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__eo_ite carry rFlat (__str_membership_re first))) eps
          let second := __str_re_consume_rec nextS nextR nextS
          first = Term.Boolean false ∨ second = Term.Boolean false := by
    intro r0 hR hSideFalse
    subst r
    exact StrInReConsumeInternal.str_re_consume_mult_false_rec_cases_local s r0 side hSNe hSide
      hSideNe hSideFalse
  have hMultFinalProgress :
      ∀ r0,
        r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
        side ≠ Term.Boolean false ->
          let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s))
          let rFlat :=
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          let first := __str_re_consume_rec sFlat rFlat sFlat
          let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          let carry :=
            __eo_and (Term.Boolean true)
              (__eo_not (__eo_eq (__str_membership_re first) eps))
          let nextS :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_ite carry sFlat (__str_membership_str first))
          let nextR :=
            __re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__eo_ite carry rFlat (__str_membership_re first))) eps
          let second := __str_re_consume_rec nextS nextR nextS
          let final :=
            __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_in_re)
                (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
                  (__str_collect (__str_membership_str second))))
              (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
                (__re_unflatten (Term.Boolean true)
                  (__str_membership_re second)))
          let candidate :=
            __eo_ite (__eo_eq first (Term.Boolean false))
              (Term.Boolean false)
              (__eo_ite (__eo_eq second (Term.Boolean false))
                (Term.Boolean false) final)
          let rebuild :=
            __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_in_re)
                (__str_membership_str candidate))
              (Term.Apply (Term.UOp UserOp.re_mult) r0)
          side = rebuild ∧ candidate = final ∧
            __str_membership_re candidate =
              Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) := by
    intro r0 hR hSideNotFalse
    subst r
    exact StrInReConsumeInternal.str_re_consume_mult_final_eq_local s r0 side hSNe hSide hSideNe
      hSideNotFalse
  have hMultFinalSubtermProgress :
      ∀ r0,
        r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
        side ≠ Term.Boolean false ->
          let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s))
          let rFlat :=
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          let first := __str_re_consume_rec sFlat rFlat sFlat
          let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          let carry :=
            __eo_and (Term.Boolean true)
              (__eo_not (__eo_eq (__str_membership_re first) eps))
          let nextS :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_ite carry sFlat (__str_membership_str first))
          let nextR :=
            __re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__eo_ite carry rFlat (__str_membership_re first))) eps
          let second := __str_re_consume_rec nextS nextR nextS
          let final :=
            __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_in_re)
                (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
                  (__str_collect (__str_membership_str second))))
              (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
                (__re_unflatten (Term.Boolean true)
                  (__str_membership_re second)))
          let candidate :=
            __eo_ite (__eo_eq first (Term.Boolean false))
              (Term.Boolean false)
              (__eo_ite (__eo_eq second (Term.Boolean false))
                (Term.Boolean false) final)
          let rebuild :=
            __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_in_re)
                (__str_membership_str candidate))
              (Term.Apply (Term.UOp UserOp.re_mult) r0)
          side = rebuild ∧ candidate = final ∧
            __str_membership_re candidate =
              Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) ∧
            __str_collect (__str_membership_str second) ≠ Term.Stuck ∧
            __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
                (__re_unflatten (Term.Boolean true)
                  (__str_membership_re second)) ≠
              Term.Stuck := by
    intro r0 hR hSideNotFalse
    subst r
    exact StrInReConsumeInternal.str_re_consume_mult_final_subterms_ne_stuck_local s r0 side hSNe
      hSide hSideNe hSideNotFalse
  have hMultFinalArgTypeProgress :
      ∀ r0,
        r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
        side ≠ Term.Boolean false ->
          let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s))
          let rFlat :=
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          let first := __str_re_consume_rec sFlat rFlat sFlat
          let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          let carry :=
            __eo_and (Term.Boolean true)
              (__eo_not (__eo_eq (__str_membership_re first) eps))
          let nextS :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_ite carry sFlat (__str_membership_str first))
          let nextR :=
            __re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__eo_ite carry rFlat (__str_membership_re first))) eps
          let second := __str_re_consume_rec nextS nextR nextS
          let final :=
            __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_in_re)
                (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
                  (__str_collect (__str_membership_str second))))
              (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
                (__re_unflatten (Term.Boolean true)
                  (__str_membership_re second)))
          let candidate :=
            __eo_ite (__eo_eq first (Term.Boolean false))
              (Term.Boolean false)
              (__eo_ite (__eo_eq second (Term.Boolean false))
                (Term.Boolean false) final)
          __smtx_typeof (__eo_to_smt (__str_membership_str candidate)) =
              SmtType.Seq SmtType.Char ∧
            __smtx_typeof
                (__eo_to_smt
                  (Term.Apply (Term.UOp UserOp.re_mult) r0)) =
              SmtType.RegLan ∧
            __str_collect (__str_membership_str second) ≠ Term.Stuck ∧
            __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
                (__re_unflatten (Term.Boolean true)
                  (__str_membership_re second)) ≠
              Term.Stuck := by
    intro r0 hR hSideNotFalse
    subst r
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    let final :=
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
            (__str_collect (__str_membership_str second))))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)))
    let candidate :=
      __eo_ite (__eo_eq first (Term.Boolean false))
        (Term.Boolean false)
        (__eo_ite (__eo_eq second (Term.Boolean false))
          (Term.Boolean false) final)
    let rebuild :=
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__str_membership_str candidate))
        (Term.Apply (Term.UOp UserOp.re_mult) r0)
    rcases hMultFinalProgress r0 rfl hSideNotFalse with
      ⟨hSideRebuild, _hCandidateFinal, _hCandidateMem⟩
    rcases hMultFinalSubtermProgress r0 rfl hSideNotFalse with
      ⟨_hSideRebuild, _hCandidateFinal, _hCandidateMem, hCollectNe,
        hRePartNe⟩
    have hSideTy :=
      str_re_consume_side_smt_type s
        (Term.Apply (Term.UOp UserOp.re_mult) r0) side hEqTrans
    rcases StrInReConsumeInternal.str_re_consume_final_args_type_of_side_local side
        (__str_membership_str candidate)
        (Term.Apply (Term.UOp UserOp.re_mult) r0) hSideTy (by
          simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second,
            final, candidate, rebuild] using hSideRebuild)
        hSideNe with
      ⟨hCandidateStrTy, hMultTy⟩
    exact ⟨hCandidateStrTy, hMultTy,
      by simpa [second] using hCollectNe,
      by simpa [second] using hRePartNe⟩
  have hMultFinalRawProjectionProgress :
      ∀ r0,
        r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
        side ≠ Term.Boolean false ->
          let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s))
          let rFlat :=
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          let first := __str_re_consume_rec sFlat rFlat sFlat
          let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          let carry :=
            __eo_and (Term.Boolean true)
              (__eo_not (__eo_eq (__str_membership_re first) eps))
          let nextS :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_ite carry sFlat (__str_membership_str first))
          let nextR :=
            __re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__eo_ite carry rFlat (__str_membership_re first))) eps
          let second := __str_re_consume_rec nextS nextR nextS
          __str_membership_str second ≠ Term.Stuck ∧
            __str_membership_re second ≠ Term.Stuck := by
    intro r0 hR hSideNotFalse
    subst r
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    rcases hMultFinalArgTypeProgress r0 rfl hSideNotFalse with
      ⟨_hStrPartTy, _hRePartTy, hCollectNe, hRePartNe⟩
    have hMemStrNe : __str_membership_str second ≠ Term.Stuck :=
      StrInReConsumeInternal.str_collect_arg_ne_stuck_of_ne_stuck_local
        (__str_membership_str second)
        (by simpa [second] using hCollectNe)
    have hUnflatNe :
        __re_unflatten (Term.Boolean true)
            (__str_membership_re second) ≠
          Term.Stuck :=
      StrInReConsumeInternal.eo_list_singleton_elim_arg_ne_stuck_of_ne_stuck_local
        (Term.UOp UserOp.re_concat)
        (__re_unflatten (Term.Boolean true)
          (__str_membership_re second))
        (by simpa [second] using hRePartNe)
    have hMemReNe : __str_membership_re second ≠ Term.Stuck :=
      StrInReConsumeInternal.re_unflatten_tree_ne_stuck_of_ne_stuck_local
        (Term.Boolean true) (__str_membership_re second)
        (by simpa [second] using hUnflatNe)
    exact ⟨hMemStrNe, hMemReNe⟩
  have hMultFinalPartsListProgress :
      ∀ r0,
        r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
        side ≠ Term.Boolean false ->
          let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s))
          let rFlat :=
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          let first := __str_re_consume_rec sFlat rFlat sFlat
          let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          let carry :=
            __eo_and (Term.Boolean true)
              (__eo_not (__eo_eq (__str_membership_re first) eps))
          let nextS :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_ite carry sFlat (__str_membership_str first))
          let nextR :=
            __re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__eo_ite carry rFlat (__str_membership_re first))) eps
          let second := __str_re_consume_rec nextS nextR nextS
          __eo_is_list (Term.UOp UserOp.str_concat)
              (__str_membership_str second) =
            Term.Boolean true := by
    intro r0 hR hSideNotFalse
    subst r
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    rcases hMultFinalArgTypeProgress r0 rfl hSideNotFalse with
      ⟨_hStrPartTy, _hRePartTy, hCollectNe, _hRePartNe⟩
    exact StrInReConsumeInternal.str_collect_arg_is_list_true_of_ne_stuck_local
      (__str_membership_str second) (by simpa [second] using hCollectNe)
  have hMultFinalSecondRebuildProgress :
      ∀ r0,
        r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
        side ≠ Term.Boolean false ->
          let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s))
          let rFlat :=
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          let first := __str_re_consume_rec sFlat rFlat sFlat
          let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          let carry :=
            __eo_and (Term.Boolean true)
              (__eo_not (__eo_eq (__str_membership_re first) eps))
          let nextS :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_ite carry sFlat (__str_membership_str first))
          let nextR :=
            __re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__eo_ite carry rFlat (__str_membership_re first))) eps
          let second := __str_re_consume_rec nextS nextR nextS
          second =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (__str_membership_str second))
              (__str_membership_re second) := by
    intro r0 hR hSideNotFalse
    subst r
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    rcases hMultFinalRawProjectionProgress r0 rfl hSideNotFalse with
      ⟨_hMemStrNe, hMemReNe⟩
    exact str_membership_re_eq_rebuild second
      (__str_membership_re second) rfl
      (by simpa [second] using hMemReNe)
  have hMultCarryProgress :
      ∀ r0,
        r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
        side ≠ Term.Boolean false ->
          let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s))
          let rFlat :=
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          let first := __str_re_consume_rec sFlat rFlat sFlat
          let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          let carry :=
            __eo_and (Term.Boolean true)
              (__eo_not (__eo_eq (__str_membership_re first) eps))
          let nextS :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_ite carry sFlat (__str_membership_str first))
          let nextR :=
            __re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__eo_ite carry rFlat (__str_membership_re first))) eps
          let second := __str_re_consume_rec nextS nextR nextS
          let final :=
            __eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_in_re)
                (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
                  (__str_collect (__str_membership_str second))))
              (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
                (__re_unflatten (Term.Boolean true)
                  (__str_membership_re second)))
          let candidate :=
            __eo_ite (__eo_eq first (Term.Boolean false))
              (Term.Boolean false)
              (__eo_ite (__eo_eq second (Term.Boolean false))
                (Term.Boolean false) final)
          carry = __eo_not (__eo_eq (__str_membership_re first) eps) ∧
            second ≠ Term.Stuck ∧
            __eo_eq first (Term.Boolean false) = Term.Boolean false ∧
            __eo_eq second (Term.Boolean false) = Term.Boolean false := by
    intro r0 hR hSideNotFalse
    subst r
    exact StrInReConsumeInternal.str_re_consume_mult_final_carry_eq_local s r0 side hSNe hSide
      hSideNe hSideNotFalse
  have hMultSecondInputNeProgress :
      ∀ r0,
        r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
        side ≠ Term.Boolean false ->
          let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s))
          let rFlat :=
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          let first := __str_re_consume_rec sFlat rFlat sFlat
          let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          let carry :=
            __eo_and (Term.Boolean true)
              (__eo_not (__eo_eq (__str_membership_re first) eps))
          let nextS :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_ite carry sFlat (__str_membership_str first))
          let nextR :=
            __re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__eo_ite carry rFlat (__str_membership_re first))) eps
          let second := __str_re_consume_rec nextS nextR nextS
          __str_membership_re first ≠ Term.Stuck ∧
            carry ≠ Term.Stuck ∧
            nextS ≠ Term.Stuck ∧
            nextR ≠ Term.Stuck ∧
            second ≠ Term.Stuck := by
    intro r0 hR hSideNotFalse
    subst r
    exact StrInReConsumeInternal.str_re_consume_mult_second_input_ne_stuck_facts_local s r0 side
      hSNe hSide hSideNe hSideNotFalse
  have hMultFirstInputProgress :
      ∀ r0,
        r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
        side ≠ Term.Boolean false ->
          let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s))
          let rFlat :=
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          let first := __str_re_consume_rec sFlat rFlat sFlat
          __smtx_typeof (__eo_to_smt sFlat) = SmtType.Seq SmtType.Char ∧
            __smtx_typeof (__eo_to_smt rFlat) = SmtType.RegLan ∧
            __eo_is_list (Term.UOp UserOp.str_concat) sFlat =
              Term.Boolean true ∧
            __eo_is_list (Term.UOp UserOp.re_concat) rFlat =
              Term.Boolean true ∧
            first ≠ Term.Stuck ∧
            sFlat ≠ Term.Stuck ∧
            rFlat ≠ Term.Stuck := by
    intro r0 hR hSideNotFalse
    subst r
    exact StrInReConsumeInternal.str_re_consume_mult_first_input_type_facts_local M hM s r0 side
      hEqTrans hSNe hSide hSideNe hSideNotFalse
  have hMultFinalNotFalseProgress :
      ∀ r0,
        r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
        side ≠ Term.Boolean false ->
          let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s))
          let rFlat :=
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          let first := __str_re_consume_rec sFlat rFlat sFlat
          let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          let carry :=
            __eo_and (Term.Boolean true)
              (__eo_not (__eo_eq (__str_membership_re first) eps))
          let nextS :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_ite carry sFlat (__str_membership_str first))
          let nextR :=
            __re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__eo_ite carry rFlat (__str_membership_re first))) eps
          let second := __str_re_consume_rec nextS nextR nextS
          first ≠ Term.Boolean false ∧
            second ≠ Term.Boolean false ∧
            first ≠ Term.Stuck ∧
            second ≠ Term.Stuck := by
    intro r0 hR hSideNotFalse
    subst r
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    rcases hMultCarryProgress r0 rfl hSideNotFalse with
      ⟨_hCarryEq, hSecondNe, hFirstEqFalse, hSecondEqFalse⟩
    rcases hMultFirstInputProgress r0 rfl hSideNotFalse with
      ⟨_hSFlatTy, _hRFlatTy, _hSFlatList, _hRFlatList, hFirstNe,
        _hSFlatNe, _hRFlatNe⟩
    exact ⟨
      StrInReConsumeInternal.ne_of_eo_eq_false_local first (Term.Boolean false)
        (by simpa [first] using hFirstEqFalse),
      StrInReConsumeInternal.ne_of_eo_eq_false_local second (Term.Boolean false)
        (by simpa [second] using hSecondEqFalse),
      by simpa [first] using hFirstNe,
      by simpa [second] using hSecondNe⟩
  have hMultFirstNativeEqProgress :
      ∀ r0,
        r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
        side ≠ Term.Boolean false ->
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        ∀ sFlatSs rFlatRv firstSs firstRv,
          __smtx_model_eval M (__eo_to_smt sFlat) =
            SmtValue.Seq sFlatSs ->
          __smtx_model_eval M (__eo_to_smt rFlat) =
            SmtValue.RegLan rFlatRv ->
          __smtx_model_eval M
              (__eo_to_smt (__str_membership_str first)) =
            SmtValue.Seq firstSs ->
          __smtx_model_eval M
              (__eo_to_smt (__str_membership_re first)) =
            SmtValue.RegLan firstRv ->
            native_str_in_re (native_unpack_string sFlatSs) rFlatRv =
              native_str_in_re (native_unpack_string firstSs) firstRv) := by
    intro r0 hR hSideNotFalse
    subst r
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    rcases hMultFirstInputProgress r0 rfl hSideNotFalse with
      ⟨hSFlatTy, hRFlatTy, _hSFlatList, _hRFlatList, hFirstNe,
        _hSFlatNe, _hRFlatNe⟩
    rcases hMultSecondInputNeProgress r0 rfl hSideNotFalse with
      ⟨hMemReNe, _hCarryNe, _hNextSNe, _hNextRNe, _hSecondNe⟩
    have hFirstTy :
        __smtx_typeof (__eo_to_smt first) = SmtType.Bool :=
      hRecType sFlat rFlat sFlat
        (by simpa [sFlat] using hSFlatTy)
        (by simpa [rFlat] using hRFlatTy)
        (by simpa [first] using hFirstNe)
    have hFirstRebuild :
        first =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (__str_membership_str first))
            (__str_membership_re first) :=
      str_membership_re_eq_rebuild first (__str_membership_re first) rfl
        (by simpa [first] using hMemReNe)
    exact StrInReConsumeInternal.str_re_consume_rec_native_eq_of_rebuilt_result_local M hM
      sFlat rFlat sFlat first (hRecModelRel sFlat rFlat sFlat) rfl
      hFirstRebuild
      (by simpa [first] using hFirstNe)
      (by simpa [sFlat] using hSFlatTy)
      (by simpa [rFlat] using hRFlatTy)
      hFirstTy
  have hMultFirstInputEvalProgress :
      ∀ r0,
        r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
        side ≠ Term.Boolean false ->
          let sFlatSource := __str_flatten (__str_nary_intro s)
          let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat) sFlatSource
          let rFlatSource :=
            __re_flatten (Term.Boolean true) r0
          let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          let rFlat :=
            __re_rev_map_rev rFlatSource eps
          ∃ ss flatSs sFlatSs rv flatRv rFlatRv,
            __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
            __smtx_model_eval M (__eo_to_smt sFlatSource) =
              SmtValue.Seq flatSs ∧
            __smtx_model_eval M (__eo_to_smt sFlat) =
              SmtValue.Seq sFlatSs ∧
            __smtx_model_eval M (__eo_to_smt r0) =
              SmtValue.RegLan rv ∧
            __smtx_model_eval M (__eo_to_smt rFlatSource) =
              SmtValue.RegLan flatRv ∧
            __smtx_model_eval M (__eo_to_smt rFlat) =
              SmtValue.RegLan rFlatRv ∧
            __smtx_typeof (__eo_to_smt sFlatSource) =
              SmtType.Seq SmtType.Char ∧
            __smtx_typeof (__eo_to_smt sFlat) =
              SmtType.Seq SmtType.Char ∧
            __smtx_typeof (__eo_to_smt rFlatSource) = SmtType.RegLan ∧
            __smtx_typeof (__eo_to_smt rFlat) = SmtType.RegLan ∧
            __eo_is_list (Term.UOp UserOp.str_concat) sFlatSource =
              Term.Boolean true ∧
            __eo_is_list (Term.UOp UserOp.str_concat) sFlat =
              Term.Boolean true ∧
            __eo_is_list (Term.UOp UserOp.re_concat) rFlatSource =
              Term.Boolean true ∧
            __eo_is_list (Term.UOp UserOp.re_concat) rFlat =
              Term.Boolean true ∧
            RuleProofs.smt_value_rel (SmtValue.Seq flatSs)
              (SmtValue.Seq ss) := by
    intro r0 hR hSideNotFalse
    subst r
    let multR := Term.Apply (Term.UOp UserOp.re_mult) r0
    let sFlatSource := __str_flatten (__str_nary_intro s)
    let sFlat := __eo_list_rev (Term.UOp UserOp.str_concat) sFlatSource
    let rFlatSource :=
      __re_flatten (Term.Boolean true) r0
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let rFlat := __re_rev_map_rev rFlatSource eps
    rcases hMultFirstInputProgress r0 rfl hSideNotFalse with
      ⟨_hSFlatTy, _hRFlatTy, _hSFlatList, _hRFlatList, _hFirstNe,
        hSFlatNe, hRFlatNe⟩
    rcases str_re_consume_translation_facts s multR side (by
        simpa [multR] using hEqTrans) with
      ⟨_hStrInTrans, _hSideTrans, _hSTy, hMultRTy, _hEqBool⟩
    have hR0Ty : __smtx_typeof (__eo_to_smt r0) = SmtType.RegLan :=
      StrInReConsumeInternal.re_mult_arg_type_of_reglan_consume_local r0
        (by simpa [multR] using hMultRTy)
    exact StrInReConsumeInternal.str_re_consume_first_input_eval_context_local M hM s multR side
      r0 (by simpa [multR] using hEqTrans) hR0Ty
      (by simpa [sFlatSource, sFlat, __str_nary_intro] using hSFlatNe)
      (by simpa [rFlatSource, eps, rFlat] using hRFlatNe)
  have hMultFirstInputEvalForValuesProgress :
      ∀ r0,
        r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
        side ≠ Term.Boolean false ->
        ∀ ss starRv,
          __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r0)) =
            SmtValue.RegLan starRv ->
          ∃ r0Rv flatSs sFlatSs flatRv rFlatRv,
            __smtx_model_eval M (__eo_to_smt r0) =
              SmtValue.RegLan r0Rv ∧
            starRv = native_re_mult r0Rv ∧
            __smtx_model_eval M
                (__eo_to_smt (__str_flatten (__str_nary_intro s))) =
              SmtValue.Seq flatSs ∧
            __smtx_model_eval M
                (__eo_to_smt
                  (__eo_list_rev (Term.UOp UserOp.str_concat)
                    (__str_flatten (__str_nary_intro s)))) =
              SmtValue.Seq sFlatSs ∧
            __smtx_model_eval M
                (__eo_to_smt
                  (__re_flatten (Term.Boolean true)
                    r0)) =
              SmtValue.RegLan flatRv ∧
            __smtx_model_eval M
                (__eo_to_smt
                  (__re_rev_map_rev
                    (__re_flatten (Term.Boolean true) r0)
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String [])))) =
              SmtValue.RegLan rFlatRv ∧
            __smtx_typeof
                (__eo_to_smt (__str_flatten (__str_nary_intro s))) =
              SmtType.Seq SmtType.Char ∧
            __smtx_typeof
                (__eo_to_smt
                  (__eo_list_rev (Term.UOp UserOp.str_concat)
                    (__str_flatten (__str_nary_intro s)))) =
              SmtType.Seq SmtType.Char ∧
            __smtx_typeof
                (__eo_to_smt
                  (__re_flatten (Term.Boolean true)
                    r0)) =
              SmtType.RegLan ∧
            __smtx_typeof
                (__eo_to_smt
                  (__re_rev_map_rev
                    (__re_flatten (Term.Boolean true) r0)
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String [])))) =
              SmtType.RegLan ∧
            __eo_is_list (Term.UOp UserOp.str_concat)
                (__str_flatten (__str_nary_intro s)) =
              Term.Boolean true ∧
            __eo_is_list (Term.UOp UserOp.str_concat)
                (__eo_list_rev (Term.UOp UserOp.str_concat)
                  (__str_flatten (__str_nary_intro s))) =
              Term.Boolean true ∧
            __eo_is_list (Term.UOp UserOp.re_concat)
                (__re_flatten (Term.Boolean true) r0) =
              Term.Boolean true ∧
            __eo_is_list (Term.UOp UserOp.re_concat)
                (__re_rev_map_rev
                  (__re_flatten (Term.Boolean true) r0)
                  (Term.Apply (Term.UOp UserOp.str_to_re)
                    (Term.String []))) =
              Term.Boolean true ∧
            RuleProofs.smt_value_rel (SmtValue.Seq flatSs)
              (SmtValue.Seq ss) := by
    intro r0 hR hSideNotFalse ss starRv hSEval hStarEval
    rcases hMultFirstInputEvalProgress r0 hR hSideNotFalse with
      ⟨ss0, flatSs, sFlatSs, r0Rv, flatRv, rFlatRv, hSEval0,
        hSFlatSourceEval, hSFlatEval, hR0Eval, hRFlatSourceEval,
        hRFlatEval, hSFlatSourceTy, hSFlatTy, hRFlatSourceTy,
        hRFlatTy, hSFlatSourceList, hSFlatList, hRFlatSourceList,
        hRFlatList, hSFlatSourceRel⟩
    have hSs : ss0 = ss := by
      rw [hSEval] at hSEval0
      cases hSEval0
      rfl
    have hStarRv : starRv = native_re_mult r0Rv := by
      have hStarEval0 :
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r0)) =
            SmtValue.RegLan (native_re_mult r0Rv) :=
        eval_re_mult_reglan_consume_local M r0 r0Rv hR0Eval
      rw [hStarEval] at hStarEval0
      cases hStarEval0
      rfl
    subst ss0
    exact ⟨r0Rv, flatSs, sFlatSs, flatRv, rFlatRv, hR0Eval,
      hStarRv, hSFlatSourceEval, hSFlatEval, hRFlatSourceEval,
      hRFlatEval, hSFlatSourceTy, hSFlatTy, hRFlatSourceTy, hRFlatTy,
      hSFlatSourceList, hSFlatList, hRFlatSourceList, hRFlatList,
      hSFlatSourceRel⟩
  have hMultSecondInputTypeProgress :
      ∀ r0,
        r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
        side ≠ Term.Boolean false ->
          let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s))
          let rFlat :=
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          let first := __str_re_consume_rec sFlat rFlat sFlat
          let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          let carry :=
            __eo_and (Term.Boolean true)
              (__eo_not (__eo_eq (__str_membership_re first) eps))
          let nextS :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_ite carry sFlat (__str_membership_str first))
          let nextR :=
            __re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__eo_ite carry rFlat (__str_membership_re first))) eps
          __smtx_typeof (__eo_to_smt nextS) =
              SmtType.Seq SmtType.Char ∧
            __smtx_typeof (__eo_to_smt nextR) = SmtType.RegLan := by
    intro r0 hR hSideNotFalse
    subst r
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    rcases hMultFirstInputProgress r0 rfl hSideNotFalse with
      ⟨hSFlatTy, hRFlatTy, _hSFlatList, _hRFlatList, hFirstNe,
        _hSFlatNe, _hRFlatNe⟩
    rcases hMultSecondInputNeProgress r0 rfl hSideNotFalse with
      ⟨hMemReNe, _hCarryNe, hNextSNe, hNextRNe, _hSecondNe⟩
    have hFirstTy :
        __smtx_typeof (__eo_to_smt first) = SmtType.Bool :=
      hRecType sFlat rFlat sFlat
        (by simpa [sFlat] using hSFlatTy)
        (by simpa [rFlat] using hRFlatTy)
        (by simpa [first] using hFirstNe)
    rcases StrInReConsumeInternal.str_re_consume_rec_projection_types_of_bool_local first
        hFirstTy (by simpa [first] using hMemReNe) with
      ⟨hMemStrTy, hMemReTy⟩
    have hIteSNe :
        __eo_ite carry sFlat (__str_membership_str first) ≠ Term.Stuck :=
      eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first)) hNextSNe
    have hIteSTy :
        __smtx_typeof
            (__eo_to_smt
              (__eo_ite carry sFlat (__str_membership_str first))) =
          SmtType.Seq SmtType.Char :=
      StrInReConsumeInternal.smt_typeof_eo_ite_of_branches_local carry sFlat
        (__str_membership_str first) hSFlatTy hMemStrTy hIteSNe
    have hIteSList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first)) =
          Term.Boolean true :=
      eo_list_rev_is_list_true_of_ne_stuck
        (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
        (by simpa [nextS] using hNextSNe)
    have hNextSTy :
        __smtx_typeof (__eo_to_smt nextS) =
          SmtType.Seq SmtType.Char := by
      simpa [nextS] using
        smt_typeof_list_rev_str_concat_of_seq
          (__eo_ite carry sFlat (__str_membership_str first))
          SmtType.Char hIteSList hIteSTy
          (by simpa [nextS] using hNextSNe)
    have hFlatNextRNe :
        __re_flatten (Term.Boolean true)
            (__eo_ite carry rFlat (__str_membership_re first)) ≠
          Term.Stuck :=
      StrInReConsumeInternal.re_rev_map_rev_arg_ne_stuck_of_ne_stuck_local
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps hNextRNe
    have hIteRNe :
        __eo_ite carry rFlat (__str_membership_re first) ≠ Term.Stuck :=
      StrInReConsumeInternal.re_flatten_tree_ne_stuck_of_ne_stuck_local
        (Term.Boolean true)
        (__eo_ite carry rFlat (__str_membership_re first)) hFlatNextRNe
    have hIteRTy :
        __smtx_typeof
            (__eo_to_smt
              (__eo_ite carry rFlat (__str_membership_re first))) =
          SmtType.RegLan :=
      StrInReConsumeInternal.smt_typeof_eo_ite_of_branches_local carry rFlat
        (__str_membership_re first) hRFlatTy hMemReTy hIteRNe
    have hNextRTy :
        __smtx_typeof (__eo_to_smt nextR) = SmtType.RegLan := by
      rcases StrInReConsumeInternal.str_re_consume_rflat_type_facts_local M hM
          (__eo_ite carry rFlat (__str_membership_re first)) hIteRTy
          (by simpa [nextR] using hNextRNe) with
        ⟨hTy, _hList, _hFlatNe, _hFlatList, _hFlatTy⟩
      simpa [nextR] using hTy
    exact ⟨hNextSTy, hNextRTy⟩
  have hMultSecondNativeEqProgress :
      ∀ r0,
        r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
        side ≠ Term.Boolean false ->
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean true)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextS :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first))
        let nextR :=
          __re_rev_map_rev
            (__re_flatten (Term.Boolean true)
              (__eo_ite carry rFlat (__str_membership_re first))) eps
        let second := __str_re_consume_rec nextS nextR nextS
        ∀ nextSs nextRv partsSs reRv,
          __smtx_model_eval M (__eo_to_smt nextS) =
            SmtValue.Seq nextSs ->
          __smtx_model_eval M (__eo_to_smt nextR) =
            SmtValue.RegLan nextRv ->
          __smtx_model_eval M
              (__eo_to_smt (__str_membership_str second)) =
            SmtValue.Seq partsSs ->
          __smtx_model_eval M
              (__eo_to_smt (__str_membership_re second)) =
            SmtValue.RegLan reRv ->
            native_str_in_re (native_unpack_string nextSs) nextRv =
              native_str_in_re (native_unpack_string partsSs) reRv) := by
    intro r0 hR hSideNotFalse
    subst r
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    rcases hMultSecondInputTypeProgress r0 rfl hSideNotFalse with
      ⟨hNextSTy, hNextRTy⟩
    rcases hMultFinalNotFalseProgress r0 rfl hSideNotFalse with
      ⟨_hFirstNotFalse, _hSecondNotFalse, _hFirstNe, hSecondNe⟩
    have hSecondTy :
        __smtx_typeof (__eo_to_smt second) = SmtType.Bool := by
      simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
        StrInReConsumeInternal.str_re_consume_mult_second_type_from_rec_type_local M hM hRecType
          s r0 side hEqTrans hSNe hSide hSideNe hSideNotFalse
    have hSecondRebuild :
        second =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (__str_membership_str second))
            (__str_membership_re second) := by
      simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
        hMultFinalSecondRebuildProgress r0 rfl hSideNotFalse
    exact StrInReConsumeInternal.str_re_consume_rec_native_eq_of_rebuilt_result_local M hM
      nextS nextR nextS second (hRecModelRel nextS nextR nextS) rfl
      hSecondRebuild
      (by simpa [second] using hSecondNe)
      (by simpa [sFlat, rFlat, first, eps, carry, nextS] using hNextSTy)
      (by simpa [sFlat, rFlat, first, eps, carry, nextR] using hNextRTy)
      hSecondTy
  have hMultFinalRelOfCandidateNativeEqProgress :
      ∀ r0,
        r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
        side ≠ Term.Boolean false ->
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean true)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextS :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first))
        let nextR :=
          __re_rev_map_rev
            (__re_flatten (Term.Boolean true)
              (__eo_ite carry rFlat (__str_membership_re first))) eps
        let second := __str_re_consume_rec nextS nextR nextS
        let final :=
          __eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.str_in_re)
              (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
                (__str_collect (__str_membership_str second))))
            (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
              (__re_unflatten (Term.Boolean true)
                (__str_membership_re second)))
        let candidate :=
          __eo_ite (__eo_eq first (Term.Boolean false))
            (Term.Boolean false)
            (__eo_ite (__eo_eq second (Term.Boolean false))
              (Term.Boolean false) final)
        ∀ ss rv partsSs,
          __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r0)) =
            SmtValue.RegLan rv ->
          __smtx_model_eval M
              (__eo_to_smt (__str_membership_str candidate)) =
            SmtValue.Seq partsSs ->
            native_str_in_re (native_unpack_string ss) rv =
              native_str_in_re (native_unpack_string partsSs) rv) ->
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
          (__smtx_model_eval M (__eo_to_smt side)) := by
    intro r0 hR hSideNotFalse hCandidateNativeEq
    subst r
    let multR := Term.Apply (Term.UOp UserOp.re_mult) r0
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    let final :=
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
            (__str_collect (__str_membership_str second))))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)))
    let candidate :=
      __eo_ite (__eo_eq first (Term.Boolean false))
        (Term.Boolean false)
        (__eo_ite (__eo_eq second (Term.Boolean false))
          (Term.Boolean false) final)
    simpa [multR] using
      StrInReConsumeInternal.str_re_consume_mult_model_rel_of_final_candidate_native_eq_local
        M hM s r0 side (by simpa [multR] using hEqTrans) hSNe
        (by simpa [multR] using hSide) hSideNe hSideNotFalse
        (by
          simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second,
            final, candidate] using hCandidateNativeEq)
  have hMultFinalRelOfSecondStrNativeEqProgress :
      ∀ r0,
        r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
        side ≠ Term.Boolean false ->
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean true)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextS :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first))
        let nextR :=
          __re_rev_map_rev
            (__re_flatten (Term.Boolean true)
              (__eo_ite carry rFlat (__str_membership_re first))) eps
        let second := __str_re_consume_rec nextS nextR nextS
        ∀ ss rv partsSs,
          __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r0)) =
            SmtValue.RegLan rv ->
          __smtx_model_eval M
              (__eo_to_smt (__str_membership_str second)) =
            SmtValue.Seq partsSs ->
          __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
              (__re_unflatten (Term.Boolean true)
                (__str_membership_re second)) =
            Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) ->
            native_str_in_re (native_unpack_string ss) rv =
              native_str_in_re (native_unpack_string partsSs) rv) ->
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
          (__smtx_model_eval M (__eo_to_smt side)) := by
    intro r0 hR hSideNotFalse hSecondStrNativeEq
    subst r
    let multR := Term.Apply (Term.UOp UserOp.re_mult) r0
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    let final :=
      __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
            (__str_collect (__str_membership_str second))))
        (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)))
    let candidate :=
      __eo_ite (__eo_eq first (Term.Boolean false))
        (Term.Boolean false)
        (__eo_ite (__eo_eq second (Term.Boolean false))
          (Term.Boolean false) final)
    rcases hMultFinalProgress r0 rfl hSideNotFalse with
      ⟨_hSideRebuild, hCandidateFinal, hCandidateMem⟩
    rcases hMultFinalSubtermProgress r0 rfl hSideNotFalse with
      ⟨_hSideRebuild, _hCandidateFinal, _hCandidateMem, hCollectNe,
        hUnflatElimNe⟩
    have hSecondTy :
        __smtx_typeof (__eo_to_smt second) = SmtType.Bool := by
      simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
        StrInReConsumeInternal.str_re_consume_mult_second_type_from_rec_type_local M hM hRecType
          s r0 side (by simpa [multR] using hEqTrans) hSNe
          (by simpa [multR] using hSide) hSideNe hSideNotFalse
    rcases StrInReConsumeInternal.str_re_consume_final_raw_projection_types_of_second_bool_local
        second hSecondTy (by simpa [second] using hUnflatElimNe) with
      ⟨hPartsTy, _hRePartTy⟩
    have hPartsList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (__str_membership_str second) =
          Term.Boolean true := by
      simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
        hMultFinalPartsListProgress r0 rfl hSideNotFalse
    have hCandidateNativeEq :
        ∀ ss rv partsSs,
          __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
          __smtx_model_eval M (__eo_to_smt multR) =
            SmtValue.RegLan rv ->
          __smtx_model_eval M
              (__eo_to_smt (__str_membership_str candidate)) =
            SmtValue.Seq partsSs ->
            native_str_in_re (native_unpack_string ss) rv =
              native_str_in_re (native_unpack_string partsSs) rv := by
      exact StrInReConsumeInternal.str_re_consume_candidate_str_native_eq_of_second_parts_local
        M hM s multR candidate second
        (by
          simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second,
            final, candidate] using hCandidateFinal)
        (by
          simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second,
            final, candidate] using hCandidateMem)
        hPartsList hPartsTy
        (by
          simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second,
            multR] using hSecondStrNativeEq)
        (by simpa [second] using hCollectNe)
    simpa [multR] using
      hMultFinalRelOfCandidateNativeEqProgress r0 rfl hSideNotFalse
        (by
          simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second,
            final, candidate, multR] using hCandidateNativeEq)
  let nonMultInputNativeEq
      (_hSideNotFalse : side ≠ Term.Boolean false)
      (_hNotMult :
        ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) :
      Prop :=
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    ∀ ss rv nextSs nextRv,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
      __smtx_model_eval M (__eo_to_smt nextS) =
        SmtValue.Seq nextSs ->
      __smtx_model_eval M (__eo_to_smt nextR) =
        SmtValue.RegLan nextRv ->
        native_str_in_re (native_unpack_string ss) rv =
          native_str_in_re (native_unpack_string nextSs) nextRv
  let multSecondStrNativeEq
      (r0 : Term)
      (_hSideNotFalse : side ≠ Term.Boolean false) : Prop :=
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    ∀ ss rv partsSs,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r0)) =
        SmtValue.RegLan rv ->
      __smtx_model_eval M
          (__eo_to_smt (__str_membership_str second)) =
        SmtValue.Seq partsSs ->
      __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__re_unflatten (Term.Boolean true)
            (__str_membership_re second)) =
        Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) ->
        native_str_in_re (native_unpack_string ss) rv =
          native_str_in_re (native_unpack_string partsSs) rv
  let nonMultFirstFalseNative
      (_hNotMult :
        ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) :
      Prop :=
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    first = Term.Boolean false ->
      ∀ ss rv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
          native_str_in_re (native_unpack_string ss) rv = false
  let multFirstFalseNative
      (r0 : Term)
      (_hR : r = Term.Apply (Term.UOp UserOp.re_mult) r0) :
      Prop :=
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    first = Term.Boolean false ->
      ∀ ss rv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M
            (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r0)) =
          SmtValue.RegLan rv ->
          native_str_in_re (native_unpack_string ss) rv = false
  let nonMultSecondFalseInputNativeEq
      (_hNotMult :
        ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False) :
      Prop :=
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    first ≠ Term.Boolean false ->
    second = Term.Boolean false ->
      ∀ ss rv nextSs nextRv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
        __smtx_model_eval M (__eo_to_smt nextS) =
          SmtValue.Seq nextSs ->
        __smtx_model_eval M (__eo_to_smt nextR) =
          SmtValue.RegLan nextRv ->
          native_str_in_re (native_unpack_string ss) rv =
            native_str_in_re (native_unpack_string nextSs) nextRv
  let multSecondFalseInputNativeEq
      (r0 : Term)
      (_hR : r = Term.Apply (Term.UOp UserOp.re_mult) r0) :
      Prop :=
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    first ≠ Term.Boolean false ->
    second = Term.Boolean false ->
      ∀ ss rv nextSs nextRv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M
            (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r0)) =
          SmtValue.RegLan rv ->
        __smtx_model_eval M (__eo_to_smt nextS) =
          SmtValue.Seq nextSs ->
        __smtx_model_eval M (__eo_to_smt nextR) =
          SmtValue.RegLan nextRv ->
          native_str_in_re (native_unpack_string ss) rv =
            native_str_in_re (native_unpack_string nextSs) nextRv
  have hNonMultFalseOfSecondFalseInputNativeEqProgress :
      ∀ (hNotMult :
          ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False),
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean false)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextS :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first))
        let nextR :=
          __re_rev_map_rev
            (__re_flatten (Term.Boolean true)
              (__eo_ite carry rFlat (__str_membership_re first))) eps
        let second := __str_re_consume_rec nextS nextR nextS
        second = Term.Boolean false) ->
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean false)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextS :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first))
        __smtx_typeof (__eo_to_smt nextS) = SmtType.Seq SmtType.Char) ->
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean false)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextR :=
          __re_rev_map_rev
            (__re_flatten (Term.Boolean true)
              (__eo_ite carry rFlat (__str_membership_re first))) eps
        __smtx_typeof (__eo_to_smt nextR) = SmtType.RegLan) ->
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean false)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextS :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first))
        let nextR :=
          __re_rev_map_rev
            (__re_flatten (Term.Boolean true)
              (__eo_ite carry rFlat (__str_membership_re first))) eps
        ∀ ss rv nextSs nextRv,
          __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
          __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
          __smtx_model_eval M (__eo_to_smt nextS) =
            SmtValue.Seq nextSs ->
          __smtx_model_eval M (__eo_to_smt nextR) =
            SmtValue.RegLan nextRv ->
            native_str_in_re (native_unpack_string ss) rv =
              native_str_in_re (native_unpack_string nextSs) nextRv) ->
          ∀ ss rv,
            __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
            __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
              native_str_in_re (native_unpack_string ss) rv = false := by
    intro hNotMult hSecondFalse hNextSTy hNextRTy hInputNativeEq
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    exact hOriginalFalseOfInputNativeEqAndRecFalseProgress nextS nextR
      second
      (by simpa [sFlat, rFlat, first, eps, carry, nextS] using hNextSTy)
      (by simpa [sFlat, rFlat, first, eps, carry, nextR] using hNextRTy)
      (by simpa [second])
      (by
        simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
          hSecondFalse)
      (by
        simpa [sFlat, rFlat, first, eps, carry, nextS, nextR] using
          hInputNativeEq)
  have hMultFalseOfSecondFalseInputNativeEqProgress :
      ∀ r0,
        r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean true)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextS :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first))
        let nextR :=
          __re_rev_map_rev
            (__re_flatten (Term.Boolean true)
              (__eo_ite carry rFlat (__str_membership_re first))) eps
        let second := __str_re_consume_rec nextS nextR nextS
        second = Term.Boolean false) ->
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean true)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextS :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first))
        __smtx_typeof (__eo_to_smt nextS) = SmtType.Seq SmtType.Char) ->
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean true)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextR :=
          __re_rev_map_rev
            (__re_flatten (Term.Boolean true)
              (__eo_ite carry rFlat (__str_membership_re first))) eps
        __smtx_typeof (__eo_to_smt nextR) = SmtType.RegLan) ->
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean true)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextS :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first))
        let nextR :=
          __re_rev_map_rev
            (__re_flatten (Term.Boolean true)
              (__eo_ite carry rFlat (__str_membership_re first))) eps
        ∀ ss rv nextSs nextRv,
          __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r0)) =
            SmtValue.RegLan rv ->
          __smtx_model_eval M (__eo_to_smt nextS) =
            SmtValue.Seq nextSs ->
          __smtx_model_eval M (__eo_to_smt nextR) =
            SmtValue.RegLan nextRv ->
            native_str_in_re (native_unpack_string ss) rv =
              native_str_in_re (native_unpack_string nextSs) nextRv) ->
          ∀ ss rv,
            __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
            __smtx_model_eval M
                (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r0)) =
              SmtValue.RegLan rv ->
              native_str_in_re (native_unpack_string ss) rv = false := by
    intro r0 hR hSecondFalse hNextSTy hNextRTy hInputNativeEq
    subst r
    let multR := Term.Apply (Term.UOp UserOp.re_mult) r0
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    simpa [multR] using
      hOriginalFalseOfInputNativeEqAndRecFalseProgress nextS nextR
        second
        (by simpa [sFlat, rFlat, first, eps, carry, nextS] using hNextSTy)
        (by simpa [sFlat, rFlat, first, eps, carry, nextR] using hNextRTy)
        (by simpa [second])
        (by
          simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second]
            using hSecondFalse)
        (by
          simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, multR]
            using hInputNativeEq)
  have hNonMultSecondInputTypeOfSecondFalseProgress :
      ∀ (hNotMult :
          ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False),
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean false)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextS :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first))
        let nextR :=
          __re_rev_map_rev
            (__re_flatten (Term.Boolean true)
              (__eo_ite carry rFlat (__str_membership_re first))) eps
        let second := __str_re_consume_rec nextS nextR nextS
        second = Term.Boolean false) ->
          (let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s))
          let rFlat :=
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          let first := __str_re_consume_rec sFlat rFlat sFlat
          let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          let carry :=
            __eo_and (Term.Boolean false)
              (__eo_not (__eo_eq (__str_membership_re first) eps))
          let nextS :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_ite carry sFlat (__str_membership_str first))
          let nextR :=
            __re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__eo_ite carry rFlat (__str_membership_re first))) eps
          __smtx_typeof (__eo_to_smt nextS) = SmtType.Seq SmtType.Char ∧
            __smtx_typeof (__eo_to_smt nextR) = SmtType.RegLan) := by
    intro hNotMult hSecondFalse
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean false)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    rcases str_re_consume_translation_facts s r side hEqTrans with
      ⟨_hStrInTrans, _hSideTrans, _hSTy, hRTy, _hEqBool⟩
    have hSecondFalseLocal : second = Term.Boolean false := by
      simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
        hSecondFalse
    have hSecondNe : second ≠ Term.Stuck := by
      intro hBad
      rw [hBad] at hSecondFalseLocal
      cases hSecondFalseLocal
    have hNextSNe : nextS ≠ Term.Stuck :=
      StrInReConsumeInternal.str_re_consume_rec_left_ne_stuck_of_ne_stuck nextS nextR nextS
        hSecondNe
    have hNextRNe : nextR ≠ Term.Stuck :=
      StrInReConsumeInternal.str_re_consume_rec_right_ne_stuck_of_ne_stuck nextS nextR nextS
        hSecondNe
    have hIteSNe :
        __eo_ite carry sFlat (__str_membership_str first) ≠ Term.Stuck :=
      eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first)) hNextSNe
    have hCarryNe : carry ≠ Term.Stuck := by
      rcases eo_ite_cases_of_ne_stuck carry sFlat
          (__str_membership_str first) hIteSNe with hCarryTrue |
          hCarryFalse
      · rw [hCarryTrue]
        simp
      · rw [hCarryFalse]
        simp
    have hCarryFalseLocal : carry = Term.Boolean false :=
      StrInReConsumeInternal.eo_and_false_left_eq_false_of_ne_stuck_local
        (__eo_not (__eo_eq (__str_membership_re first) eps)) hCarryNe
    have hMemStrNe : __str_membership_str first ≠ Term.Stuck := by
      simpa [hCarryFalseLocal, eo_ite_false] using hIteSNe
    have hFlatNextRNe :
        __re_flatten (Term.Boolean true)
            (__eo_ite carry rFlat (__str_membership_re first)) ≠
          Term.Stuck :=
      StrInReConsumeInternal.re_rev_map_rev_arg_ne_stuck_of_ne_stuck_local
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps hNextRNe
    have hIteRNe :
        __eo_ite carry rFlat (__str_membership_re first) ≠ Term.Stuck :=
      StrInReConsumeInternal.re_flatten_tree_ne_stuck_of_ne_stuck_local
        (Term.Boolean true)
        (__eo_ite carry rFlat (__str_membership_re first)) hFlatNextRNe
    have hMemReNe : __str_membership_re first ≠ Term.Stuck := by
      simpa [hCarryFalseLocal, eo_ite_false] using hIteRNe
    have hFirstNe : first ≠ Term.Stuck := by
      intro hBad
      apply hMemReNe
      simp [hBad, __str_membership_re]
    have hSFlatNe : sFlat ≠ Term.Stuck :=
      StrInReConsumeInternal.str_re_consume_rec_left_ne_stuck_of_ne_stuck sFlat rFlat sFlat
        hFirstNe
    have hRFlatNe : rFlat ≠ Term.Stuck :=
      StrInReConsumeInternal.str_re_consume_rec_right_ne_stuck_of_ne_stuck sFlat rFlat sFlat
        hFirstNe
    rcases StrInReConsumeInternal.str_re_consume_sflat_type_facts_local M hM s r side hEqTrans
        (by simpa [sFlat, __str_nary_intro] using hSFlatNe) with
      ⟨hSFlatTy, _hSFlatList, _hFlatNe, _hFlatList, _hFlatTy⟩
    rcases StrInReConsumeInternal.str_re_consume_rflat_type_facts_local M hM r hRTy
        (by simpa [rFlat] using hRFlatNe) with
      ⟨hRFlatTy, _hRFlatList, _hReFlatNe, _hReFlatList, _hReFlatTy⟩
    have hFirstTy :
        __smtx_typeof (__eo_to_smt first) = SmtType.Bool :=
      hRecType sFlat rFlat sFlat
        (by simpa [sFlat] using hSFlatTy)
        (by simpa [rFlat] using hRFlatTy)
        (by simpa [first] using hFirstNe)
    rcases StrInReConsumeInternal.str_re_consume_rec_projection_types_of_bool_local first
        hFirstTy (by simpa [first] using hMemReNe) with
      ⟨hMemStrTy, hMemReTy⟩
    have hIteSTy :
        __smtx_typeof
            (__eo_to_smt
              (__eo_ite carry sFlat (__str_membership_str first))) =
          SmtType.Seq SmtType.Char := by
      simpa [hCarryFalseLocal, eo_ite_false] using hMemStrTy
    have hIteSList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first)) =
          Term.Boolean true :=
      eo_list_rev_is_list_true_of_ne_stuck
        (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
        (by simpa [nextS] using hNextSNe)
    have hNextSTy :
        __smtx_typeof (__eo_to_smt nextS) =
          SmtType.Seq SmtType.Char := by
      simpa [nextS] using
        smt_typeof_list_rev_str_concat_of_seq
          (__eo_ite carry sFlat (__str_membership_str first))
          SmtType.Char hIteSList hIteSTy
          (by simpa [nextS] using hNextSNe)
    have hIteRTy :
        __smtx_typeof
            (__eo_to_smt
              (__eo_ite carry rFlat (__str_membership_re first))) =
          SmtType.RegLan := by
      simpa [hCarryFalseLocal, eo_ite_false] using hMemReTy
    have hNextRTy :
        __smtx_typeof (__eo_to_smt nextR) = SmtType.RegLan := by
      rcases StrInReConsumeInternal.str_re_consume_rflat_type_facts_local M hM
          (__eo_ite carry rFlat (__str_membership_re first)) hIteRTy
          (by simpa [nextR] using hNextRNe) with
        ⟨hTy, _hList, _hFlatNe, _hFlatList, _hFlatTy⟩
      simpa [nextR] using hTy
    exact ⟨
      by simpa [sFlat, rFlat, first, eps, carry, nextS] using hNextSTy,
      by simpa [sFlat, rFlat, first, eps, carry, nextR] using hNextRTy⟩
  have hMultSecondInputTypeOfSecondFalseProgress :
      ∀ r0,
        r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean true)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextS :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first))
        let nextR :=
          __re_rev_map_rev
            (__re_flatten (Term.Boolean true)
              (__eo_ite carry rFlat (__str_membership_re first))) eps
        let second := __str_re_consume_rec nextS nextR nextS
        second = Term.Boolean false) ->
          (let sFlat :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s))
          let rFlat :=
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
          let first := __str_re_consume_rec sFlat rFlat sFlat
          let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          let carry :=
            __eo_and (Term.Boolean true)
              (__eo_not (__eo_eq (__str_membership_re first) eps))
          let nextS :=
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_ite carry sFlat (__str_membership_str first))
          let nextR :=
            __re_rev_map_rev
              (__re_flatten (Term.Boolean true)
                (__eo_ite carry rFlat (__str_membership_re first))) eps
          __smtx_typeof (__eo_to_smt nextS) = SmtType.Seq SmtType.Char ∧
            __smtx_typeof (__eo_to_smt nextR) = SmtType.RegLan) := by
    intro r0 hR hSecondFalse
    subst r
    let multR := Term.Apply (Term.UOp UserOp.re_mult) r0
    let sFlat :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__str_flatten (__eo_list_singleton_intro
          (Term.UOp UserOp.str_concat) s))
    let rFlat :=
      __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
    let first := __str_re_consume_rec sFlat rFlat sFlat
    let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
    let carry :=
      __eo_and (Term.Boolean true)
        (__eo_not (__eo_eq (__str_membership_re first) eps))
    let nextS :=
      __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
    let nextR :=
      __re_rev_map_rev
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps
    let second := __str_re_consume_rec nextS nextR nextS
    rcases str_re_consume_translation_facts s multR side
        (by simpa [multR] using hEqTrans) with
      ⟨_hStrInTrans, _hSideTrans, _hSTy, hMultRTy, _hEqBool⟩
    have hR0Ty : __smtx_typeof (__eo_to_smt r0) = SmtType.RegLan :=
      StrInReConsumeInternal.re_mult_arg_type_of_reglan_consume_local r0
        (by simpa [multR] using hMultRTy)
    have hSecondFalseLocal : second = Term.Boolean false := by
      simpa [sFlat, rFlat, first, eps, carry, nextS, nextR, second] using
        hSecondFalse
    have hSecondNe : second ≠ Term.Stuck := by
      intro hBad
      rw [hBad] at hSecondFalseLocal
      cases hSecondFalseLocal
    have hNextSNe : nextS ≠ Term.Stuck :=
      StrInReConsumeInternal.str_re_consume_rec_left_ne_stuck_of_ne_stuck nextS nextR nextS
        hSecondNe
    have hNextRNe : nextR ≠ Term.Stuck :=
      StrInReConsumeInternal.str_re_consume_rec_right_ne_stuck_of_ne_stuck nextS nextR nextS
        hSecondNe
    have hIteSNe :
        __eo_ite carry sFlat (__str_membership_str first) ≠ Term.Stuck :=
      eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first)) hNextSNe
    have hCarryNe : carry ≠ Term.Stuck := by
      rcases eo_ite_cases_of_ne_stuck carry sFlat
          (__str_membership_str first) hIteSNe with hCarryTrue |
          hCarryFalse
      · rw [hCarryTrue]
        simp
      · rw [hCarryFalse]
        simp
    have hCarryEqLocal :
        carry = __eo_not (__eo_eq (__str_membership_re first) eps) :=
      StrInReConsumeInternal.eo_and_true_left_eq_arg_of_ne_stuck_local
        (__eo_not (__eo_eq (__str_membership_re first) eps)) hCarryNe
    have hNotNe :
        __eo_not (__eo_eq (__str_membership_re first) eps) ≠
          Term.Stuck := by
      simpa [← hCarryEqLocal] using hCarryNe
    have hEqNe :
        __eo_eq (__str_membership_re first) eps ≠ Term.Stuck :=
      StrInReConsumeInternal.eo_not_arg_ne_stuck_of_ne_stuck_local
        (__eo_eq (__str_membership_re first) eps) hNotNe
    have hMemReNe : __str_membership_re first ≠ Term.Stuck :=
      StrInReConsumeInternal.eo_eq_left_ne_stuck_of_ne_stuck_local (__str_membership_re first) eps
        hEqNe
    have hFirstNe : first ≠ Term.Stuck := by
      intro hBad
      apply hMemReNe
      simp [hBad, __str_membership_re]
    have hSFlatNe : sFlat ≠ Term.Stuck :=
      StrInReConsumeInternal.str_re_consume_rec_left_ne_stuck_of_ne_stuck sFlat rFlat sFlat
        hFirstNe
    have hRFlatNe : rFlat ≠ Term.Stuck :=
      StrInReConsumeInternal.str_re_consume_rec_right_ne_stuck_of_ne_stuck sFlat rFlat sFlat
        hFirstNe
    rcases StrInReConsumeInternal.str_re_consume_sflat_type_facts_local M hM s multR side
        (by simpa [multR] using hEqTrans)
        (by simpa [sFlat, __str_nary_intro] using hSFlatNe) with
      ⟨hSFlatTy, _hSFlatList, _hFlatNe, _hFlatList, _hFlatTy⟩
    rcases StrInReConsumeInternal.str_re_consume_rflat_type_facts_local M hM r0 hR0Ty
        (by simpa [rFlat] using hRFlatNe) with
      ⟨hRFlatTy, _hRFlatList, _hReFlatNe, _hReFlatList, _hReFlatTy⟩
    have hFirstTy :
        __smtx_typeof (__eo_to_smt first) = SmtType.Bool :=
      hRecType sFlat rFlat sFlat
        (by simpa [sFlat] using hSFlatTy)
        (by simpa [rFlat] using hRFlatTy)
        (by simpa [first] using hFirstNe)
    rcases StrInReConsumeInternal.str_re_consume_rec_projection_types_of_bool_local first
        hFirstTy (by simpa [first] using hMemReNe) with
      ⟨hMemStrTy, hMemReTy⟩
    have hIteSTy :
        __smtx_typeof
            (__eo_to_smt
              (__eo_ite carry sFlat (__str_membership_str first))) =
          SmtType.Seq SmtType.Char :=
      StrInReConsumeInternal.smt_typeof_eo_ite_of_branches_local carry sFlat
        (__str_membership_str first) hSFlatTy hMemStrTy hIteSNe
    have hIteSList :
        __eo_is_list (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first)) =
          Term.Boolean true :=
      eo_list_rev_is_list_true_of_ne_stuck
        (Term.UOp UserOp.str_concat)
        (__eo_ite carry sFlat (__str_membership_str first))
        (by simpa [nextS] using hNextSNe)
    have hNextSTy :
        __smtx_typeof (__eo_to_smt nextS) =
          SmtType.Seq SmtType.Char := by
      simpa [nextS] using
        smt_typeof_list_rev_str_concat_of_seq
          (__eo_ite carry sFlat (__str_membership_str first))
          SmtType.Char hIteSList hIteSTy
          (by simpa [nextS] using hNextSNe)
    have hFlatNextRNe :
        __re_flatten (Term.Boolean true)
            (__eo_ite carry rFlat (__str_membership_re first)) ≠
          Term.Stuck :=
      StrInReConsumeInternal.re_rev_map_rev_arg_ne_stuck_of_ne_stuck_local
        (__re_flatten (Term.Boolean true)
          (__eo_ite carry rFlat (__str_membership_re first))) eps hNextRNe
    have hIteRNe :
        __eo_ite carry rFlat (__str_membership_re first) ≠ Term.Stuck :=
      StrInReConsumeInternal.re_flatten_tree_ne_stuck_of_ne_stuck_local
        (Term.Boolean true)
        (__eo_ite carry rFlat (__str_membership_re first)) hFlatNextRNe
    have hIteRTy :
        __smtx_typeof
            (__eo_to_smt
              (__eo_ite carry rFlat (__str_membership_re first))) =
          SmtType.RegLan :=
      StrInReConsumeInternal.smt_typeof_eo_ite_of_branches_local carry rFlat
        (__str_membership_re first) hRFlatTy hMemReTy hIteRNe
    have hNextRTy :
        __smtx_typeof (__eo_to_smt nextR) = SmtType.RegLan := by
      rcases StrInReConsumeInternal.str_re_consume_rflat_type_facts_local M hM
          (__eo_ite carry rFlat (__str_membership_re first)) hIteRTy
          (by simpa [nextR] using hNextRNe) with
        ⟨hTy, _hList, _hFlatNe, _hFlatList, _hFlatTy⟩
      simpa [nextR] using hTy
    exact ⟨
      by simpa [sFlat, rFlat, first, eps, carry, nextS] using hNextSTy,
      by simpa [sFlat, rFlat, first, eps, carry, nextR] using hNextRTy⟩
  have hActionableFrontierInputBridgeProgress :
      (∀ (hNotMult :
          ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False),
        nonMultFirstFalseNative hNotMult) ∧
      (∀ r0
          (hR : r = Term.Apply (Term.UOp UserOp.re_mult) r0),
        multFirstFalseNative r0 hR) ∧
      (∀ (hSideNotFalse : side ≠ Term.Boolean false)
          (hNotMult :
            ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False),
        nonMultInputNativeEq hSideNotFalse hNotMult) ∧
      (∀ (hNotMult :
          ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False),
        nonMultSecondFalseInputNativeEq hNotMult) ∧
      (∀ r0
          (hR : r = Term.Apply (Term.UOp UserOp.re_mult) r0),
        multSecondFalseInputNativeEq r0 hR) ∧
      (∀ r0
          (_hR : r = Term.Apply (Term.UOp UserOp.re_mult) r0)
          (hSideNotFalse : side ≠ Term.Boolean false),
        multSecondStrNativeEq r0 hSideNotFalse) := by
    -- Corrected diagnosis (2026-07-02): a per-side single-reversal
    -- evaluator bridge (`eval rFlat ~ native_re_reverse rv`) is FALSE for
    -- opaque atoms (e.g. RegLan/String variables), which `__re_rev_comp`
    -- and `__eo_list_rev` leave unchanged.  The conjuncts below are instead
    -- derived from the "unrev" motives (see the block above
    -- `StrInReConsumeInternal.str_re_consume_rec_unrev_no_suffix_motive`): the unrev transforms
    -- of the reversed pair `(sFlat, rFlat)` recover original-orientation
    -- terms via the proven involutions, and the unrev transforms of the
    -- residual memberships of `first` are literally `(nextS, nextR)`.
    have hUnrevCore :
        ∀ rSrc : Term,
          __smtx_typeof (__eo_to_smt rSrc) = SmtType.RegLan ->
          __str_re_consume_rec
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_flatten (__eo_list_singleton_intro
                  (Term.UOp UserOp.str_concat) s)))
              (__re_rev_map_rev (__re_flatten (Term.Boolean true) rSrc)
                (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_flatten (__eo_list_singleton_intro
                  (Term.UOp UserOp.str_concat) s))) ≠ Term.Stuck ->
            __eo_list_rev (Term.UOp UserOp.str_concat)
                (__eo_list_rev (Term.UOp UserOp.str_concat)
                  (__str_flatten (__eo_list_singleton_intro
                    (Term.UOp UserOp.str_concat) s))) =
              __str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s) ∧
            __re_rev_map_rev
                (__re_rev_map_rev (__re_flatten (Term.Boolean true) rSrc)
                  (Term.Apply (Term.UOp UserOp.str_to_re)
                    (Term.String [])))
                (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
              __re_flatten (Term.Boolean true) rSrc ∧
            __smtx_typeof
                (__eo_to_smt
                  (__str_flatten (__eo_list_singleton_intro
                    (Term.UOp UserOp.str_concat) s))) =
              SmtType.Seq SmtType.Char ∧
            __smtx_typeof
                (__eo_to_smt (__re_flatten (Term.Boolean true) rSrc)) =
              SmtType.RegLan ∧
            __smtx_typeof
                (__eo_to_smt
                  (__eo_list_rev (Term.UOp UserOp.str_concat)
                    (__str_flatten (__eo_list_singleton_intro
                      (Term.UOp UserOp.str_concat) s)))) =
              SmtType.Seq SmtType.Char ∧
            __smtx_typeof
                (__eo_to_smt
                  (__re_rev_map_rev
                    (__re_flatten (Term.Boolean true) rSrc)
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String [])))) =
              SmtType.RegLan ∧
            __eo_is_list (Term.UOp UserOp.str_concat)
                (__str_flatten (__eo_list_singleton_intro
                  (Term.UOp UserOp.str_concat) s)) =
              Term.Boolean true ∧
            ∃ ss flatSs rvS flatRv,
              __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
              __smtx_model_eval M
                  (__eo_to_smt
                    (__str_flatten (__eo_list_singleton_intro
                      (Term.UOp UserOp.str_concat) s))) =
                SmtValue.Seq flatSs ∧
              native_unpack_string flatSs = native_unpack_string ss ∧
              native_string_valid (native_unpack_string ss) = true ∧
              __smtx_model_eval M (__eo_to_smt rSrc) =
                SmtValue.RegLan rvS ∧
              __smtx_model_eval M
                  (__eo_to_smt (__re_flatten (Term.Boolean true) rSrc)) =
                SmtValue.RegLan flatRv ∧
              (∀ str,
                native_str_in_re str flatRv =
                  native_str_in_re str rvS) := by
      intro rSrc hRSrcTy hFirstNe
      have hSFlatNe :
          __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s)) ≠ Term.Stuck := by
        intro hBad
        rw [hBad] at hFirstNe
        exact str_re_consume_rec_stuck_left_absurd _ _ _ rfl hFirstNe
      have hRFlatNe :
          __re_rev_map_rev (__re_flatten (Term.Boolean true) rSrc)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) ≠
            Term.Stuck := by
        intro hBad
        rw [hBad] at hFirstNe
        exact str_re_consume_rec_stuck_right_absurd _ _ _ hSFlatNe rfl
          hFirstNe
      have hFlatRNe :
          __re_flatten (Term.Boolean true) rSrc ≠ Term.Stuck :=
        StrInReConsumeInternal.re_rev_map_rev_arg_ne_stuck_of_ne_stuck_local _ _ hRFlatNe
      rcases StrInReConsumeInternal.str_re_consume_first_input_eval_context_local M hM s r side
          rSrc hEqTrans hRSrcTy
          (by simpa [__str_nary_intro] using hSFlatNe) hRFlatNe with
        ⟨ss, flatSs, _sFlatSs, rvS, _flatRv0, _rFlatRv, hSEval,
          hFlatSrcEval, _hSFlatEval, hREvalS, _hFlatREval0, _hRFlatEval,
          hFlatSrcTy, hSFlatTyC, _hFlatRTy0, hRFlatTyC, hFlatSrcList,
          _hSFlatList, _hFlatRList, _hRFlatList, hFlatRel⟩
      rcases re_flatten_false_eval_rel M hM (Term.Boolean true) rSrc rvS
          hRSrcTy hREvalS hFlatRNe with
        ⟨flatRv, hFlatREval, hFlatRTy, hFlatRRel⟩
      have hInvS :
          __eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_flatten (__eo_list_singleton_intro
                  (Term.UOp UserOp.str_concat) s))) =
            __str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s) :=
        eo_list_rev_list_rev_str_concat_eq_of_list_true _
          (by simpa [__str_nary_intro] using hFlatSrcList) hSFlatNe
      have hInvR :
          __re_rev_map_rev
              (__re_rev_map_rev (__re_flatten (Term.Boolean true) rSrc)
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (Term.String [])))
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) =
            __re_flatten (Term.Boolean true) rSrc := by
        have hInv :=
          StrInReConsumeInternal.re_flatten_true_action_double_eps_local rSrc hFlatRNe
        rw [show StrInReConsumeInternal.re_empty_string_re_consume_local =
          Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
          from rfl] at hInv
        exact hInv
      have hSsValTy :
          __smtx_typeof_value (SmtValue.Seq ss) =
            SmtType.Seq SmtType.Char := by
        have h := smt_model_eval_preserves_type_of_non_none M hM
          (__eo_to_smt s) (by
            unfold term_has_non_none_type
            rw [_hSTy]
            simp)
        rw [hSEval, _hSTy] at h
        exact h
      have hWValid :
          native_string_valid (native_unpack_string ss) = true :=
        native_unpack_string_valid_of_typeof_seq_char hSsValTy
      have hUnpackEq :
          native_unpack_string flatSs = native_unpack_string ss :=
        StrInReConsumeInternal.consume_native_unpack_string_eq_of_seq_rel hFlatRel
      exact ⟨hInvS, hInvR,
        by simpa [__str_nary_intro] using hFlatSrcTy,
        hFlatRTy,
        by simpa [__str_nary_intro] using hSFlatTyC,
        hRFlatTyC,
        by simpa [__str_nary_intro] using hFlatSrcList,
        ss, flatSs, rvS, flatRv,
        hSEval,
        by simpa [__str_nary_intro] using hFlatSrcEval,
        hUnpackEq, hWValid, hREvalS, hFlatREval,
        fun str =>
          StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local hFlatRRel str⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- nonMultFirstFalseNative
      intro hNotMult
      simp only [nonMultFirstFalseNative]
      intro hFirstFalse ss1 rv1 hSEval1 hREval1
      have hFirstNe :
          __str_re_consume_rec
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_flatten (__eo_list_singleton_intro
                  (Term.UOp UserOp.str_concat) s)))
              (__re_rev_map_rev (__re_flatten (Term.Boolean true) r)
                (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_flatten (__eo_list_singleton_intro
                  (Term.UOp UserOp.str_concat) s))) ≠ Term.Stuck := by
        rw [hFirstFalse]
        intro h
        cases h
      rcases hUnrevCore r _hRTy hFirstNe with
        ⟨hInvS, hInvR, hFlatSrcTy, hFlatRTy, hSFlatTy, hRFlatTy,
          _hFlatSrcList, ss0, flatSs,
          rvS0, flatRv, hSEval0, hFlatSrcEval, hUnpackEq, hWValid,
          hREval0, hFlatREval, hTransfer⟩
      injection hSEval0.symm.trans hSEval1 with hSsEq
      subst hSsEq
      injection hREval0.symm.trans hREval1 with hRvEq
      subst hRvEq
      have hMotive :=
        (StrInReConsumeInternal.str_re_consume_rec_unrev_no_suffix_local M hM _ _ _
          (Term.Boolean false)
          hSFlatTy hRFlatTy
          hFirstFalse.symm rfl
          (StrInReConsumeInternal.consume_wf_chain_rev_flatten_local _) flatSs
          (by
            simp only [StrInReConsumeInternal.consume_unrev_str_local]
            rw [hInvS]
            exact hFlatSrcEval)).1 flatRv
          (by
            simp only [StrInReConsumeInternal.consume_unrev_re_local]
            rw [hInvR]
            exact hFlatREval)
      rcases hMotive with ⟨_hWNe, hNoSuffix⟩
      have hFlatFalse :
          native_str_in_re (native_unpack_string flatSs) flatRv =
            false :=
        hNoSuffix [] (native_unpack_string flatSs) (by simp)
      rw [hUnpackEq] at hFlatFalse
      rw [← hTransfer (native_unpack_string ss0)]
      exact hFlatFalse
    · -- multFirstFalseNative
      intro r0 hR
      simp only [multFirstFalseNative]
      intro hFirstFalse ss1 rv1 hSEval1 hREval1
      have hR0Ty : __smtx_typeof (__eo_to_smt r0) = SmtType.RegLan :=
        RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_mult_arg_of_reglan
          r0 (by
            simp only [ReUnfoldNegSupport.mkReMult]
            rw [← hR]
            exact _hRTy)
      have hFirstNe :
          __str_re_consume_rec
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_flatten (__eo_list_singleton_intro
                  (Term.UOp UserOp.str_concat) s)))
              (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
                (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_flatten (__eo_list_singleton_intro
                  (Term.UOp UserOp.str_concat) s))) ≠ Term.Stuck := by
        rw [hFirstFalse]
        intro h
        cases h
      rcases hUnrevCore r0 hR0Ty hFirstNe with
        ⟨hInvS, hInvR, hFlatSrcTy, hFlatRTy, hSFlatTy, hRFlatTy,
          _hFlatSrcList, ss0, flatSs,
          rvS0, flatRv, hSEval0, hFlatSrcEval, hUnpackEq, hWValid,
          hREval0, hFlatREval, hTransfer⟩
      injection hSEval0.symm.trans hSEval1 with hSsEq
      subst hSsEq
      have hMultEval :
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r0)) =
            SmtValue.RegLan (native_re_mult rvS0) := by
        change __smtx_model_eval M
            (SmtTerm.re_mult (__eo_to_smt r0)) = _
        simp [__smtx_model_eval, __smtx_model_eval_re_mult, hREval0]
      injection hMultEval.symm.trans hREval1 with hRvEq
      subst hRvEq
      have hMotive :=
        (StrInReConsumeInternal.str_re_consume_rec_unrev_no_suffix_local M hM _ _ _
          (Term.Boolean false)
          hSFlatTy hRFlatTy
          hFirstFalse.symm rfl
          (StrInReConsumeInternal.consume_wf_chain_rev_flatten_local _) flatSs
          (by
            simp only [StrInReConsumeInternal.consume_unrev_str_local]
            rw [hInvS]
            exact hFlatSrcEval)).1 flatRv
          (by
            simp only [StrInReConsumeInternal.consume_unrev_re_local]
            rw [hInvR]
            exact hFlatREval)
      rcases hMotive with ⟨hWNe, hNoSuffix⟩
      rw [hUnpackEq] at hWNe
      apply StrInReConsumeInternal.native_str_in_re_star_false_of_no_suffix_local _ _ hWNe
      intro pre suf hApp
      have hSufFail :
          native_str_in_re suf flatRv = false :=
        hNoSuffix pre suf (by rw [hApp, hUnpackEq])
      rw [← hTransfer suf]
      exact hSufFail
    · -- nonMultInputNativeEq
      intro hSideNotFalse hNotMult
      simp only [nonMultInputNativeEq]
      intro ss1 rv1 nextSs nextRv hSEval1 hREval1 hNextSEval hNextREval
      rcases hNonMultSecondInputTypeProgress hSideNotFalse hNotMult with
        ⟨hNextSTy, _hNextRTy⟩
      have hNextSsTy :
          __smtx_typeof_value (SmtValue.Seq nextSs) =
            SmtType.Seq SmtType.Char := by
        rw [← hNextSEval]
        exact
          (smt_model_eval_preserves_type_of_non_none M hM _ (by
            unfold term_has_non_none_type
            rw [hNextSTy]
            simp)).trans hNextSTy
      rcases hNonMultFinalNotFalseProgress hSideNotFalse hNotMult with
        ⟨hFirstNotFalse, _hSecondNotFalse, hFirstNe, _hSecondNe⟩
      rcases hNonMultSecondInputNeProgress hSideNotFalse hNotMult with
        ⟨_hMemStrNe, hMemReNe, _hNextSNe, _hNextRNe, _hSecondNe2⟩
      rcases hNonMultCarryProgress hSideNotFalse hNotMult with
        ⟨hCarryFalse, _, _, _⟩
      rcases hUnrevCore r _hRTy hFirstNe with
        ⟨hInvS, hInvR, hFlatSrcTy, hFlatRTy, hSFlatTy, hRFlatTy,
          _hFlatSrcList, ss0, flatSs,
          rvS0, flatRv, hSEval0, hFlatSrcEval, hUnpackEq, hWValid,
          hREval0, hFlatREval, hTransfer⟩
      injection hSEval0.symm.trans hSEval1 with hSsEq
      subst hSsEq
      injection hREval0.symm.trans hREval1 with hRvEq
      subst hRvEq
      have hFlatSsTy :
          __smtx_typeof_value (SmtValue.Seq flatSs) =
            SmtType.Seq SmtType.Char := by
        rw [← hFlatSrcEval]
        exact
          (smt_model_eval_preserves_type_of_non_none M hM _ (by
            unfold term_has_non_none_type
            rw [hFlatSrcTy]
            simp)).trans hFlatSrcTy
      rw [hCarryFalse] at hNextSEval hNextREval
      simp only [eo_ite_false] at hNextSEval hNextREval
      have hRel :=
        StrInReConsumeInternal.str_re_consume_rec_unrev_model_rel_local M hM _ _ _ _
          hSFlatTy hRFlatTy
          rfl hFirstNe hFirstNotFalse hMemReNe
          (by
            simp only [StrInReConsumeInternal.consume_unrev_str_local]
            exact eo_list_rev_list_rev_ne_stuck_of_ne_stuck _ _ (by
              intro hBad
              rw [hBad] at hFirstNe
              exact str_re_consume_rec_stuck_left_absurd _ _ _ rfl
                hFirstNe))
          ⟨flatRv, by
            simp only [StrInReConsumeInternal.consume_unrev_re_local]
            rw [hInvR]
            exact hFlatREval⟩
          (StrInReConsumeInternal.consume_wf_chain_rev_flatten_local _)
      have hLhsEval :
          __smtx_model_eval M
              (__eo_to_smt
                (StrInReConsumeInternal.consume_unrev_pair_local
                  (__eo_list_rev (Term.UOp UserOp.str_concat)
                    (__str_flatten (__eo_list_singleton_intro
                      (Term.UOp UserOp.str_concat) s)))
                  (__re_rev_map_rev
                    (__re_flatten (Term.Boolean true) r)
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String []))))) =
            SmtValue.Boolean
              (native_str_in_re (native_unpack_string flatSs) flatRv) := by
        simp only [StrInReConsumeInternal.consume_unrev_pair_local, StrInReConsumeInternal.consume_unrev_str_local,
          StrInReConsumeInternal.consume_unrev_re_local]
        rw [hInvS, hInvR]
        change __smtx_model_eval M
            (SmtTerm.str_in_re
              (__eo_to_smt
                (__str_flatten (__eo_list_singleton_intro
                  (Term.UOp UserOp.str_concat) s)))
                (__eo_to_smt (__re_flatten (Term.Boolean true) r))) = _
        simp [__smtx_model_eval, __smtx_model_eval_str_in_re,
          hFlatSrcEval, hFlatREval,
          model_str_in_re_unpack_eq_string_of_value_type flatSs flatRv
            hFlatSsTy]
      rw [hLhsEval] at hRel
      have hRhsBool := StrInReConsumeInternal.consume_smt_value_rel_boolean_inv_local hRel
      rcases StrInReConsumeInternal.consume_eval_unrev_pair_inv_local M _ _ _ hRhsBool with
        ⟨_msv, mRv, _hMSEval, hMEval, _hBEq⟩
      simp only [StrInReConsumeInternal.consume_unrev_re_local] at hMEval
      have hSFlatNe2 :
          __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__eo_list_singleton_intro
                (Term.UOp UserOp.str_concat) s)) ≠ Term.Stuck := by
        intro hBad
        rw [hBad] at hFirstNe
        exact str_re_consume_rec_stuck_left_absurd _ _ _ rfl hFirstNe
      have hRFlatNe2 :
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
              (Term.Apply (Term.UOp UserOp.str_to_re)
                (Term.String [])) ≠ Term.Stuck := by
        intro hBad
        rw [hBad] at hFirstNe
        exact str_re_consume_rec_stuck_right_absurd _ _ _ hSFlatNe2 rfl
          hFirstNe
      have hMRel := StrInReConsumeInternal.eval_first_residual_unrev_rel_local M s r
        hRFlatNe2 nextRv mRv hNextREval hMEval
      have hRhsEval :
          __smtx_model_eval M
              (__eo_to_smt
                (StrInReConsumeInternal.consume_unrev_pair_local
                  (__str_membership_str
                    (__str_re_consume_rec
                      (__eo_list_rev (Term.UOp UserOp.str_concat)
                        (__str_flatten (__eo_list_singleton_intro
                          (Term.UOp UserOp.str_concat) s)))
                      (__re_rev_map_rev
                        (__re_flatten (Term.Boolean true) r)
                        (Term.Apply (Term.UOp UserOp.str_to_re)
                          (Term.String [])))
                      (__eo_list_rev (Term.UOp UserOp.str_concat)
                        (__str_flatten (__eo_list_singleton_intro
                          (Term.UOp UserOp.str_concat) s)))))
                  (__str_membership_re
                    (__str_re_consume_rec
                      (__eo_list_rev (Term.UOp UserOp.str_concat)
                        (__str_flatten (__eo_list_singleton_intro
                          (Term.UOp UserOp.str_concat) s)))
                      (__re_rev_map_rev
                        (__re_flatten (Term.Boolean true) r)
                        (Term.Apply (Term.UOp UserOp.str_to_re)
                          (Term.String [])))
                      (__eo_list_rev (Term.UOp UserOp.str_concat)
                        (__str_flatten (__eo_list_singleton_intro
                          (Term.UOp UserOp.str_concat) s))))))) =
            SmtValue.Boolean
              (native_str_in_re (native_unpack_string nextSs) mRv) := by
        simp only [StrInReConsumeInternal.consume_unrev_pair_local, StrInReConsumeInternal.consume_unrev_str_local,
          StrInReConsumeInternal.consume_unrev_re_local]
        change __smtx_model_eval M
            (SmtTerm.str_in_re _ _) = _
        simp [__smtx_model_eval, __smtx_model_eval_str_in_re,
          hNextSEval, hMEval,
          model_str_in_re_unpack_eq_string_of_value_type nextSs mRv
            hNextSsTy]
      rw [hRhsEval] at hRel
      have hBoolEq :=
        smt_value_rel_boolean_eq_consume_local hRel
      rw [hUnpackEq] at hBoolEq
      rw [← StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local hMRel
        (native_unpack_string nextSs)] at hBoolEq
      rw [← hTransfer (native_unpack_string ss0)]
      exact hBoolEq
    · -- nonMultSecondFalseInputNativeEq
      intro hNotMult
      simp only [nonMultSecondFalseInputNativeEq]
      intro hFirstNotFalse hSecondFalse ss1 rv1 nextSs nextRv hSEval1
        hREval1 hNextSEval hNextREval
      rcases hNonMultSecondInputTypeOfSecondFalseProgress hNotMult
          hSecondFalse with
        ⟨hNextSTy, _hNextRTy⟩
      have hNextSsTy :
          __smtx_typeof_value (SmtValue.Seq nextSs) =
            SmtType.Seq SmtType.Char := by
        rw [← hNextSEval]
        exact
          (smt_model_eval_preserves_type_of_non_none M hM _ (by
            unfold term_has_non_none_type
            rw [hNextSTy]
            simp)).trans hNextSTy
      have hNextSNe :=
        StrInReConsumeInternal.str_re_consume_rec_false_left_ne_stuck_consume_local _ _ _
          hSecondFalse
      have hIteNe := eo_list_rev_arg_ne_stuck_of_ne_stuck
        (Term.UOp UserOp.str_concat) _ hNextSNe
      rcases eo_ite_cases_of_ne_stuck _ _ _ hIteNe with
        hCarryTrue | hCarryFalse
      · exact absurd hCarryTrue
          (StrInReConsumeInternal.eo_and_false_left_ne_true_consume_local _)
      · rcases StrInReConsumeInternal.eo_and_boolean_arg_boolean_consume_local _ _ _
            hCarryFalse with ⟨d, hNotBool⟩
        rcases StrInReConsumeInternal.eo_not_boolean_arg_boolean_consume_local _ _ hNotBool with
          ⟨c, hEqBool⟩
        rcases StrInReConsumeInternal.eo_eq_boolean_args_ne_stuck_consume_local _ _ _ hEqBool with
          ⟨hMemReNe, _⟩
        have hFirstNe :=
          StrInReConsumeInternal.str_membership_re_ne_stuck_imp_ne_stuck_consume_local _ hMemReNe
        rcases hUnrevCore r _hRTy hFirstNe with
          ⟨hInvS, hInvR, hFlatSrcTy, hFlatRTy, hSFlatTy, hRFlatTy,
          _hFlatSrcList, ss0, flatSs,
            rvS0, flatRv, hSEval0, hFlatSrcEval, hUnpackEq, hWValid,
            hREval0, hFlatREval, hTransfer⟩
        injection hSEval0.symm.trans hSEval1 with hSsEq
        subst hSsEq
        injection hREval0.symm.trans hREval1 with hRvEq
        subst hRvEq
        have hFlatSsTy :
            __smtx_typeof_value (SmtValue.Seq flatSs) =
              SmtType.Seq SmtType.Char := by
          rw [← hFlatSrcEval]
          exact
            (smt_model_eval_preserves_type_of_non_none M hM _ (by
              unfold term_has_non_none_type
              rw [hFlatSrcTy]
              simp)).trans hFlatSrcTy
        rw [hCarryFalse] at hNextSEval hNextREval
        simp only [eo_ite_false] at hNextSEval hNextREval
        have hRel :=
          StrInReConsumeInternal.str_re_consume_rec_unrev_model_rel_local M hM _ _ _ _
            hSFlatTy hRFlatTy
            rfl hFirstNe hFirstNotFalse hMemReNe
            (by
              simp only [StrInReConsumeInternal.consume_unrev_str_local]
              exact eo_list_rev_list_rev_ne_stuck_of_ne_stuck _ _ (by
                intro hBad
                rw [hBad] at hFirstNe
                exact str_re_consume_rec_stuck_left_absurd _ _ _ rfl
                  hFirstNe))
            ⟨flatRv, by
              simp only [StrInReConsumeInternal.consume_unrev_re_local]
              rw [hInvR]
              exact hFlatREval⟩
            (StrInReConsumeInternal.consume_wf_chain_rev_flatten_local _)
        have hLhsEval :
            __smtx_model_eval M
                (__eo_to_smt
                  (StrInReConsumeInternal.consume_unrev_pair_local
                    (__eo_list_rev (Term.UOp UserOp.str_concat)
                      (__str_flatten (__eo_list_singleton_intro
                        (Term.UOp UserOp.str_concat) s)))
                    (__re_rev_map_rev
                      (__re_flatten (Term.Boolean true) r)
                      (Term.Apply (Term.UOp UserOp.str_to_re)
                        (Term.String []))))) =
              SmtValue.Boolean
                (native_str_in_re (native_unpack_string flatSs)
                  flatRv) := by
          simp only [StrInReConsumeInternal.consume_unrev_pair_local, StrInReConsumeInternal.consume_unrev_str_local,
            StrInReConsumeInternal.consume_unrev_re_local]
          rw [hInvS, hInvR]
          change __smtx_model_eval M
              (SmtTerm.str_in_re
                (__eo_to_smt
                  (__str_flatten (__eo_list_singleton_intro
                    (Term.UOp UserOp.str_concat) s)))
                  (__eo_to_smt (__re_flatten (Term.Boolean true) r))) = _
          simp [__smtx_model_eval, __smtx_model_eval_str_in_re,
            hFlatSrcEval, hFlatREval,
            model_str_in_re_unpack_eq_string_of_value_type flatSs flatRv
              hFlatSsTy]
        rw [hLhsEval] at hRel
        have hRhsBool := StrInReConsumeInternal.consume_smt_value_rel_boolean_inv_local hRel
        rcases StrInReConsumeInternal.consume_eval_unrev_pair_inv_local M _ _ _ hRhsBool with
          ⟨_msv, mRv, _hMSEval, hMEval, _hBEq⟩
        simp only [StrInReConsumeInternal.consume_unrev_re_local] at hMEval
        have hSFlatNe2 :
            __eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_flatten (__eo_list_singleton_intro
                  (Term.UOp UserOp.str_concat) s)) ≠ Term.Stuck := by
          intro hBad
          rw [hBad] at hFirstNe
          exact str_re_consume_rec_stuck_left_absurd _ _ _ rfl hFirstNe
        have hRFlatNe2 :
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (Term.String [])) ≠ Term.Stuck := by
          intro hBad
          rw [hBad] at hFirstNe
          exact str_re_consume_rec_stuck_right_absurd _ _ _ hSFlatNe2 rfl
            hFirstNe
        have hMRel := StrInReConsumeInternal.eval_first_residual_unrev_rel_local M s r
          hRFlatNe2 nextRv mRv hNextREval hMEval
        have hRhsEval :
            __smtx_model_eval M
                (__eo_to_smt
                  (StrInReConsumeInternal.consume_unrev_pair_local
                    (__str_membership_str
                      (__str_re_consume_rec
                        (__eo_list_rev (Term.UOp UserOp.str_concat)
                          (__str_flatten (__eo_list_singleton_intro
                            (Term.UOp UserOp.str_concat) s)))
                        (__re_rev_map_rev
                          (__re_flatten (Term.Boolean true) r)
                          (Term.Apply (Term.UOp UserOp.str_to_re)
                            (Term.String [])))
                        (__eo_list_rev (Term.UOp UserOp.str_concat)
                          (__str_flatten (__eo_list_singleton_intro
                            (Term.UOp UserOp.str_concat) s)))))
                    (__str_membership_re
                      (__str_re_consume_rec
                        (__eo_list_rev (Term.UOp UserOp.str_concat)
                          (__str_flatten (__eo_list_singleton_intro
                            (Term.UOp UserOp.str_concat) s)))
                        (__re_rev_map_rev
                          (__re_flatten (Term.Boolean true) r)
                          (Term.Apply (Term.UOp UserOp.str_to_re)
                            (Term.String [])))
                        (__eo_list_rev (Term.UOp UserOp.str_concat)
                          (__str_flatten (__eo_list_singleton_intro
                            (Term.UOp UserOp.str_concat) s))))))) =
              SmtValue.Boolean
                (native_str_in_re (native_unpack_string nextSs)
                  mRv) := by
          simp only [StrInReConsumeInternal.consume_unrev_pair_local, StrInReConsumeInternal.consume_unrev_str_local,
            StrInReConsumeInternal.consume_unrev_re_local]
          change __smtx_model_eval M
              (SmtTerm.str_in_re _ _) = _
          simp [__smtx_model_eval, __smtx_model_eval_str_in_re,
            hNextSEval, hMEval,
            model_str_in_re_unpack_eq_string_of_value_type nextSs mRv
              hNextSsTy]
        rw [hRhsEval] at hRel
        have hBoolEq :=
          smt_value_rel_boolean_eq_consume_local hRel
        rw [hUnpackEq] at hBoolEq
        rw [← StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local hMRel
          (native_unpack_string nextSs)] at hBoolEq
        rw [← hTransfer (native_unpack_string ss0)]
        exact hBoolEq
    · -- multSecondFalseInputNativeEq
      intro r0 hR
      simp only [multSecondFalseInputNativeEq]
      intro hFirstNotFalse hSecondFalse ss1 rv1 nextSs nextRv hSEval1
        hREval1 hNextSEval hNextREval
      have hR0Ty : __smtx_typeof (__eo_to_smt r0) = SmtType.RegLan :=
        RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_mult_arg_of_reglan
          r0 (by
            simp only [ReUnfoldNegSupport.mkReMult]
            rw [← hR]
            exact _hRTy)
      by_cases hMemEps :
          __str_membership_re
              (__str_re_consume_rec
                (__eo_list_rev (Term.UOp UserOp.str_concat)
                  (__str_flatten (__eo_list_singleton_intro
                    (Term.UOp UserOp.str_concat) s)))
                (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
                  (Term.Apply (Term.UOp UserOp.str_to_re)
                    (Term.String [])))
                (__eo_list_rev (Term.UOp UserOp.str_concat)
                  (__str_flatten (__eo_list_singleton_intro
                    (Term.UOp UserOp.str_concat) s)))) =
            Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
      · -- carry is false, `nextR` is the eps atom, and `second = false`
        -- is impossible: the flat no-prefix motive at `(nextS, eps)`
        -- yields `ε ∉ {ε}`.
        exfalso
        rcases hMultSecondInputTypeOfSecondFalseProgress r0 hR
            hSecondFalse with
          ⟨hNextSTy, hNextRTy⟩
        rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM
            _ hNextSTy with
          ⟨nextSs2, hNextSEval2⟩
        rcases smt_model_eval_reglan_of_type M hM _ hNextRTy with
          ⟨nextRv2, hNextREval2⟩
        have hNoPrefix :=
          hRecNoPrefix _ _ _ _ hNextSTy hNextRTy rfl hSecondFalse
            nextSs2 nextRv2 hNextSEval2 hNextREval2
        have hNilFalse :
            native_str_in_re [] nextRv2 = false :=
          hNoPrefix [] (native_unpack_string nextSs2) (by simp)
        have hNextRTermEq :
            __re_rev_map_rev
                (__re_flatten (Term.Boolean true)
                  (__eo_ite
                    (__eo_and (Term.Boolean true)
                      (__eo_not
                        (__eo_eq
                          (__str_membership_re
                            (__str_re_consume_rec
                              (__eo_list_rev (Term.UOp UserOp.str_concat)
                                (__str_flatten (__eo_list_singleton_intro
                                  (Term.UOp UserOp.str_concat) s)))
                              (__re_rev_map_rev
                                (__re_flatten (Term.Boolean true) r0)
                                (Term.Apply (Term.UOp UserOp.str_to_re)
                                  (Term.String [])))
                              (__eo_list_rev (Term.UOp UserOp.str_concat)
                                (__str_flatten (__eo_list_singleton_intro
                                  (Term.UOp UserOp.str_concat) s)))))
                          (Term.Apply (Term.UOp UserOp.str_to_re)
                            (Term.String [])))))
                    (__re_rev_map_rev
                      (__re_flatten (Term.Boolean true) r0)
                      (Term.Apply (Term.UOp UserOp.str_to_re)
                        (Term.String [])))
                    (__str_membership_re
                      (__str_re_consume_rec
                        (__eo_list_rev (Term.UOp UserOp.str_concat)
                          (__str_flatten (__eo_list_singleton_intro
                            (Term.UOp UserOp.str_concat) s)))
                        (__re_rev_map_rev
                          (__re_flatten (Term.Boolean true) r0)
                          (Term.Apply (Term.UOp UserOp.str_to_re)
                            (Term.String [])))
                        (__eo_list_rev (Term.UOp UserOp.str_concat)
                          (__str_flatten (__eo_list_singleton_intro
                            (Term.UOp UserOp.str_concat) s)))))))
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (Term.String [])) =
              Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []) := by
          rw [hMemEps]
          simp [__eo_eq, __eo_not, __eo_and, native_teq,
            SmtEval.native_not, SmtEval.native_and, eo_ite_false,
            __re_flatten, __re_rev_map_rev]
        rw [hNextRTermEq] at hNextREval2
        have hEpsEval :
            __smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.UOp UserOp.str_to_re)
                    (Term.String []))) =
              SmtValue.RegLan (native_str_to_re []) := by
          change __smtx_model_eval M
              (SmtTerm.str_to_re (SmtTerm.String [])) = _
          simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
           ]
        injection hEpsEval.symm.trans hNextREval2 with hRvEq2
        rw [← hRvEq2] at hNilFalse
        rw [StrInReConsumeInternal.native_str_in_re_nil_str_to_re_nil_consume_local]
          at hNilFalse
        cases hNilFalse
      · -- carry is true: both sides evaluate to `false` (the flat
        -- no-prefix motive at the retried unreversed pair kills every
        -- prefix of the string value, and the star wrapper adds only
        -- the empty word, excluded by the nonemptiness motive).
        have hNextSNe :=
          StrInReConsumeInternal.str_re_consume_rec_false_left_ne_stuck_consume_local _ _ _
            hSecondFalse
        have hIteNe := eo_list_rev_arg_ne_stuck_of_ne_stuck
          (Term.UOp UserOp.str_concat) _ hNextSNe
        have hMemReNe :
            __str_membership_re
                (__str_re_consume_rec
                  (__eo_list_rev (Term.UOp UserOp.str_concat)
                    (__str_flatten (__eo_list_singleton_intro
                      (Term.UOp UserOp.str_concat) s)))
                  (__re_rev_map_rev
                    (__re_flatten (Term.Boolean true) r0)
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String [])))
                  (__eo_list_rev (Term.UOp UserOp.str_concat)
                    (__str_flatten (__eo_list_singleton_intro
                      (Term.UOp UserOp.str_concat) s)))) ≠
              Term.Stuck := by
          rcases eo_ite_cases_of_ne_stuck _ _ _ hIteNe with
            hCarry | hCarry <;>
          · rcases StrInReConsumeInternal.eo_and_boolean_arg_boolean_consume_local _ _ _
                hCarry with ⟨d, hNotBool⟩
            rcases StrInReConsumeInternal.eo_not_boolean_arg_boolean_consume_local _ _
                hNotBool with ⟨c, hEqBool⟩
            exact (StrInReConsumeInternal.eo_eq_boolean_args_ne_stuck_consume_local _ _ _
              hEqBool).1
        have hCarryTrue :
            __eo_and (Term.Boolean true)
                (__eo_not
                  (__eo_eq
                    (__str_membership_re
                      (__str_re_consume_rec
                        (__eo_list_rev (Term.UOp UserOp.str_concat)
                          (__str_flatten (__eo_list_singleton_intro
                            (Term.UOp UserOp.str_concat) s)))
                        (__re_rev_map_rev
                          (__re_flatten (Term.Boolean true) r0)
                          (Term.Apply (Term.UOp UserOp.str_to_re)
                            (Term.String [])))
                        (__eo_list_rev (Term.UOp UserOp.str_concat)
                          (__str_flatten (__eo_list_singleton_intro
                            (Term.UOp UserOp.str_concat) s)))))
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String []))))
              = Term.Boolean true := by
          rw [StrInReConsumeInternal.eo_eq_eq_of_ne_stuck_consume_local _ _ hMemReNe (by
            intro h
            cases h)]
          rw [show native_teq
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
              (__str_membership_re
                (__str_re_consume_rec
                  (__eo_list_rev (Term.UOp UserOp.str_concat)
                    (__str_flatten (__eo_list_singleton_intro
                      (Term.UOp UserOp.str_concat) s)))
                  (__re_rev_map_rev
                    (__re_flatten (Term.Boolean true) r0)
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String [])))
                  (__eo_list_rev (Term.UOp UserOp.str_concat)
                    (__str_flatten (__eo_list_singleton_intro
                      (Term.UOp UserOp.str_concat) s))))) = false from by
            simp [native_teq]
            intro hBad
            exact hMemEps hBad.symm]
          simp [__eo_not, __eo_and, SmtEval.native_not,
            SmtEval.native_and]
        have hFirstNe :=
          StrInReConsumeInternal.str_membership_re_ne_stuck_imp_ne_stuck_consume_local _ hMemReNe
        rcases hUnrevCore r0 hR0Ty hFirstNe with
          ⟨hInvS, hInvR, hFlatSrcTy, hFlatRTy, hSFlatTy, hRFlatTy,
          _hFlatSrcList, ss0, flatSs,
            rvS0, flatRv, hSEval0, hFlatSrcEval, hUnpackEq, hWValid,
            hREval0, hFlatREval, hTransfer⟩
        injection hSEval0.symm.trans hSEval1 with hSsEq
        subst hSsEq
        have hMultEval :
            __smtx_model_eval M
                (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r0)) =
              SmtValue.RegLan (native_re_mult rvS0) := by
          change __smtx_model_eval M
              (SmtTerm.re_mult (__eo_to_smt r0)) = _
          simp [__smtx_model_eval, __smtx_model_eval_re_mult, hREval0]
        injection hMultEval.symm.trans hREval1 with hRvEq
        subst hRvEq
        -- flat no-prefix and nonemptiness at the (original) second pair
        rcases hMultSecondInputTypeOfSecondFalseProgress r0 hR
            hSecondFalse with
          ⟨hNextSTy, hNextRTy⟩
        have hNoPrefix :=
          hRecNoPrefix _ _ _ _ hNextSTy hNextRTy rfl hSecondFalse
            nextSs nextRv hNextSEval hNextREval
        have hNonempty :=
          StrInReConsumeInternal.str_re_consume_rec_false_nonempty_local M hM _ _ _ _
            hNextSTy hNextRTy rfl hSecondFalse nextSs hNextSEval
        -- identify the second-pass string value with the original word
        rw [hCarryTrue] at hNextSEval hNextREval
        simp only [eo_ite_true] at hNextSEval hNextREval
        rw [hInvS] at hNextSEval
        injection hFlatSrcEval.symm.trans hNextSEval with hNextSsEq
        subst hNextSsEq
        -- relate the second-pass regex value to the flattened body value
        have hSFlatNe' :
            __eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_flatten (__eo_list_singleton_intro
                  (Term.UOp UserOp.str_concat) s)) ≠ Term.Stuck := by
          intro hBad
          rw [hBad] at hFirstNe
          exact str_re_consume_rec_stuck_left_absurd _ _ _ rfl hFirstNe
        have hRFlatNe' :
            __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (Term.String [])) ≠ Term.Stuck := by
          intro hBad
          rw [hBad] at hFirstNe
          exact str_re_consume_rec_stuck_right_absurd _ _ _ hSFlatNe' rfl
            hFirstNe
        have hNRel := StrInReConsumeInternal.eval_rev_flatten_rev_rflat_rel_local M r0
          hRFlatNe' nextRv flatRv hNextREval hFlatREval
        have hRhsFalse :
            native_str_in_re (native_unpack_string flatSs) nextRv =
              false :=
          hNoPrefix (native_unpack_string flatSs) [] (by simp)
        rw [hRhsFalse]
        rw [hUnpackEq] at hNonempty
        apply StrInReConsumeInternal.native_str_in_re_star_false_of_no_prefix_consume_local _ _
          hNonempty
        intro pre suf hApp
        have hPreFail : native_str_in_re pre nextRv = false :=
          hNoPrefix pre suf (by rw [hApp, hUnpackEq])
        rw [← hTransfer pre]
        rw [← StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_consume_local hNRel
          pre]
        exact hPreFail
    · -- multSecondStrNativeEq: the star-level trim equality
      -- `str_in_re w (star r0v) = str_in_re parts (star r0v)`.
      -- Carry-false subcase: the first pass fully consumed one body
      -- copy from the reversed end; needs the unrev LEFT-continuation
      -- residual motive (`StrInReConsumeInternal.str_re_consume_rec_unrev_residual_local`,
      -- with `q := re_mult r0` and a right-unrolling of star) plus a
      -- suffix-decomposition strengthening.  Carry-true subcase: the
      -- second pass runs on the unreversed pair; needs the flat
      -- residual motive with `q := re_mult r0` and a left-unrolling of
      -- star, plus an eps-shape inversion for `memb_re second` from the
      -- final `requires` guard.
      intro r0 hR hSideNotFalse
      simp only [multSecondStrNativeEq]
      intro ss rv partsSs hSEval hMultEval hPartsEval hElimEps
      have hR0Ty : __smtx_typeof (__eo_to_smt r0) = SmtType.RegLan :=
        RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_mult_arg_of_reglan
          r0 (by
            simp only [ReUnfoldNegSupport.mkReMult]
            rw [← hR]
            exact _hRTy)
      rcases hMultSecondInputTypeProgress r0 hR hSideNotFalse with
        ⟨hNextSTy, hNextRTy⟩
      rcases smt_eval_seq_char_of_smt_type_seq_char_consume_local M hM
          _ hNextSTy with ⟨nextSs, hNextSEval⟩
      rcases smt_model_eval_reglan_of_type M hM _ hNextRTy with
        ⟨nextRv, hNextREval⟩
      rcases hRecResidual _ _ _ _ hNextSTy hNextRTy rfl hElimEps with
        ⟨hPartsTy2, hTransport⟩
      have hStar :=
        hTransport (Term.Apply (Term.UOp UserOp.re_mult) r0) nextSs
          nextRv partsSs rv hNextSEval hNextREval hPartsEval hMultEval
      have hAllInst :=
        hTransport (Term.UOp UserOp.re_all) nextSs nextRv partsSs
          native_re_all hNextSEval hNextREval hPartsEval
          (StrInReConsumeInternal.consume_eval_re_all_local M)
      have hPartsValid :=
        StrInReConsumeInternal.consume_seq_valid_of_eval_typeof_local M hM _ partsSs hPartsEval
          hPartsTy2
      have hAllRhsTrue :
          native_str_in_re (native_unpack_string partsSs)
            native_re_all = true :=
        native_str_in_re_re_all _ hPartsValid
      rw [hAllRhsTrue] at hAllInst
      rw [← hStar]
      rcases hMultSecondInputNeProgress r0 hR hSideNotFalse with
        ⟨hMemReFirstNe, _hCarryNe, _hNextSNe, _hNextRNe, _hSecondNe⟩
      have hFirstNe : (__str_re_consume_rec (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))) (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s)))) ≠ Term.Stuck :=
        StrInReConsumeInternal.str_membership_re_ne_stuck_imp_ne_stuck_consume_local _
          hMemReFirstNe
      have hSFlatNe : (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))) ≠ Term.Stuck := by
        intro hBad
        rw [hBad] at hFirstNe
        exact str_re_consume_rec_stuck_left_absurd _ _ _ rfl hFirstNe
      rcases hUnrevCore r0 hR0Ty hFirstNe with
        ⟨hInvS, hInvR, _hFlatSrcTy, _hFlatRTy, hSFlatTy, hRFlatTy,
          _hFlatSrcList, ss0, flatSs, rvS0, flatRv, hSEval0,
          hFlatSrcEval, hUnpackEq, hWValid, hREval0, hFlatREval,
          hTransfer⟩
      injection hSEval0.symm.trans hSEval with hSsEq
      subst hSsEq
      have hMultEvalStar :
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r0)) =
            SmtValue.RegLan (native_re_mult rvS0) := by
        change __smtx_model_eval M
            (SmtTerm.re_mult (__eo_to_smt r0)) = _
        simp [__smtx_model_eval, __smtx_model_eval_re_mult, hREval0]
      injection hMultEval.symm.trans hMultEvalStar with hRvEq
      subst hRvEq
      by_cases hMemEps :
          __str_membership_re (__str_re_consume_rec (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))) (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s)))) = (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
      · -- carry false: nextR is the eps atom, nextS the unreversed
        -- first-pass residual
        have hNextRTermEq : (__re_rev_map_rev (__re_flatten (Term.Boolean true) (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))) (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))))) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))) (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) (__str_membership_re (__str_re_consume_rec (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))) (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))))))) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) = (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) := by
          rw [hMemEps]
          simp [__eo_eq, __eo_not, __eo_and, native_teq,
            SmtEval.native_not, SmtEval.native_and, eo_ite_false,
            __re_flatten, __re_rev_map_rev]
        have hNextSTermEq : (__eo_list_rev (Term.UOp UserOp.str_concat) (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))) (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))))) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))) (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))) (__str_membership_str (__str_re_consume_rec (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))) (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))))))) =
            __eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_membership_str (__str_re_consume_rec (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))) (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))))) := by
          rw [hMemEps]
          simp [__eo_eq, __eo_not, __eo_and, native_teq,
            SmtEval.native_not, SmtEval.native_and, eo_ite_false]
        rw [hNextRTermEq] at hNextREval
        have hNextRvEps : nextRv = native_str_to_re [] := by
          rw [StrInReConsumeInternal.consume_eval_eps_re_early_local M] at hNextREval
          injection hNextREval with hh
          exact hh.symm
        subst hNextRvEps
        rw [native_re_concat_left_empty_local]
        rw [hNextSTermEq] at hNextSEval
        have hMotive := StrInReConsumeInternal.str_re_consume_rec_unrev_residual_local M hM
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))) (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))) (__str_re_consume_rec (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))) (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))))
          hSFlatTy hRFlatTy rfl
          (by rw [hMemEps])
          (by
            simp only [StrInReConsumeInternal.consume_unrev_str_local]
            exact eo_list_rev_list_rev_ne_stuck_of_ne_stuck _ _
              hSFlatNe)
          (StrInReConsumeInternal.consume_wf_chain_rev_flatten_local _)
        rcases hMotive with ⟨_hTyRaw, _hTyU, hCore⟩
        rcases hCore flatSs nextSs
            (by
              simp only [StrInReConsumeInternal.consume_unrev_str_local]
              rw [hInvS]
              exact hFlatSrcEval)
            (by
              simp only [StrInReConsumeInternal.consume_unrev_str_local]
              exact hNextSEval)
          with ⟨hRvUPart, _hRevCompPart⟩
        rcases hRvUPart flatRv
            (by
              simp only [StrInReConsumeInternal.consume_unrev_re_local]
              rw [hInvR]
              exact hFlatREval)
          with ⟨⟨u, hDecomp, hUMem⟩, hQ⟩
        have hQStar := hQ (Term.Apply (Term.UOp UserOp.re_mult) r0)
          (native_re_mult rvS0) hMultEval
        rw [hUnpackEq] at hQStar hDecomp
        rw [← hQStar]
        exact StrInReConsumeInternal.consume_star_concat_right_eq_local _ _ _ rvS0 flatRv
          hWValid hTransfer hDecomp hUMem
      · -- carry true: nextS is the flat source, nextR the re-flattened
        -- reversal (bridge 1)
        have hNe' : (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) ≠ __str_membership_re (__str_re_consume_rec (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))) (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s)))) :=
          fun h => hMemEps h.symm
        have hCarryEq : (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))) (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))))) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))) = Term.Boolean true := by
          simp [__eo_eq, __eo_not, __eo_and, native_teq,
            SmtEval.native_not, SmtEval.native_and, hNe']
        have hNextSTermEq : (__eo_list_rev (Term.UOp UserOp.str_concat) (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))) (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))))) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))) (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))) (__str_membership_str (__str_re_consume_rec (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))) (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))))))) = (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s)) := by
          rw [hCarryEq, eo_ite_true]
          exact hInvS
        have hNextRTermEq : (__re_rev_map_rev (__re_flatten (Term.Boolean true) (__eo_ite (__eo_and (Term.Boolean true) (__eo_not (__eo_eq (__str_membership_re (__str_re_consume_rec (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))) (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))))) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))) (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) (__str_membership_re (__str_re_consume_rec (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))) (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_flatten (__eo_list_singleton_intro (Term.UOp UserOp.str_concat) s))))))) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) =
            __re_rev_map_rev
              (__re_flatten (Term.Boolean true) (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) := by
          rw [hCarryEq, eo_ite_true]
        rw [hNextSTermEq] at hNextSEval
        injection hNextSEval.symm.trans hFlatSrcEval with hNextSsEq
        subst hNextSsEq
        rw [hUnpackEq] at hAllInst ⊢
        rw [hNextRTermEq] at hNextREval
        have hRFlatNe2 : (__re_rev_map_rev (__re_flatten (Term.Boolean true) r0) (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) ≠ Term.Stuck := by
          intro hBad
          rw [hBad] at hFirstNe
          exact str_re_consume_rec_stuck_right_absurd _ _ _ hSFlatNe
            rfl hFirstNe
        have hNRel := StrInReConsumeInternal.eval_rev_flatten_rev_rflat_rel_local M r0
          hRFlatNe2 nextRv flatRv hNextREval hFlatREval
        have hPtwiseN : ∀ str,
            native_str_in_re str nextRv =
              native_str_in_re str rvS0 := by
          intro str
          rw [StrInReConsumeInternal.native_str_in_re_congr_of_reglan_rel_early_local hNRel
            str]
          exact hTransfer str
        exact StrInReConsumeInternal.consume_star_concat_left_eq_local _ rvS0 nextRv hWValid
          hPtwiseN
          (fun hWNil => by
            rw [hWNil] at hAllInst
            rcases StrInReConsumeInternal.consume_str_in_re_concat_elim_local [] nextRv
                native_re_all (by simp [native_string_valid])
                hAllInst with ⟨x1, x2, hApp, hX1, _⟩
            rcases List.append_eq_nil_iff.mp hApp with ⟨h1, _⟩
            subst h1
            exact hX1)
  rcases hActionableFrontierInputBridgeProgress with
    ⟨hNonMultFirstFalseNative, hMultFirstFalseNative,
      hNonMultInputNativeBridge, hNonMultSecondFalseInputNative,
      hMultSecondFalseInputNative, hMultSecondStrNativeFinal⟩
  have hNonMultSecondFalseNative :
      ∀ (hNotMult :
          ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False),
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean false)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextS :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first))
        let nextR :=
          __re_rev_map_rev
            (__re_flatten (Term.Boolean true)
              (__eo_ite carry rFlat (__str_membership_re first))) eps
        let second := __str_re_consume_rec nextS nextR nextS
        first ≠ Term.Boolean false ->
        second = Term.Boolean false ->
          ∀ ss rv,
            __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
            __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
              native_str_in_re (native_unpack_string ss) rv = false) := by
    intro hNotMult
    dsimp
    intro hFirstNotFalse hSecondFalse ss rv hSEval hREval
    rcases hNonMultSecondInputTypeOfSecondFalseProgress
        hNotMult hSecondFalse with
      ⟨hNextSTy, hNextRTy⟩
    exact hNonMultFalseOfSecondFalseInputNativeEqProgress hNotMult
      hSecondFalse hNextSTy hNextRTy
      (by
        simpa [nonMultSecondFalseInputNativeEq] using
          hNonMultSecondFalseInputNative hNotMult hFirstNotFalse
            hSecondFalse)
      ss rv hSEval hREval
  have hMultSecondFalseNative :
      ∀ r0
          (hR : r = Term.Apply (Term.UOp UserOp.re_mult) r0),
        (let sFlat :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__str_flatten (__eo_list_singleton_intro
              (Term.UOp UserOp.str_concat) s))
        let rFlat :=
          __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
        let first := __str_re_consume_rec sFlat rFlat sFlat
        let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
        let carry :=
          __eo_and (Term.Boolean true)
            (__eo_not (__eo_eq (__str_membership_re first) eps))
        let nextS :=
          __eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_ite carry sFlat (__str_membership_str first))
        let nextR :=
          __re_rev_map_rev
            (__re_flatten (Term.Boolean true)
              (__eo_ite carry rFlat (__str_membership_re first))) eps
        let second := __str_re_consume_rec nextS nextR nextS
        first ≠ Term.Boolean false ->
        second = Term.Boolean false ->
          ∀ ss rv,
            __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
            __smtx_model_eval M
                (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r0)) =
              SmtValue.RegLan rv ->
              native_str_in_re (native_unpack_string ss) rv = false) := by
    intro r0 hR
    dsimp
    intro hFirstNotFalse hSecondFalse ss rv hSEval hREval
    rcases hMultSecondInputTypeOfSecondFalseProgress
        r0 hR hSecondFalse with
      ⟨hNextSTy, hNextRTy⟩
    exact hMultFalseOfSecondFalseInputNativeEqProgress r0 hR
      hSecondFalse hNextSTy hNextRTy
      (by
        simpa [multSecondFalseInputNativeEq] using
          hMultSecondFalseInputNative r0 hR hFirstNotFalse
            hSecondFalse)
      ss rv hSEval hREval
  have hRemainingSemantic :
      (∀ (hSideFalse : side = Term.Boolean false)
          (hNotMult :
            ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False),
          ∀ ss rv,
            __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
            __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
              native_str_in_re (native_unpack_string ss) rv = false) ∧
      (∀ (hSideNotFalse : side ≠ Term.Boolean false)
          (hNotMult :
            ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False),
          nonMultInputNativeEq hSideNotFalse hNotMult) ∧
      (∀ r0,
          r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
          side = Term.Boolean false ->
          ∀ ss rv,
            __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
            __smtx_model_eval M
                (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r0)) =
              SmtValue.RegLan rv ->
              native_str_in_re (native_unpack_string ss) rv = false) ∧
      (∀ r0,
          r = Term.Apply (Term.UOp UserOp.re_mult) r0 ->
          ∀ hSideNotFalse : side ≠ Term.Boolean false,
            multSecondStrNativeEq r0 hSideNotFalse) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hSideFalse hNotMult ss rv hSEval hREval
      rcases hNonMultFalseProgress hSideFalse hNotMult with
        hFirstFalse | hSecondFalse
      · exact hNonMultFirstFalseNative hNotMult hFirstFalse
          ss rv hSEval hREval
      · by_cases hFirstFalse :
            (let sFlat :=
              __eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_flatten (__eo_list_singleton_intro
                  (Term.UOp UserOp.str_concat) s))
            let rFlat :=
              __re_rev_map_rev (__re_flatten (Term.Boolean true) r)
                (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
            let first := __str_re_consume_rec sFlat rFlat sFlat
            first = Term.Boolean false)
        · exact hNonMultFirstFalseNative hNotMult hFirstFalse
            ss rv hSEval hREval
        · exact hNonMultSecondFalseNative hNotMult hFirstFalse
            hSecondFalse ss rv hSEval hREval
    · intro hSideNotFalse hNotMult
      exact hNonMultInputNativeBridge hSideNotFalse hNotMult
    · intro r0 hR hSideFalse ss rv hSEval hREval
      rcases hMultFalseProgress r0 hR hSideFalse with
        hFirstFalse | hSecondFalse
      · exact hMultFirstFalseNative r0 hR hFirstFalse
          ss rv hSEval hREval
      · by_cases hFirstFalse :
            (let sFlat :=
              __eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_flatten (__eo_list_singleton_intro
                  (Term.UOp UserOp.str_concat) s))
            let rFlat :=
              __re_rev_map_rev (__re_flatten (Term.Boolean true) r0)
                (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))
            let first := __str_re_consume_rec sFlat rFlat sFlat
            first = Term.Boolean false)
        · exact hMultFirstFalseNative r0 hR hFirstFalse
            ss rv hSEval hREval
        · exact hMultSecondFalseNative r0 hR hFirstFalse
            hSecondFalse ss rv hSEval hREval
    · intro r0 hR hSideNotFalse
      exact hMultSecondStrNativeFinal r0 hR hSideNotFalse
  rcases hRemainingSemantic with
    ⟨hNonMultFalseNative, hNonMultInputNative, hMultFalseNative,
      hMultSecondStrNative⟩
  by_cases hRMult : ∃ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0
  · rcases hRMult with ⟨r0, hR⟩
    by_cases hSideFalse : side = Term.Boolean false
    · exact str_re_consume_model_rel_of_side_false M hM s r side hEqTrans
        hSideFalse (by
          intro ss rv hSEval hREval
          exact hMultFalseNative r0 hR hSideFalse ss rv hSEval
            (by simpa [hR] using hREval))
    · exact hMultFinalRelOfSecondStrNativeEqProgress r0 hR hSideFalse
        (by
          simpa [multSecondStrNativeEq] using
            hMultSecondStrNative r0 hR hSideFalse)
  · have hNotMult :
        ∀ r0, r = Term.Apply (Term.UOp UserOp.re_mult) r0 -> False := by
      intro r0 hR
      exact hRMult ⟨r0, hR⟩
    by_cases hSideFalse : side = Term.Boolean false
    · exact str_re_consume_model_rel_of_side_false M hM s r side hEqTrans
        hSideFalse (hNonMultFalseNative hSideFalse hNotMult)
    · exact hNonMultFinalRelOfInputNativeEqProgress hSideFalse hNotMult
        (by
          simpa [nonMultInputNativeEq] using
            hNonMultInputNative hSideFalse hNotMult)

private theorem StrInReConsumeInternal.str_in_re_consume_valid_properties
    (M : SmtModel) (hM : model_wf M)
    (s r b : Term)
    (hArgTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) b))
    (hProgNe :
      __eo_prog_str_in_re_consume
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) b) ≠
        Term.Stuck) :
    StepRuleProperties M []
      (__eo_prog_str_in_re_consume
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) b)) := by
  let strIn := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r
  let side := __str_re_consume s r
  let body := Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) b
  change __eo_requires side b body ≠ Term.Stuck at hProgNe
  have hSideEqB : side = b :=
    eo_requires_eq_of_ne_stuck side b body hProgNe
  have hReqResult : __eo_requires side b body = body :=
    eo_requires_result_eq_of_ne_stuck side b body hProgNe
  have hSideNe : side ≠ Term.Stuck :=
    eo_requires_left_ne_stuck_of_ne_stuck side b body hProgNe
  subst b
  change StepRuleProperties M [] (__eo_requires side side body)
  rw [hReqResult]
  have hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side) := by
    simpa [strIn, side, body] using hArgTrans
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side) := by
    unfold RuleProofs.eo_has_bool_type
    have hNN :
        term_has_non_none_type
          (SmtTerm.eq (__eo_to_smt strIn) (__eo_to_smt side)) := by
      unfold term_has_non_none_type
      change __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side)) ≠
        SmtType.None
      exact hEqTrans
    exact Smtm.eq_term_typeof_of_non_none hNN
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt strIn))
        (__smtx_model_eval M (__eo_to_smt side)) :=
    RuleProofs.str_re_consume_model_rel M hM s r side hEqTrans rfl hSideNe
  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
    (by simpa [strIn, side] using hEqBool)⟩
  intro _hPremises
  exact RuleProofs.eo_interprets_eq_of_rel M strIn side hEqBool hRel

end RuleProofs

public theorem cmd_step_str_in_re_consume_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_consume args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_in_re_consume args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_consume args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_in_re_consume args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hCmdTrans.1
              cases a1 with
              | Apply eqApp b =>
                  cases eqApp with
                  | Apply eqOp lhs =>
                      cases eqOp with
                      | UOp eqOpName =>
                          cases eqOpName with
                          | eq =>
                              cases lhs with
                              | Apply inApp r =>
                                  cases inApp with
                                  | Apply inOp str =>
                                      cases inOp with
                                      | UOp inOpName =>
                                          cases inOpName with
                                          | str_in_re =>
                                              have hProps :=
                                                RuleProofs.StrInReConsumeInternal.str_in_re_consume_valid_properties
                                                  M hM str r b (by
                                                    simpa using hA1Trans) (by
                                                    change
                                                      __eo_prog_str_in_re_consume
                                                        (Term.Apply
                                                          (Term.Apply (Term.UOp UserOp.eq)
                                                            (Term.Apply
                                                              (Term.Apply
                                                                (Term.UOp UserOp.str_in_re) str) r)) b) ≠
                                                        Term.Stuck at hProg
                                                    exact hProg)
                                              change StepRuleProperties M []
                                                (__eo_prog_str_in_re_consume
                                                  (Term.Apply
                                                    (Term.Apply (Term.UOp UserOp.eq)
                                                      (Term.Apply
                                                        (Term.Apply
                                                          (Term.UOp UserOp.str_in_re) str) r)) b))
                                              simpa [premiseTermList] using hProps
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
