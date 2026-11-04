module

public import Cpc.Proofs.RuleSupport.Evaluate.Prelude
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def EvaluateProofInternal.RunEvaluateTypeofGoal (t : Term) : Prop :=
  RuleProofs.eo_has_smt_translation t ->
  __run_evaluate t ≠ Term.Stuck ->
  __eo_typeof (__run_evaluate t) = __eo_typeof t

theorem EvaluateProofInternal.run_evaluate_typeof_apply_uop
    (op : UserOp) (x : Term)
    (recX : EvaluateProofInternal.RunEvaluateTypeofGoal x)
    (hRun :
      __run_evaluate (Term.Apply (Term.UOp op) x) ≠
        Term.Apply (Term.UOp op) x)
    (hTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp op) x))
    (hRunNe : __run_evaluate (Term.Apply (Term.UOp op) x) ≠ Term.Stuck) :
    __eo_typeof (__run_evaluate (Term.Apply (Term.UOp op) x)) =
      __eo_typeof (Term.Apply (Term.UOp op) x) := by
  cases op with
  | not =>
      have hNotBool :
          RuleProofs.eo_has_bool_type
            (Term.Apply (Term.UOp UserOp.not) x) :=
        EvaluateProofInternal.has_bool_type_not_of_has_translation x hTrans
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_not_arg x hNotBool
      have hXTrans : RuleProofs.eo_has_smt_translation x :=
        RuleProofs.eo_has_smt_translation_of_has_bool_type x hXBool
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hXEoBool : __eo_typeof x = Term.Bool :=
        TranslationProofs.eo_to_smt_type_eq_bool
          (hXMatch.symm.trans hXBool)
      have hRunNotNe : __eo_not (__run_evaluate x) ≠ Term.Stuck := by
        simpa [__run_evaluate] using hRunNe
      have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
        EvaluateProofInternal.eo_not_arg_ne_stuck hRunNotNe
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunXBool : __eo_typeof (__run_evaluate x) = Term.Bool :=
        hXPres.trans hXEoBool
      cases hRunX : __run_evaluate x <;>
        simp [__run_evaluate, hRunX, __eo_not] at hRunNotNe hRunXBool ⊢
      all_goals
        first
        | change Term.Bool = __eo_typeof_not (__eo_typeof x)
          rw [hXEoBool]
          rfl
        | cases hRunXBool
  | bvnot =>
      have hBvNotNN :
          term_has_non_none_type
            (SmtTerm.bvnot (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      rcases bv_unop_arg_of_non_none
          (op := SmtTerm.bvnot) (t := __eo_to_smt x)
          (by rw [__smtx_typeof.eq_39])
          hBvNotNN with
        ⟨w, hXTy⟩
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTy]
        simp
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hXEoBv :
          __eo_typeof x =
            Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w)) :=
        TranslationProofs.eo_to_smt_type_eq_bitvec
          (hXMatch.symm.trans hXTy)
      have hRunNotNe : __eo_not (__run_evaluate x) ≠ Term.Stuck := by
        simpa [__run_evaluate] using hRunNe
      have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
        EvaluateProofInternal.eo_not_arg_ne_stuck hRunNotNe
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunXBv :
          __eo_typeof (__run_evaluate x) =
            Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w)) :=
        hXPres.trans hXEoBv
      cases hRunX : __run_evaluate x <;>
        simp [__run_evaluate, hRunX, __eo_not] at hRunNotNe hRunXBv ⊢
      all_goals
        cases hRunXBv
        change __eo_lit_type_Binary _ =
          __eo_typeof_bvnot (__eo_typeof x)
        simp [__eo_lit_type_Binary, __eo_len, __eo_mk_apply,
          __eo_typeof_bvnot, hXEoBv]
  | bvneg =>
      have hBvNegNN :
          term_has_non_none_type
            (SmtTerm.bvneg (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      rcases bv_unop_arg_of_non_none
          (op := SmtTerm.bvneg) (t := __eo_to_smt x)
          (by rw [__smtx_typeof.eq_47])
          hBvNegNN with
        ⟨w, hXTy⟩
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTy]
        simp
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hXEoBv :
          __eo_typeof x =
            Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w)) :=
        TranslationProofs.eo_to_smt_type_eq_bitvec
          (hXMatch.symm.trans hXTy)
      have hRunNegNe : __eo_neg (__run_evaluate x) ≠ Term.Stuck := by
        simpa [__run_evaluate] using hRunNe
      have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
        EvaluateProofInternal.eo_neg_arg_ne_stuck hRunNegNe
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunXBv :
          __eo_typeof (__run_evaluate x) =
            Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w)) :=
        hXPres.trans hXEoBv
      cases hRunX : __run_evaluate x <;>
        simp [__run_evaluate, hRunX, __eo_neg] at hRunNegNe hRunXBv ⊢
      all_goals
        try cases hRunXBv
        try
          change __eo_lit_type_Binary _ =
            __eo_typeof_bvnot (__eo_typeof x)
          simp [__eo_lit_type_Binary, __eo_len, __eo_mk_apply,
            __eo_typeof_bvnot, hXEoBv]
  | to_real =>
      have hToRealNN :
          term_has_non_none_type
            (SmtTerm.to_real (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      have hRunToQNe :
          __eo_to_q (__run_evaluate x) ≠ Term.Stuck := by
        simpa [__run_evaluate] using hRunNe
      have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
        EvaluateProofInternal.eo_to_q_arg_ne_stuck hRunToQNe
      have hXInt := to_real_arg_of_non_none (t := __eo_to_smt x) hToRealNN
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXInt]
        simp
      have hXPres :=
        recX hXTrans hRunXNe
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hXMatch.symm.trans hXInt)
      have hRunXEoInt :
          __eo_typeof (__run_evaluate x) = Term.UOp UserOp.Int :=
        hXPres.trans hXEoInt
      cases hRunX : __run_evaluate x <;>
        simp [__run_evaluate, hRunX, __eo_to_q] at hRunToQNe hRunXEoInt ⊢
      all_goals
        first
        | change Term.UOp UserOp.Real =
            Term.UOp UserOp.Int at hRunXEoInt
          cases hRunXEoInt
        | change Term.UOp UserOp.Real =
            __eo_typeof_to_real (__eo_typeof x)
          rw [hXEoInt]
          rfl
  | to_int =>
      have hToIntNN :
          term_has_non_none_type
            (SmtTerm.to_int (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      have hRunToZNe :
          __eo_to_z (__run_evaluate x) ≠ Term.Stuck := by
        simpa [__run_evaluate] using hRunNe
      have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
        EvaluateProofInternal.eo_to_z_arg_ne_stuck hRunToZNe
      have hXReal :
          __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
        real_arg_of_non_none (op := SmtTerm.to_int)
          (typeof_to_int_eq (__eo_to_smt x)) hToIntNN
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXReal]
        simp
      have hXPres :=
        recX hXTrans hRunXNe
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hXEoReal : __eo_typeof x = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real
          (hXMatch.symm.trans hXReal)
      have hRunXEoReal :
          __eo_typeof (__run_evaluate x) = Term.UOp UserOp.Real :=
        hXPres.trans hXEoReal
      cases hRunX : __run_evaluate x <;>
        simp [__run_evaluate, hRunX, __eo_to_z] at hRunToZNe hRunXEoReal ⊢
      all_goals
        first
        | change Term.UOp UserOp.Int =
            Term.UOp UserOp.Real at hRunXEoReal
          cases hRunXEoReal
        | change
            Term.Apply (Term.UOp UserOp.BitVec) _ =
              Term.UOp UserOp.Real at hRunXEoReal
          cases hRunXEoReal
        | change
            Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) =
              Term.UOp UserOp.Real at hRunXEoReal
          cases hRunXEoReal
        | change Term.UOp UserOp.Int =
            __eo_typeof_to_int (__eo_typeof x)
          rw [hXEoReal]
          rfl
  | is_int =>
      have hIsIntNN :
          term_has_non_none_type
            (SmtTerm.is_int (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      have hRunEqNe :
          __eo_eq (__eo_to_q (__eo_to_z (__run_evaluate x)))
              (__eo_to_q (__run_evaluate x)) ≠ Term.Stuck := by
        simpa [__run_evaluate] using hRunNe
      have hRunToQNe :
          __eo_to_q (__run_evaluate x) ≠ Term.Stuck :=
        EvaluateProofInternal.eo_eq_right_ne_stuck hRunEqNe
      have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
        EvaluateProofInternal.eo_to_q_arg_ne_stuck hRunToQNe
      have hXReal :
          __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
        real_arg_of_non_none (op := SmtTerm.is_int)
          (typeof_is_int_eq (__eo_to_smt x)) hIsIntNN
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXReal]
        simp
      have hXPres :=
        recX hXTrans hRunXNe
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hXEoReal : __eo_typeof x = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real
          (hXMatch.symm.trans hXReal)
      have hRunXEoReal :
          __eo_typeof (__run_evaluate x) = Term.UOp UserOp.Real :=
        hXPres.trans hXEoReal
      cases hRunX : __run_evaluate x <;>
        simp [__run_evaluate, hRunX, __eo_to_q] at hRunToQNe hRunXEoReal ⊢
      all_goals
        first
        | change Term.UOp UserOp.Int =
            Term.UOp UserOp.Real at hRunXEoReal
          cases hRunXEoReal
        | change Term.Bool =
            __eo_typeof_is_int (__eo_typeof x)
          rw [hXEoReal]
          rfl
  | __eoo_neg_2 =>
      have hUnegNN :
          term_has_non_none_type
            (SmtTerm.uneg (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      have hRunNegNe :
          __eo_neg (__run_evaluate x) ≠ Term.Stuck := by
        simpa [__run_evaluate] using hRunNe
      have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
        EvaluateProofInternal.eo_neg_arg_ne_stuck hRunNegNe
      rcases arith_unop_arg_of_non_none
          (op := SmtTerm.uneg) (t := __eo_to_smt x)
          (typeof_uneg_eq (__eo_to_smt x)) hUnegNN with
        hXInt | hXReal
      · have hXTrans : RuleProofs.eo_has_smt_translation x := by
          unfold RuleProofs.eo_has_smt_translation
          rw [hXInt]
          simp
        have hXPres :=
          recX hXTrans hRunXNe
        have hXMatch :=
          TranslationProofs.eo_to_smt_typeof_matches_translation
            x hXTrans
        have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
          TranslationProofs.eo_to_smt_type_eq_int
            (hXMatch.symm.trans hXInt)
        have hRunXEoInt :
            __eo_typeof (__run_evaluate x) =
              Term.UOp UserOp.Int :=
          hXPres.trans hXEoInt
        cases hRunX : __run_evaluate x <;>
          simp [__run_evaluate, hRunX, __eo_neg] at hRunNegNe hRunXEoInt ⊢
        all_goals
          first
          | change Term.UOp UserOp.Real =
              Term.UOp UserOp.Int at hRunXEoInt
            cases hRunXEoInt
          | change
              Term.Apply (Term.UOp UserOp.BitVec) _ =
                Term.UOp UserOp.Int at hRunXEoInt
            cases hRunXEoInt
          | change Term.UOp UserOp.Int =
              __eo_typeof_abs (__eo_typeof x)
            rw [hXEoInt]
            simp [__eo_typeof_abs, __eo_requires,
              __is_arith_type, native_ite, native_teq,
              native_not, SmtEval.native_not]
      · have hXTrans : RuleProofs.eo_has_smt_translation x := by
          unfold RuleProofs.eo_has_smt_translation
          rw [hXReal]
          simp
        have hXPres :=
          recX hXTrans hRunXNe
        have hXMatch :=
          TranslationProofs.eo_to_smt_typeof_matches_translation
            x hXTrans
        have hXEoReal : __eo_typeof x = Term.UOp UserOp.Real :=
          TranslationProofs.eo_to_smt_type_eq_real
            (hXMatch.symm.trans hXReal)
        have hRunXEoReal :
            __eo_typeof (__run_evaluate x) =
              Term.UOp UserOp.Real :=
          hXPres.trans hXEoReal
        cases hRunX : __run_evaluate x <;>
          simp [__run_evaluate, hRunX, __eo_neg] at hRunNegNe hRunXEoReal ⊢
        all_goals
          first
          | change Term.UOp UserOp.Int =
              Term.UOp UserOp.Real at hRunXEoReal
            cases hRunXEoReal
          | change
              Term.Apply (Term.UOp UserOp.BitVec) _ =
                Term.UOp UserOp.Real at hRunXEoReal
            cases hRunXEoReal
          | change Term.UOp UserOp.Real =
              __eo_typeof_abs (__eo_typeof x)
            rw [hXEoReal]
            simp [__eo_typeof_abs, __eo_requires,
              __is_arith_type, native_ite, native_teq,
              native_not, SmtEval.native_not]
  | abs =>
      have hAbsNN :
          term_has_non_none_type
            (SmtTerm.abs (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      have hRunAbsNe :
          __eo_ite (__eo_is_neg (__run_evaluate x))
              (__eo_neg (__run_evaluate x))
              (__run_evaluate x) ≠ Term.Stuck := by
        simpa [__run_evaluate] using hRunNe
      have hRunIsNegNe :
          __eo_is_neg (__run_evaluate x) ≠ Term.Stuck :=
          EvaluateProofInternal.eo_ite_cond_ne_stuck hRunAbsNe
      have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
        EvaluateProofInternal.eo_is_neg_arg_ne_stuck hRunIsNegNe
      rcases abs_arg_of_non_none hAbsNN with hXInt | hXReal
      · have hXTrans : RuleProofs.eo_has_smt_translation x := by
          unfold RuleProofs.eo_has_smt_translation
          rw [hXInt]
          simp
        have hXPres :=
          recX hXTrans hRunXNe
        have hXMatch :=
          TranslationProofs.eo_to_smt_typeof_matches_translation
            x hXTrans
        have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
          TranslationProofs.eo_to_smt_type_eq_int
            (hXMatch.symm.trans hXInt)
        have hRunXEoInt :
            __eo_typeof (__run_evaluate x) = Term.UOp UserOp.Int :=
          hXPres.trans hXEoInt
        cases hRunX : __run_evaluate x <;>
          simp [__run_evaluate, hRunX, __eo_is_neg, __eo_ite,
            __eo_neg, native_ite, native_teq] at hRunAbsNe hRunXEoInt ⊢
        all_goals
          first
          | change Term.UOp UserOp.Real =
              Term.UOp UserOp.Int at hRunXEoInt
            cases hRunXEoInt
          | change
              Term.Apply (Term.UOp UserOp.BitVec) _ =
                Term.UOp UserOp.Int at hRunXEoInt
            cases hRunXEoInt
          | rename_i n
            cases hNeg : native_zlt n 0 <;>
              simp [hNeg, __eo_lit_type_Numeral]
            all_goals
              change Term.UOp UserOp.Int =
                __eo_typeof_abs (__eo_typeof x)
              rw [hXEoInt]
              simp [__eo_typeof_abs, __eo_requires,
                __is_arith_type, native_ite, native_teq,
                native_not, SmtEval.native_not]
      · have hXTrans : RuleProofs.eo_has_smt_translation x := by
          unfold RuleProofs.eo_has_smt_translation
          rw [hXReal]
          simp
        have hXPres :=
          recX hXTrans hRunXNe
        have hXMatch :=
          TranslationProofs.eo_to_smt_typeof_matches_translation
            x hXTrans
        have hXEoReal : __eo_typeof x = Term.UOp UserOp.Real :=
          TranslationProofs.eo_to_smt_type_eq_real
            (hXMatch.symm.trans hXReal)
        have hRunXEoReal :
            __eo_typeof (__run_evaluate x) = Term.UOp UserOp.Real :=
          hXPres.trans hXEoReal
        cases hRunX : __run_evaluate x <;>
          simp [__run_evaluate, hRunX, __eo_is_neg, __eo_ite,
            __eo_neg, native_ite, native_teq] at hRunAbsNe hRunXEoReal ⊢
        all_goals
          first
          | change Term.UOp UserOp.Int =
              Term.UOp UserOp.Real at hRunXEoReal
            cases hRunXEoReal
          | change
              Term.Apply (Term.UOp UserOp.BitVec) _ =
                Term.UOp UserOp.Real at hRunXEoReal
            cases hRunXEoReal
          | rename_i q
            cases hNeg : native_qlt q (native_mk_rational 0 1) <;>
              simp [hNeg, __eo_lit_type_Rational]
            all_goals
              change Term.UOp UserOp.Real =
                __eo_typeof_abs (__eo_typeof x)
              rw [hXEoReal]
              simp [__eo_typeof_abs, __eo_requires,
                __is_arith_type, native_ite, native_teq,
                native_not, SmtEval.native_not]
  | int_pow2 =>
      have hPowNN :
          term_has_non_none_type
            (SmtTerm.int_pow2 (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      have hXInt :
          __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
        int_ret_arg_of_non_none (op := SmtTerm.int_pow2)
          (typeof_int_pow2_eq (__eo_to_smt x)) hPowNN
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXInt]
        simp
      have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
        intro hStuck
        apply hRunNe
        simp [__run_evaluate, hStuck, __eo_is_z,
          __eo_is_z_internal, __eo_is_neg, __eo_ite,
          __eo_pow, __eo_mk_apply, native_ite, native_teq,
          native_not, native_and]
      have hXPres :=
        recX hXTrans hRunXNe
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hXMatch.symm.trans hXInt)
      have hRunXEoInt :
          __eo_typeof (__run_evaluate x) = Term.UOp UserOp.Int :=
        hXPres.trans hXEoInt
      have hRunBodyTy :
          __eo_typeof
              (__eo_ite (__eo_is_z (__run_evaluate x))
                (__eo_ite (__eo_is_neg (__run_evaluate x))
                  (Term.Numeral 0)
                  (__eo_pow (Term.Numeral 2) (__run_evaluate x)))
                (__eo_mk_apply (Term.UOp UserOp.int_pow2)
                  (__run_evaluate x))) =
            Term.UOp UserOp.Int :=
        EvaluateProofInternal.eo_int_pow2_body_typeof_int (__run_evaluate x) hRunXEoInt
      change
        __eo_typeof
            (__eo_ite (__eo_is_z (__run_evaluate x))
              (__eo_ite (__eo_is_neg (__run_evaluate x))
                (Term.Numeral 0)
                (__eo_pow (Term.Numeral 2) (__run_evaluate x)))
              (__eo_mk_apply (Term.UOp UserOp.int_pow2)
                (__run_evaluate x))) =
          __eo_typeof_int_pow2 (__eo_typeof x)
      rw [hRunBodyTy, hXEoInt]
      rfl
  | int_log2 =>
      have hLogNN :
          term_has_non_none_type
            (SmtTerm.int_log2 (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      have hXInt :
          __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
        int_ret_arg_of_non_none (op := SmtTerm.int_log2)
          (typeof_int_log2_eq (__eo_to_smt x)) hLogNN
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXInt]
        simp
      have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
        intro hStuck
        apply hRunNe
        simp [__run_evaluate, hStuck, __eo_is_z,
          __eo_is_z_internal, __eo_is_neg, __eo_ite,
          __eo_log, __eo_mk_apply, native_ite, native_teq,
          native_not, native_and]
      have hXPres :=
        recX hXTrans hRunXNe
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hXMatch.symm.trans hXInt)
      have hRunXEoInt :
          __eo_typeof (__run_evaluate x) = Term.UOp UserOp.Int :=
        hXPres.trans hXEoInt
      have hRunBodyTy :
          __eo_typeof
              (__eo_ite (__eo_is_z (__run_evaluate x))
                (__eo_ite (__eo_is_neg (__run_evaluate x))
                  (Term.Numeral 0)
                  (__eo_log (Term.Numeral 2) (__run_evaluate x)))
                (__eo_mk_apply (Term.UOp UserOp.int_log2)
                  (__run_evaluate x))) =
            Term.UOp UserOp.Int :=
        EvaluateProofInternal.eo_int_log2_body_typeof_int (__run_evaluate x) hRunXEoInt
      change
        __eo_typeof
            (__eo_ite (__eo_is_z (__run_evaluate x))
              (__eo_ite (__eo_is_neg (__run_evaluate x))
                (Term.Numeral 0)
                (__eo_log (Term.Numeral 2) (__run_evaluate x)))
              (__eo_mk_apply (Term.UOp UserOp.int_log2)
                (__run_evaluate x))) =
          __eo_typeof_int_pow2 (__eo_typeof x)
      rw [hRunBodyTy, hXEoInt]
      rfl
  | int_ispow2 =>
      let geqTerm :=
        SmtTerm.geq (__eo_to_smt x) (SmtTerm.Numeral 0)
      let eqTerm :=
        SmtTerm.eq (__eo_to_smt x)
          (SmtTerm.int_pow2 (SmtTerm.int_log2 (__eo_to_smt x)))
      have hIspowNN :
          term_has_non_none_type (SmtTerm.and geqTerm eqTerm) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation, geqTerm, eqTerm] at hsimpa ⊢
        exact hsimpa
      have hArgs :
          __smtx_typeof geqTerm = SmtType.Bool ∧
            __smtx_typeof eqTerm = SmtType.Bool :=
        bool_binop_args_bool_of_non_none (op := SmtTerm.and)
          (typeof_and_eq geqTerm eqTerm) hIspowNN
      have hGeqNN : term_has_non_none_type geqTerm := by
        unfold term_has_non_none_type
        rw [hArgs.1]
        simp
      have hGeqArgs :
          (__smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
              __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int) ∨
            (__smtx_typeof (__eo_to_smt x) = SmtType.Real ∧
              __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Real) :=
        arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq)
          (typeof_geq_eq (__eo_to_smt x) (SmtTerm.Numeral 0))
          hGeqNN
      have hXInt :
          __smtx_typeof (__eo_to_smt x) = SmtType.Int := by
        rcases hGeqArgs with hInt | hReal
        · exact hInt.1
        · have hZeroReal := hReal.2
          rw [__smtx_typeof.eq_2] at hZeroReal
          simp at hZeroReal
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXInt]
        simp
      have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
        intro hStuck
        apply hRunNe
        simp [__run_evaluate, hStuck, __eo_is_z,
          __eo_is_z_internal, __eo_ite, __eo_mk_apply,
          native_ite, native_teq, native_not, native_and]
      have hXPres :=
        recX hXTrans hRunXNe
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hXMatch.symm.trans hXInt)
      have hRunXEoInt :
          __eo_typeof (__run_evaluate x) = Term.UOp UserOp.Int :=
        hXPres.trans hXEoInt
      have hRunBodyTy :
          __eo_typeof
              (let isNeg := __eo_is_neg (__run_evaluate x)
               let isZ := __eo_is_z (__run_evaluate x)
               __eo_ite isZ
                (__eo_ite isNeg (Term.Boolean false)
                  (__eo_eq (__run_evaluate x)
                    (__eo_pow (Term.Numeral 2)
                      (__eo_ite isZ
                        (__eo_ite isNeg (Term.Numeral 0)
                          (__eo_log (Term.Numeral 2)
                            (__run_evaluate x)))
                        (__eo_mk_apply (Term.UOp UserOp.int_log2)
                          (__run_evaluate x))))))
                (__eo_mk_apply (Term.UOp UserOp.int_ispow2)
                  (__run_evaluate x))) =
            Term.Bool :=
        EvaluateProofInternal.eo_int_ispow2_body_typeof_bool (__run_evaluate x)
          hRunXEoInt
      change
        __eo_typeof
            (let isNeg := __eo_is_neg (__run_evaluate x)
             let isZ := __eo_is_z (__run_evaluate x)
             __eo_ite isZ
              (__eo_ite isNeg (Term.Boolean false)
                (__eo_eq (__run_evaluate x)
                  (__eo_pow (Term.Numeral 2)
                    (__eo_ite isZ
                      (__eo_ite isNeg (Term.Numeral 0)
                        (__eo_log (Term.Numeral 2)
                          (__run_evaluate x)))
                      (__eo_mk_apply (Term.UOp UserOp.int_log2)
                        (__run_evaluate x))))))
              (__eo_mk_apply (Term.UOp UserOp.int_ispow2)
                (__run_evaluate x))) =
          __eo_typeof_int_ispow2 (__eo_typeof x)
      rw [hRunBodyTy, hXEoInt]
      rfl
  | _at_bvsize =>
      have hBvsizeNN :
          term_has_non_none_type
            (let _v0 := __eo_to_smt_bv_size
                (__smtx_typeof (__eo_to_smt x))
             native_ite (native_zleq 0 _v0)
              (SmtTerm._at_purify (SmtTerm.Numeral _v0))
              SmtTerm.None) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      have hArgExists :
          ∃ w : native_Nat,
            __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
        apply TranslationProofs.smtx_bv_sizeof_term_non_none
          (t := __eo_to_smt x)
        unfold term_has_non_none_type at hBvsizeNN
        exact hBvsizeNN
      rcases hArgExists with ⟨w, hXTy⟩
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTy]
        simp
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hXEoBv :
          __eo_typeof x =
            Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w)) :=
        TranslationProofs.eo_to_smt_type_eq_bitvec
          (hXMatch.symm.trans hXTy)
      change
        __eo_typeof (__bv_bitwidth (__eo_typeof x)) =
          __eo_typeof__at_bvsize (__eo_typeof x)
      rw [hXEoBv]
      change
        __eo_lit_type_Numeral
            (Term.Numeral (native_nat_to_int w)) =
          Term.UOp UserOp.Int
      rfl
  | str_len =>
      have hLenNN :
          term_has_non_none_type
            (SmtTerm.str_len (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
          (typeof_str_len_eq (__eo_to_smt x)) hLenNN with
        ⟨T, hXTySeq⟩
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTySeq]
        simp
      rcases EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq x hXTrans hXTySeq with
        ⟨U, hXEoSeq, _hUSmt⟩
      have hRunLenNe :
          __eo_len (__run_evaluate x) ≠ Term.Stuck := by
        simpa [__run_evaluate] using hRunNe
      have hRunLenTy :
          __eo_typeof (__eo_len (__run_evaluate x)) =
            Term.UOp UserOp.Int :=
        EvaluateProofInternal.eo_len_typeof_int_of_ne_stuck (__run_evaluate x) hRunLenNe
      change
        __eo_typeof (__eo_len (__run_evaluate x)) =
          __eo_typeof_str_len (__eo_typeof x)
      rw [hRunLenTy, hXEoSeq]
      rfl
  | ubv_to_int =>
      have hUbvNN :
          term_has_non_none_type
            (SmtTerm.ubv_to_int (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      rcases bv_unop_ret_arg_of_non_none
          (op := SmtTerm.ubv_to_int) (ret := SmtType.Int)
          (by rw [smtx_typeof_ubv_to_int_term_eq]) hUbvNN with
        ⟨w, hXTy⟩
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTy]
        simp
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hXEoBv :
          __eo_typeof x =
            Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w)) :=
        TranslationProofs.eo_to_smt_type_eq_bitvec
          (hXMatch.symm.trans hXTy)
      have hRunToZNe :
          __eo_to_z (__run_evaluate x) ≠ Term.Stuck := by
        simpa [__run_evaluate] using hRunNe
      have hRunToZTy :
          __eo_typeof (__eo_to_z (__run_evaluate x)) =
            Term.UOp UserOp.Int :=
        EvaluateProofInternal.eo_to_z_typeof_int_of_ne_stuck (__run_evaluate x) hRunToZNe
      change
        __eo_typeof (__eo_to_z (__run_evaluate x)) =
          __eo_typeof__at_bvsize (__eo_typeof x)
      rw [hRunToZTy, hXEoBv]
      rfl
  | sbv_to_int =>
      have hSbvNN :
          term_has_non_none_type
            (SmtTerm.sbv_to_int (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      rcases bv_unop_ret_arg_of_non_none
          (op := SmtTerm.sbv_to_int) (ret := SmtType.Int)
          (by rw [__smtx_typeof.eq_def] <;> simp only)
          hSbvNN with
        ⟨w, hXTy⟩
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTy]
        simp
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hXEoBv :
          __eo_typeof x =
            Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w)) :=
        TranslationProofs.eo_to_smt_type_eq_bitvec
          (hXMatch.symm.trans hXTy)
      have hRunBodyNe :
          EvaluateProofInternal.eo_eval_sbv_to_int_rhs x ≠ Term.Stuck := by
        simpa [EvaluateProofInternal.eo_eval_sbv_to_int_rhs, __run_evaluate] using hRunNe
      have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
        intro hStuck
        apply hRunBodyNe
        dsimp [EvaluateProofInternal.eo_eval_sbv_to_int_rhs]
        rw [hStuck]
        rw [show
            __eo_eq (__bv_bitwidth (__eo_typeof Term.Stuck))
                (Term.Numeral 0) =
              Term.Stuck by
          rfl]
        rfl
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunXEoBv :
          __eo_typeof (__run_evaluate x) =
            Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w)) :=
        hXPres.trans hXEoBv
      by_cases hwZero : w = 0
      · subst w
        have hRunBodyEq :
            EvaluateProofInternal.eo_eval_sbv_to_int_rhs x = Term.Numeral 0 := by
          simpa [native_nat_to_int, SmtEval.native_nat_to_int] using
            EvaluateProofInternal.eo_eval_sbv_to_int_rhs_eq_zero_of_run_typeof_zero
              x hRunXEoBv
        change
          __eo_typeof (EvaluateProofInternal.eo_eval_sbv_to_int_rhs x) =
            __eo_typeof__at_bvsize (__eo_typeof x)
        rw [hRunBodyEq, hXEoBv]
        rfl
      · have hwNatPos : 0 < w := Nat.pos_of_ne_zero hwZero
        have hwIntPos : 0 < native_nat_to_int w := by
          have hCast : (Int.ofNat 0) < (Int.ofNat w) :=
            Int.ofNat_lt.mpr hwNatPos
          simpa [native_nat_to_int, SmtEval.native_nat_to_int]
            using hCast
        have hRunBodyTy :
            __eo_typeof (EvaluateProofInternal.eo_eval_sbv_to_int_rhs x) =
              Term.UOp UserOp.Int :=
          EvaluateProofInternal.eo_eval_sbv_to_int_rhs_typeof_int_of_pos_run_typeof
            x hRunXEoBv hwIntPos hRunBodyNe
        change
          __eo_typeof (EvaluateProofInternal.eo_eval_sbv_to_int_rhs x) =
            __eo_typeof__at_bvsize (__eo_typeof x)
        rw [hRunBodyTy, hXEoBv]
        rfl
  | str_to_code =>
      have hCodeNN :
          term_has_non_none_type
            (SmtTerm.str_to_code (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      have hXTyChar :
          __smtx_typeof (__eo_to_smt x) =
            SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_code)
          (typeof_str_to_code_eq (__eo_to_smt x)) hCodeNN
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyChar]
        simp
      have hXEoSeqChar :
          __eo_typeof x =
            Term.Apply (Term.UOp UserOp.Seq)
              (Term.UOp UserOp.Char) :=
        EvaluateProofInternal.eo_typeof_seq_char_of_smt_type_seq_char x hXTrans hXTyChar
      have hRunBodyNe :
          (let len := __eo_len (__run_evaluate x)
           __eo_ite (__eo_eq len (Term.Numeral 1))
            (__eo_to_z (__run_evaluate x))
            (__eo_ite (__eo_is_z len)
              (Term.Numeral (-1 : native_Int))
              (__eo_mk_apply (Term.UOp UserOp.str_to_code)
                (__run_evaluate x)))) ≠ Term.Stuck := by
        simpa [__run_evaluate] using hRunNe
      have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
        intro hStuck
        apply hRunBodyNe
        simp [hStuck, __eo_len, __eo_eq, __eo_ite, __eo_is_z,
          __eo_is_z_internal, __eo_to_z, __eo_mk_apply,
          native_ite, native_teq, native_not, native_and]
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunXEoSeqChar :
          __eo_typeof (__run_evaluate x) =
            Term.Apply (Term.UOp UserOp.Seq)
              (Term.UOp UserOp.Char) :=
        hXPres.trans hXEoSeqChar
      have hRunBodyTy :
          __eo_typeof
              (let len := __eo_len (__run_evaluate x)
               __eo_ite (__eo_eq len (Term.Numeral 1))
                (__eo_to_z (__run_evaluate x))
                (__eo_ite (__eo_is_z len)
                  (Term.Numeral (-1 : native_Int))
                  (__eo_mk_apply (Term.UOp UserOp.str_to_code)
                    (__run_evaluate x)))) =
            Term.UOp UserOp.Int :=
        EvaluateProofInternal.eo_str_to_code_body_typeof_int (__run_evaluate x)
          hRunXEoSeqChar hRunBodyNe
      change
        __eo_typeof
            (let len := __eo_len (__run_evaluate x)
             __eo_ite (__eo_eq len (Term.Numeral 1))
              (__eo_to_z (__run_evaluate x))
              (__eo_ite (__eo_is_z len)
                (Term.Numeral (-1 : native_Int))
                (__eo_mk_apply (Term.UOp UserOp.str_to_code)
                  (__run_evaluate x)))) =
          __eo_typeof_str_to_code (__eo_typeof x)
      rw [hRunBodyTy, hXEoSeqChar]
      rfl
  | str_to_int =>
      have hIntNN :
          term_has_non_none_type
            (SmtTerm.str_to_int (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      have hXTyChar :
          __smtx_typeof (__eo_to_smt x) =
            SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_int)
          (typeof_str_to_int_eq (__eo_to_smt x)) hIntNN
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyChar]
        simp
      have hXEoSeqChar :
          __eo_typeof x =
            Term.Apply (Term.UOp UserOp.Seq)
              (Term.UOp UserOp.Char) :=
        EvaluateProofInternal.eo_typeof_seq_char_of_smt_type_seq_char x hXTrans hXTyChar
      have hRunBodyNe :
          __eo_ite (__eo_is_str (__run_evaluate x))
            (__eo_ite (__eo_eq (__run_evaluate x) (Term.String []))
              (Term.Numeral (-1 : native_Int))
              (__str_to_int_eval_rec
                (__eo_list_rev (Term.UOp UserOp.str_concat)
                  (__str_flatten
                    (__str_nary_intro (__run_evaluate x))))
                (Term.Numeral 1) (Term.Numeral 0)))
            (__eo_mk_apply (Term.UOp UserOp.str_to_int)
              (__run_evaluate x)) ≠ Term.Stuck := by
        simpa [__run_evaluate] using hRunNe
      have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
        intro hStuck
        apply hRunBodyNe
        simp [hStuck, __eo_is_str, __eo_is_str_internal,
          __eo_ite, __eo_mk_apply, native_and, native_not,
          native_ite, native_teq]
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunXEoSeqChar :
          __eo_typeof (__run_evaluate x) =
            Term.Apply (Term.UOp UserOp.Seq)
              (Term.UOp UserOp.Char) :=
        hXPres.trans hXEoSeqChar
      have hRunBodyTy :
          __eo_typeof
              (__eo_ite (__eo_is_str (__run_evaluate x))
                (__eo_ite
                  (__eo_eq (__run_evaluate x) (Term.String []))
                  (Term.Numeral (-1 : native_Int))
                  (__str_to_int_eval_rec
                    (__eo_list_rev (Term.UOp UserOp.str_concat)
                      (__str_flatten
                        (__str_nary_intro (__run_evaluate x))))
                    (Term.Numeral 1) (Term.Numeral 0)))
                (__eo_mk_apply (Term.UOp UserOp.str_to_int)
                  (__run_evaluate x))) =
            Term.UOp UserOp.Int :=
        EvaluateProofInternal.eo_str_to_int_body_typeof_int (__run_evaluate x)
          hRunXEoSeqChar hRunBodyNe
      change
        __eo_typeof
            (__eo_ite (__eo_is_str (__run_evaluate x))
              (__eo_ite
                (__eo_eq (__run_evaluate x) (Term.String []))
                (Term.Numeral (-1 : native_Int))
                (__str_to_int_eval_rec
                  (__eo_list_rev (Term.UOp UserOp.str_concat)
                    (__str_flatten
                      (__str_nary_intro (__run_evaluate x))))
                  (Term.Numeral 1) (Term.Numeral 0)))
              (__eo_mk_apply (Term.UOp UserOp.str_to_int)
                (__run_evaluate x))) =
          __eo_typeof_str_to_code (__eo_typeof x)
      rw [hRunBodyTy, hXEoSeqChar]
      rfl
  | str_from_int =>
      have hFromNN :
          term_has_non_none_type
            (SmtTerm.str_from_int (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      have hXInt :
          __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
        int_arg_of_non_none_ret (op := SmtTerm.str_from_int)
          (typeof_str_from_int_eq (__eo_to_smt x)) hFromNN
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXInt]
        simp
      have hRunBodyNe :
          EvaluateProofInternal.eo_eval_str_from_int_rhs x ≠ Term.Stuck := by
        simpa [EvaluateProofInternal.eo_eval_str_from_int_rhs, __run_evaluate] using hRunNe
      have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
        intro hStuck
        apply hRunBodyNe
        dsimp [EvaluateProofInternal.eo_eval_str_from_int_rhs]
        rw [hStuck]
        simp [__eo_is_z, __eo_is_z_internal, __eo_ite,
          __eo_mk_apply, native_and, native_not, native_ite,
          native_teq]
      have hXPres :=
        recX hXTrans hRunXNe
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hXMatch.symm.trans hXInt)
      have hRunXEoInt :
          __eo_typeof (__run_evaluate x) = Term.UOp UserOp.Int :=
        hXPres.trans hXEoInt
      have hRunBodyTy :
          __eo_typeof (EvaluateProofInternal.eo_eval_str_from_int_rhs x) =
            Term.Apply (Term.UOp UserOp.Seq)
              (Term.UOp UserOp.Char) :=
        EvaluateProofInternal.eo_eval_str_from_int_rhs_typeof_seq_char x hRunXEoInt
      change
        __eo_typeof (EvaluateProofInternal.eo_eval_str_from_int_rhs x) =
          __eo_typeof_str_from_code (__eo_typeof x)
      rw [hRunBodyTy, hXEoInt]
      rfl
  | str_from_code =>
      have hFromNN :
          term_has_non_none_type
            (SmtTerm.str_from_code (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      have hXInt :
          __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
        int_arg_of_non_none_ret (op := SmtTerm.str_from_code)
          (typeof_str_from_code_eq (__eo_to_smt x)) hFromNN
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXInt]
        simp
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hXMatch.symm.trans hXInt)
      have hRunBodyNe :
          EvaluateProofInternal.eo_eval_str_from_code_rhs x ≠ Term.Stuck := by
        simpa [EvaluateProofInternal.eo_eval_str_from_code_rhs, __run_evaluate] using hRunNe
      have hActive :
          EvaluateProofInternal.eo_eval_str_from_code_rhs x ≠
            Term.Apply (Term.UOp UserOp.str_from_code) x := by
        intro hSelf
        apply hRun
        simpa [EvaluateProofInternal.eo_eval_str_from_code_rhs, __run_evaluate] using hSelf
      have hRunBodyTy :
          __eo_typeof (EvaluateProofInternal.eo_eval_str_from_code_rhs x) =
            Term.Apply (Term.UOp UserOp.Seq)
              (Term.UOp UserOp.Char) :=
        EvaluateProofInternal.eo_eval_str_from_code_rhs_typeof_seq_char x hXEoInt
          hRunBodyNe hActive
      change
        __eo_typeof (EvaluateProofInternal.eo_eval_str_from_code_rhs x) =
          __eo_typeof_str_from_code (__eo_typeof x)
      rw [hRunBodyTy, hXEoInt]
      rfl
  | str_to_lower =>
      have hLowerNN :
          term_has_non_none_type
            (SmtTerm.str_to_lower (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      have hXTyChar :
          __smtx_typeof (__eo_to_smt x) =
            SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_lower)
          (typeof_str_to_lower_eq (__eo_to_smt x)) hLowerNN
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyChar]
        simp
      have hXEoSeqChar :
          __eo_typeof x =
            Term.Apply (Term.UOp UserOp.Seq)
              (Term.UOp UserOp.Char) :=
        EvaluateProofInternal.eo_typeof_seq_char_of_smt_type_seq_char x hXTrans hXTyChar
      have hRunBodyNe :
          __eo_ite (__eo_is_str (__run_evaluate x))
            (__str_case_conv_rec
              (__str_flatten (__str_nary_intro (__run_evaluate x)))
              (Term.Boolean true))
            (__eo_mk_apply (Term.UOp UserOp.str_to_lower)
              (__run_evaluate x)) ≠ Term.Stuck := by
        simpa [__run_evaluate] using hRunNe
      have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
        intro hStuck
        apply hRunBodyNe
        simp [hStuck, __eo_is_str, __eo_is_str_internal,
          __eo_ite, __eo_mk_apply, native_and, native_not,
          native_ite, native_teq]
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunXEoSeqChar :
          __eo_typeof (__run_evaluate x) =
            Term.Apply (Term.UOp UserOp.Seq)
              (Term.UOp UserOp.Char) :=
        hXPres.trans hXEoSeqChar
      have hRunBodyTy :
          __eo_typeof
              (__eo_ite (__eo_is_str (__run_evaluate x))
                (__str_case_conv_rec
                  (__str_flatten
                    (__str_nary_intro (__run_evaluate x)))
                  (Term.Boolean true))
                (__eo_mk_apply (Term.UOp UserOp.str_to_lower)
                  (__run_evaluate x))) =
            Term.Apply (Term.UOp UserOp.Seq)
              (Term.UOp UserOp.Char) :=
        EvaluateProofInternal.eo_str_to_lower_body_typeof_seq_char (__run_evaluate x)
          hRunXEoSeqChar hRunBodyNe
      change
        __eo_typeof
            (__eo_ite (__eo_is_str (__run_evaluate x))
              (__str_case_conv_rec
                (__str_flatten
                  (__str_nary_intro (__run_evaluate x)))
                (Term.Boolean true))
              (__eo_mk_apply (Term.UOp UserOp.str_to_lower)
                (__run_evaluate x))) =
          __eo_typeof_str_to_lower (__eo_typeof x)
      rw [hRunBodyTy, hXEoSeqChar]
      rfl
  | str_to_upper =>
      have hUpperNN :
          term_has_non_none_type
            (SmtTerm.str_to_upper (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      have hXTyChar :
          __smtx_typeof (__eo_to_smt x) =
            SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_upper)
          (typeof_str_to_upper_eq (__eo_to_smt x)) hUpperNN
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyChar]
        simp
      have hXEoSeqChar :
          __eo_typeof x =
            Term.Apply (Term.UOp UserOp.Seq)
              (Term.UOp UserOp.Char) :=
        EvaluateProofInternal.eo_typeof_seq_char_of_smt_type_seq_char x hXTrans hXTyChar
      have hRunBodyNe :
          __eo_ite (__eo_is_str (__run_evaluate x))
            (__str_case_conv_rec
              (__str_flatten (__str_nary_intro (__run_evaluate x)))
              (Term.Boolean false))
            (__eo_mk_apply (Term.UOp UserOp.str_to_upper)
              (__run_evaluate x)) ≠ Term.Stuck := by
        simpa [__run_evaluate] using hRunNe
      have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
        intro hStuck
        apply hRunBodyNe
        simp [hStuck, __eo_is_str, __eo_is_str_internal,
          __eo_ite, __eo_mk_apply, native_and, native_not,
          native_ite, native_teq]
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunXEoSeqChar :
          __eo_typeof (__run_evaluate x) =
            Term.Apply (Term.UOp UserOp.Seq)
              (Term.UOp UserOp.Char) :=
        hXPres.trans hXEoSeqChar
      have hRunBodyTy :
          __eo_typeof
              (__eo_ite (__eo_is_str (__run_evaluate x))
                (__str_case_conv_rec
                  (__str_flatten
                    (__str_nary_intro (__run_evaluate x)))
                  (Term.Boolean false))
                (__eo_mk_apply (Term.UOp UserOp.str_to_upper)
                  (__run_evaluate x))) =
            Term.Apply (Term.UOp UserOp.Seq)
              (Term.UOp UserOp.Char) :=
        EvaluateProofInternal.eo_str_to_upper_body_typeof_seq_char (__run_evaluate x)
          hRunXEoSeqChar hRunBodyNe
      change
        __eo_typeof
            (__eo_ite (__eo_is_str (__run_evaluate x))
              (__str_case_conv_rec
                (__str_flatten
                  (__str_nary_intro (__run_evaluate x)))
                (Term.Boolean false))
              (__eo_mk_apply (Term.UOp UserOp.str_to_upper)
                (__run_evaluate x))) =
          __eo_typeof_str_to_lower (__eo_typeof x)
      rw [hRunBodyTy, hXEoSeqChar]
      rfl
  | str_rev =>
      have hRevNN :
          term_has_non_none_type
            (SmtTerm.str_rev (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      rcases seq_arg_of_non_none (op := SmtTerm.str_rev)
          (typeof_str_rev_eq (__eo_to_smt x)) hRevNN with
        ⟨T, hXTySeq⟩
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTySeq]
        simp
      rcases EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq x hXTrans hXTySeq with
        ⟨U, hXEoSeq, _hUSmt⟩
      have hRunBodyNe :
          __eo_ite (__eo_is_str (__run_evaluate x))
            (__str_nary_elim
              (__str_collect
                (__eo_list_rev (Term.UOp UserOp.str_concat)
                  (__str_flatten
                    (__str_nary_intro (__run_evaluate x))))))
            (__eo_mk_apply (Term.UOp UserOp.str_rev)
              (__run_evaluate x)) ≠ Term.Stuck := by
        simpa [__run_evaluate] using hRunNe
      have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
        intro hStuck
        apply hRunBodyNe
        simp [hStuck, __eo_is_str, __eo_is_str_internal,
          __eo_ite, __eo_mk_apply, native_and, native_not,
          native_ite, native_teq]
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunXEoSeq :
          __eo_typeof (__run_evaluate x) =
            Term.Apply (Term.UOp UserOp.Seq) U :=
        hXPres.trans hXEoSeq
      have hRunBodyTy :
          __eo_typeof
              (__eo_ite (__eo_is_str (__run_evaluate x))
                (__str_nary_elim
                  (__str_collect
                    (__eo_list_rev (Term.UOp UserOp.str_concat)
                      (__str_flatten
                        (__str_nary_intro (__run_evaluate x))))))
                (__eo_mk_apply (Term.UOp UserOp.str_rev)
                  (__run_evaluate x))) =
            Term.Apply (Term.UOp UserOp.Seq) U :=
        EvaluateProofInternal.eo_str_rev_body_typeof_seq (__run_evaluate x) U
          hRunXEoSeq hRunBodyNe
      change
        __eo_typeof
            (__eo_ite (__eo_is_str (__run_evaluate x))
              (__str_nary_elim
                (__str_collect
                  (__eo_list_rev (Term.UOp UserOp.str_concat)
                    (__str_flatten
                      (__str_nary_intro (__run_evaluate x))))))
              (__eo_mk_apply (Term.UOp UserOp.str_rev)
                (__run_evaluate x))) =
          __eo_typeof_str_rev (__eo_typeof x)
      rw [hRunBodyTy, hXEoSeq]
      rfl
  | _ =>
    exact False.elim (hRun rfl)

theorem EvaluateProofInternal.run_evaluate_typeof_apply_binary_uop
    (op : UserOp) (y x : Term)
    (recY : EvaluateProofInternal.RunEvaluateTypeofGoal y)
    (recX : EvaluateProofInternal.RunEvaluateTypeofGoal x)
    (hRun :
      __run_evaluate (Term.Apply (Term.Apply (Term.UOp op) y) x) ≠
        Term.Apply (Term.Apply (Term.UOp op) y) x)
    (hTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp op) y) x))
    (hRunNe :
      __run_evaluate (Term.Apply (Term.Apply (Term.UOp op) y) x) ≠
        Term.Stuck) :
    __eo_typeof
        (__run_evaluate (Term.Apply (Term.Apply (Term.UOp op) y) x)) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) y) x) := by
  cases op with
  | eq =>
    rcases eq_operands_same_smt_type_of_eq_has_smt_translation
        y x hTrans with
      ⟨hYXTy, hYNonNone⟩
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      simpa [RuleProofs.eo_has_smt_translation] using
        hYNonNone
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      intro hXNone
      exact hYNonNone (hYXTy.trans hXNone)
    have hYMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        y hYTrans
    have hXMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        x hXTrans
    have hYEoValid :=
      TranslationProofs.eo_type_valid_typeof_of_smt_translation
        y hYTrans
    have hYEoEq :
        __eo_typeof y = __eo_typeof x := by
      have hEoSmt :
          __eo_to_smt_type (__eo_typeof y) =
            __eo_to_smt_type (__eo_typeof x) := by
        rw [← hYMatch, ← hXMatch]
        exact hYXTy
      exact EvaluateProofInternal.eo_to_smt_type_eq_of_top_valid hYEoValid hEoSmt
    have hRunEqNe :
        __run_evaluate
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq) y) x) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck := by
      intro hStuck
      apply hRunEqNe
      cases hx : __run_evaluate x <;>
        simp [__run_evaluate, hStuck, hx, __eo_ite,
          __eo_and, __eo_is_q, __eo_is_q_internal,
          __eo_is_z, __eo_is_z_internal, __eo_is_bin,
          __eo_is_bin_internal, __eo_is_str,
          __eo_is_str_internal, __eo_is_bool,
          __eo_is_bool_internal, __eo_mk_apply, native_ite,
          native_and, native_not, native_teq]
    have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
      intro hStuck
      apply hRunEqNe
      cases hy : __run_evaluate y <;>
        simp [__run_evaluate, hStuck, hy, __eo_ite,
          __eo_and, __eo_is_q, __eo_is_q_internal,
          __eo_is_z, __eo_is_z_internal, __eo_is_bin,
          __eo_is_bin_internal, __eo_is_str,
          __eo_is_str_internal, __eo_is_bool,
          __eo_is_bool_internal, __eo_mk_apply, native_ite,
          native_and, native_not, native_teq]
    have hYPres :=
      recY hYTrans hRunYNe
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunTyEq :
        __eo_typeof (__run_evaluate y) =
          __eo_typeof (__run_evaluate x) := by
      calc
        __eo_typeof (__run_evaluate y) = __eo_typeof y :=
          hYPres
        _ = __eo_typeof x := hYEoEq
        _ = __eo_typeof (__run_evaluate x) := hXPres.symm
    have hYTypeNe : __eo_typeof y ≠ Term.Stuck := by
      have hYMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          y hYTrans
      have hYTypeNN :
          __eo_to_smt_type (__eo_typeof y) ≠
            SmtType.None := by
        intro hNone
        exact hYTrans (hYMatch.trans hNone)
      exact
        TranslationProofs.eo_term_ne_stuck_of_smt_type_non_none
          (__eo_typeof y) hYTypeNN
    have hRunYTypeNe :
        __eo_typeof (__run_evaluate y) ≠ Term.Stuck := by
      rw [hYPres]
      exact hYTypeNe
    have hRunBodyTy :
        __eo_typeof
            (__run_evaluate
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.eq) y) x)) =
          Term.Bool :=
      EvaluateProofInternal.run_evaluate_apply_eq_typeof_bool_of_run_typeof_eq
        y x hRunTyEq hRunYTypeNe hRunEqNe
    have hOrigTy :
        __eo_typeof_eq (__eo_typeof y) (__eo_typeof x) =
          Term.Bool := by
      rw [hYEoEq]
      change
        __eo_typeof
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq) x) x) =
          Term.Bool
      exact EvaluateProofInternal.eo_typeof_eq_self_bool_of_has_smt_translation
        x hXTrans
    change
      __eo_typeof
          (__run_evaluate
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq) y) x)) =
        __eo_typeof_eq (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hOrigTy]
  | and =>
    have hAndBool :
        RuleProofs.eo_has_bool_type
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.and) y) x) :=
      EvaluateProofInternal.has_bool_type_and_of_has_translation y x hTrans
    have hYBool : RuleProofs.eo_has_bool_type y :=
      RuleProofs.eo_has_bool_type_and_left y x hAndBool
    have hXBool : RuleProofs.eo_has_bool_type x :=
      RuleProofs.eo_has_bool_type_and_right y x hAndBool
    have hYTrans : RuleProofs.eo_has_smt_translation y :=
      RuleProofs.eo_has_smt_translation_of_has_bool_type
        y hYBool
    have hXTrans : RuleProofs.eo_has_smt_translation x :=
      RuleProofs.eo_has_smt_translation_of_has_bool_type
        x hXBool
    have hYMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        y hYTrans
    have hXMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        x hXTrans
    have hYEoBool : __eo_typeof y = Term.Bool :=
      TranslationProofs.eo_to_smt_type_eq_bool
        (hYMatch.symm.trans hYBool)
    have hXEoBool : __eo_typeof x = Term.Bool :=
      TranslationProofs.eo_to_smt_type_eq_bool
        (hXMatch.symm.trans hXBool)
    have hRunAndNe :
        __eo_and (__run_evaluate y) (__run_evaluate x) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_and_left_ne_stuck hRunAndNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_and_right_ne_stuck hRunAndNe
    have hYPres :=
      recY hYTrans hRunYNe
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunYBool :
        __eo_typeof (__run_evaluate y) = Term.Bool :=
      hYPres.trans hYEoBool
    have hRunXBool :
        __eo_typeof (__run_evaluate x) = Term.Bool :=
      hXPres.trans hXEoBool
    have hRunBodyTy :
        __eo_typeof
            (__eo_and (__run_evaluate y)
              (__run_evaluate x)) =
          Term.Bool :=
      EvaluateProofInternal.eo_and_typeof_bool_of_args_bool
        (__run_evaluate y) (__run_evaluate x)
        hRunYBool hRunXBool hRunAndNe
    change
      __eo_typeof
          (__eo_and (__run_evaluate y)
            (__run_evaluate x)) =
        __eo_typeof_or (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hYEoBool, hXEoBool]
    rfl
  | or =>
    have hOrBool :
        RuleProofs.eo_has_bool_type
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.or) y) x) :=
      EvaluateProofInternal.has_bool_type_or_of_has_translation y x hTrans
    have hYBool : RuleProofs.eo_has_bool_type y :=
      EvaluateProofInternal.has_bool_type_or_left y x hOrBool
    have hXBool : RuleProofs.eo_has_bool_type x :=
      EvaluateProofInternal.has_bool_type_or_right y x hOrBool
    have hYTrans : RuleProofs.eo_has_smt_translation y :=
      RuleProofs.eo_has_smt_translation_of_has_bool_type
        y hYBool
    have hXTrans : RuleProofs.eo_has_smt_translation x :=
      RuleProofs.eo_has_smt_translation_of_has_bool_type
        x hXBool
    have hYMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        y hYTrans
    have hXMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        x hXTrans
    have hYEoBool : __eo_typeof y = Term.Bool :=
      TranslationProofs.eo_to_smt_type_eq_bool
        (hYMatch.symm.trans hYBool)
    have hXEoBool : __eo_typeof x = Term.Bool :=
      TranslationProofs.eo_to_smt_type_eq_bool
        (hXMatch.symm.trans hXBool)
    have hRunOrNe :
        __eo_or (__run_evaluate y) (__run_evaluate x) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_left_ne_stuck hRunOrNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_right_ne_stuck hRunOrNe
    have hYPres :=
      recY hYTrans hRunYNe
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunYBool :
        __eo_typeof (__run_evaluate y) = Term.Bool :=
      hYPres.trans hYEoBool
    have hRunXBool :
        __eo_typeof (__run_evaluate x) = Term.Bool :=
      hXPres.trans hXEoBool
    have hRunBodyTy :
        __eo_typeof
            (__eo_or (__run_evaluate y)
              (__run_evaluate x)) =
          Term.Bool :=
      EvaluateProofInternal.eo_or_typeof_bool_of_args_bool
        (__run_evaluate y) (__run_evaluate x)
        hRunYBool hRunXBool hRunOrNe
    change
      __eo_typeof
          (__eo_or (__run_evaluate y)
            (__run_evaluate x)) =
        __eo_typeof_or (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hYEoBool, hXEoBool]
    rfl
  | xor =>
    have hXorBool :
        RuleProofs.eo_has_bool_type
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.xor) y) x) :=
      EvaluateProofInternal.has_bool_type_xor_of_has_translation y x hTrans
    have hYBool : RuleProofs.eo_has_bool_type y :=
      EvaluateProofInternal.has_bool_type_xor_left y x hXorBool
    have hXBool : RuleProofs.eo_has_bool_type x :=
      EvaluateProofInternal.has_bool_type_xor_right y x hXorBool
    have hYTrans : RuleProofs.eo_has_smt_translation y :=
      RuleProofs.eo_has_smt_translation_of_has_bool_type
        y hYBool
    have hXTrans : RuleProofs.eo_has_smt_translation x :=
      RuleProofs.eo_has_smt_translation_of_has_bool_type
        x hXBool
    have hYMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        y hYTrans
    have hXMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        x hXTrans
    have hYEoBool : __eo_typeof y = Term.Bool :=
      TranslationProofs.eo_to_smt_type_eq_bool
        (hYMatch.symm.trans hYBool)
    have hXEoBool : __eo_typeof x = Term.Bool :=
      TranslationProofs.eo_to_smt_type_eq_bool
        (hXMatch.symm.trans hXBool)
    have hRunXorNe :
        __eo_xor (__run_evaluate y) (__run_evaluate x) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_xor_left_ne_stuck hRunXorNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_xor_right_ne_stuck hRunXorNe
    have hYPres :=
      recY hYTrans hRunYNe
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunYBool :
        __eo_typeof (__run_evaluate y) = Term.Bool :=
      hYPres.trans hYEoBool
    have hRunXBool :
        __eo_typeof (__run_evaluate x) = Term.Bool :=
      hXPres.trans hXEoBool
    have hRunBodyTy :
        __eo_typeof
            (__eo_xor (__run_evaluate y)
              (__run_evaluate x)) =
          Term.Bool :=
      EvaluateProofInternal.eo_xor_typeof_bool_of_args_bool
        (__run_evaluate y) (__run_evaluate x)
        hRunYBool hRunXBool hRunXorNe
    change
      __eo_typeof
          (__eo_xor (__run_evaluate y)
            (__run_evaluate x)) =
        __eo_typeof_or (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hYEoBool, hXEoBool]
    rfl
  | imp =>
    have hImpBool :
        RuleProofs.eo_has_bool_type
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.imp) y) x) :=
      EvaluateProofInternal.has_bool_type_imp_of_has_translation y x hTrans
    have hYBool : RuleProofs.eo_has_bool_type y :=
      EvaluateProofInternal.has_bool_type_imp_left y x hImpBool
    have hXBool : RuleProofs.eo_has_bool_type x :=
      EvaluateProofInternal.has_bool_type_imp_right y x hImpBool
    have hYTrans : RuleProofs.eo_has_smt_translation y :=
      RuleProofs.eo_has_smt_translation_of_has_bool_type
        y hYBool
    have hXTrans : RuleProofs.eo_has_smt_translation x :=
      RuleProofs.eo_has_smt_translation_of_has_bool_type
        x hXBool
    have hYMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        y hYTrans
    have hXMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        x hXTrans
    have hYEoBool : __eo_typeof y = Term.Bool :=
      TranslationProofs.eo_to_smt_type_eq_bool
        (hYMatch.symm.trans hYBool)
    have hXEoBool : __eo_typeof x = Term.Bool :=
      TranslationProofs.eo_to_smt_type_eq_bool
        (hXMatch.symm.trans hXBool)
    have hRunImpNe :
        __eo_or (__eo_not (__run_evaluate y))
            (__run_evaluate x) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunNotYNe :
        __eo_not (__run_evaluate y) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_left_ne_stuck hRunImpNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_not_arg_ne_stuck hRunNotYNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_right_ne_stuck hRunImpNe
    have hYPres :=
      recY hYTrans hRunYNe
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunYBool :
        __eo_typeof (__run_evaluate y) = Term.Bool :=
      hYPres.trans hYEoBool
    have hRunXBool :
        __eo_typeof (__run_evaluate x) = Term.Bool :=
      hXPres.trans hXEoBool
    have hRunNotYBool :
        __eo_typeof (__eo_not (__run_evaluate y)) =
          Term.Bool :=
      EvaluateProofInternal.eo_not_typeof_bool_of_arg_bool
        (__run_evaluate y) hRunYBool hRunNotYNe
    have hRunBodyTy :
        __eo_typeof
            (__eo_or (__eo_not (__run_evaluate y))
              (__run_evaluate x)) =
          Term.Bool :=
      EvaluateProofInternal.eo_or_typeof_bool_of_args_bool
        (__eo_not (__run_evaluate y)) (__run_evaluate x)
        hRunNotYBool hRunXBool hRunImpNe
    change
      __eo_typeof
          (__eo_or (__eo_not (__run_evaluate y))
            (__run_evaluate x)) =
        __eo_typeof_or (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hYEoBool, hXEoBool]
    rfl
  | plus =>
    have hPlusNN :
        term_has_non_none_type
          (SmtTerm.plus (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunAddNe :
        __eo_add (__run_evaluate y) (__run_evaluate x) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_add_left_ne_stuck hRunAddNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_add_right_ne_stuck hRunAddNe
    rcases arith_binop_args_of_non_none
        (op := SmtTerm.plus) (t1 := __eo_to_smt y)
        (t2 := __eo_to_smt x)
        (typeof_plus_eq (__eo_to_smt y) (__eo_to_smt x))
        hPlusNN with
      hArgsInt | hArgsReal
    · rcases hArgsInt with ⟨hYTyInt, hXTyInt⟩
      have hYTrans : RuleProofs.eo_has_smt_translation y := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hYTyInt]
        simp
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyInt]
        simp
      have hYMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          y hYTrans
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hYEoInt : __eo_typeof y = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hYMatch.symm.trans hYTyInt)
      have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hXMatch.symm.trans hXTyInt)
      have hYPres :=
        recY hYTrans hRunYNe
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunYInt :
          __eo_typeof (__run_evaluate y) =
            Term.UOp UserOp.Int :=
        hYPres.trans hYEoInt
      have hRunXInt :
          __eo_typeof (__run_evaluate x) =
            Term.UOp UserOp.Int :=
        hXPres.trans hXEoInt
      have hRunBodyTy :
          __eo_typeof
              (__eo_add (__run_evaluate y)
                (__run_evaluate x)) =
            Term.UOp UserOp.Int :=
        EvaluateProofInternal.eo_add_typeof_int_of_args_int
          (__run_evaluate y) (__run_evaluate x)
          hRunYInt hRunXInt hRunAddNe
      change
        __eo_typeof
            (__eo_add (__run_evaluate y)
              (__run_evaluate x)) =
          __eo_typeof_plus (__eo_typeof y) (__eo_typeof x)
      rw [hRunBodyTy, hYEoInt, hXEoInt]
      simp [__eo_typeof_plus, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq,
        native_not, SmtEval.native_not]
    · rcases hArgsReal with ⟨hYTyReal, hXTyReal⟩
      have hYTrans : RuleProofs.eo_has_smt_translation y := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hYTyReal]
        simp
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyReal]
        simp
      have hYMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          y hYTrans
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hYEoReal : __eo_typeof y = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real
          (hYMatch.symm.trans hYTyReal)
      have hXEoReal : __eo_typeof x = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real
          (hXMatch.symm.trans hXTyReal)
      have hYPres :=
        recY hYTrans hRunYNe
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunYReal :
          __eo_typeof (__run_evaluate y) =
            Term.UOp UserOp.Real :=
        hYPres.trans hYEoReal
      have hRunXReal :
          __eo_typeof (__run_evaluate x) =
            Term.UOp UserOp.Real :=
        hXPres.trans hXEoReal
      have hRunBodyTy :
          __eo_typeof
              (__eo_add (__run_evaluate y)
                (__run_evaluate x)) =
            Term.UOp UserOp.Real :=
        EvaluateProofInternal.eo_add_typeof_real_of_args_real
          (__run_evaluate y) (__run_evaluate x)
          hRunYReal hRunXReal hRunAddNe
      change
        __eo_typeof
            (__eo_add (__run_evaluate y)
              (__run_evaluate x)) =
          __eo_typeof_plus (__eo_typeof y) (__eo_typeof x)
      rw [hRunBodyTy, hYEoReal, hXEoReal]
      simp [__eo_typeof_plus, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq,
        native_not, SmtEval.native_not]
  | mult =>
    have hMultNN :
        term_has_non_none_type
          (SmtTerm.mult (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunMulNe :
        __eo_mul (__run_evaluate y) (__run_evaluate x) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_mul_left_ne_stuck hRunMulNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_mul_right_ne_stuck hRunMulNe
    rcases arith_binop_args_of_non_none
        (op := SmtTerm.mult) (t1 := __eo_to_smt y)
        (t2 := __eo_to_smt x)
        (typeof_mult_eq (__eo_to_smt y) (__eo_to_smt x))
        hMultNN with
      hArgsInt | hArgsReal
    · rcases hArgsInt with ⟨hYTyInt, hXTyInt⟩
      have hYTrans : RuleProofs.eo_has_smt_translation y := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hYTyInt]
        simp
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyInt]
        simp
      have hYMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          y hYTrans
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hYEoInt : __eo_typeof y = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hYMatch.symm.trans hYTyInt)
      have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hXMatch.symm.trans hXTyInt)
      have hYPres :=
        recY hYTrans hRunYNe
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunYInt :
          __eo_typeof (__run_evaluate y) =
            Term.UOp UserOp.Int :=
        hYPres.trans hYEoInt
      have hRunXInt :
          __eo_typeof (__run_evaluate x) =
            Term.UOp UserOp.Int :=
        hXPres.trans hXEoInt
      have hRunBodyTy :
          __eo_typeof
              (__eo_mul (__run_evaluate y)
                (__run_evaluate x)) =
            Term.UOp UserOp.Int :=
        EvaluateProofInternal.eo_mul_typeof_int_of_args_int
          (__run_evaluate y) (__run_evaluate x)
          hRunYInt hRunXInt hRunMulNe
      change
        __eo_typeof
            (__eo_mul (__run_evaluate y)
              (__run_evaluate x)) =
          __eo_typeof_plus (__eo_typeof y) (__eo_typeof x)
      rw [hRunBodyTy, hYEoInt, hXEoInt]
      simp [__eo_typeof_plus, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq,
        native_not, SmtEval.native_not]
    · rcases hArgsReal with ⟨hYTyReal, hXTyReal⟩
      have hYTrans : RuleProofs.eo_has_smt_translation y := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hYTyReal]
        simp
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyReal]
        simp
      have hYMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          y hYTrans
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hYEoReal : __eo_typeof y = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real
          (hYMatch.symm.trans hYTyReal)
      have hXEoReal : __eo_typeof x = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real
          (hXMatch.symm.trans hXTyReal)
      have hYPres :=
        recY hYTrans hRunYNe
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunYReal :
          __eo_typeof (__run_evaluate y) =
            Term.UOp UserOp.Real :=
        hYPres.trans hYEoReal
      have hRunXReal :
          __eo_typeof (__run_evaluate x) =
            Term.UOp UserOp.Real :=
        hXPres.trans hXEoReal
      have hRunBodyTy :
          __eo_typeof
              (__eo_mul (__run_evaluate y)
                (__run_evaluate x)) =
            Term.UOp UserOp.Real :=
        EvaluateProofInternal.eo_mul_typeof_real_of_args_real
          (__run_evaluate y) (__run_evaluate x)
          hRunYReal hRunXReal hRunMulNe
      change
        __eo_typeof
            (__eo_mul (__run_evaluate y)
              (__run_evaluate x)) =
          __eo_typeof_plus (__eo_typeof y) (__eo_typeof x)
      rw [hRunBodyTy, hYEoReal, hXEoReal]
      simp [__eo_typeof_plus, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq,
        native_not, SmtEval.native_not]
  | neg =>
    have hNegNN :
        term_has_non_none_type
          (SmtTerm.neg (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunSubNe :
        __eo_add (__run_evaluate y)
            (__eo_neg (__run_evaluate x)) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_add_left_ne_stuck hRunSubNe
    have hRunNegXNe :
        __eo_neg (__run_evaluate x) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_add_right_ne_stuck hRunSubNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_neg_arg_ne_stuck hRunNegXNe
    rcases arith_binop_args_of_non_none
        (op := SmtTerm.neg) (t1 := __eo_to_smt y)
        (t2 := __eo_to_smt x)
        (typeof_neg_eq (__eo_to_smt y) (__eo_to_smt x))
        hNegNN with
      hArgsInt | hArgsReal
    · rcases hArgsInt with ⟨hYTyInt, hXTyInt⟩
      have hYTrans : RuleProofs.eo_has_smt_translation y := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hYTyInt]
        simp
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyInt]
        simp
      have hYMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          y hYTrans
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hYEoInt : __eo_typeof y = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hYMatch.symm.trans hYTyInt)
      have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hXMatch.symm.trans hXTyInt)
      have hYPres :=
        recY hYTrans hRunYNe
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunYInt :
          __eo_typeof (__run_evaluate y) =
            Term.UOp UserOp.Int :=
        hYPres.trans hYEoInt
      have hRunXInt :
          __eo_typeof (__run_evaluate x) =
            Term.UOp UserOp.Int :=
        hXPres.trans hXEoInt
      have hRunNegXInt :
          __eo_typeof (__eo_neg (__run_evaluate x)) =
            Term.UOp UserOp.Int :=
        EvaluateProofInternal.eo_neg_typeof_int_of_arg_int
          (__run_evaluate x) hRunXInt hRunNegXNe
      have hRunBodyTy :
          __eo_typeof
              (__eo_add (__run_evaluate y)
                (__eo_neg (__run_evaluate x))) =
            Term.UOp UserOp.Int :=
        EvaluateProofInternal.eo_add_typeof_int_of_args_int
          (__run_evaluate y)
          (__eo_neg (__run_evaluate x))
          hRunYInt hRunNegXInt hRunSubNe
      change
        __eo_typeof
            (__eo_add (__run_evaluate y)
              (__eo_neg (__run_evaluate x))) =
          __eo_typeof_plus (__eo_typeof y) (__eo_typeof x)
      rw [hRunBodyTy, hYEoInt, hXEoInt]
      simp [__eo_typeof_plus, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq,
        native_not, SmtEval.native_not]
    · rcases hArgsReal with ⟨hYTyReal, hXTyReal⟩
      have hYTrans : RuleProofs.eo_has_smt_translation y := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hYTyReal]
        simp
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyReal]
        simp
      have hYMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          y hYTrans
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hYEoReal : __eo_typeof y = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real
          (hYMatch.symm.trans hYTyReal)
      have hXEoReal : __eo_typeof x = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real
          (hXMatch.symm.trans hXTyReal)
      have hYPres :=
        recY hYTrans hRunYNe
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunYReal :
          __eo_typeof (__run_evaluate y) =
            Term.UOp UserOp.Real :=
        hYPres.trans hYEoReal
      have hRunXReal :
          __eo_typeof (__run_evaluate x) =
            Term.UOp UserOp.Real :=
        hXPres.trans hXEoReal
      have hRunNegXReal :
          __eo_typeof (__eo_neg (__run_evaluate x)) =
            Term.UOp UserOp.Real :=
        EvaluateProofInternal.eo_neg_typeof_real_of_arg_real
          (__run_evaluate x) hRunXReal hRunNegXNe
      have hRunBodyTy :
          __eo_typeof
              (__eo_add (__run_evaluate y)
                (__eo_neg (__run_evaluate x))) =
            Term.UOp UserOp.Real :=
        EvaluateProofInternal.eo_add_typeof_real_of_args_real
          (__run_evaluate y)
          (__eo_neg (__run_evaluate x))
          hRunYReal hRunNegXReal hRunSubNe
      change
        __eo_typeof
            (__eo_add (__run_evaluate y)
              (__eo_neg (__run_evaluate x))) =
          __eo_typeof_plus (__eo_typeof y) (__eo_typeof x)
      rw [hRunBodyTy, hYEoReal, hXEoReal]
      simp [__eo_typeof_plus, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq,
        native_not, SmtEval.native_not]
  | lt =>
    have hLtNN :
        term_has_non_none_type
          (SmtTerm.lt (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunLtNe :
        __eo_is_neg
            (__eo_add (__run_evaluate y)
              (__eo_neg (__run_evaluate x))) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunAddNe :
        __eo_add (__run_evaluate y)
            (__eo_neg (__run_evaluate x)) ≠
          Term.Stuck :=
      EvaluateProofInternal.eo_is_neg_arg_ne_stuck hRunLtNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_add_left_ne_stuck hRunAddNe
    have hRunNegXNe :
        __eo_neg (__run_evaluate x) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_add_right_ne_stuck hRunAddNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_neg_arg_ne_stuck hRunNegXNe
    rcases arith_binop_ret_bool_args_of_non_none
        (op := SmtTerm.lt) (t1 := __eo_to_smt y)
        (t2 := __eo_to_smt x)
        (typeof_lt_eq (__eo_to_smt y) (__eo_to_smt x))
        hLtNN with
      hArgsInt | hArgsReal
    · rcases hArgsInt with ⟨hYTyInt, hXTyInt⟩
      have hYTrans : RuleProofs.eo_has_smt_translation y := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hYTyInt]
        simp
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyInt]
        simp
      have hYMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          y hYTrans
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hYEoInt : __eo_typeof y = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hYMatch.symm.trans hYTyInt)
      have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hXMatch.symm.trans hXTyInt)
      have hYPres :=
        recY hYTrans hRunYNe
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunYInt :
          __eo_typeof (__run_evaluate y) =
            Term.UOp UserOp.Int :=
        hYPres.trans hYEoInt
      have hRunXInt :
          __eo_typeof (__run_evaluate x) =
            Term.UOp UserOp.Int :=
        hXPres.trans hXEoInt
      have hRunNegXInt :
          __eo_typeof (__eo_neg (__run_evaluate x)) =
            Term.UOp UserOp.Int :=
        EvaluateProofInternal.eo_neg_typeof_int_of_arg_int
          (__run_evaluate x) hRunXInt hRunNegXNe
      have hRunDiffTy :
          __eo_typeof
              (__eo_add (__run_evaluate y)
                (__eo_neg (__run_evaluate x))) =
            Term.UOp UserOp.Int :=
        EvaluateProofInternal.eo_add_typeof_int_of_args_int
          (__run_evaluate y)
          (__eo_neg (__run_evaluate x))
          hRunYInt hRunNegXInt hRunAddNe
      have hRunBodyTy :
          __eo_typeof
              (__eo_is_neg
                (__eo_add (__run_evaluate y)
                  (__eo_neg (__run_evaluate x)))) =
            Term.Bool :=
        EvaluateProofInternal.eo_is_neg_typeof_bool_of_arg_int
          (__eo_add (__run_evaluate y)
            (__eo_neg (__run_evaluate x)))
          hRunDiffTy hRunLtNe
      change
        __eo_typeof
            (__eo_is_neg
              (__eo_add (__run_evaluate y)
                (__eo_neg (__run_evaluate x)))) =
          __eo_typeof_lt (__eo_typeof y) (__eo_typeof x)
      rw [hRunBodyTy, hYEoInt, hXEoInt]
      simp [__eo_typeof_lt, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq,
        native_not, SmtEval.native_not]
    · rcases hArgsReal with ⟨hYTyReal, hXTyReal⟩
      have hYTrans : RuleProofs.eo_has_smt_translation y := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hYTyReal]
        simp
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyReal]
        simp
      have hYMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          y hYTrans
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hYEoReal : __eo_typeof y = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real
          (hYMatch.symm.trans hYTyReal)
      have hXEoReal : __eo_typeof x = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real
          (hXMatch.symm.trans hXTyReal)
      have hYPres :=
        recY hYTrans hRunYNe
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunYReal :
          __eo_typeof (__run_evaluate y) =
            Term.UOp UserOp.Real :=
        hYPres.trans hYEoReal
      have hRunXReal :
          __eo_typeof (__run_evaluate x) =
            Term.UOp UserOp.Real :=
        hXPres.trans hXEoReal
      have hRunNegXReal :
          __eo_typeof (__eo_neg (__run_evaluate x)) =
            Term.UOp UserOp.Real :=
        EvaluateProofInternal.eo_neg_typeof_real_of_arg_real
          (__run_evaluate x) hRunXReal hRunNegXNe
      have hRunDiffTy :
          __eo_typeof
              (__eo_add (__run_evaluate y)
                (__eo_neg (__run_evaluate x))) =
            Term.UOp UserOp.Real :=
        EvaluateProofInternal.eo_add_typeof_real_of_args_real
          (__run_evaluate y)
          (__eo_neg (__run_evaluate x))
          hRunYReal hRunNegXReal hRunAddNe
      have hRunBodyTy :
          __eo_typeof
              (__eo_is_neg
                (__eo_add (__run_evaluate y)
                  (__eo_neg (__run_evaluate x)))) =
            Term.Bool :=
        EvaluateProofInternal.eo_is_neg_typeof_bool_of_arg_real
          (__eo_add (__run_evaluate y)
            (__eo_neg (__run_evaluate x)))
          hRunDiffTy hRunLtNe
      change
        __eo_typeof
            (__eo_is_neg
              (__eo_add (__run_evaluate y)
                (__eo_neg (__run_evaluate x)))) =
          __eo_typeof_lt (__eo_typeof y) (__eo_typeof x)
      rw [hRunBodyTy, hYEoReal, hXEoReal]
      simp [__eo_typeof_lt, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq,
        native_not, SmtEval.native_not]
  | gt =>
    have hGtNN :
        term_has_non_none_type
          (SmtTerm.gt (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunGtNe :
        __eo_is_neg
            (__eo_add (__run_evaluate x)
              (__eo_neg (__run_evaluate y))) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunAddNe :
        __eo_add (__run_evaluate x)
            (__eo_neg (__run_evaluate y)) ≠
          Term.Stuck :=
      EvaluateProofInternal.eo_is_neg_arg_ne_stuck hRunGtNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_add_left_ne_stuck hRunAddNe
    have hRunNegYNe :
        __eo_neg (__run_evaluate y) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_add_right_ne_stuck hRunAddNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_neg_arg_ne_stuck hRunNegYNe
    rcases arith_binop_ret_bool_args_of_non_none
        (op := SmtTerm.gt) (t1 := __eo_to_smt y)
        (t2 := __eo_to_smt x)
        (typeof_gt_eq (__eo_to_smt y) (__eo_to_smt x))
        hGtNN with
      hArgsInt | hArgsReal
    · rcases hArgsInt with ⟨hYTyInt, hXTyInt⟩
      have hYTrans : RuleProofs.eo_has_smt_translation y := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hYTyInt]
        simp
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyInt]
        simp
      have hYMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          y hYTrans
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hYEoInt : __eo_typeof y = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hYMatch.symm.trans hYTyInt)
      have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hXMatch.symm.trans hXTyInt)
      have hYPres :=
        recY hYTrans hRunYNe
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunYInt :
          __eo_typeof (__run_evaluate y) =
            Term.UOp UserOp.Int :=
        hYPres.trans hYEoInt
      have hRunXInt :
          __eo_typeof (__run_evaluate x) =
            Term.UOp UserOp.Int :=
        hXPres.trans hXEoInt
      have hRunNegYInt :
          __eo_typeof (__eo_neg (__run_evaluate y)) =
            Term.UOp UserOp.Int :=
        EvaluateProofInternal.eo_neg_typeof_int_of_arg_int
          (__run_evaluate y) hRunYInt hRunNegYNe
      have hRunDiffTy :
          __eo_typeof
              (__eo_add (__run_evaluate x)
                (__eo_neg (__run_evaluate y))) =
            Term.UOp UserOp.Int :=
        EvaluateProofInternal.eo_add_typeof_int_of_args_int
          (__run_evaluate x)
          (__eo_neg (__run_evaluate y))
          hRunXInt hRunNegYInt hRunAddNe
      have hRunBodyTy :
          __eo_typeof
              (__eo_is_neg
                (__eo_add (__run_evaluate x)
                  (__eo_neg (__run_evaluate y)))) =
            Term.Bool :=
        EvaluateProofInternal.eo_is_neg_typeof_bool_of_arg_int
          (__eo_add (__run_evaluate x)
            (__eo_neg (__run_evaluate y)))
          hRunDiffTy hRunGtNe
      change
        __eo_typeof
            (__eo_is_neg
              (__eo_add (__run_evaluate x)
                (__eo_neg (__run_evaluate y)))) =
          __eo_typeof_lt (__eo_typeof y) (__eo_typeof x)
      rw [hRunBodyTy, hYEoInt, hXEoInt]
      simp [__eo_typeof_lt, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq,
        native_not, SmtEval.native_not]
    · rcases hArgsReal with ⟨hYTyReal, hXTyReal⟩
      have hYTrans : RuleProofs.eo_has_smt_translation y := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hYTyReal]
        simp
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyReal]
        simp
      have hYMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          y hYTrans
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hYEoReal : __eo_typeof y = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real
          (hYMatch.symm.trans hYTyReal)
      have hXEoReal : __eo_typeof x = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real
          (hXMatch.symm.trans hXTyReal)
      have hYPres :=
        recY hYTrans hRunYNe
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunYReal :
          __eo_typeof (__run_evaluate y) =
            Term.UOp UserOp.Real :=
        hYPres.trans hYEoReal
      have hRunXReal :
          __eo_typeof (__run_evaluate x) =
            Term.UOp UserOp.Real :=
        hXPres.trans hXEoReal
      have hRunNegYReal :
          __eo_typeof (__eo_neg (__run_evaluate y)) =
            Term.UOp UserOp.Real :=
        EvaluateProofInternal.eo_neg_typeof_real_of_arg_real
          (__run_evaluate y) hRunYReal hRunNegYNe
      have hRunDiffTy :
          __eo_typeof
              (__eo_add (__run_evaluate x)
                (__eo_neg (__run_evaluate y))) =
            Term.UOp UserOp.Real :=
        EvaluateProofInternal.eo_add_typeof_real_of_args_real
          (__run_evaluate x)
          (__eo_neg (__run_evaluate y))
          hRunXReal hRunNegYReal hRunAddNe
      have hRunBodyTy :
          __eo_typeof
              (__eo_is_neg
                (__eo_add (__run_evaluate x)
                  (__eo_neg (__run_evaluate y)))) =
            Term.Bool :=
        EvaluateProofInternal.eo_is_neg_typeof_bool_of_arg_real
          (__eo_add (__run_evaluate x)
            (__eo_neg (__run_evaluate y)))
          hRunDiffTy hRunGtNe
      change
        __eo_typeof
            (__eo_is_neg
              (__eo_add (__run_evaluate x)
                (__eo_neg (__run_evaluate y)))) =
          __eo_typeof_lt (__eo_typeof y) (__eo_typeof x)
      rw [hRunBodyTy, hYEoReal, hXEoReal]
      simp [__eo_typeof_lt, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq,
        native_not, SmtEval.native_not]
  | leq =>
    have hLeqNN :
        term_has_non_none_type
          (SmtTerm.leq (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunLeqNe :
        (let d :=
          __eo_add (__run_evaluate y)
            (__eo_neg (__run_evaluate x))
         __eo_or (__eo_is_neg d)
          (__eo_eq (__eo_to_q d)
            (Term.Rational (native_mk_rational 0 1)))) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunIsNegNe :
        __eo_is_neg
            (__eo_add (__run_evaluate y)
              (__eo_neg (__run_evaluate x))) ≠
          Term.Stuck := by
      exact EvaluateProofInternal.eo_or_left_ne_stuck (by
        simpa using hRunLeqNe)
    have hRunAddNe :
        __eo_add (__run_evaluate y)
            (__eo_neg (__run_evaluate x)) ≠
          Term.Stuck :=
      EvaluateProofInternal.eo_is_neg_arg_ne_stuck hRunIsNegNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_add_left_ne_stuck hRunAddNe
    have hRunNegXNe :
        __eo_neg (__run_evaluate x) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_add_right_ne_stuck hRunAddNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_neg_arg_ne_stuck hRunNegXNe
    rcases arith_binop_ret_bool_args_of_non_none
        (op := SmtTerm.leq) (t1 := __eo_to_smt y)
        (t2 := __eo_to_smt x)
        (typeof_leq_eq (__eo_to_smt y) (__eo_to_smt x))
        hLeqNN with
      hArgsInt | hArgsReal
    · rcases hArgsInt with ⟨hYTyInt, hXTyInt⟩
      have hYTrans : RuleProofs.eo_has_smt_translation y := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hYTyInt]
        simp
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyInt]
        simp
      have hYMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          y hYTrans
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hYEoInt : __eo_typeof y = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hYMatch.symm.trans hYTyInt)
      have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hXMatch.symm.trans hXTyInt)
      have hYPres :=
        recY hYTrans hRunYNe
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunYInt :
          __eo_typeof (__run_evaluate y) =
            Term.UOp UserOp.Int :=
        hYPres.trans hYEoInt
      have hRunXInt :
          __eo_typeof (__run_evaluate x) =
            Term.UOp UserOp.Int :=
        hXPres.trans hXEoInt
      have hRunBodyTy :
          __eo_typeof
              (let d :=
                __eo_add (__run_evaluate y)
                  (__eo_neg (__run_evaluate x))
               __eo_or (__eo_is_neg d)
                (__eo_eq (__eo_to_q d)
                  (Term.Rational
                    (native_mk_rational 0 1)))) =
            Term.Bool :=
        EvaluateProofInternal.eo_leq_body_typeof_bool_of_int_args
          (__run_evaluate y) (__run_evaluate x)
          hRunYInt hRunXInt hRunLeqNe
      change
        __eo_typeof
            (let d :=
              __eo_add (__run_evaluate y)
                (__eo_neg (__run_evaluate x))
             __eo_or (__eo_is_neg d)
              (__eo_eq (__eo_to_q d)
                (Term.Rational
                  (native_mk_rational 0 1)))) =
          __eo_typeof_lt (__eo_typeof y) (__eo_typeof x)
      rw [hRunBodyTy, hYEoInt, hXEoInt]
      simp [__eo_typeof_lt, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq,
        native_not, SmtEval.native_not]
    · rcases hArgsReal with ⟨hYTyReal, hXTyReal⟩
      have hYTrans : RuleProofs.eo_has_smt_translation y := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hYTyReal]
        simp
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyReal]
        simp
      have hYMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          y hYTrans
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hYEoReal : __eo_typeof y = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real
          (hYMatch.symm.trans hYTyReal)
      have hXEoReal : __eo_typeof x = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real
          (hXMatch.symm.trans hXTyReal)
      have hYPres :=
        recY hYTrans hRunYNe
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunYReal :
          __eo_typeof (__run_evaluate y) =
            Term.UOp UserOp.Real :=
        hYPres.trans hYEoReal
      have hRunXReal :
          __eo_typeof (__run_evaluate x) =
            Term.UOp UserOp.Real :=
        hXPres.trans hXEoReal
      have hRunBodyTy :
          __eo_typeof
              (let d :=
                __eo_add (__run_evaluate y)
                  (__eo_neg (__run_evaluate x))
               __eo_or (__eo_is_neg d)
                (__eo_eq (__eo_to_q d)
                  (Term.Rational
                    (native_mk_rational 0 1)))) =
            Term.Bool :=
        EvaluateProofInternal.eo_leq_body_typeof_bool_of_real_args
          (__run_evaluate y) (__run_evaluate x)
          hRunYReal hRunXReal hRunLeqNe
      change
        __eo_typeof
            (let d :=
              __eo_add (__run_evaluate y)
                (__eo_neg (__run_evaluate x))
             __eo_or (__eo_is_neg d)
              (__eo_eq (__eo_to_q d)
                (Term.Rational
                  (native_mk_rational 0 1)))) =
          __eo_typeof_lt (__eo_typeof y) (__eo_typeof x)
      rw [hRunBodyTy, hYEoReal, hXEoReal]
      simp [__eo_typeof_lt, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq,
        native_not, SmtEval.native_not]
  | geq =>
    have hGeqNN :
        term_has_non_none_type
          (SmtTerm.geq (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunGeqNe :
        (let d :=
          __eo_add (__run_evaluate x)
            (__eo_neg (__run_evaluate y))
         __eo_or (__eo_is_neg d)
          (__eo_eq (__eo_to_q d)
            (Term.Rational (native_mk_rational 0 1)))) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunIsNegNe :
        __eo_is_neg
            (__eo_add (__run_evaluate x)
              (__eo_neg (__run_evaluate y))) ≠
          Term.Stuck := by
      exact EvaluateProofInternal.eo_or_left_ne_stuck (by
        simpa using hRunGeqNe)
    have hRunAddNe :
        __eo_add (__run_evaluate x)
            (__eo_neg (__run_evaluate y)) ≠
          Term.Stuck :=
      EvaluateProofInternal.eo_is_neg_arg_ne_stuck hRunIsNegNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_add_left_ne_stuck hRunAddNe
    have hRunNegYNe :
        __eo_neg (__run_evaluate y) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_add_right_ne_stuck hRunAddNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_neg_arg_ne_stuck hRunNegYNe
    rcases arith_binop_ret_bool_args_of_non_none
        (op := SmtTerm.geq) (t1 := __eo_to_smt y)
        (t2 := __eo_to_smt x)
        (typeof_geq_eq (__eo_to_smt y) (__eo_to_smt x))
        hGeqNN with
      hArgsInt | hArgsReal
    · rcases hArgsInt with ⟨hYTyInt, hXTyInt⟩
      have hYTrans : RuleProofs.eo_has_smt_translation y := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hYTyInt]
        simp
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyInt]
        simp
      have hYMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          y hYTrans
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hYEoInt : __eo_typeof y = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hYMatch.symm.trans hYTyInt)
      have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hXMatch.symm.trans hXTyInt)
      have hYPres :=
        recY hYTrans hRunYNe
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunYInt :
          __eo_typeof (__run_evaluate y) =
            Term.UOp UserOp.Int :=
        hYPres.trans hYEoInt
      have hRunXInt :
          __eo_typeof (__run_evaluate x) =
            Term.UOp UserOp.Int :=
        hXPres.trans hXEoInt
      have hRunBodyTy :
          __eo_typeof
              (let d :=
                __eo_add (__run_evaluate x)
                  (__eo_neg (__run_evaluate y))
               __eo_or (__eo_is_neg d)
                (__eo_eq (__eo_to_q d)
                  (Term.Rational
                    (native_mk_rational 0 1)))) =
            Term.Bool :=
        EvaluateProofInternal.eo_leq_body_typeof_bool_of_int_args
          (__run_evaluate x) (__run_evaluate y)
          hRunXInt hRunYInt hRunGeqNe
      change
        __eo_typeof
            (let d :=
              __eo_add (__run_evaluate x)
                (__eo_neg (__run_evaluate y))
             __eo_or (__eo_is_neg d)
              (__eo_eq (__eo_to_q d)
                (Term.Rational
                  (native_mk_rational 0 1)))) =
          __eo_typeof_lt (__eo_typeof y) (__eo_typeof x)
      rw [hRunBodyTy, hYEoInt, hXEoInt]
      simp [__eo_typeof_lt, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq,
        native_not, SmtEval.native_not]
    · rcases hArgsReal with ⟨hYTyReal, hXTyReal⟩
      have hYTrans : RuleProofs.eo_has_smt_translation y := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hYTyReal]
        simp
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyReal]
        simp
      have hYMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          y hYTrans
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hYEoReal : __eo_typeof y = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real
          (hYMatch.symm.trans hYTyReal)
      have hXEoReal : __eo_typeof x = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real
          (hXMatch.symm.trans hXTyReal)
      have hYPres :=
        recY hYTrans hRunYNe
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunYReal :
          __eo_typeof (__run_evaluate y) =
            Term.UOp UserOp.Real :=
        hYPres.trans hYEoReal
      have hRunXReal :
          __eo_typeof (__run_evaluate x) =
            Term.UOp UserOp.Real :=
        hXPres.trans hXEoReal
      have hRunBodyTy :
          __eo_typeof
              (let d :=
                __eo_add (__run_evaluate x)
                  (__eo_neg (__run_evaluate y))
               __eo_or (__eo_is_neg d)
                (__eo_eq (__eo_to_q d)
                  (Term.Rational
                    (native_mk_rational 0 1)))) =
            Term.Bool :=
        EvaluateProofInternal.eo_leq_body_typeof_bool_of_real_args
          (__run_evaluate x) (__run_evaluate y)
          hRunXReal hRunYReal hRunGeqNe
      change
        __eo_typeof
            (let d :=
              __eo_add (__run_evaluate x)
                (__eo_neg (__run_evaluate y))
             __eo_or (__eo_is_neg d)
              (__eo_eq (__eo_to_q d)
                (Term.Rational
                  (native_mk_rational 0 1)))) =
          __eo_typeof_lt (__eo_typeof y) (__eo_typeof x)
      rw [hRunBodyTy, hYEoReal, hXEoReal]
      simp [__eo_typeof_lt, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq,
        native_not, SmtEval.native_not]
  | div =>
    have hDivNN :
        term_has_non_none_type
          (SmtTerm.div (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunDivNe :
        __eo_zdiv (__run_evaluate y) (__run_evaluate x) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_zdiv_left_ne_stuck hRunDivNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_zdiv_right_ne_stuck hRunDivNe
    rcases int_binop_args_of_non_none
        (op := SmtTerm.div) (t1 := __eo_to_smt y)
        (t2 := __eo_to_smt x) (R := SmtType.Int)
        (typeof_div_eq (__eo_to_smt y) (__eo_to_smt x))
        hDivNN with
      ⟨hYTyInt, hXTyInt⟩
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTyInt]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTyInt]
      simp
    have hYMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        y hYTrans
    have hXMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        x hXTrans
    have hYEoInt : __eo_typeof y = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int
        (hYMatch.symm.trans hYTyInt)
    have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int
        (hXMatch.symm.trans hXTyInt)
    have hYPres :=
      recY hYTrans hRunYNe
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunYInt :
        __eo_typeof (__run_evaluate y) =
          Term.UOp UserOp.Int :=
      hYPres.trans hYEoInt
    have hRunXInt :
        __eo_typeof (__run_evaluate x) =
          Term.UOp UserOp.Int :=
      hXPres.trans hXEoInt
    have hRunBodyTy :
        __eo_typeof
            (__eo_zdiv (__run_evaluate y)
              (__run_evaluate x)) =
          Term.UOp UserOp.Int :=
      EvaluateProofInternal.eo_zdiv_typeof_int_of_args_int_and_ne_stuck
        (__run_evaluate y) (__run_evaluate x)
        hRunYInt hRunXInt hRunDivNe
    change
      __eo_typeof
          (__eo_zdiv (__run_evaluate y)
            (__run_evaluate x)) =
        __eo_typeof_div (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hYEoInt, hXEoInt]
    rfl
  | mod =>
    have hModNN :
        term_has_non_none_type
          (SmtTerm.mod (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunModNe :
        __eo_zmod (__run_evaluate y) (__run_evaluate x) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_zmod_left_ne_stuck hRunModNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_zmod_right_ne_stuck hRunModNe
    rcases int_binop_args_of_non_none
        (op := SmtTerm.mod) (t1 := __eo_to_smt y)
        (t2 := __eo_to_smt x) (R := SmtType.Int)
        (typeof_mod_eq (__eo_to_smt y) (__eo_to_smt x))
        hModNN with
      ⟨hYTyInt, hXTyInt⟩
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTyInt]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTyInt]
      simp
    have hYMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        y hYTrans
    have hXMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        x hXTrans
    have hYEoInt : __eo_typeof y = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int
        (hYMatch.symm.trans hYTyInt)
    have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int
        (hXMatch.symm.trans hXTyInt)
    have hYPres :=
      recY hYTrans hRunYNe
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunYInt :
        __eo_typeof (__run_evaluate y) =
          Term.UOp UserOp.Int :=
      hYPres.trans hYEoInt
    have hRunXInt :
        __eo_typeof (__run_evaluate x) =
          Term.UOp UserOp.Int :=
      hXPres.trans hXEoInt
    have hRunBodyTy :
        __eo_typeof
            (__eo_zmod (__run_evaluate y)
              (__run_evaluate x)) =
          Term.UOp UserOp.Int :=
      EvaluateProofInternal.eo_zmod_typeof_int_of_args_int_and_ne_stuck
        (__run_evaluate y) (__run_evaluate x)
        hRunYInt hRunXInt hRunModNe
    change
      __eo_typeof
          (__eo_zmod (__run_evaluate y)
            (__run_evaluate x)) =
        __eo_typeof_div (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hYEoInt, hXEoInt]
    rfl
  | qdiv =>
    have hQDivNN :
        term_has_non_none_type
          (SmtTerm.qdiv (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunQDivNe :
        __eo_qdiv (__eo_to_q (__run_evaluate y))
            (__eo_to_q (__run_evaluate x)) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunToQYNe :
        __eo_to_q (__run_evaluate y) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_qdiv_left_ne_stuck hRunQDivNe
    have hRunToQXNe :
        __eo_to_q (__run_evaluate x) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_qdiv_right_ne_stuck hRunQDivNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_to_q_arg_ne_stuck hRunToQYNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_to_q_arg_ne_stuck hRunToQXNe
    rcases arith_binop_ret_args_of_non_none
        (op := SmtTerm.qdiv) (R := SmtType.Real)
        (t1 := __eo_to_smt y) (t2 := __eo_to_smt x)
        (typeof_qdiv_eq (__eo_to_smt y) (__eo_to_smt x))
        hQDivNN with
      hArgsInt | hArgsReal
    · rcases hArgsInt with ⟨hYTyInt, hXTyInt⟩
      have hYTrans : RuleProofs.eo_has_smt_translation y := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hYTyInt]
        simp
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyInt]
        simp
      have hYMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          y hYTrans
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hYEoInt : __eo_typeof y = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hYMatch.symm.trans hYTyInt)
      have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hXMatch.symm.trans hXTyInt)
      have hYPres :=
        recY hYTrans hRunYNe
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunYInt :
          __eo_typeof (__run_evaluate y) =
            Term.UOp UserOp.Int :=
        hYPres.trans hYEoInt
      have hRunXInt :
          __eo_typeof (__run_evaluate x) =
            Term.UOp UserOp.Int :=
        hXPres.trans hXEoInt
      have hRunToQYNe :
          __eo_to_q (__run_evaluate y) ≠ Term.Stuck :=
        EvaluateProofInternal.eo_qdiv_left_ne_stuck hRunQDivNe
      have hRunToQXNe :
          __eo_to_q (__run_evaluate x) ≠ Term.Stuck :=
        EvaluateProofInternal.eo_qdiv_right_ne_stuck hRunQDivNe
      have hRunToQYReal :
          __eo_typeof (__eo_to_q (__run_evaluate y)) =
            Term.UOp UserOp.Real :=
        EvaluateProofInternal.eo_to_q_typeof_real_of_arg_int
          (__run_evaluate y) hRunYInt hRunToQYNe
      have hRunToQXReal :
          __eo_typeof (__eo_to_q (__run_evaluate x)) =
            Term.UOp UserOp.Real :=
        EvaluateProofInternal.eo_to_q_typeof_real_of_arg_int
          (__run_evaluate x) hRunXInt hRunToQXNe
      have hRunBodyTy :
          __eo_typeof
              (__eo_qdiv
                (__eo_to_q (__run_evaluate y))
                (__eo_to_q (__run_evaluate x))) =
            Term.UOp UserOp.Real :=
        EvaluateProofInternal.eo_qdiv_typeof_real_of_ne_stuck
          (__eo_to_q (__run_evaluate y))
          (__eo_to_q (__run_evaluate x))
          hRunQDivNe
      change
        __eo_typeof
            (__eo_qdiv
              (__eo_to_q (__run_evaluate y))
              (__eo_to_q (__run_evaluate x))) =
          __eo_typeof_qdiv (__eo_typeof y) (__eo_typeof x)
      rw [hRunBodyTy, hYEoInt, hXEoInt]
      simp [__eo_typeof_qdiv, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq,
        native_not, SmtEval.native_not]
    · rcases hArgsReal with ⟨hYTyReal, hXTyReal⟩
      have hYTrans : RuleProofs.eo_has_smt_translation y := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hYTyReal]
        simp
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyReal]
        simp
      have hYMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          y hYTrans
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hYEoReal : __eo_typeof y = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real
          (hYMatch.symm.trans hYTyReal)
      have hXEoReal : __eo_typeof x = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real
          (hXMatch.symm.trans hXTyReal)
      have hYPres :=
        recY hYTrans hRunYNe
      have hXPres :=
        recX hXTrans hRunXNe
      have hRunYReal :
          __eo_typeof (__run_evaluate y) =
            Term.UOp UserOp.Real :=
        hYPres.trans hYEoReal
      have hRunXReal :
          __eo_typeof (__run_evaluate x) =
            Term.UOp UserOp.Real :=
        hXPres.trans hXEoReal
      have hRunToQYNe :
          __eo_to_q (__run_evaluate y) ≠ Term.Stuck :=
        EvaluateProofInternal.eo_qdiv_left_ne_stuck hRunQDivNe
      have hRunToQXNe :
          __eo_to_q (__run_evaluate x) ≠ Term.Stuck :=
        EvaluateProofInternal.eo_qdiv_right_ne_stuck hRunQDivNe
      have hRunToQYReal :
          __eo_typeof (__eo_to_q (__run_evaluate y)) =
            Term.UOp UserOp.Real :=
        EvaluateProofInternal.eo_to_q_typeof_real_of_arg_real
          (__run_evaluate y) hRunYReal hRunToQYNe
      have hRunToQXReal :
          __eo_typeof (__eo_to_q (__run_evaluate x)) =
            Term.UOp UserOp.Real :=
        EvaluateProofInternal.eo_to_q_typeof_real_of_arg_real
          (__run_evaluate x) hRunXReal hRunToQXNe
      have hRunBodyTy :
          __eo_typeof
              (__eo_qdiv
                (__eo_to_q (__run_evaluate y))
                (__eo_to_q (__run_evaluate x))) =
            Term.UOp UserOp.Real :=
        EvaluateProofInternal.eo_qdiv_typeof_real_of_ne_stuck
          (__eo_to_q (__run_evaluate y))
          (__eo_to_q (__run_evaluate x))
          hRunQDivNe
      change
        __eo_typeof
            (__eo_qdiv
              (__eo_to_q (__run_evaluate y))
              (__eo_to_q (__run_evaluate x))) =
          __eo_typeof_qdiv (__eo_typeof y) (__eo_typeof x)
      rw [hRunBodyTy, hYEoReal, hXEoReal]
      simp [__eo_typeof_qdiv, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq,
        native_not, SmtEval.native_not]
  | qdiv_total =>
    have hQDivTotalNN :
        term_has_non_none_type
          (SmtTerm.qdiv_total (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunQDivTotalNe :
        __eo_ite
            (__eo_eq (__eo_to_q (__run_evaluate x))
              (Term.Rational (native_mk_rational 0 1)))
            (Term.Rational (native_mk_rational 0 1))
            (__eo_qdiv (__eo_to_q (__run_evaluate y))
              (__eo_to_q (__run_evaluate x))) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    rcases arith_binop_ret_args_of_non_none
        (op := SmtTerm.qdiv_total) (R := SmtType.Real)
        (t1 := __eo_to_smt y) (t2 := __eo_to_smt x)
        (typeof_qdiv_total_eq (__eo_to_smt y)
          (__eo_to_smt x))
        hQDivTotalNN with
      hArgsInt | hArgsReal
    · rcases hArgsInt with ⟨hYTyInt, hXTyInt⟩
      have hYTrans : RuleProofs.eo_has_smt_translation y := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hYTyInt]
        simp
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyInt]
        simp
      have hYMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          y hYTrans
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hYEoInt : __eo_typeof y = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hYMatch.symm.trans hYTyInt)
      have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hXMatch.symm.trans hXTyInt)
      have hRunBodyTy :
          __eo_typeof
              (__eo_ite
                (__eo_eq (__eo_to_q (__run_evaluate x))
                  (Term.Rational
                    (native_mk_rational 0 1)))
                (Term.Rational
                  (native_mk_rational 0 1))
                (__eo_qdiv
                  (__eo_to_q (__run_evaluate y))
                  (__eo_to_q (__run_evaluate x)))) =
            Term.UOp UserOp.Real :=
        EvaluateProofInternal.eo_qdiv_total_body_typeof_real_of_ne_stuck
          (__eo_to_q (__run_evaluate y))
          (__eo_to_q (__run_evaluate x))
          hRunQDivTotalNe
      change
        __eo_typeof
            (__eo_ite
              (__eo_eq (__eo_to_q (__run_evaluate x))
                (Term.Rational
                  (native_mk_rational 0 1)))
              (Term.Rational
                (native_mk_rational 0 1))
              (__eo_qdiv
                (__eo_to_q (__run_evaluate y))
                (__eo_to_q (__run_evaluate x)))) =
          __eo_typeof_qdiv (__eo_typeof y) (__eo_typeof x)
      rw [hRunBodyTy, hYEoInt, hXEoInt]
      simp [__eo_typeof_qdiv, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq,
        native_not, SmtEval.native_not]
    · rcases hArgsReal with ⟨hYTyReal, hXTyReal⟩
      have hYTrans : RuleProofs.eo_has_smt_translation y := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hYTyReal]
        simp
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyReal]
        simp
      have hYMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          y hYTrans
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hYEoReal : __eo_typeof y = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real
          (hYMatch.symm.trans hYTyReal)
      have hXEoReal : __eo_typeof x = Term.UOp UserOp.Real :=
        TranslationProofs.eo_to_smt_type_eq_real
          (hXMatch.symm.trans hXTyReal)
      have hRunBodyTy :
          __eo_typeof
              (__eo_ite
                (__eo_eq (__eo_to_q (__run_evaluate x))
                  (Term.Rational
                    (native_mk_rational 0 1)))
                (Term.Rational
                  (native_mk_rational 0 1))
                (__eo_qdiv
                  (__eo_to_q (__run_evaluate y))
                  (__eo_to_q (__run_evaluate x)))) =
            Term.UOp UserOp.Real :=
        EvaluateProofInternal.eo_qdiv_total_body_typeof_real_of_ne_stuck
          (__eo_to_q (__run_evaluate y))
          (__eo_to_q (__run_evaluate x))
          hRunQDivTotalNe
      change
        __eo_typeof
            (__eo_ite
              (__eo_eq (__eo_to_q (__run_evaluate x))
                (Term.Rational
                  (native_mk_rational 0 1)))
              (Term.Rational
                (native_mk_rational 0 1))
              (__eo_qdiv
                (__eo_to_q (__run_evaluate y))
                (__eo_to_q (__run_evaluate x)))) =
          __eo_typeof_qdiv (__eo_typeof y) (__eo_typeof x)
      rw [hRunBodyTy, hYEoReal, hXEoReal]
      simp [__eo_typeof_qdiv, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq,
        native_not, SmtEval.native_not]
  | div_total =>
    have hDivTotalNN :
        term_has_non_none_type
          (SmtTerm.div_total (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunDivTotalNe :
        __eo_ite
            (__eo_eq (__run_evaluate x) (Term.Numeral 0))
            (Term.Numeral 0)
            (__eo_zdiv (__run_evaluate y)
              (__run_evaluate x)) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hCondNe :
        __eo_eq (__run_evaluate x) (Term.Numeral 0) ≠
          Term.Stuck :=
      EvaluateProofInternal.eo_ite_cond_ne_stuck hRunDivTotalNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_eq_left_ne_stuck hCondNe
    rcases int_binop_args_of_non_none
        (op := SmtTerm.div_total)
        (t1 := __eo_to_smt y) (t2 := __eo_to_smt x)
        (R := SmtType.Int)
        (typeof_div_total_eq (__eo_to_smt y)
          (__eo_to_smt x))
        hDivTotalNN with
      ⟨hYTyInt, hXTyInt⟩
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTyInt]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTyInt]
      simp
    have hYMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        y hYTrans
    have hXMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        x hXTrans
    have hYEoInt : __eo_typeof y = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int
        (hYMatch.symm.trans hYTyInt)
    have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int
        (hXMatch.symm.trans hXTyInt)
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunXInt :
        __eo_typeof (__run_evaluate x) =
          Term.UOp UserOp.Int :=
      hXPres.trans hXEoInt
    have hRunBodyTy :
        __eo_typeof
            (__eo_ite
              (__eo_eq (__run_evaluate x)
                (Term.Numeral 0))
              (Term.Numeral 0)
              (__eo_zdiv (__run_evaluate y)
                (__run_evaluate x))) =
          Term.UOp UserOp.Int :=
      EvaluateProofInternal.eo_div_total_body_typeof_int_of_right_int
        (__run_evaluate y) (__run_evaluate x)
        hRunXInt hRunDivTotalNe
    change
      __eo_typeof
          (__eo_ite
            (__eo_eq (__run_evaluate x)
              (Term.Numeral 0))
            (Term.Numeral 0)
            (__eo_zdiv (__run_evaluate y)
              (__run_evaluate x))) =
        __eo_typeof_div (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hYEoInt, hXEoInt]
    rfl
  | mod_total =>
    have hModTotalNN :
        term_has_non_none_type
          (SmtTerm.mod_total (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunModTotalNe :
        __eo_ite
            (__eo_eq (__run_evaluate x) (Term.Numeral 0))
            (__run_evaluate y)
            (__eo_zmod (__run_evaluate y)
              (__run_evaluate x)) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hCondNe :
        __eo_eq (__run_evaluate x) (Term.Numeral 0) ≠
          Term.Stuck :=
      EvaluateProofInternal.eo_ite_cond_ne_stuck hRunModTotalNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_eq_left_ne_stuck hCondNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_mod_total_left_ne_stuck hRunModTotalNe
    rcases int_binop_args_of_non_none
        (op := SmtTerm.mod_total)
        (t1 := __eo_to_smt y) (t2 := __eo_to_smt x)
        (R := SmtType.Int)
        (typeof_mod_total_eq (__eo_to_smt y)
          (__eo_to_smt x))
        hModTotalNN with
      ⟨hYTyInt, hXTyInt⟩
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTyInt]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTyInt]
      simp
    have hYMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        y hYTrans
    have hXMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        x hXTrans
    have hYEoInt : __eo_typeof y = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int
        (hYMatch.symm.trans hYTyInt)
    have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int
        (hXMatch.symm.trans hXTyInt)
    have hYPres :=
      recY hYTrans hRunYNe
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunYInt :
        __eo_typeof (__run_evaluate y) =
          Term.UOp UserOp.Int :=
      hYPres.trans hYEoInt
    have hRunXInt :
        __eo_typeof (__run_evaluate x) =
          Term.UOp UserOp.Int :=
      hXPres.trans hXEoInt
    have hRunBodyTy :
        __eo_typeof
            (__eo_ite
              (__eo_eq (__run_evaluate x)
                (Term.Numeral 0))
              (__run_evaluate y)
              (__eo_zmod (__run_evaluate y)
                (__run_evaluate x))) =
          Term.UOp UserOp.Int :=
      EvaluateProofInternal.eo_mod_total_body_typeof_int_of_args_int
        (__run_evaluate y) (__run_evaluate x)
        hRunYInt hRunXInt hRunModTotalNe
    change
      __eo_typeof
          (__eo_ite
            (__eo_eq (__run_evaluate x)
              (Term.Numeral 0))
            (__run_evaluate y)
            (__eo_zmod (__run_evaluate y)
              (__run_evaluate x))) =
        __eo_typeof_div (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hYEoInt, hXEoInt]
    rfl
  | bvand =>
    have hBvAndNN :
        term_has_non_none_type
          (SmtTerm.bvand (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      simpa [RuleProofs.eo_has_smt_translation] using hTrans
    have hRunAndNe :
        __eo_and (__run_evaluate y) (__run_evaluate x) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_and_left_ne_stuck hRunAndNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_and_right_ne_stuck hRunAndNe
    rcases bv_binop_args_of_non_none
        (op := SmtTerm.bvand) (t1 := __eo_to_smt y)
        (t2 := __eo_to_smt x)
        (by rw [__smtx_typeof.eq_40]) hBvAndNN with
      ⟨w, hYTyBv, hXTyBv⟩
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTyBv]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTyBv]
      simp
    have hYMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        y hYTrans
    have hXMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        x hXTrans
    have hYEoBv :
        __eo_typeof y =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      TranslationProofs.eo_to_smt_type_eq_bitvec
        (hYMatch.symm.trans hYTyBv)
    have hXEoBv :
        __eo_typeof x =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      TranslationProofs.eo_to_smt_type_eq_bitvec
        (hXMatch.symm.trans hXTyBv)
    have hYPres :=
      recY hYTrans hRunYNe
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunYBv :
        __eo_typeof (__run_evaluate y) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      hYPres.trans hYEoBv
    have hRunXBv :
        __eo_typeof (__run_evaluate x) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      hXPres.trans hXEoBv
    have hRunBodyTy :
        __eo_typeof
            (__eo_and (__run_evaluate y)
              (__run_evaluate x)) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      EvaluateProofInternal.eo_and_typeof_bitvec_of_args_bitvec
        (__run_evaluate y) (__run_evaluate x)
        (native_nat_to_int w) hRunYBv hRunXBv hRunAndNe
    change
      __eo_typeof
          (__eo_and (__run_evaluate y)
            (__run_evaluate x)) =
        __eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hYEoBv, hXEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq,
      native_ite, native_teq, native_not]
  | bvor =>
    have hBvOrNN :
        term_has_non_none_type
          (SmtTerm.bvor (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      simpa [RuleProofs.eo_has_smt_translation] using hTrans
    have hRunOrNe :
        __eo_or (__run_evaluate y) (__run_evaluate x) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_left_ne_stuck hRunOrNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_right_ne_stuck hRunOrNe
    rcases bv_binop_args_of_non_none
        (op := SmtTerm.bvor) (t1 := __eo_to_smt y)
        (t2 := __eo_to_smt x)
        (by rw [__smtx_typeof.eq_41]) hBvOrNN with
      ⟨w, hYTyBv, hXTyBv⟩
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTyBv]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTyBv]
      simp
    have hYMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        y hYTrans
    have hXMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        x hXTrans
    have hYEoBv :
        __eo_typeof y =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      TranslationProofs.eo_to_smt_type_eq_bitvec
        (hYMatch.symm.trans hYTyBv)
    have hXEoBv :
        __eo_typeof x =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      TranslationProofs.eo_to_smt_type_eq_bitvec
        (hXMatch.symm.trans hXTyBv)
    have hYPres :=
      recY hYTrans hRunYNe
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunYBv :
        __eo_typeof (__run_evaluate y) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      hYPres.trans hYEoBv
    have hRunXBv :
        __eo_typeof (__run_evaluate x) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      hXPres.trans hXEoBv
    have hRunBodyTy :
        __eo_typeof
            (__eo_or (__run_evaluate y)
              (__run_evaluate x)) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      EvaluateProofInternal.eo_or_typeof_bitvec_of_args_bitvec
        (__run_evaluate y) (__run_evaluate x)
        (native_nat_to_int w) hRunYBv hRunXBv hRunOrNe
    change
      __eo_typeof
          (__eo_or (__run_evaluate y)
            (__run_evaluate x)) =
        __eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hYEoBv, hXEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq,
      native_ite, native_teq, native_not]
  | bvxor =>
    have hBvXorNN :
        term_has_non_none_type
          (SmtTerm.bvxor (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      simpa [RuleProofs.eo_has_smt_translation] using hTrans
    have hRunXorNe :
        __eo_xor (__run_evaluate y) (__run_evaluate x) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_xor_left_ne_stuck hRunXorNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_xor_right_ne_stuck hRunXorNe
    rcases bv_binop_args_of_non_none
        (op := SmtTerm.bvxor) (t1 := __eo_to_smt y)
        (t2 := __eo_to_smt x)
        (by rw [__smtx_typeof.eq_44]) hBvXorNN with
      ⟨w, hYTyBv, hXTyBv⟩
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTyBv]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTyBv]
      simp
    have hYMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        y hYTrans
    have hXMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        x hXTrans
    have hYEoBv :
        __eo_typeof y =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      TranslationProofs.eo_to_smt_type_eq_bitvec
        (hYMatch.symm.trans hYTyBv)
    have hXEoBv :
        __eo_typeof x =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      TranslationProofs.eo_to_smt_type_eq_bitvec
        (hXMatch.symm.trans hXTyBv)
    have hYPres :=
      recY hYTrans hRunYNe
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunYBv :
        __eo_typeof (__run_evaluate y) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      hYPres.trans hYEoBv
    have hRunXBv :
        __eo_typeof (__run_evaluate x) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      hXPres.trans hXEoBv
    have hRunBodyTy :
        __eo_typeof
            (__eo_xor (__run_evaluate y)
              (__run_evaluate x)) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      EvaluateProofInternal.eo_xor_typeof_bitvec_of_args_bitvec
        (__run_evaluate y) (__run_evaluate x)
        (native_nat_to_int w) hRunYBv hRunXBv hRunXorNe
    change
      __eo_typeof
          (__eo_xor (__run_evaluate y)
            (__run_evaluate x)) =
        __eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hYEoBv, hXEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq,
      native_ite, native_teq, native_not]
  | concat =>
    have hConcatNN :
        term_has_non_none_type
          (SmtTerm.concat (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      simpa [RuleProofs.eo_has_smt_translation] using hTrans
    have hRunConcatNe :
        __eo_concat (__run_evaluate y) (__run_evaluate x) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_left_ne_stuck hRunConcatNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_right_ne_stuck hRunConcatNe
    rcases bv_concat_args_of_non_none hConcatNN with
      ⟨wy, wx, hYTyBv, hXTyBv⟩
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTyBv]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTyBv]
      simp
    have hYMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        y hYTrans
    have hXMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        x hXTrans
    have hYEoBv :
        __eo_typeof y =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int wy)) :=
      TranslationProofs.eo_to_smt_type_eq_bitvec
        (hYMatch.symm.trans hYTyBv)
    have hXEoBv :
        __eo_typeof x =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int wx)) :=
      TranslationProofs.eo_to_smt_type_eq_bitvec
        (hXMatch.symm.trans hXTyBv)
    have hYPres :=
      recY hYTrans hRunYNe
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunYBv :
        __eo_typeof (__run_evaluate y) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int wy)) :=
      hYPres.trans hYEoBv
    have hRunXBv :
        __eo_typeof (__run_evaluate x) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int wx)) :=
      hXPres.trans hXEoBv
    have hRunBodyTy :
        __eo_typeof
            (__eo_concat (__run_evaluate y)
              (__run_evaluate x)) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral
              (native_zplus (native_nat_to_int wy)
                (native_nat_to_int wx))) :=
      EvaluateProofInternal.eo_concat_typeof_bitvec_of_args_bitvec_and_ne_stuck
        (__run_evaluate y) (__run_evaluate x)
        (native_nat_to_int wy) (native_nat_to_int wx)
        hRunYBv hRunXBv hRunConcatNe
    change
      __eo_typeof
          (__eo_concat (__run_evaluate y)
            (__run_evaluate x)) =
        __eo_typeof_concat (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hYEoBv, hXEoBv]
    simp [__eo_typeof_concat, __eo_add, __eo_mk_apply]
  | bvadd =>
    have hBvAddNN :
        term_has_non_none_type
          (SmtTerm.bvadd (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunAddNe :
        __eo_add (__run_evaluate y) (__run_evaluate x) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_add_left_ne_stuck hRunAddNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_add_right_ne_stuck hRunAddNe
    rcases bv_binop_args_of_non_none
        (op := SmtTerm.bvadd) (t1 := __eo_to_smt y)
        (t2 := __eo_to_smt x)
        (by rw [__smtx_typeof.eq_48]) hBvAddNN with
      ⟨w, hYTyBv, hXTyBv⟩
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTyBv]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTyBv]
      simp
    have hYMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        y hYTrans
    have hXMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        x hXTrans
    have hYEoBv :
        __eo_typeof y =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      TranslationProofs.eo_to_smt_type_eq_bitvec
        (hYMatch.symm.trans hYTyBv)
    have hXEoBv :
        __eo_typeof x =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      TranslationProofs.eo_to_smt_type_eq_bitvec
        (hXMatch.symm.trans hXTyBv)
    have hYPres :=
      recY hYTrans hRunYNe
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunYBv :
        __eo_typeof (__run_evaluate y) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      hYPres.trans hYEoBv
    have hRunXBv :
        __eo_typeof (__run_evaluate x) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      hXPres.trans hXEoBv
    have hRunBodyTy :
        __eo_typeof
            (__eo_add (__run_evaluate y)
              (__run_evaluate x)) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      EvaluateProofInternal.eo_add_typeof_bitvec_of_args_bitvec
        (__run_evaluate y) (__run_evaluate x)
        (native_nat_to_int w) hRunYBv hRunXBv hRunAddNe
    change
      __eo_typeof
          (__eo_add (__run_evaluate y)
            (__run_evaluate x)) =
        __eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hYEoBv, hXEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq,
      native_ite, native_teq, native_not]
  | bvmul =>
    have hBvMulNN :
        term_has_non_none_type
          (SmtTerm.bvmul (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunMulNe :
        __eo_mul (__run_evaluate y) (__run_evaluate x) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_mul_left_ne_stuck hRunMulNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_mul_right_ne_stuck hRunMulNe
    rcases bv_binop_args_of_non_none
        (op := SmtTerm.bvmul) (t1 := __eo_to_smt y)
        (t2 := __eo_to_smt x)
        (by rw [__smtx_typeof.eq_49]) hBvMulNN with
      ⟨w, hYTyBv, hXTyBv⟩
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTyBv]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTyBv]
      simp
    have hYMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        y hYTrans
    have hXMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        x hXTrans
    have hYEoBv :
        __eo_typeof y =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      TranslationProofs.eo_to_smt_type_eq_bitvec
        (hYMatch.symm.trans hYTyBv)
    have hXEoBv :
        __eo_typeof x =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      TranslationProofs.eo_to_smt_type_eq_bitvec
        (hXMatch.symm.trans hXTyBv)
    have hYPres :=
      recY hYTrans hRunYNe
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunYBv :
        __eo_typeof (__run_evaluate y) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      hYPres.trans hYEoBv
    have hRunXBv :
        __eo_typeof (__run_evaluate x) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      hXPres.trans hXEoBv
    have hRunBodyTy :
        __eo_typeof
            (__eo_mul (__run_evaluate y)
              (__run_evaluate x)) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      EvaluateProofInternal.eo_mul_typeof_bitvec_of_args_bitvec
        (__run_evaluate y) (__run_evaluate x)
        (native_nat_to_int w) hRunYBv hRunXBv hRunMulNe
    change
      __eo_typeof
          (__eo_mul (__run_evaluate y)
            (__run_evaluate x)) =
        __eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hYEoBv, hXEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq,
      native_ite, native_teq, native_not]
  | bvsub =>
    have hBvSubNN :
        term_has_non_none_type
          (SmtTerm.bvsub (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunSubNe :
        __eo_add (__run_evaluate y)
            (__eo_neg (__run_evaluate x)) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_add_left_ne_stuck hRunSubNe
    have hRunNegXNe :
        __eo_neg (__run_evaluate x) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_add_right_ne_stuck hRunSubNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_neg_arg_ne_stuck hRunNegXNe
    rcases bv_binop_args_of_non_none
        (op := SmtTerm.bvsub) (t1 := __eo_to_smt y)
        (t2 := __eo_to_smt x)
        (by rw [__smtx_typeof.eq_52]) hBvSubNN with
      ⟨w, hYTyBv, hXTyBv⟩
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTyBv]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTyBv]
      simp
    have hYMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        y hYTrans
    have hXMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        x hXTrans
    have hYEoBv :
        __eo_typeof y =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      TranslationProofs.eo_to_smt_type_eq_bitvec
        (hYMatch.symm.trans hYTyBv)
    have hXEoBv :
        __eo_typeof x =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      TranslationProofs.eo_to_smt_type_eq_bitvec
        (hXMatch.symm.trans hXTyBv)
    have hYPres :=
      recY hYTrans hRunYNe
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunYBv :
        __eo_typeof (__run_evaluate y) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      hYPres.trans hYEoBv
    have hRunXBv :
        __eo_typeof (__run_evaluate x) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      hXPres.trans hXEoBv
    have hRunNegXBv :
        __eo_typeof (__eo_neg (__run_evaluate x)) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      EvaluateProofInternal.eo_neg_typeof_bitvec_of_arg_bitvec
        (__run_evaluate x) (native_nat_to_int w)
        hRunXBv hRunNegXNe
    have hRunBodyTy :
        __eo_typeof
            (__eo_add (__run_evaluate y)
              (__eo_neg (__run_evaluate x))) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      EvaluateProofInternal.eo_add_typeof_bitvec_of_args_bitvec
        (__run_evaluate y) (__eo_neg (__run_evaluate x))
        (native_nat_to_int w) hRunYBv hRunNegXBv
        hRunSubNe
    change
      __eo_typeof
          (__eo_add (__run_evaluate y)
            (__eo_neg (__run_evaluate x))) =
        __eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hYEoBv, hXEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq,
      native_ite, native_teq, native_not]
  | bvudiv =>
    have hBvUdivNN :
        term_has_non_none_type
          (SmtTerm.bvudiv (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    rcases bv_binop_args_of_non_none
        (op := SmtTerm.bvudiv) (t1 := __eo_to_smt y)
        (t2 := __eo_to_smt x)
        (by rw [__smtx_typeof.eq_50]) hBvUdivNN with
      ⟨w, hYTyBv, hXTyBv⟩
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTyBv]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTyBv]
      simp
    have hYEoBv :=
      EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec y w hYTyBv
    have hXEoBv :=
      EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec x w hXTyBv
    have hRunDivNe :
        __run_evaluate
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvudiv) y) x) ≠
          Term.Stuck := by
      simpa using hRunNe
    change __eo_ite _ _ _ ≠ Term.Stuck at hRunDivNe
    have hRunBodyTy :
        __eo_typeof
            (__run_evaluate
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.bvudiv) y) x)) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) := by
      change
        __eo_typeof
            (__eo_ite
              (__eo_eq (__eo_to_z (__run_evaluate x))
                (Term.Numeral 0)) _ _) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w))
      rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
          _ _ _ hRunDivNe with
        ⟨b, hCond, hSel⟩
      cases b
      · rw [hCond]
        change
          __eo_zdiv (__run_evaluate y)
              (__run_evaluate x) ≠
            Term.Stuck at hSel
        have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
          EvaluateProofInternal.eo_zdiv_left_ne_stuck hSel
        have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
          EvaluateProofInternal.eo_zdiv_right_ne_stuck hSel
        have hYPres :=
          recY hYTrans hRunYNe
        have hXPres :=
          recX hXTrans hRunXNe
        have hRunYBv :
            __eo_typeof (__run_evaluate y) =
              Term.Apply (Term.UOp UserOp.BitVec)
                (Term.Numeral (native_nat_to_int w)) :=
          hYPres.trans hYEoBv
        have hRunXBv :
            __eo_typeof (__run_evaluate x) =
              Term.Apply (Term.UOp UserOp.BitVec)
                (Term.Numeral (native_nat_to_int w)) :=
          hXPres.trans hXEoBv
        have hZDivTy :
            __eo_typeof
                (__eo_zdiv (__run_evaluate y)
                  (__run_evaluate x)) =
              Term.Apply (Term.UOp UserOp.BitVec)
                (Term.Numeral (native_nat_to_int w)) :=
          EvaluateProofInternal.eo_zdiv_typeof_bitvec_of_args_bitvec_and_ne_stuck
            (__run_evaluate y) (__run_evaluate x)
            (native_nat_to_int w) hRunYBv hRunXBv hSel
        have hsimpa := hZDivTy
        try simp [__eo_ite] at hsimpa ⊢
        exact hsimpa
      · rw [hCond]
        change
          __eo_to_bin (__bv_bitwidth (__eo_typeof y)) _ ≠
            Term.Stuck at hSel
        rw [hYEoBv] at hSel
        have hThenTy :
            __eo_typeof
                (__eo_to_bin
                  (Term.Numeral (native_nat_to_int w)) _) =
              Term.Apply (Term.UOp UserOp.BitVec)
                (Term.Numeral (native_nat_to_int w)) :=
          EvaluateProofInternal.eo_to_bin_typeof_bitvec_of_width_numeral_and_ne_stuck
            (native_nat_to_int w) _
            (by simpa [__bv_bitwidth] using hSel)
        have hsimpa := hThenTy
        try simp [__eo_ite, hYEoBv, __bv_bitwidth] at hsimpa ⊢
        exact hsimpa
    have hRhsTy :
        __eo_typeof_bvand (__eo_typeof y)
            (__eo_typeof x) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      EvaluateProofInternal.eo_typeof_bvand_bitvec_of_smt_bitvec_args
        y x w hYTyBv hXTyBv
    change
      __eo_typeof
          (__run_evaluate
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvudiv) y) x)) =
        __eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hRhsTy]
  | bvurem =>
    have hBvUremNN :
        term_has_non_none_type
          (SmtTerm.bvurem (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    rcases bv_binop_args_of_non_none
        (op := SmtTerm.bvurem) (t1 := __eo_to_smt y)
        (t2 := __eo_to_smt x)
        (by rw [__smtx_typeof.eq_51]) hBvUremNN with
      ⟨w, hYTyBv, hXTyBv⟩
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTyBv]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTyBv]
      simp
    have hYEoBv :=
      EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec y w hYTyBv
    have hXEoBv :=
      EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec x w hXTyBv
    have hRunRemNe :
        __run_evaluate
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvurem) y) x) ≠
          Term.Stuck := by
      simpa using hRunNe
    change __eo_ite _ _ _ ≠ Term.Stuck at hRunRemNe
    have hRunBodyTy :
        __eo_typeof
            (__run_evaluate
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.bvurem) y) x)) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) := by
      change
        __eo_typeof
            (__eo_ite
              (__eo_eq (__eo_to_z (__run_evaluate x))
                (Term.Numeral 0)) _ _) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w))
      rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
          _ _ _ hRunRemNe with
        ⟨b, hCond, hSel⟩
      cases b
      · rw [hCond]
        change
          __eo_zmod (__run_evaluate y)
              (__run_evaluate x) ≠
            Term.Stuck at hSel
        have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
          EvaluateProofInternal.eo_zmod_left_ne_stuck hSel
        have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
          EvaluateProofInternal.eo_zmod_right_ne_stuck hSel
        have hYPres :=
          recY hYTrans hRunYNe
        have hXPres :=
          recX hXTrans hRunXNe
        have hRunYBv :
            __eo_typeof (__run_evaluate y) =
              Term.Apply (Term.UOp UserOp.BitVec)
                (Term.Numeral (native_nat_to_int w)) :=
          hYPres.trans hYEoBv
        have hRunXBv :
            __eo_typeof (__run_evaluate x) =
              Term.Apply (Term.UOp UserOp.BitVec)
                (Term.Numeral (native_nat_to_int w)) :=
          hXPres.trans hXEoBv
        have hZModTy :
            __eo_typeof
                (__eo_zmod (__run_evaluate y)
                  (__run_evaluate x)) =
              Term.Apply (Term.UOp UserOp.BitVec)
                (Term.Numeral (native_nat_to_int w)) :=
          EvaluateProofInternal.eo_zmod_typeof_bitvec_of_args_bitvec_and_ne_stuck
            (__run_evaluate y) (__run_evaluate x)
            (native_nat_to_int w) hRunYBv hRunXBv hSel
        have hsimpa := hZModTy
        try simp [__eo_ite] at hsimpa ⊢
        exact hsimpa
      · rw [hCond]
        change __run_evaluate y ≠ Term.Stuck at hSel
        have hYPres :=
          recY hYTrans hSel
        have hRunYBv :
            __eo_typeof (__run_evaluate y) =
              Term.Apply (Term.UOp UserOp.BitVec)
                (Term.Numeral (native_nat_to_int w)) :=
          hYPres.trans hYEoBv
        have hsimpa := hRunYBv
        try simp [__eo_ite] at hsimpa ⊢
        exact hsimpa
    have hRhsTy :
        __eo_typeof_bvand (__eo_typeof y)
            (__eo_typeof x) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      EvaluateProofInternal.eo_typeof_bvand_bitvec_of_smt_bitvec_args
        y x w hYTyBv hXTyBv
    change
      __eo_typeof
          (__run_evaluate
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvurem) y) x)) =
        __eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hRhsTy]
  | bvult =>
    have hBvUltNN :
        term_has_non_none_type
          (SmtTerm.bvult (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunCmpNe :
        __eo_gt (__eo_to_z (__run_evaluate x))
            (__eo_to_z (__run_evaluate y)) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunBodyTy :
        __eo_typeof
            (__eo_gt (__eo_to_z (__run_evaluate x))
              (__eo_to_z (__run_evaluate y))) =
          Term.Bool :=
      EvaluateProofInternal.eo_gt_typeof_bool_of_ne_stuck
        (__eo_to_z (__run_evaluate x))
        (__eo_to_z (__run_evaluate y)) hRunCmpNe
    rcases bv_binop_ret_args_of_non_none
        (op := SmtTerm.bvult) (ret := SmtType.Bool)
        (by rw [__smtx_typeof.eq_56]) hBvUltNN with
      ⟨w, hYTyBv, hXTyBv⟩
    have hRhsTy :
        __eo_typeof_bvult (__eo_typeof y)
            (__eo_typeof x) =
          Term.Bool :=
      EvaluateProofInternal.eo_typeof_bvult_bool_of_smt_bitvec_args
        y x w hYTyBv hXTyBv
    change
      __eo_typeof
          (__eo_gt (__eo_to_z (__run_evaluate x))
            (__eo_to_z (__run_evaluate y))) =
        __eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hRhsTy]
  | bvugt =>
    have hBvUgtNN :
        term_has_non_none_type
          (SmtTerm.bvugt (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunCmpNe :
        __eo_gt (__eo_to_z (__run_evaluate y))
            (__eo_to_z (__run_evaluate x)) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunBodyTy :
        __eo_typeof
            (__eo_gt (__eo_to_z (__run_evaluate y))
              (__eo_to_z (__run_evaluate x))) =
          Term.Bool :=
      EvaluateProofInternal.eo_gt_typeof_bool_of_ne_stuck
        (__eo_to_z (__run_evaluate y))
        (__eo_to_z (__run_evaluate x)) hRunCmpNe
    rcases bv_binop_ret_args_of_non_none
        (op := SmtTerm.bvugt) (ret := SmtType.Bool)
        (by rw [__smtx_typeof.eq_58]) hBvUgtNN with
      ⟨w, hYTyBv, hXTyBv⟩
    have hRhsTy :
        __eo_typeof_bvult (__eo_typeof y)
            (__eo_typeof x) =
          Term.Bool :=
      EvaluateProofInternal.eo_typeof_bvult_bool_of_smt_bitvec_args
        y x w hYTyBv hXTyBv
    change
      __eo_typeof
          (__eo_gt (__eo_to_z (__run_evaluate y))
            (__eo_to_z (__run_evaluate x))) =
        __eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hRhsTy]
  | bvule =>
    have hBvUleNN :
        term_has_non_none_type
          (SmtTerm.bvule (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    let rx := __run_evaluate x
    let ry := __run_evaluate y
    have hRunOrNe :
        __eo_or (__eo_gt rx ry) (__eo_eq ry rx) ≠
          Term.Stuck := by
      simpa [__run_evaluate, rx, ry] using hRunNe
    have hGtNe : __eo_gt rx ry ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_left_ne_stuck hRunOrNe
    have hEqNe : __eo_eq ry rx ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_right_ne_stuck hRunOrNe
    have hGtTy : __eo_typeof (__eo_gt rx ry) = Term.Bool :=
      EvaluateProofInternal.eo_gt_typeof_bool_of_ne_stuck rx ry hGtNe
    have hEqTy : __eo_typeof (__eo_eq ry rx) = Term.Bool :=
      EvaluateProofInternal.eo_eq_typeof_bool_of_ne_stuck ry rx hEqNe
    have hRunBodyTy :
        __eo_typeof (__eo_or (__eo_gt rx ry)
            (__eo_eq ry rx)) =
          Term.Bool :=
      EvaluateProofInternal.eo_or_typeof_bool_of_args_bool
        (__eo_gt rx ry) (__eo_eq ry rx) hGtTy hEqTy
        hRunOrNe
    rcases bv_binop_ret_args_of_non_none
        (op := SmtTerm.bvule) (ret := SmtType.Bool)
        (by rw [__smtx_typeof.eq_57]) hBvUleNN with
      ⟨w, hYTyBv, hXTyBv⟩
    have hRhsTy :
        __eo_typeof_bvult (__eo_typeof y)
            (__eo_typeof x) =
          Term.Bool :=
      EvaluateProofInternal.eo_typeof_bvult_bool_of_smt_bitvec_args
        y x w hYTyBv hXTyBv
    change
      __eo_typeof
          (__eo_or (__eo_gt rx ry) (__eo_eq ry rx)) =
        __eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hRhsTy]
  | bvuge =>
    have hBvUgeNN :
        term_has_non_none_type
          (SmtTerm.bvuge (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    let rx := __run_evaluate x
    let ry := __run_evaluate y
    have hRunOrNe :
        __eo_or (__eo_gt ry rx) (__eo_eq ry rx) ≠
          Term.Stuck := by
      simpa [__run_evaluate, rx, ry] using hRunNe
    have hGtNe : __eo_gt ry rx ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_left_ne_stuck hRunOrNe
    have hEqNe : __eo_eq ry rx ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_right_ne_stuck hRunOrNe
    have hGtTy : __eo_typeof (__eo_gt ry rx) = Term.Bool :=
      EvaluateProofInternal.eo_gt_typeof_bool_of_ne_stuck ry rx hGtNe
    have hEqTy : __eo_typeof (__eo_eq ry rx) = Term.Bool :=
      EvaluateProofInternal.eo_eq_typeof_bool_of_ne_stuck ry rx hEqNe
    have hRunBodyTy :
        __eo_typeof (__eo_or (__eo_gt ry rx)
            (__eo_eq ry rx)) =
          Term.Bool :=
      EvaluateProofInternal.eo_or_typeof_bool_of_args_bool
        (__eo_gt ry rx) (__eo_eq ry rx) hGtTy hEqTy
        hRunOrNe
    rcases bv_binop_ret_args_of_non_none
        (op := SmtTerm.bvuge) (ret := SmtType.Bool)
        (by rw [__smtx_typeof.eq_59]) hBvUgeNN with
      ⟨w, hYTyBv, hXTyBv⟩
    have hRhsTy :
        __eo_typeof_bvult (__eo_typeof y)
            (__eo_typeof x) =
          Term.Bool :=
      EvaluateProofInternal.eo_typeof_bvult_bool_of_smt_bitvec_args
        y x w hYTyBv hXTyBv
    change
      __eo_typeof
          (__eo_or (__eo_gt ry rx) (__eo_eq ry rx)) =
        __eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hRhsTy]
  | bvslt =>
    have hBvSltNN :
        term_has_non_none_type
          (SmtTerm.bvslt (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunCmpNe :
        __run_evaluate
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvslt) y) x) ≠
          Term.Stuck := by
      simpa using hRunNe
    change __eo_gt _ _ ≠ Term.Stuck at hRunCmpNe
    have hRunBodyTy :
        __eo_typeof
            (__run_evaluate
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.bvslt) y) x)) =
          Term.Bool := by
      change __eo_typeof (__eo_gt _ _) = Term.Bool
      exact EvaluateProofInternal.eo_gt_typeof_bool_of_ne_stuck _ _ hRunCmpNe
    rcases bv_binop_ret_args_of_non_none
        (op := SmtTerm.bvslt) (ret := SmtType.Bool)
        (by rw [__smtx_typeof.eq_def] <;> simp only)
        hBvSltNN with
      ⟨w, hYTyBv, hXTyBv⟩
    have hRhsTy :
        __eo_typeof_bvult (__eo_typeof y)
            (__eo_typeof x) =
          Term.Bool :=
      EvaluateProofInternal.eo_typeof_bvult_bool_of_smt_bitvec_args
        y x w hYTyBv hXTyBv
    change
      __eo_typeof
          (__run_evaluate
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvslt) y) x)) =
        __eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hRhsTy]
  | bvsle =>
    have hBvSleNN :
        term_has_non_none_type
          (SmtTerm.bvsle (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunOrNe :
        __run_evaluate
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvsle) y) x) ≠
          Term.Stuck := by
      simpa using hRunNe
    change __eo_or _ _ ≠ Term.Stuck at hRunOrNe
    have hGtNe : _ ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_left_ne_stuck hRunOrNe
    have hEqNe : _ ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_right_ne_stuck hRunOrNe
    have hGtTy : __eo_typeof _ = Term.Bool :=
      EvaluateProofInternal.eo_gt_typeof_bool_of_ne_stuck _ _ hGtNe
    have hEqTy : __eo_typeof _ = Term.Bool :=
      EvaluateProofInternal.eo_eq_typeof_bool_of_ne_stuck _ _ hEqNe
    have hRunBodyTy :
        __eo_typeof
            (__run_evaluate
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.bvsle) y) x)) =
          Term.Bool := by
      change __eo_typeof (__eo_or _ _) = Term.Bool
      exact EvaluateProofInternal.eo_or_typeof_bool_of_args_bool _ _ hGtTy hEqTy
        hRunOrNe
    rcases bv_binop_ret_args_of_non_none
        (op := SmtTerm.bvsle) (ret := SmtType.Bool)
        (by rw [__smtx_typeof.eq_def] <;> simp only)
        hBvSleNN with
      ⟨w, hYTyBv, hXTyBv⟩
    have hRhsTy :
        __eo_typeof_bvult (__eo_typeof y)
            (__eo_typeof x) =
          Term.Bool :=
      EvaluateProofInternal.eo_typeof_bvult_bool_of_smt_bitvec_args
        y x w hYTyBv hXTyBv
    change
      __eo_typeof
          (__run_evaluate
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvsle) y) x)) =
        __eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hRhsTy]
  | bvsgt =>
    have hBvSgtNN :
        term_has_non_none_type
          (SmtTerm.bvsgt (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunCmpNe :
        __run_evaluate
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvsgt) y) x) ≠
          Term.Stuck := by
      simpa using hRunNe
    change __eo_gt _ _ ≠ Term.Stuck at hRunCmpNe
    have hRunBodyTy :
        __eo_typeof
            (__run_evaluate
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.bvsgt) y) x)) =
          Term.Bool := by
      change __eo_typeof (__eo_gt _ _) = Term.Bool
      exact EvaluateProofInternal.eo_gt_typeof_bool_of_ne_stuck _ _ hRunCmpNe
    rcases bv_binop_ret_args_of_non_none
        (op := SmtTerm.bvsgt) (ret := SmtType.Bool)
        (by rw [__smtx_typeof.eq_def] <;> simp only)
        hBvSgtNN with
      ⟨w, hYTyBv, hXTyBv⟩
    have hRhsTy :
        __eo_typeof_bvult (__eo_typeof y)
            (__eo_typeof x) =
          Term.Bool :=
      EvaluateProofInternal.eo_typeof_bvult_bool_of_smt_bitvec_args
        y x w hYTyBv hXTyBv
    change
      __eo_typeof
          (__run_evaluate
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvsgt) y) x)) =
        __eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hRhsTy]
  | bvsge =>
    have hBvSgeNN :
        term_has_non_none_type
          (SmtTerm.bvsge (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunOrNe :
        __run_evaluate
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvsge) y) x) ≠
          Term.Stuck := by
      simpa using hRunNe
    change __eo_or _ _ ≠ Term.Stuck at hRunOrNe
    have hGtNe : _ ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_left_ne_stuck hRunOrNe
    have hEqNe : _ ≠ Term.Stuck :=
      EvaluateProofInternal.eo_or_right_ne_stuck hRunOrNe
    have hGtTy : __eo_typeof _ = Term.Bool :=
      EvaluateProofInternal.eo_gt_typeof_bool_of_ne_stuck _ _ hGtNe
    have hEqTy : __eo_typeof _ = Term.Bool :=
      EvaluateProofInternal.eo_eq_typeof_bool_of_ne_stuck _ _ hEqNe
    have hRunBodyTy :
        __eo_typeof
            (__run_evaluate
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.bvsge) y) x)) =
          Term.Bool := by
      change __eo_typeof (__eo_or _ _) = Term.Bool
      exact EvaluateProofInternal.eo_or_typeof_bool_of_args_bool _ _ hGtTy hEqTy
        hRunOrNe
    rcases bv_binop_ret_args_of_non_none
        (op := SmtTerm.bvsge) (ret := SmtType.Bool)
        (by rw [__smtx_typeof.eq_def] <;> simp only)
        hBvSgeNN with
      ⟨w, hYTyBv, hXTyBv⟩
    have hRhsTy :
        __eo_typeof_bvult (__eo_typeof y)
            (__eo_typeof x) =
          Term.Bool :=
      EvaluateProofInternal.eo_typeof_bvult_bool_of_smt_bitvec_args
        y x w hYTyBv hXTyBv
    change
      __eo_typeof
          (__run_evaluate
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvsge) y) x)) =
        __eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hRhsTy]
  | bvshl =>
    have hBvShlNN :
        term_has_non_none_type
          (SmtTerm.bvshl (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    rcases bv_binop_args_of_non_none
        (op := SmtTerm.bvshl) (t1 := __eo_to_smt y)
        (t2 := __eo_to_smt x)
        (by rw [__smtx_typeof.eq_def] <;> simp only)
        hBvShlNN with
      ⟨w, hYTyBv, hXTyBv⟩
    have hYEoBv :=
      EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec y w hYTyBv
    have hRunShiftNe :
        __run_evaluate
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvshl) y) x) ≠
          Term.Stuck := by
      simpa using hRunNe
    change
      __eo_ite _ (__eo_to_bin (__bv_bitwidth (__eo_typeof y)) _)
          (__eo_to_bin (__bv_bitwidth (__eo_typeof y)) _) ≠
        Term.Stuck at hRunShiftNe
    have hRunBodyTy :
        __eo_typeof
            (__run_evaluate
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.bvshl) y) x)) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) := by
      change
        __eo_typeof
            (__eo_ite _
              (__eo_to_bin (__bv_bitwidth (__eo_typeof y)) _)
              (__eo_to_bin (__bv_bitwidth (__eo_typeof y)) _)) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w))
      rw [hYEoBv] at hRunShiftNe ⊢
      simpa [__bv_bitwidth] using
        EvaluateProofInternal.eo_ite_to_bin_typeof_bitvec_of_width_numeral_and_ne_stuck
          _ _ _ (native_nat_to_int w)
          (by simpa [__bv_bitwidth] using hRunShiftNe)
    have hRhsTy :
        __eo_typeof_bvand (__eo_typeof y)
            (__eo_typeof x) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      EvaluateProofInternal.eo_typeof_bvand_bitvec_of_smt_bitvec_args
        y x w hYTyBv hXTyBv
    change
      __eo_typeof
          (__run_evaluate
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvshl) y) x)) =
        __eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hRhsTy]
  | bvlshr =>
    have hBvLshrNN :
        term_has_non_none_type
          (SmtTerm.bvlshr (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    rcases bv_binop_args_of_non_none
        (op := SmtTerm.bvlshr) (t1 := __eo_to_smt y)
        (t2 := __eo_to_smt x)
        (by rw [__smtx_typeof.eq_def] <;> simp only)
        hBvLshrNN with
      ⟨w, hYTyBv, hXTyBv⟩
    have hYEoBv :=
      EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec y w hYTyBv
    have hRunShiftNe :
        __run_evaluate
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvlshr) y) x) ≠
          Term.Stuck := by
      simpa using hRunNe
    change
      __eo_ite _ (__eo_to_bin (__bv_bitwidth (__eo_typeof y)) _)
          (__eo_to_bin (__bv_bitwidth (__eo_typeof y)) _) ≠
        Term.Stuck at hRunShiftNe
    have hRunBodyTy :
        __eo_typeof
            (__run_evaluate
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.bvlshr) y) x)) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) := by
      change
        __eo_typeof
            (__eo_ite _
              (__eo_to_bin (__bv_bitwidth (__eo_typeof y)) _)
              (__eo_to_bin (__bv_bitwidth (__eo_typeof y)) _)) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w))
      rw [hYEoBv] at hRunShiftNe ⊢
      simpa [__bv_bitwidth] using
        EvaluateProofInternal.eo_ite_to_bin_typeof_bitvec_of_width_numeral_and_ne_stuck
          _ _ _ (native_nat_to_int w)
          (by simpa [__bv_bitwidth] using hRunShiftNe)
    have hRhsTy :
        __eo_typeof_bvand (__eo_typeof y)
            (__eo_typeof x) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      EvaluateProofInternal.eo_typeof_bvand_bitvec_of_smt_bitvec_args
        y x w hYTyBv hXTyBv
    change
      __eo_typeof
          (__run_evaluate
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvlshr) y) x)) =
        __eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hRhsTy]
  | bvashr =>
    have hBvAshrNN :
        term_has_non_none_type
          (SmtTerm.bvashr (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    rcases bv_binop_args_of_non_none
        (op := SmtTerm.bvashr) (t1 := __eo_to_smt y)
        (t2 := __eo_to_smt x)
        (by rw [__smtx_typeof.eq_def] <;> simp only)
        hBvAshrNN with
      ⟨w, hYTyBv, hXTyBv⟩
    have hYEoBv :=
      EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec y w hYTyBv
    have hRunShiftNe :
        __run_evaluate
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvashr) y) x) ≠
          Term.Stuck := by
      simpa using hRunNe
    change
      __eo_to_bin (__bv_bitwidth (__eo_typeof y)) _ ≠
        Term.Stuck at hRunShiftNe
    have hRunBodyTy :
        __eo_typeof
            (__run_evaluate
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.bvashr) y) x)) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) := by
      change
        __eo_typeof
            (__eo_to_bin (__bv_bitwidth (__eo_typeof y)) _) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w))
      rw [hYEoBv] at hRunShiftNe ⊢
      simpa [__bv_bitwidth] using
        EvaluateProofInternal.eo_to_bin_typeof_bitvec_of_width_numeral_and_ne_stuck
          (native_nat_to_int w) _
          (by simpa [__bv_bitwidth] using hRunShiftNe)
    have hRhsTy :
        __eo_typeof_bvand (__eo_typeof y)
            (__eo_typeof x) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      EvaluateProofInternal.eo_typeof_bvand_bitvec_of_smt_bitvec_args
        y x w hYTyBv hXTyBv
    change
      __eo_typeof
          (__run_evaluate
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvashr) y) x)) =
        __eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hRhsTy]
  | str_concat =>
    have hConcatNN :
        term_has_non_none_type
          (SmtTerm.str_concat (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      simpa [RuleProofs.eo_has_smt_translation] using hTrans
    have hRunConcatNe :
        __eo_concat (__run_evaluate y)
            (__run_evaluate x) ≠ Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_left_ne_stuck hRunConcatNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_right_ne_stuck hRunConcatNe
    rcases seq_binop_args_of_non_none
        (op := SmtTerm.str_concat)
        (typeof_str_concat_eq (__eo_to_smt y)
          (__eo_to_smt x)) hConcatNN with
      ⟨T, hYTySeq, hXTySeq⟩
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTySeq]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTySeq]
      simp
    rcases EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq y hYTrans
        hYTySeq with
      ⟨UY, hYEoSeq, hUYSmt⟩
    rcases EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq x hXTrans
        hXTySeq with
      ⟨UX, hXEoSeq, hUXSmt⟩
    have hYEoValid :=
      TranslationProofs.eo_type_valid_typeof_of_smt_translation
        y hYTrans
    have hYSeqValid :
        TranslationProofs.eo_type_valid
          (Term.Apply (Term.UOp UserOp.Seq) UY) := by
      simpa [hYEoSeq] using hYEoValid
    have hSeqEq :
        Term.Apply (Term.UOp UserOp.Seq) UY =
          Term.Apply (Term.UOp UserOp.Seq) UX := by
      apply EvaluateProofInternal.eo_to_smt_type_eq_of_top_valid hYSeqValid
      simp [__eo_to_smt_type, hUYSmt, hUXSmt]
    cases hSeqEq
    have hUNe : UY ≠ Term.Stuck := by
      intro hStuck
      subst UY
      simpa [TranslationProofs.eo_type_valid,
        TranslationProofs.eo_type_valid_rec, TranslationProofs.noNoneTy,
        __eo_to_smt_type, __smtx_typeof_guard, native_ite,
        native_Teq] using hYSeqValid
    have hUEq : __eo_eq UY UY = Term.Boolean true := by
      cases UY <;> simp [__eo_eq, native_teq] at hUNe ⊢
    have hYPres :=
      recY hYTrans hRunYNe
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunYSeq :
        __eo_typeof (__run_evaluate y) =
          Term.Apply (Term.UOp UserOp.Seq) UY :=
      hYPres.trans hYEoSeq
    have hRunXSeq :
        __eo_typeof (__run_evaluate x) =
          Term.Apply (Term.UOp UserOp.Seq) UY :=
      hXPres.trans hXEoSeq
    have hRunBodyTy :
        __eo_typeof
            (__eo_concat (__run_evaluate y)
              (__run_evaluate x)) =
          Term.Apply (Term.UOp UserOp.Seq) UY :=
      EvaluateProofInternal.eo_concat_typeof_seq_of_args_seq_and_ne_stuck
        (__run_evaluate y) (__run_evaluate x) UY
        hRunYSeq hRunXSeq hRunConcatNe
    change
      __eo_typeof
          (__eo_concat (__run_evaluate y)
            (__run_evaluate x)) =
        __eo_typeof_str_concat (__eo_typeof y)
          (__eo_typeof x)
    rw [hRunBodyTy, hYEoSeq, hXEoSeq]
    simp [__eo_typeof_str_concat, __eo_requires,
      hUEq, native_ite, native_teq, native_not]
  | str_at =>
    have hAtNN :
        term_has_non_none_type
          (SmtTerm.str_at (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    have hRunAtNe :
        __eo_extract (__run_evaluate y)
            (__run_evaluate x) (__run_evaluate x) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck :=
      EvaluateProofInternal.eo_extract_target_ne_stuck hRunAtNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_extract_start_ne_stuck hRunAtNe
    rcases str_at_args_of_non_none hAtNN with
      ⟨T, hYTySeq, hXTyInt⟩
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTySeq]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTyInt]
      simp
    rcases EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq y hYTrans
        hYTySeq with
      ⟨UY, hYEoSeq, _hUYSmt⟩
    have hXMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        x hXTrans
    have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int
        (hXMatch.symm.trans hXTyInt)
    have hYPres :=
      recY hYTrans hRunYNe
    have hRunYSeq :
        __eo_typeof (__run_evaluate y) =
          Term.Apply (Term.UOp UserOp.Seq) UY :=
      hYPres.trans hYEoSeq
    have hRunBodyTy :
        __eo_typeof
            (__eo_extract (__run_evaluate y)
              (__run_evaluate x) (__run_evaluate x)) =
          Term.Apply (Term.UOp UserOp.Seq) UY :=
      EvaluateProofInternal.eo_extract_typeof_seq_of_target_seq_and_ne_stuck
        (__run_evaluate y) (__run_evaluate x)
        (__run_evaluate x) UY hRunYSeq hRunAtNe
    change
      __eo_typeof
          (__eo_extract (__run_evaluate y)
            (__run_evaluate x) (__run_evaluate x)) =
        __eo_typeof_str_at (__eo_typeof y)
          (__eo_typeof x)
    rw [hRunBodyTy, hYEoSeq, hXEoInt]
    rfl
  | str_prefixof =>
    have hPrefixNN :
        term_has_non_none_type
          (SmtTerm.str_prefixof (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    rcases seq_binop_args_of_non_none_ret
        (op := SmtTerm.str_prefixof)
        (typeof_str_prefixof_eq (__eo_to_smt y)
          (__eo_to_smt x)) hPrefixNN with
      ⟨T, hYTySeq, hXTySeq⟩
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTySeq]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTySeq]
      simp
    rcases EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq y hYTrans
        hYTySeq with
      ⟨UY, hYEoSeq, hUYSmt⟩
    rcases EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq x hXTrans
        hXTySeq with
      ⟨UX, hXEoSeq, hUXSmt⟩
    have hYEoValid :=
      TranslationProofs.eo_type_valid_typeof_of_smt_translation
        y hYTrans
    have hYSeqValid :
        TranslationProofs.eo_type_valid
          (Term.Apply (Term.UOp UserOp.Seq) UY) := by
      simpa [hYEoSeq] using hYEoValid
    have hSeqEq :
        Term.Apply (Term.UOp UserOp.Seq) UY =
          Term.Apply (Term.UOp UserOp.Seq) UX := by
      apply EvaluateProofInternal.eo_to_smt_type_eq_of_top_valid hYSeqValid
      simp [__eo_to_smt_type, hUYSmt, hUXSmt]
    cases hSeqEq
    have hUNe : UY ≠ Term.Stuck := by
      intro hStuck
      subst UY
      simpa [TranslationProofs.eo_type_valid,
        TranslationProofs.eo_type_valid_rec, TranslationProofs.noNoneTy,
        __eo_to_smt_type, __smtx_typeof_guard, native_ite,
        native_Teq] using hYSeqValid
    have hUEq : __eo_eq UY UY = Term.Boolean true := by
      cases UY <;> simp [__eo_eq, native_teq] at hUNe ⊢
    have hRunPrefixNe :
        __eo_eq (__run_evaluate y)
            (__eo_extract (__run_evaluate x)
              (Term.Numeral 0)
              (__eo_add (__eo_len (__run_evaluate y))
                (Term.Numeral (-1 : native_Int)))) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunBodyTy :
        __eo_typeof
            (__eo_eq (__run_evaluate y)
              (__eo_extract (__run_evaluate x)
                (Term.Numeral 0)
                (__eo_add (__eo_len (__run_evaluate y))
                  (Term.Numeral (-1 : native_Int))))) =
          Term.Bool :=
      EvaluateProofInternal.eo_eq_typeof_bool_of_ne_stuck _ _ hRunPrefixNe
    change
      __eo_typeof
          (__eo_eq (__run_evaluate y)
            (__eo_extract (__run_evaluate x)
              (Term.Numeral 0)
              (__eo_add (__eo_len (__run_evaluate y))
                (Term.Numeral (-1 : native_Int))))) =
        __eo_typeof_str_contains (__eo_typeof y)
          (__eo_typeof x)
    rw [hRunBodyTy, hYEoSeq, hXEoSeq]
    simp [__eo_typeof_str_contains, __eo_requires,
      hUEq, native_ite, native_teq, native_not]
  | str_suffixof =>
    have hSuffixNN :
        term_has_non_none_type
          (SmtTerm.str_suffixof (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    rcases seq_binop_args_of_non_none_ret
        (op := SmtTerm.str_suffixof)
        (typeof_str_suffixof_eq (__eo_to_smt y)
          (__eo_to_smt x)) hSuffixNN with
      ⟨T, hYTySeq, hXTySeq⟩
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTySeq]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTySeq]
      simp
    rcases EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq y hYTrans
        hYTySeq with
      ⟨UY, hYEoSeq, hUYSmt⟩
    rcases EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq x hXTrans
        hXTySeq with
      ⟨UX, hXEoSeq, hUXSmt⟩
    have hYEoValid :=
      TranslationProofs.eo_type_valid_typeof_of_smt_translation
        y hYTrans
    have hYSeqValid :
        TranslationProofs.eo_type_valid
          (Term.Apply (Term.UOp UserOp.Seq) UY) := by
      simpa [hYEoSeq] using hYEoValid
    have hSeqEq :
        Term.Apply (Term.UOp UserOp.Seq) UY =
          Term.Apply (Term.UOp UserOp.Seq) UX := by
      apply EvaluateProofInternal.eo_to_smt_type_eq_of_top_valid hYSeqValid
      simp [__eo_to_smt_type, hUYSmt, hUXSmt]
    cases hSeqEq
    have hUNe : UY ≠ Term.Stuck := by
      intro hStuck
      subst UY
      simpa [TranslationProofs.eo_type_valid,
        TranslationProofs.eo_type_valid_rec, TranslationProofs.noNoneTy,
        __eo_to_smt_type, __smtx_typeof_guard, native_ite,
        native_Teq] using hYSeqValid
    have hUEq : __eo_eq UY UY = Term.Boolean true := by
      cases UY <;> simp [__eo_eq, native_teq] at hUNe ⊢
    have hRunSuffixNe :
        (let _v0 := __run_evaluate x
         let _v1 := __eo_len _v0
         let _v2 := __run_evaluate y
         __eo_eq _v2
          (__eo_extract _v0
            (__eo_add _v1 (__eo_neg (__eo_len _v2)))
            (__eo_add _v1
              (Term.Numeral (-1 : native_Int))))) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunBodyTy :
        __eo_typeof
            (let _v0 := __run_evaluate x
             let _v1 := __eo_len _v0
             let _v2 := __run_evaluate y
             __eo_eq _v2
              (__eo_extract _v0
                (__eo_add _v1 (__eo_neg (__eo_len _v2)))
                (__eo_add _v1
                  (Term.Numeral (-1 : native_Int))))) =
          Term.Bool :=
      EvaluateProofInternal.eo_eq_typeof_bool_of_ne_stuck _ _ hRunSuffixNe
    change
      __eo_typeof
          (let _v0 := __run_evaluate x
           let _v1 := __eo_len _v0
           let _v2 := __run_evaluate y
           __eo_eq _v2
            (__eo_extract _v0
              (__eo_add _v1 (__eo_neg (__eo_len _v2)))
              (__eo_add _v1
                (Term.Numeral (-1 : native_Int))))) =
        __eo_typeof_str_contains (__eo_typeof y)
          (__eo_typeof x)
    rw [hRunBodyTy, hYEoSeq, hXEoSeq]
    simp [__eo_typeof_str_contains, __eo_requires,
      hUEq, native_ite, native_teq, native_not]
  | str_contains =>
    have hContainsNN :
        term_has_non_none_type
          (SmtTerm.str_contains (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    rcases seq_binop_args_of_non_none_ret
        (op := SmtTerm.str_contains)
        (typeof_str_contains_eq (__eo_to_smt y)
          (__eo_to_smt x)) hContainsNN with
      ⟨T, hYTySeq, hXTySeq⟩
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTySeq]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTySeq]
      simp
    rcases EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq y hYTrans
        hYTySeq with
      ⟨UY, hYEoSeq, hUYSmt⟩
    rcases EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq x hXTrans
        hXTySeq with
      ⟨UX, hXEoSeq, hUXSmt⟩
    have hYEoValid :=
      TranslationProofs.eo_type_valid_typeof_of_smt_translation
        y hYTrans
    have hYSeqValid :
        TranslationProofs.eo_type_valid
          (Term.Apply (Term.UOp UserOp.Seq) UY) := by
      simpa [hYEoSeq] using hYEoValid
    have hSeqEq :
        Term.Apply (Term.UOp UserOp.Seq) UY =
          Term.Apply (Term.UOp UserOp.Seq) UX := by
      apply EvaluateProofInternal.eo_to_smt_type_eq_of_top_valid hYSeqValid
      simp [__eo_to_smt_type, hUYSmt, hUXSmt]
    cases hSeqEq
    have hUNe : UY ≠ Term.Stuck := by
      intro hStuck
      subst UY
      simpa [TranslationProofs.eo_type_valid,
        TranslationProofs.eo_type_valid_rec, TranslationProofs.noNoneTy,
        __eo_to_smt_type, __smtx_typeof_guard, native_ite,
        native_Teq] using hYSeqValid
    have hUEq : __eo_eq UY UY = Term.Boolean true := by
      cases UY <;> simp [__eo_eq, native_teq] at hUNe ⊢
    have hRunContainsNe :
        __eo_not
            (__eo_is_neg
              (__eo_find (__run_evaluate y)
                (__run_evaluate x))) ≠ Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunBodyTy :
        __eo_typeof
            (__eo_not
              (__eo_is_neg
                (__eo_find (__run_evaluate y)
                  (__run_evaluate x)))) =
          Term.Bool :=
      EvaluateProofInternal.eo_not_is_neg_find_typeof_bool_of_ne_stuck
        (__run_evaluate y) (__run_evaluate x)
        hRunContainsNe
    change
      __eo_typeof
          (__eo_not
            (__eo_is_neg
              (__eo_find (__run_evaluate y)
                (__run_evaluate x)))) =
        __eo_typeof_str_contains (__eo_typeof y)
          (__eo_typeof x)
    rw [hRunBodyTy, hYEoSeq, hXEoSeq]
    simp [__eo_typeof_str_contains, __eo_requires,
      hUEq, native_ite, native_teq, native_not]
  | str_leq =>
    have hLeqNN :
        term_has_non_none_type
          (SmtTerm.str_leq (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    rcases seq_char_binop_args_of_non_none
        (op := SmtTerm.str_leq)
        (typeof_str_leq_eq (__eo_to_smt y)
          (__eo_to_smt x)) hLeqNN with
      ⟨hYTyChar, hXTyChar⟩
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTyChar]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTyChar]
      simp
    have hYEoChar :=
      EvaluateProofInternal.eo_typeof_seq_char_of_smt_type_seq_char y
        hYTrans hYTyChar
    have hXEoChar :=
      EvaluateProofInternal.eo_typeof_seq_char_of_smt_type_seq_char x
        hXTrans hXTyChar
    have hRunLeqNe :
        __eo_ite
            (__eo_and (__eo_is_str (__run_evaluate y))
              (__eo_is_str (__run_evaluate x)))
            (__str_leq_eval_rec
              (__str_flatten
                (__str_nary_intro (__run_evaluate y)))
              (__str_flatten
                (__str_nary_intro (__run_evaluate x))))
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_leq)
                (__run_evaluate y))
              (__run_evaluate x)) ≠ Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunYNe : __run_evaluate y ≠ Term.Stuck := by
      intro hStuck
      apply hRunLeqNe
      rw [hStuck]
      cases hx : __run_evaluate x <;>
        simp [__eo_is_str, __eo_is_str_internal, __eo_and,
          __eo_ite, __eo_mk_apply, native_and, native_not,
          native_ite, native_teq]
    have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
      intro hStuck
      apply hRunLeqNe
      rw [hStuck]
      cases hy : __run_evaluate y <;>
        simp [__eo_is_str, __eo_is_str_internal, __eo_and,
          __eo_ite, __eo_mk_apply, native_and, native_not,
          native_ite, native_teq]
    have hYPres :=
      recY hYTrans hRunYNe
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunYSeq :
        __eo_typeof (__run_evaluate y) =
          Term.Apply (Term.UOp UserOp.Seq)
            (Term.UOp UserOp.Char) :=
      hYPres.trans hYEoChar
    have hRunXSeq :
        __eo_typeof (__run_evaluate x) =
          Term.Apply (Term.UOp UserOp.Seq)
            (Term.UOp UserOp.Char) :=
      hXPres.trans hXEoChar
    have hRunBodyTy :
        __eo_typeof
            (__eo_ite
              (__eo_and (__eo_is_str (__run_evaluate y))
                (__eo_is_str (__run_evaluate x)))
              (__str_leq_eval_rec
                (__str_flatten
                  (__str_nary_intro (__run_evaluate y)))
                (__str_flatten
                  (__str_nary_intro (__run_evaluate x))))
              (__eo_mk_apply
                (__eo_mk_apply (Term.UOp UserOp.str_leq)
                  (__run_evaluate y))
                (__run_evaluate x))) =
          Term.Bool :=
      EvaluateProofInternal.eo_str_leq_body_typeof_bool_of_seq_char_args_and_ne_stuck
        (__run_evaluate y) (__run_evaluate x)
        hRunYSeq hRunXSeq hRunLeqNe
    change
      __eo_typeof
          (__eo_ite
            (__eo_and (__eo_is_str (__run_evaluate y))
              (__eo_is_str (__run_evaluate x)))
            (__str_leq_eval_rec
              (__str_flatten
                (__str_nary_intro (__run_evaluate y)))
              (__str_flatten
                (__str_nary_intro (__run_evaluate x))))
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_leq)
                (__run_evaluate y))
              (__run_evaluate x))) =
        __eo_typeof_str_lt (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hYEoChar, hXEoChar]
    rfl
  | _ =>
    exact False.elim (hRun rfl)

theorem EvaluateProofInternal.run_evaluate_typeof_apply_ternary_uop
    (op : UserOp) (b y x : Term)
    (recB : EvaluateProofInternal.RunEvaluateTypeofGoal b)
    (recY : EvaluateProofInternal.RunEvaluateTypeofGoal y)
    (recX : EvaluateProofInternal.RunEvaluateTypeofGoal x)
    (hRun :
      __run_evaluate
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) b) y) x) ≠
        Term.Apply (Term.Apply (Term.Apply (Term.UOp op) b) y) x)
    (hTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) b) y) x))
    (hRunNe :
      __run_evaluate
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) b) y) x) ≠
        Term.Stuck) :
    __eo_typeof
        (__run_evaluate
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) b) y) x)) =
      __eo_typeof
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) b) y) x) := by
  cases op with
  | ite =>
    have hIteNN :
        term_has_non_none_type
          (SmtTerm.ite (__eo_to_smt b) (__eo_to_smt y)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      simpa [RuleProofs.eo_has_smt_translation] using hTrans
    rcases ite_args_of_non_none hIteNN with
      ⟨T, hBTyBool, hYTy, hXTy, hTNN⟩
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTyBool]
      simp
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTy]
      exact hTNN
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTy]
      exact hTNN
    have hBMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        b hBTrans
    have hYMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        y hYTrans
    have hXMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        x hXTrans
    have hBEoBool : __eo_typeof b = Term.Bool :=
      TranslationProofs.eo_to_smt_type_eq_bool
        (hBMatch.symm.trans hBTyBool)
    have hYEoValid :=
      TranslationProofs.eo_type_valid_typeof_of_smt_translation
        y hYTrans
    have hYEoEq : __eo_typeof y = __eo_typeof x := by
      have hEoSmt :
          __eo_to_smt_type (__eo_typeof y) =
            __eo_to_smt_type (__eo_typeof x) := by
        rw [← hYMatch, ← hXMatch, hYTy, hXTy]
      exact EvaluateProofInternal.eo_to_smt_type_eq_of_top_valid hYEoValid hEoSmt
    have hYTypeNe : __eo_typeof y ≠ Term.Stuck := by
      have hYTypeSmtNN :
          __eo_to_smt_type (__eo_typeof y) ≠ SmtType.None := by
        rw [← hYMatch, hYTy]
        exact hTNN
      exact
        TranslationProofs.eo_term_ne_stuck_of_smt_type_non_none
          (__eo_typeof y) hYTypeSmtNN
    have hOrigIteTy :
        __eo_typeof_ite (__eo_typeof b) (__eo_typeof y)
            (__eo_typeof x) =
          __eo_typeof y := by
      rw [hBEoBool, ← hYEoEq]
      exact
        EvaluateProofInternal.eo_typeof_ite_bool_same_of_ne_stuck
          (__eo_typeof y) hYTypeNe
    have hRunIteNe :
        __eo_ite (__run_evaluate b) (__run_evaluate y)
            (__run_evaluate x) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
        (__run_evaluate b) (__run_evaluate y)
        (__run_evaluate x) hRunIteNe with
      ⟨runCond, hRunCond, hSelectedNe⟩
    change
      __eo_typeof
          (__eo_ite (__run_evaluate b) (__run_evaluate y)
            (__run_evaluate x)) =
        __eo_typeof_ite (__eo_typeof b) (__eo_typeof y)
          (__eo_typeof x)
    cases runCond
    · rw [hRunCond]
      change
        __eo_typeof (__run_evaluate x) =
          __eo_typeof_ite (__eo_typeof b) (__eo_typeof y)
            (__eo_typeof x)
      have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
        simpa using hSelectedNe
      have hXPres :=
        recX hXTrans hRunXNe
      exact hXPres.trans (hYEoEq.symm.trans hOrigIteTy.symm)
    · rw [hRunCond]
      change
        __eo_typeof (__run_evaluate y) =
          __eo_typeof_ite (__eo_typeof b) (__eo_typeof y)
            (__eo_typeof x)
      have hRunYNe : __run_evaluate y ≠ Term.Stuck := by
        simpa using hSelectedNe
      have hYPres :=
        recY hYTrans hRunYNe
      exact hYPres.trans hOrigIteTy.symm
    | str_substr =>
      have hSubstrNN :
          term_has_non_none_type
            (SmtTerm.str_substr (__eo_to_smt b)
              (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        have hsimpa := hTrans
        try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
        exact hsimpa
      rcases str_substr_args_of_non_none hSubstrNN with
        ⟨T, hBTySeq, hYTyInt, hXTyInt⟩
      have hBTrans : RuleProofs.eo_has_smt_translation b := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hBTySeq]
        simp
      have hYTrans : RuleProofs.eo_has_smt_translation y := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hYTyInt]
        simp
      have hXTrans : RuleProofs.eo_has_smt_translation x := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hXTyInt]
        simp
      rcases EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq b hBTrans
          hBTySeq with
        ⟨U, hBEoSeq, _hUSmt⟩
      have hYMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          y hYTrans
      have hXMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation
          x hXTrans
      have hYEoInt : __eo_typeof y = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hYMatch.symm.trans hYTyInt)
      have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int
          (hXMatch.symm.trans hXTyInt)
      have hRunSubstrNe :
          (let runY := __run_evaluate y
           __eo_extract (__run_evaluate b) runY
            (__eo_add (__eo_add runY (__run_evaluate x))
              (Term.Numeral (-1 : native_Int)))) ≠
            Term.Stuck := by
        simpa [__run_evaluate] using hRunNe
      have hRunBNe : __run_evaluate b ≠ Term.Stuck :=
        EvaluateProofInternal.eo_extract_target_ne_stuck
          (by simpa using hRunSubstrNe)
      have hBPres :=
        recB hBTrans hRunBNe
      have hRunBSeq :
          __eo_typeof (__run_evaluate b) =
            Term.Apply (Term.UOp UserOp.Seq) U :=
        hBPres.trans hBEoSeq
      have hRunBodyTy :
          __eo_typeof
              (let runY := __run_evaluate y
               __eo_extract (__run_evaluate b) runY
                (__eo_add (__eo_add runY (__run_evaluate x))
                  (Term.Numeral (-1 : native_Int)))) =
            Term.Apply (Term.UOp UserOp.Seq) U :=
        EvaluateProofInternal.eo_extract_typeof_seq_of_target_seq_and_ne_stuck
          (__run_evaluate b) (__run_evaluate y)
          (__eo_add
            (__eo_add (__run_evaluate y) (__run_evaluate x))
            (Term.Numeral (-1 : native_Int)))
          U hRunBSeq
          (by simpa using hRunSubstrNe)
      change
        __eo_typeof
            (let runY := __run_evaluate y
             __eo_extract (__run_evaluate b) runY
              (__eo_add (__eo_add runY (__run_evaluate x))
                (Term.Numeral (-1 : native_Int)))) =
          __eo_typeof_str_substr (__eo_typeof b)
            (__eo_typeof y) (__eo_typeof x)
      rw [hRunBodyTy, hBEoSeq, hYEoInt, hXEoInt]
      rfl
  | str_replace =>
    have hReplaceNN :
        term_has_non_none_type
          (SmtTerm.str_replace (__eo_to_smt b)
            (__eo_to_smt y) (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    rcases seq_triop_args_of_non_none
        (op := SmtTerm.str_replace)
        (typeof_str_replace_eq (__eo_to_smt b)
          (__eo_to_smt y) (__eo_to_smt x)) hReplaceNN with
      ⟨T, hBTySeq, hYTySeq, hXTySeq⟩
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTySeq]
      simp
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTySeq]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTySeq]
      simp
    rcases EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq b hBTrans
        hBTySeq with
      ⟨U, hBEoSeq, hUSmt⟩
    rcases EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq y hYTrans
        hYTySeq with
      ⟨UY, hYEoSeq, hUYSmt⟩
    rcases EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq x hXTrans
        hXTySeq with
      ⟨UX, hXEoSeq, hUXSmt⟩
    have hBValid :=
      TranslationProofs.eo_type_valid_typeof_of_smt_translation
        b hBTrans
    have hBSeqValid :
        TranslationProofs.eo_type_valid
          (Term.Apply (Term.UOp UserOp.Seq) U) := by
      simpa [hBEoSeq] using hBValid
    have hSeqYEq :
        Term.Apply (Term.UOp UserOp.Seq) U =
          Term.Apply (Term.UOp UserOp.Seq) UY :=
      EvaluateProofInternal.eo_seq_type_eq_of_same_smt_elem hBSeqValid hUSmt hUYSmt
    cases hSeqYEq
    have hSeqXEq :
        Term.Apply (Term.UOp UserOp.Seq) U =
          Term.Apply (Term.UOp UserOp.Seq) UX :=
      EvaluateProofInternal.eo_seq_type_eq_of_same_smt_elem hBSeqValid hUSmt hUXSmt
    cases hSeqXEq
    have hUNe : U ≠ Term.Stuck := by
      intro hStuck
      subst U
      simpa [TranslationProofs.eo_type_valid,
        TranslationProofs.eo_type_valid_rec, TranslationProofs.noNoneTy,
        __eo_to_smt_type, __smtx_typeof_guard, native_ite,
        native_Teq] using hBSeqValid
    have hUEq : __eo_eq U U = Term.Boolean true := by
      cases U <;> simp [__eo_eq, native_teq] at hUNe ⊢
    have hRunReplaceNe :
        (let runB := __run_evaluate b
         let runY := __run_evaluate y
         let idx := __eo_find (__eo_to_str runB) (__eo_to_str runY)
         __eo_ite (__eo_is_neg idx) runB
          (__eo_concat
            (__eo_concat
              (__eo_extract runB (Term.Numeral 0)
                (__eo_add idx (Term.Numeral (-1 : native_Int))))
              (__run_evaluate x))
            (__eo_extract runB
              (__eo_add idx (__eo_len runY)) (__eo_len runB)))) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunBNe : __run_evaluate b ≠ Term.Stuck :=
      EvaluateProofInternal.eo_str_replace_body_source_ne_stuck_of_ne_stuck
        (__run_evaluate b) (__run_evaluate y)
        (__run_evaluate x) (by simpa using hRunReplaceNe)
    have hBPres :=
      recB hBTrans hRunBNe
    have hRunBSeq :
        __eo_typeof (__run_evaluate b) =
          Term.Apply (Term.UOp UserOp.Seq) U :=
      hBPres.trans hBEoSeq
    have hRunXSeqOfNe :
        __run_evaluate x ≠ Term.Stuck ->
          __eo_typeof (__run_evaluate x) =
            Term.Apply (Term.UOp UserOp.Seq) U := by
      intro hRunXNe
      have hXPres :=
        recX hXTrans hRunXNe
      exact hXPres.trans hXEoSeq
    have hRunBodyTy :
        __eo_typeof
          (let runB := __run_evaluate b
           let runY := __run_evaluate y
           let idx :=
            __eo_find (__eo_to_str runB) (__eo_to_str runY)
           __eo_ite (__eo_is_neg idx) runB
            (__eo_concat
              (__eo_concat
                (__eo_extract runB (Term.Numeral 0)
                  (__eo_add idx
                    (Term.Numeral (-1 : native_Int))))
                (__run_evaluate x))
              (__eo_extract runB
                (__eo_add idx (__eo_len runY))
                (__eo_len runB)))) =
          Term.Apply (Term.UOp UserOp.Seq) U :=
      EvaluateProofInternal.eo_str_replace_body_typeof_seq_of_args_seq_and_ne_stuck
        (__run_evaluate b) (__run_evaluate y)
        (__run_evaluate x) U hRunBSeq hRunXSeqOfNe
        (by simpa using hRunReplaceNe)
    change
      __eo_typeof
        (let runB := __run_evaluate b
         let runY := __run_evaluate y
         let idx :=
          __eo_find (__eo_to_str runB) (__eo_to_str runY)
         __eo_ite (__eo_is_neg idx) runB
          (__eo_concat
            (__eo_concat
              (__eo_extract runB (Term.Numeral 0)
                (__eo_add idx
                  (Term.Numeral (-1 : native_Int))))
              (__run_evaluate x))
            (__eo_extract runB
              (__eo_add idx (__eo_len runY))
              (__eo_len runB)))) =
        __eo_typeof_str_replace (__eo_typeof b)
          (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hBEoSeq, hYEoSeq, hXEoSeq]
    simp [__eo_typeof_str_replace, __eo_requires, __eo_and,
      hUEq, native_ite, native_teq, native_and, native_not]
  | str_indexof =>
    have hIndexNN :
        term_has_non_none_type
          (SmtTerm.str_indexof (__eo_to_smt b)
            (__eo_to_smt y) (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    rcases str_indexof_args_of_non_none hIndexNN with
      ⟨T, hBTySeq, hYTySeq, hXTyInt⟩
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTySeq]
      simp
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTySeq]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTyInt]
      simp
    rcases EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq b hBTrans
        hBTySeq with
      ⟨U, hBEoSeq, hUSmt⟩
    rcases EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq y hYTrans
        hYTySeq with
      ⟨UY, hYEoSeq, hUYSmt⟩
    have hBValid :=
      TranslationProofs.eo_type_valid_typeof_of_smt_translation
        b hBTrans
    have hBSeqValid :
        TranslationProofs.eo_type_valid
          (Term.Apply (Term.UOp UserOp.Seq) U) := by
      simpa [hBEoSeq] using hBValid
    have hSeqYEq :
        Term.Apply (Term.UOp UserOp.Seq) U =
          Term.Apply (Term.UOp UserOp.Seq) UY :=
      EvaluateProofInternal.eo_seq_type_eq_of_same_smt_elem hBSeqValid hUSmt hUYSmt
    cases hSeqYEq
    have hUNe : U ≠ Term.Stuck := by
      intro hStuck
      subst U
      simpa [TranslationProofs.eo_type_valid,
        TranslationProofs.eo_type_valid_rec, TranslationProofs.noNoneTy,
        __eo_to_smt_type, __smtx_typeof_guard, native_ite,
        native_Teq] using hBSeqValid
    have hUEq : __eo_eq U U = Term.Boolean true := by
      cases U <;> simp [__eo_eq, native_teq] at hUNe ⊢
    have hXMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        x hXTrans
    have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int
        (hXMatch.symm.trans hXTyInt)
    have hRunIndexNe :
        (let lenS := __eo_len (__run_evaluate b)
         let find :=
          __eo_find
            (__eo_to_str
              (__eo_extract (__run_evaluate b) x lenS))
            (__eo_to_str (__run_evaluate y))
         __eo_ite (__eo_is_neg (__run_evaluate x))
          (Term.Numeral (-1 : native_Int))
          (__eo_ite (__eo_gt (__run_evaluate x) lenS)
            (Term.Numeral (-1 : native_Int))
            (__eo_ite (__eo_is_neg find) find
              (__eo_add x find)))) ≠ Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunBodyTy :
        __eo_typeof
          (let lenS := __eo_len (__run_evaluate b)
           let find :=
            __eo_find
              (__eo_to_str
                (__eo_extract (__run_evaluate b) x lenS))
              (__eo_to_str (__run_evaluate y))
           __eo_ite (__eo_is_neg (__run_evaluate x))
            (Term.Numeral (-1 : native_Int))
            (__eo_ite (__eo_gt (__run_evaluate x) lenS)
              (Term.Numeral (-1 : native_Int))
              (__eo_ite (__eo_is_neg find) find
                (__eo_add x find)))) =
          Term.UOp UserOp.Int :=
      EvaluateProofInternal.eo_str_indexof_body_typeof_int_of_start_int_and_ne_stuck
        (__run_evaluate b) (__run_evaluate y) x
        (__run_evaluate x) hXEoInt hRunIndexNe
    change
      __eo_typeof
          (let lenS := __eo_len (__run_evaluate b)
           let find :=
            __eo_find
              (__eo_to_str
                (__eo_extract (__run_evaluate b) x lenS))
              (__eo_to_str (__run_evaluate y))
           __eo_ite (__eo_is_neg (__run_evaluate x))
            (Term.Numeral (-1 : native_Int))
            (__eo_ite (__eo_gt (__run_evaluate x) lenS)
              (Term.Numeral (-1 : native_Int))
              (__eo_ite (__eo_is_neg find) find
                (__eo_add x find)))) =
        __eo_typeof_str_indexof (__eo_typeof b)
          (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hBEoSeq, hYEoSeq, hXEoInt]
    simp [__eo_typeof_str_indexof, __eo_requires, hUEq,
      native_ite, native_teq, native_not]
  | str_update =>
    have hUpdateNN :
        term_has_non_none_type
          (SmtTerm.str_update (__eo_to_smt b)
            (__eo_to_smt y) (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    rcases str_update_args_of_non_none hUpdateNN with
      ⟨T, hBTySeq, hYTyInt, hXTySeq⟩
    have hBTrans : RuleProofs.eo_has_smt_translation b := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hBTySeq]
      simp
    have hYTrans : RuleProofs.eo_has_smt_translation y := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hYTyInt]
      simp
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hXTySeq]
      simp
    rcases EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq b hBTrans
        hBTySeq with
      ⟨U, hBEoSeq, hUSmt⟩
    rcases EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq x hXTrans
        hXTySeq with
      ⟨UX, hXEoSeq, hUXSmt⟩
    have hBValid :=
      TranslationProofs.eo_type_valid_typeof_of_smt_translation
        b hBTrans
    have hBSeqValid :
        TranslationProofs.eo_type_valid
          (Term.Apply (Term.UOp UserOp.Seq) U) := by
      simpa [hBEoSeq] using hBValid
    have hSeqXEq :
        Term.Apply (Term.UOp UserOp.Seq) U =
          Term.Apply (Term.UOp UserOp.Seq) UX :=
      EvaluateProofInternal.eo_seq_type_eq_of_same_smt_elem hBSeqValid hUSmt hUXSmt
    cases hSeqXEq
    have hUNe : U ≠ Term.Stuck := by
      intro hStuck
      subst U
      simpa [TranslationProofs.eo_type_valid,
        TranslationProofs.eo_type_valid_rec, TranslationProofs.noNoneTy,
        __eo_to_smt_type, __smtx_typeof_guard, native_ite,
        native_Teq] using hBSeqValid
    have hUEq : __eo_eq U U = Term.Boolean true := by
      cases U <;> simp [__eo_eq, native_teq] at hUNe ⊢
    have hYMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        y hYTrans
    have hYEoInt : __eo_typeof y = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int
        (hYMatch.symm.trans hYTyInt)
    have hRunUpdateNe :
        (let runB := __run_evaluate b
         let lenS := __eo_len runB
         let runX := __run_evaluate x
         let runY := __run_evaluate y
         __eo_ite
          (__eo_or (__eo_gt (Term.Numeral 0) runY)
            (__eo_gt runY lenS))
          runB
          (__eo_concat
            (__eo_concat
              (__eo_extract runB (Term.Numeral 0)
                (__eo_add runY
                  (Term.Numeral (-1 : native_Int))))
              (__eo_extract runX (Term.Numeral 0)
                (__eo_add (__eo_add (__eo_neg runY) lenS)
                  (Term.Numeral (-1 : native_Int)))))
            (__eo_extract runB
              (__eo_add runY (__eo_len runX)) lenS))) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunBNe : __run_evaluate b ≠ Term.Stuck :=
      EvaluateProofInternal.eo_str_update_body_source_ne_stuck_of_ne_stuck
        (__run_evaluate b) (__run_evaluate y)
        (__run_evaluate x) (by simpa using hRunUpdateNe)
    have hBPres :=
      recB hBTrans hRunBNe
    have hRunBSeq :
        __eo_typeof (__run_evaluate b) =
          Term.Apply (Term.UOp UserOp.Seq) U :=
      hBPres.trans hBEoSeq
    have hRunXSeqOfNe :
        __run_evaluate x ≠ Term.Stuck ->
          __eo_typeof (__run_evaluate x) =
            Term.Apply (Term.UOp UserOp.Seq) U := by
      intro hRunXNe
      have hXPres :=
        recX hXTrans hRunXNe
      exact hXPres.trans hXEoSeq
    have hRunBodyTy :
        __eo_typeof
          (let runB := __run_evaluate b
           let lenS := __eo_len runB
           let runX := __run_evaluate x
           let runY := __run_evaluate y
           __eo_ite
            (__eo_or (__eo_gt (Term.Numeral 0) runY)
              (__eo_gt runY lenS))
            runB
            (__eo_concat
              (__eo_concat
                (__eo_extract runB (Term.Numeral 0)
                  (__eo_add runY
                    (Term.Numeral (-1 : native_Int))))
                (__eo_extract runX (Term.Numeral 0)
                  (__eo_add (__eo_add (__eo_neg runY) lenS)
                    (Term.Numeral (-1 : native_Int)))))
              (__eo_extract runB
                (__eo_add runY (__eo_len runX)) lenS))) =
          Term.Apply (Term.UOp UserOp.Seq) U :=
      EvaluateProofInternal.eo_str_update_body_typeof_seq_of_args_seq_and_ne_stuck
        (__run_evaluate b) (__run_evaluate y)
        (__run_evaluate x) U hRunBSeq hRunXSeqOfNe
        (by simpa using hRunUpdateNe)
    change
      __eo_typeof
        (let runB := __run_evaluate b
         let lenS := __eo_len runB
         let runX := __run_evaluate x
         let runY := __run_evaluate y
         __eo_ite
          (__eo_or (__eo_gt (Term.Numeral 0) runY)
            (__eo_gt runY lenS))
          runB
          (__eo_concat
            (__eo_concat
              (__eo_extract runB (Term.Numeral 0)
                (__eo_add runY
                  (Term.Numeral (-1 : native_Int))))
              (__eo_extract runX (Term.Numeral 0)
                (__eo_add (__eo_add (__eo_neg runY) lenS)
                  (Term.Numeral (-1 : native_Int)))))
            (__eo_extract runB
              (__eo_add runY (__eo_len runX)) lenS))) =
        __eo_typeof_str_update (__eo_typeof b)
          (__eo_typeof y) (__eo_typeof x)
    rw [hRunBodyTy, hBEoSeq, hYEoInt, hXEoSeq]
    simp [__eo_typeof_str_update, __eo_requires, hUEq,
      native_ite, native_teq, native_not]
  | str_replace_all =>
    exact EvaluateProofInternal.run_evaluate_typeof_eq_str_replace_all b y x
  | _ =>
    exact False.elim (hRun rfl)

theorem EvaluateProofInternal.run_evaluate_typeof_apply_uop1
    (op : UserOp1) (n x : Term)
    (recX : EvaluateProofInternal.RunEvaluateTypeofGoal x)
    (hRun :
      __run_evaluate (Term.Apply (Term.UOp1 op n) x) ≠
        Term.Apply (Term.UOp1 op n) x)
    (hTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp1 op n) x))
    (hRunNe :
      __run_evaluate (Term.Apply (Term.UOp1 op n) x) ≠ Term.Stuck) :
    __eo_typeof (__run_evaluate (Term.Apply (Term.UOp1 op n) x)) =
      __eo_typeof (Term.Apply (Term.UOp1 op n) x) := by
  cases op with
  | «repeat» =>
    have hRepeatNN :
        term_has_non_none_type
          (SmtTerm.repeat (__eo_to_smt n) (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    rcases repeat_args_of_non_none hRepeatNN with
      ⟨i, w, hnSmt, hxSmtTy, hi1⟩
    have hnTerm : n = Term.Numeral i :=
      TranslationProofs.eo_to_smt_eq_numeral n i hnSmt
    subst n
    have hi : (1 : Int) <= i := by
      simpa [native_zleq, SmtEval.native_zleq] using hi1
    have hIGtZero : native_zlt 0 i = true := by
      have hlt : (0 : Int) < i := by omega
      simpa [native_zlt, SmtEval.native_zlt] using hlt
    have hiNotNeg : native_zlt i 0 = false := by
      simp [native_zlt, SmtEval.native_zlt]
      omega
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hxSmtTy]
      simp
    have hXEoBv :=
      EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec x w hxSmtTy
    have hRunRepeatNe :
        __bv_eval_concat
            (__eo_list_repeat (Term.UOp UserOp.concat)
              (__run_evaluate x) (Term.Numeral i)) ≠
          Term.Stuck := by
      intro hStuck
      apply hRunNe
      simp [__run_evaluate, __eo_is_z, __eo_is_z_internal,
        __eo_is_neg, __eo_not, __eo_and, __eo_ite, native_ite,
        native_teq, native_and, native_not, SmtEval.native_not,
        hiNotNeg, hStuck]
    have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
      intro hStuck
      apply hRunRepeatNe
      rw [hStuck]
      simp [__eo_list_repeat, __bv_eval_concat]
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunXBv :
        __eo_typeof (__run_evaluate x) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      hXPres.trans hXEoBv
    have hRunBodyTy :
        __eo_typeof
            (__bv_eval_concat
              (__eo_list_repeat (Term.UOp UserOp.concat)
                (__run_evaluate x) (Term.Numeral i))) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral
              (native_zmult i (native_nat_to_int w))) :=
      EvaluateProofInternal.eo_repeat_typeof_bitvec_of_arg_bitvec_and_ne_stuck
        (__run_evaluate x) i (native_nat_to_int w)
        hi1 hRunXBv hRunRepeatNe
    change
      __eo_typeof
          (__eo_ite
            (__eo_and (__eo_is_z (Term.Numeral i))
              (__eo_not (__eo_is_neg (Term.Numeral i))))
            (__bv_eval_concat
              (__eo_list_repeat (Term.UOp UserOp.concat)
                (__run_evaluate x) (Term.Numeral i)))
            (__eo_mk_apply
              (Term.UOp1 UserOp1.repeat (Term.Numeral i))
              (__run_evaluate x))) =
        __eo_typeof
          (Term.Apply
            (Term.UOp1 UserOp1.repeat (Term.Numeral i)) x)
    simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg,
      __eo_not, __eo_and, native_ite, native_teq, native_and,
      native_not, SmtEval.native_not, hiNotNeg]
    change
      __eo_typeof
          (__bv_eval_concat
            (__eo_list_repeat (Term.UOp UserOp.concat)
              (__run_evaluate x) (Term.Numeral i))) =
        __eo_typeof_repeat (Term.UOp UserOp.Int)
          (Term.Numeral i) (__eo_typeof x)
    rw [hXEoBv]
    simpa [__eo_typeof_repeat, __eo_requires, __eo_gt, __eo_mul,
      __eo_mk_apply, native_ite, native_teq, native_not,
      hIGtZero] using
      hRunBodyTy
  | zero_extend =>
    have hZeroNN :
        term_has_non_none_type
          (SmtTerm.zero_extend (__eo_to_smt n)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    rcases zero_extend_args_of_non_none hZeroNN with
      ⟨i, w, hnSmt, hxSmtTy, hi0⟩
    have hnTerm : n = Term.Numeral i :=
      TranslationProofs.eo_to_smt_eq_numeral n i hnSmt
    subst n
    have hIGtNegOne : native_zlt (-1 : native_Int) i = true := by
      have hi : (0 : Int) <= i := by
        simpa [native_zleq, SmtEval.native_zleq] using hi0
      have hlt : (-1 : Int) < i := by omega
      simpa [native_zlt, SmtEval.native_zlt] using hlt
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hxSmtTy]
      simp
    have hXEoBv :=
      EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec x w hxSmtTy
    have hRunZeroNe :
        __eo_to_bin
            (__eo_add
              (__bv_bitwidth (__eo_typeof (__run_evaluate x)))
              (Term.Numeral i))
            (__eo_to_z (__run_evaluate x)) ≠ Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunToZNe :
        __eo_to_z (__run_evaluate x) ≠ Term.Stuck :=
      EvaluateProofInternal.eo_to_bin_value_ne_stuck hRunZeroNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_to_z_arg_ne_stuck hRunToZNe
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunXBv :
        __eo_typeof (__run_evaluate x) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      hXPres.trans hXEoBv
    have hRunZeroNe' :
        __eo_to_bin
            (Term.Numeral
              (native_zplus (native_nat_to_int w) i))
            (__eo_to_z (__run_evaluate x)) ≠ Term.Stuck := by
      simpa [hRunXBv, __bv_bitwidth, __eo_add] using
        hRunZeroNe
    have hRunBodyTy :
        __eo_typeof
            (__eo_to_bin
              (Term.Numeral
                (native_zplus (native_nat_to_int w) i))
              (__eo_to_z (__run_evaluate x))) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral
              (native_zplus (native_nat_to_int w) i)) :=
      EvaluateProofInternal.eo_to_bin_typeof_bitvec_of_width_numeral_and_ne_stuck
        (native_zplus (native_nat_to_int w) i)
        (__eo_to_z (__run_evaluate x)) hRunZeroNe'
    change
      __eo_typeof
          (__eo_to_bin
            (__eo_add
              (__bv_bitwidth
                (__eo_typeof (__run_evaluate x)))
              (Term.Numeral i))
            (__eo_to_z (__run_evaluate x))) =
        __eo_typeof_zero_extend (Term.UOp UserOp.Int)
          (Term.Numeral i) (__eo_typeof x)
    rw [hRunXBv, hXEoBv]
    simpa [__bv_bitwidth, __eo_typeof_zero_extend, __eo_add,
      __eo_requires, __eo_gt, __eo_mk_apply, native_ite,
      native_teq, native_not, hIGtNegOne] using hRunBodyTy
  | sign_extend =>
    have hSignNN :
        term_has_non_none_type
          (SmtTerm.sign_extend (__eo_to_smt n)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    rcases sign_extend_args_of_non_none hSignNN with
      ⟨i, w, hnSmt, hxSmtTy, hi0⟩
    have hnTerm : n = Term.Numeral i :=
      TranslationProofs.eo_to_smt_eq_numeral n i hnSmt
    subst n
    have hIGtNegOne : native_zlt (-1 : native_Int) i = true := by
      have hi : (0 : Int) <= i := by
        simpa [native_zleq, SmtEval.native_zleq] using hi0
      have hlt : (-1 : Int) < i := by omega
      simpa [native_zlt, SmtEval.native_zlt] using hlt
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hxSmtTy]
      simp
    have hXEoBv :=
      EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec x w hxSmtTy
    have hRunSignNe :
        EvaluateProofInternal.eo_eval_sign_extend_rhs (__run_evaluate x)
            (Term.Numeral i) ≠ Term.Stuck := by
      simpa [__run_evaluate, EvaluateProofInternal.eo_eval_sign_extend_rhs] using
        hRunNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
      intro hStuck
      apply hRunSignNe
      rw [hStuck]
      have hTy : __eo_typeof Term.Stuck = Term.Stuck := rfl
      simp [EvaluateProofInternal.eo_eval_sign_extend_rhs, hTy, __bv_bitwidth,
        __eo_add, __eo_to_bin]
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunXBv :
        __eo_typeof (__run_evaluate x) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      hXPres.trans hXEoBv
    have hRunSignNe' :
        __eo_to_bin
            (Term.Numeral
              (native_zplus (native_nat_to_int w) i))
            (let _v1 :=
              __bv_bitwidth (__eo_typeof (__run_evaluate x))
             let _v2 :=
              __eo_to_z
                (__eo_extract (__run_evaluate x)
                  (Term.Numeral 0)
                  (__eo_add _v1
                    (Term.Numeral (-2 : native_Int))))
             let _v3 :=
              __eo_add _v1 (Term.Numeral (-1 : native_Int))
             __eo_ite
              (__eo_eq
                (__eo_extract (__run_evaluate x) _v3 _v3)
                (Term.Binary 1 1))
              (__eo_add
                (__eo_neg
                  (__eo_ite (__eo_is_z _v3)
                    (__eo_ite (__eo_is_neg _v3)
                      (Term.Numeral 0) (__eo_pow (Term.Numeral 2) _v3))
                    (__eo_mk_apply (Term.UOp UserOp.int_pow2) _v3)))
                _v2)
              _v2) ≠ Term.Stuck := by
      simpa [EvaluateProofInternal.eo_eval_sign_extend_rhs, hRunXBv, __bv_bitwidth,
        __eo_add] using hRunSignNe
    have hRunBodyTy :
        __eo_typeof
            (__eo_to_bin
              (Term.Numeral
                (native_zplus (native_nat_to_int w) i))
              (let _v1 :=
                __bv_bitwidth (__eo_typeof (__run_evaluate x))
               let _v2 :=
                __eo_to_z
                  (__eo_extract (__run_evaluate x)
                    (Term.Numeral 0)
                    (__eo_add _v1
                      (Term.Numeral (-2 : native_Int))))
               let _v3 :=
                __eo_add _v1 (Term.Numeral (-1 : native_Int))
               __eo_ite
                (__eo_eq
                  (__eo_extract (__run_evaluate x) _v3 _v3)
                  (Term.Binary 1 1))
                (__eo_add
                  (__eo_neg
                    (__eo_ite (__eo_is_z _v3)
                      (__eo_ite (__eo_is_neg _v3)
                        (Term.Numeral 0)
                        (__eo_pow (Term.Numeral 2) _v3))
                      (__eo_mk_apply (Term.UOp UserOp.int_pow2) _v3)))
                  _v2)
                _v2)) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral
              (native_zplus (native_nat_to_int w) i)) :=
      EvaluateProofInternal.eo_to_bin_typeof_bitvec_of_width_numeral_and_ne_stuck
        (native_zplus (native_nat_to_int w) i) _ hRunSignNe'
    change
      __eo_typeof
          (EvaluateProofInternal.eo_eval_sign_extend_rhs (__run_evaluate x)
            (Term.Numeral i)) =
        __eo_typeof_zero_extend (Term.UOp UserOp.Int)
          (Term.Numeral i) (__eo_typeof x)
    rw [hXEoBv]
    simpa [EvaluateProofInternal.eo_eval_sign_extend_rhs, hRunXBv, __bv_bitwidth,
      __eo_add, __eo_typeof_zero_extend, __eo_requires, __eo_gt,
      __eo_mk_apply, native_ite, native_teq, native_not,
      hIGtNegOne] using
      hRunBodyTy
  | int_to_bv =>
    have hIntToBvNN :
        term_has_non_none_type
          (SmtTerm.int_to_bv (__eo_to_smt n)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    rcases int_to_bv_args_of_non_none hIntToBvNN with
      ⟨i, hnSmt, hxSmtTy, hi0⟩
    have hnTerm : n = Term.Numeral i :=
      TranslationProofs.eo_to_smt_eq_numeral n i hnSmt
    subst n
    have hIGtNegOne : native_zlt (-1 : native_Int) i = true := by
      have hi : (0 : Int) <= i := by
        simpa [native_zleq, SmtEval.native_zleq] using hi0
      have hlt : (-1 : Int) < i := by omega
      simpa [native_zlt, SmtEval.native_zlt] using hlt
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hxSmtTy]
      simp
    have hXMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation
        x hXTrans
    have hXEoInt : __eo_typeof x = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int
        (hXMatch.symm.trans hxSmtTy)
    have hRunToBvNe :
        __eo_to_bin (Term.Numeral i) (__run_evaluate x) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunBodyTy :
        __eo_typeof
            (__eo_to_bin (Term.Numeral i)
              (__run_evaluate x)) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral i) :=
      EvaluateProofInternal.eo_to_bin_typeof_bitvec_of_width_numeral_and_ne_stuck
        i (__run_evaluate x) hRunToBvNe
    change
      __eo_typeof
          (__eo_to_bin (Term.Numeral i)
            (__run_evaluate x)) =
        __eo_typeof_int_to_bv (Term.UOp UserOp.Int)
          (Term.Numeral i) (__eo_typeof x)
    rw [hXEoInt]
    simpa [__eo_typeof_int_to_bv, __eo_requires, __eo_gt,
      native_ite, native_teq, native_not, hIGtNegOne] using
      hRunBodyTy
  | _ =>
    exact False.elim (hRun rfl)

theorem EvaluateProofInternal.run_evaluate_typeof_apply_uop2
    (op : UserOp2) (hi lo x : Term)
    (recX : EvaluateProofInternal.RunEvaluateTypeofGoal x)
    (hRun :
      __run_evaluate (Term.Apply (Term.UOp2 op hi lo) x) ≠
        Term.Apply (Term.UOp2 op hi lo) x)
    (hTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp2 op hi lo) x))
    (hRunNe :
      __run_evaluate (Term.Apply (Term.UOp2 op hi lo) x) ≠ Term.Stuck) :
    __eo_typeof (__run_evaluate (Term.Apply (Term.UOp2 op hi lo) x)) =
      __eo_typeof (Term.Apply (Term.UOp2 op hi lo) x) := by
  cases op with
  | extract =>
    have hExtNN :
        term_has_non_none_type
          (SmtTerm.extract (__eo_to_smt hi)
            (__eo_to_smt lo) (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      have hsimpa := hTrans
      try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
      exact hsimpa
    rcases extract_args_of_non_none hExtNN with
      ⟨i, j, w, hHiSmt, hLoSmt, hxSmtTy, hj0, hji, hiw⟩
    have hHiTerm : hi = Term.Numeral i :=
      TranslationProofs.eo_to_smt_eq_numeral hi i hHiSmt
    have hLoTerm : lo = Term.Numeral j :=
      TranslationProofs.eo_to_smt_eq_numeral lo j hLoSmt
    subst hi
    subst lo
    have hXTrans : RuleProofs.eo_has_smt_translation x := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hxSmtTy]
      simp
    have hXEoBv :=
      EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec x w hxSmtTy
    have hRunExtNe :
        __eo_extract (__run_evaluate x)
            (Term.Numeral j) (Term.Numeral i) ≠
          Term.Stuck := by
      simpa [__run_evaluate] using hRunNe
    have hRunXNe : __run_evaluate x ≠ Term.Stuck :=
      EvaluateProofInternal.eo_extract_target_ne_stuck hRunExtNe
    have hXPres :=
      recX hXTrans hRunXNe
    have hRunXBv :
        __eo_typeof (__run_evaluate x) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int w)) :=
      hXPres.trans hXEoBv
    have hRunBodyTy :
        __eo_typeof
            (__eo_extract (__run_evaluate x)
              (Term.Numeral j) (Term.Numeral i)) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral
              (native_zplus (native_zplus i (native_zneg j)) 1)) :=
      EvaluateProofInternal.eo_extract_typeof_bitvec_of_arg_bitvec_and_ne_stuck
        (__run_evaluate x) i j (native_nat_to_int w)
        hj0 hji hRunXBv hRunExtNe
    have hjNonneg : 0 <= j := by
      simpa [native_zleq, SmtEval.native_zleq] using hj0
    have hLowSuccPos :
        native_zlt 0 (j + 1) = true := by
      have h : 0 < j + 1 := Int.lt_add_one_of_le hjNonneg
      simpa [native_zlt, SmtEval.native_zlt] using h
    have hJGtNegOne : native_zlt (-1 : native_Int) j = true := by
      have hlt : (-1 : native_Int) < j :=
        Int.lt_of_lt_of_le (by decide) hjNonneg
      simpa [native_zlt, SmtEval.native_zlt] using hlt
    have hWidthAssoc :
        native_zplus (native_zplus i 1) (native_zneg j) =
          native_zplus (native_zplus i (native_zneg j)) 1 := by
      simp [native_zplus, SmtEval.native_zplus, native_zneg,
        SmtEval.native_zneg, Int.add_assoc, Int.add_comm,
        Int.add_left_comm]
    have hWidthPos :
        native_zlt 0
            (native_zplus (native_zplus i (native_zneg j)) 1) =
          true := by
      simpa [hWidthAssoc] using hji
    have hWidthPosRaw :
        native_zlt 0 (i + -j + 1) = true := by
      simpa [native_zplus, SmtEval.native_zplus, native_zneg,
        SmtEval.native_zneg, Int.add_assoc] using hWidthPos
    have hWidthNonneg :
        native_zleq 0
            (native_zplus (native_zplus i (native_zneg j)) 1) =
          true := by
      have hPos :
          (0 : native_Int) <
            native_zplus
              (native_zplus i (native_zneg j)) 1 := by
        simpa [native_zlt, SmtEval.native_zlt] using hWidthPos
      simpa [native_zleq, SmtEval.native_zleq] using
        Int.le_of_lt hPos
    change
      __eo_typeof
          (__eo_extract (__run_evaluate x)
            (Term.Numeral j) (Term.Numeral i)) =
      __eo_typeof_extract (Term.UOp UserOp.Int)
        (Term.Numeral i) (Term.UOp UserOp.Int)
        (Term.Numeral j) (__eo_typeof x)
    rw [hXEoBv]
    simpa [__eo_typeof_extract, __eo_add, __eo_neg, __eo_gt,
      __eo_requires, __eo_mk_apply, hLowSuccPos, hJGtNegOne,
      hWidthNonneg, hWidthPos, hWidthPosRaw, hiw, native_ite,
      native_teq,
      native_not,
      native_zplus, SmtEval.native_zplus, native_zneg,
      SmtEval.native_zneg]
      using hRunBodyTy
  | _ =>
    exact False.elim (hRun rfl)

theorem EvaluateProofInternal.run_evaluate_typeof_eq_of_has_smt_translation_and_ne_stuck
    (t : Term) : EvaluateProofInternal.RunEvaluateTypeofGoal t := by
  intro hTrans hRunNe
  by_cases hRun : __run_evaluate t = t
  · rw [hRun]
  · cases t with
    | UOp2 _ _ _ =>
        exact False.elim (hRun rfl)
    | Apply f x =>
        cases f with
        | UOp op =>
            exact EvaluateProofInternal.run_evaluate_typeof_apply_uop op x
              (EvaluateProofInternal.run_evaluate_typeof_eq_of_has_smt_translation_and_ne_stuck x) hRun hTrans hRunNe
        | Apply g y =>
            cases g with
            | UOp op =>
                exact EvaluateProofInternal.run_evaluate_typeof_apply_binary_uop op y x
                  (EvaluateProofInternal.run_evaluate_typeof_eq_of_has_smt_translation_and_ne_stuck y)
                  (EvaluateProofInternal.run_evaluate_typeof_eq_of_has_smt_translation_and_ne_stuck x) hRun hTrans hRunNe
            | Apply a b =>
                cases a with
                | UOp op =>
                    exact EvaluateProofInternal.run_evaluate_typeof_apply_ternary_uop op b y x
                      (EvaluateProofInternal.run_evaluate_typeof_eq_of_has_smt_translation_and_ne_stuck b)
                      (EvaluateProofInternal.run_evaluate_typeof_eq_of_has_smt_translation_and_ne_stuck y)
                      (EvaluateProofInternal.run_evaluate_typeof_eq_of_has_smt_translation_and_ne_stuck x)
                      hRun hTrans hRunNe
                | _ =>
                    exact False.elim (hRun rfl)
            | _ =>
                exact False.elim (hRun rfl)
        | UOp1 op n =>
            exact EvaluateProofInternal.run_evaluate_typeof_apply_uop1 op n x
              (EvaluateProofInternal.run_evaluate_typeof_eq_of_has_smt_translation_and_ne_stuck x) hRun hTrans hRunNe
        | UOp2 op hi lo =>
            exact EvaluateProofInternal.run_evaluate_typeof_apply_uop2 op hi lo x
              (EvaluateProofInternal.run_evaluate_typeof_eq_of_has_smt_translation_and_ne_stuck x) hRun hTrans hRunNe
        | _ =>
            exact False.elim (hRun rfl)
    | _ =>
        exact False.elim (hRun rfl)
termination_by sizeOf t

theorem EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_has_smt_translation
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hRunNe : __run_evaluate t ≠ Term.Stuck) :
    __eo_typeof (__eo_prog_evaluate t) = Term.Bool :=
  EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_run_typeof_eq t hTrans
    (EvaluateProofInternal.run_evaluate_typeof_eq_of_has_smt_translation_and_ne_stuck
      t hTrans hRunNe)

theorem EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_int
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int)
    (hRunNe : __run_evaluate t ≠ Term.Stuck) :
    __eo_typeof (__eo_prog_evaluate t) = Term.Bool := by
  exact EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_has_smt_translation t hTrans hRunNe

theorem EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_bitvec
    (t : Term) (w : native_Nat)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hRunNe : __run_evaluate t ≠ Term.Stuck) :
    __eo_typeof (__eo_prog_evaluate t) = Term.Bool := by
  exact EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_has_smt_translation t hTrans hRunNe

theorem EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_real
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Real)
    (hRunNe : __run_evaluate t ≠ Term.Stuck) :
    __eo_typeof (__eo_prog_evaluate t) = Term.Bool := by
  exact EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_has_smt_translation t hTrans hRunNe

theorem EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_smt_type_seq
    (t : Term) (T : SmtType)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hRunNe : __run_evaluate t ≠ Term.Stuck) :
    __eo_typeof (__eo_prog_evaluate t) = Term.Bool := by
  exact EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_has_smt_translation t hTrans hRunNe
