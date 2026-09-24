module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev lenConcatTail (s2 s3 : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat s2) s3

private abbrev lenConcatLhs (s1 s2 s3 : Term) : Term :=
  Term.Apply Term.str_len (Term.Apply (Term.Apply Term.str_concat s1)
    (lenConcatTail s2 s3))

private abbrev lenConcatRhsTail (s2 s3 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.plus)
    (Term.Apply Term.str_len (__str_nary_elim (lenConcatTail s2 s3))))
    (Term.Numeral 0)

private abbrev lenConcatRhs (s1 s2 s3 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Apply Term.str_len s1))
    (lenConcatRhsTail s2 s3)

private abbrev lenConcatConclusion (s1 s2 s3 : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (lenConcatLhs s1 s2 s3))
    (lenConcatRhs s1 s2 s3)

private theorem eo_typeof_str_len_arg_seq_of_ne_stuck
    (T : Term)
    (h : __eo_typeof_str_len T ≠ Term.Stuck) :
    ∃ U, T = Term.Apply Term.Seq U := by
  cases T <;> simp [__eo_typeof_str_len] at h ⊢
  case Apply f x =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢

private theorem eo_typeof_str_concat_args_seq
    (A B U : Term)
    (h : __eo_typeof_str_concat A B = Term.Apply Term.Seq U) :
    A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U := by
  cases A <;> simp [__eo_typeof_str_concat, Term.Seq] at h ⊢
  case Apply fA xA =>
    cases fA <;> simp [__eo_typeof_str_concat] at h ⊢
    case UOp opA =>
      cases opA <;> simp [__eo_typeof_str_concat] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_concat] at h ⊢
        case Apply fB xB =>
          cases fB <;> simp [__eo_typeof_str_concat] at h ⊢
          case UOp opB =>
            cases opB <;> simp [__eo_typeof_str_concat, Term.Seq] at h ⊢
            case Seq =>
              have hNe : __eo_requires (__eo_eq xA xB) (Term.Boolean true)
                  (Term.Apply Term.Seq xA) ≠ Term.Stuck := by
                rw [h]
                simp [Term.Seq]
              have hRes : Term.Apply Term.Seq xA = Term.Apply Term.Seq U := by
                rw [← eo_requires_eq_result_of_ne_stuck (__eo_eq xA xB)
                  (Term.Boolean true) (Term.Apply Term.Seq xA) hNe]
                exact h
              have hxAU : xA = U := (Term.Apply.inj hRes).2
              have hCond : __eo_eq xA xB = Term.Boolean true :=
                eo_requires_eq_of_ne_stuck (__eo_eq xA xB) (Term.Boolean true)
                  (Term.Apply Term.Seq xA) hNe
              have hxBA : xB = xA := RuleProofs.eq_of_eo_eq_true xA xB hCond
              exact ⟨by rw [hxAU], by rw [hxBA, hxAU]⟩

private theorem smtx_typeof_of_eo_seq
    (a T : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Apply Term.Seq T) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type T) := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  have hComponentNN : __eo_to_smt_type T ≠ SmtType.None := by
    intro hNone
    unfold RuleProofs.eo_has_smt_translation at hTrans
    apply hTrans
    rw [hTyRaw, hTy]
    simp [TranslationProofs.eo_to_smt_type_seq,
      __smtx_typeof_guard, hNone, native_ite, native_Teq]
  rw [hTy] at hTyRaw
  rw [TranslationProofs.eo_to_smt_type_seq] at hTyRaw
  simpa using hTyRaw.trans
    (TranslationProofs.smtx_typeof_guard_of_non_none
      (__eo_to_smt_type T) (SmtType.Seq (__eo_to_smt_type T)) hComponentNN)

private theorem smtx_eval_plus_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.plus x y) =
      __smtx_model_eval_plus
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_str_concat_term_eq_raw
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_concat x y) =
      __smtx_model_eval_str_concat
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem prog_str_len_concat_rec_eq_of_ne_stuck
    (s1 s2 s3 : Term)
    (hS1 : s1 ≠ Term.Stuck) (hS2 : s2 ≠ Term.Stuck)
    (hS3 : s3 ≠ Term.Stuck)
    (hElim : __str_nary_elim (lenConcatTail s2 s3) ≠ Term.Stuck) :
    __eo_prog_str_len_concat_rec s1 s2 s3 =
      lenConcatConclusion s1 s2 s3 := by
  simp [__eo_prog_str_len_concat_rec, hS1, hS2, hS3, lenConcatConclusion,
    lenConcatLhs, lenConcatRhs, lenConcatRhsTail, lenConcatTail, __str_nary_elim,
    hElim, __eo_mk_apply]

private theorem prog_str_len_concat_rec_stuck_of_elim_stuck
    (s1 s2 s3 : Term)
    (hS1 : s1 ≠ Term.Stuck) (hS2 : s2 ≠ Term.Stuck)
    (hS3 : s3 ≠ Term.Stuck)
    (hElim : __str_nary_elim (lenConcatTail s2 s3) = Term.Stuck) :
    __eo_prog_str_len_concat_rec s1 s2 s3 = Term.Stuck := by
  simp [__eo_prog_str_len_concat_rec, hS1, hS2, hS3, lenConcatTail,
    __str_nary_elim, hElim, __eo_mk_apply]

private theorem typed___eo_prog_str_len_concat_rec_impl
    (s1 s2 s3 : Term)
    (hS1Trans : RuleProofs.eo_has_smt_translation s1)
    (hS2Trans : RuleProofs.eo_has_smt_translation s2)
    (hS3Trans : RuleProofs.eo_has_smt_translation s3)
    (hS1Ty : __eo_typeof s1 = Term.Apply Term.Seq T)
    (hS2Ty : __eo_typeof s2 = Term.Apply Term.Seq T)
    (hS3Ty : __eo_typeof s3 = Term.Apply Term.Seq T)
    (hElim : __str_nary_elim (lenConcatTail s2 s3) ≠ Term.Stuck) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_len_concat_rec s1 s2 s3) := by
  let tail := lenConcatTail s2 s3
  let lhs := lenConcatLhs s1 s2 s3
  let rhsTail := lenConcatRhsTail s2 s3
  let rhs := lenConcatRhs s1 s2 s3
  have hS1SmtTy := smtx_typeof_of_eo_seq s1 T hS1Trans hS1Ty
  have hS2SmtTy := smtx_typeof_of_eo_seq s2 T hS2Trans hS2Ty
  have hS3SmtTy := smtx_typeof_of_eo_seq s3 T hS3Trans hS3Ty
  have hTailTy : __smtx_typeof (__eo_to_smt tail) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt s2) (__eo_to_smt s3)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hS2SmtTy, hS3SmtTy, __smtx_typeof_seq_op_2, native_ite, native_Teq]
  have hConcatTy : __smtx_typeof
      (__eo_to_smt (Term.Apply (Term.Apply Term.str_concat s1) tail)) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt s1) (__eo_to_smt tail)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hS1SmtTy, hTailTy, __smtx_typeof_seq_op_2, native_ite, native_Teq]
  have hElimTy : __smtx_typeof (__eo_to_smt (__str_nary_elim tail)) =
      SmtType.Seq (__eo_to_smt_type T) :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck tail (__eo_to_smt_type T)
      hTailTy hElim
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Int := by
    have hRawConcatTy :
        __smtx_typeof (SmtTerm.str_concat (__eo_to_smt s1) (__eo_to_smt tail)) =
          SmtType.Seq (__eo_to_smt_type T) := by
      simpa using hConcatTy
    change __smtx_typeof
        (SmtTerm.str_len
          (SmtTerm.str_concat (__eo_to_smt s1) (__eo_to_smt tail))) =
      SmtType.Int
    rw [typeof_str_len_eq]
    simp [hRawConcatTy, __smtx_typeof_seq_op_1_ret]
  have hLenS1Ty :
      __smtx_typeof (__eo_to_smt (Term.Apply Term.str_len s1)) = SmtType.Int := by
    change __smtx_typeof (SmtTerm.str_len (__eo_to_smt s1)) = SmtType.Int
    rw [typeof_str_len_eq]
    simp [hS1SmtTy, __smtx_typeof_seq_op_1_ret]
  have hLenElimTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply Term.str_len (__str_nary_elim tail))) =
        SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.str_len (__eo_to_smt (__str_nary_elim tail))) = SmtType.Int
    rw [typeof_str_len_eq]
    simp [hElimTy, __smtx_typeof_seq_op_1_ret]
  have hRhsTailTy : __smtx_typeof (__eo_to_smt rhsTail) = SmtType.Int := by
    have hRawLenElimTy :
        __smtx_typeof (SmtTerm.str_len (__eo_to_smt (__str_nary_elim tail))) =
          SmtType.Int := by
      exact hLenElimTy
    change __smtx_typeof
        (SmtTerm.plus (SmtTerm.str_len (__eo_to_smt (__str_nary_elim tail)))
          (SmtTerm.Numeral 0)) = SmtType.Int
    rw [typeof_plus_eq]
    simp [hRawLenElimTy, __smtx_typeof.eq_2, __smtx_typeof_arith_overload_op_2]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Int := by
    have hRawLenS1Ty :
        __smtx_typeof (SmtTerm.str_len (__eo_to_smt s1)) = SmtType.Int := by
      exact hLenS1Ty
    have hRawRhsTailTy :
        __smtx_typeof (__eo_to_smt rhsTail) = SmtType.Int := hRhsTailTy
    change __smtx_typeof
        (SmtTerm.plus (SmtTerm.str_len (__eo_to_smt s1))
          (__eo_to_smt rhsTail)) = SmtType.Int
    rw [typeof_plus_eq]
    simp [hRawLenS1Ty, hRawRhsTailTy, __smtx_typeof_arith_overload_op_2]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hS1NotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1Trans
  have hS2NotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation s2 hS2Trans
  have hS3NotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation s3 hS3Trans
  have hProg :
      __eo_prog_str_len_concat_rec s1 s2 s3 =
        Term.Apply (Term.Apply Term.eq lhs) rhs := by
    simpa [lhs, rhs, lenConcatConclusion] using
      prog_str_len_concat_rec_eq_of_ne_stuck s1 s2 s3
        hS1NotStuck hS2NotStuck hS3NotStuck hElim
  rw [hProg]
  exact hBoolEq

private theorem facts___eo_prog_str_len_concat_rec_impl
    (M : SmtModel) (hM : model_wf M) (s1 s2 s3 : Term)
    (hS1Trans : RuleProofs.eo_has_smt_translation s1)
    (hS2Trans : RuleProofs.eo_has_smt_translation s2)
    (hS3Trans : RuleProofs.eo_has_smt_translation s3)
    (hS1Ty : __eo_typeof s1 = Term.Apply Term.Seq T)
    (hS2Ty : __eo_typeof s2 = Term.Apply Term.Seq T)
    (hS3Ty : __eo_typeof s3 = Term.Apply Term.Seq T)
    (hElim : __str_nary_elim (lenConcatTail s2 s3) ≠ Term.Stuck) :
    eo_interprets M (__eo_prog_str_len_concat_rec s1 s2 s3) true := by
  let tail := lenConcatTail s2 s3
  let lhs := lenConcatLhs s1 s2 s3
  let rhsTail := lenConcatRhsTail s2 s3
  let rhs := lenConcatRhs s1 s2 s3
  have hS1NotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1Trans
  have hS2NotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation s2 hS2Trans
  have hS3NotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation s3 hS3Trans
  have hProg :
      __eo_prog_str_len_concat_rec s1 s2 s3 =
        Term.Apply (Term.Apply Term.eq lhs) rhs := by
    simpa [lhs, rhs, lenConcatConclusion] using
      prog_str_len_concat_rec_eq_of_ne_stuck s1 s2 s3
        hS1NotStuck hS2NotStuck hS3NotStuck hElim
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProg] using
      typed___eo_prog_str_len_concat_rec_impl s1 s2 s3
        hS1Trans hS2Trans hS3Trans hS1Ty hS2Ty hS3Ty hElim
  have hS1SmtTy := smtx_typeof_of_eo_seq s1 T hS1Trans hS1Ty
  have hS2SmtTy := smtx_typeof_of_eo_seq s2 T hS2Trans hS2Ty
  have hS3SmtTy := smtx_typeof_of_eo_seq s3 T hS3Trans hS3Ty
  have hTailTy : __smtx_typeof (__eo_to_smt tail) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt s2) (__eo_to_smt s3)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hS2SmtTy, hS3SmtTy, __smtx_typeof_seq_op_2, native_ite, native_Teq]
  have hS1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s1)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hS1SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s1) (by
        unfold term_has_non_none_type
        rw [hS1SmtTy]
        simp)
  have hS2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s2)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hS2SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s2) (by
        unfold term_has_non_none_type
        rw [hS2SmtTy]
        simp)
  have hS3EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s3)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hS3SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s3) (by
        unfold term_has_non_none_type
        rw [hS3SmtTy]
        simp)
  rcases seq_value_canonical hS1EvalTy with ⟨ss1, hS1Eval⟩
  rcases seq_value_canonical hS2EvalTy with ⟨ss2, hS2Eval⟩
  rcases seq_value_canonical hS3EvalTy with ⟨ss3, hS3Eval⟩
  let tailSeq := native_pack_seq (__smtx_elem_typeof_seq_value ss2)
    (native_unpack_seq ss2 ++ native_unpack_seq ss3)
  have hTailEval :
      __smtx_model_eval M (__eo_to_smt tail) = SmtValue.Seq tailSeq := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (__eo_to_smt s2) (__eo_to_smt s3)) =
      SmtValue.Seq tailSeq
    rw [smtx_eval_str_concat_term_eq_raw]
    rw [hS2Eval, hS3Eval]
    simp [tailSeq, __smtx_model_eval_str_concat, native_seq_concat]
  have hElimEvalTy :
      __smtx_typeof_value
          (__smtx_model_eval M (__eo_to_smt (__str_nary_elim tail))) =
        SmtType.Seq (__eo_to_smt_type T) := by
    have hElimTy : __smtx_typeof (__eo_to_smt (__str_nary_elim tail)) =
        SmtType.Seq (__eo_to_smt_type T) :=
      smt_typeof_str_nary_elim_of_seq_ne_stuck tail (__eo_to_smt_type T)
        hTailTy hElim
    simpa [hElimTy] using
      smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt (__str_nary_elim tail)) (by
          unfold term_has_non_none_type
          rw [hElimTy]
          simp)
  rcases seq_value_canonical hElimEvalTy with ⟨elimSeq, hElimEval⟩
  have hElimRel := smt_value_rel_str_nary_elim M hM tail
    (__eo_to_smt_type T) hTailTy hElim
  have hElimSeqEq : elimSeq = tailSeq := by
    rw [hElimEval, hTailEval] at hElimRel
    have hValEq : SmtValue.Seq elimSeq = SmtValue.Seq tailSeq :=
      (RuleProofs.smt_value_rel_iff_eq (SmtValue.Seq elimSeq)
        (SmtValue.Seq tailSeq) (by
          rintro ⟨r1, r2, h1, _h2⟩
          cases h1)).1 hElimRel
    cases hValEq
    rfl
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_len
          (SmtTerm.str_concat (__eo_to_smt s1) (__eo_to_smt tail))) =
      __smtx_model_eval M
        (SmtTerm.plus (SmtTerm.str_len (__eo_to_smt s1))
          (SmtTerm.plus
            (SmtTerm.str_len (__eo_to_smt (__str_nary_elim tail)))
            (SmtTerm.Numeral 0)))
    rw [smtx_eval_str_len_term_eq, smtx_eval_str_concat_term_eq_raw,
      hS1Eval, hTailEval]
    rw [smtx_eval_plus_term_eq, smtx_eval_str_len_term_eq, hS1Eval]
    rw [smtx_eval_plus_term_eq, smtx_eval_str_len_term_eq, hElimEval]
    rw [show __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0 by
      rw [__smtx_model_eval.eq_def]]
    rw [hElimSeqEq]
    simp [__smtx_model_eval_str_concat, __smtx_model_eval_str_len,
      __smtx_model_eval_plus, native_seq_concat, native_seq_len,
      Smtm.native_unpack_pack_seq, tailSeq, native_zplus, Int.add_assoc]
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

private theorem typeof_args_of_prog_bool
    (s1 s2 s3 : Term)
    (hS1 : s1 ≠ Term.Stuck) (hS2 : s2 ≠ Term.Stuck)
    (hS3 : s3 ≠ Term.Stuck)
    (hTy : __eo_typeof (__eo_prog_str_len_concat_rec s1 s2 s3) = Term.Bool) :
    ∃ T,
      __eo_typeof s1 = Term.Apply Term.Seq T ∧
      __eo_typeof s2 = Term.Apply Term.Seq T ∧
      __eo_typeof s3 = Term.Apply Term.Seq T ∧
      __str_nary_elim (lenConcatTail s2 s3) ≠ Term.Stuck := by
  have hElim : __str_nary_elim (lenConcatTail s2 s3) ≠ Term.Stuck := by
    intro hElim
    have hProgStuck :
        __eo_prog_str_len_concat_rec s1 s2 s3 = Term.Stuck :=
      prog_str_len_concat_rec_stuck_of_elim_stuck s1 s2 s3
        hS1 hS2 hS3 hElim
    rw [hProgStuck] at hTy
    change Term.Stuck = Term.Bool at hTy
    cases hTy
  rw [prog_str_len_concat_rec_eq_of_ne_stuck s1 s2 s3 hS1 hS2 hS3 hElim] at hTy
  change __eo_typeof_eq
      (__eo_typeof (lenConcatLhs s1 s2 s3))
      (__eo_typeof (lenConcatRhs s1 s2 s3)) = Term.Bool at hTy
  have hLhsNotStuck :
      __eo_typeof (lenConcatLhs s1 s2 s3) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy).1
  change __eo_typeof_str_len
      (__eo_typeof_str_concat (__eo_typeof s1)
        (__eo_typeof_str_concat (__eo_typeof s2) (__eo_typeof s3))) ≠
        Term.Stuck at hLhsNotStuck
  rcases eo_typeof_str_len_arg_seq_of_ne_stuck
      (__eo_typeof_str_concat (__eo_typeof s1)
        (__eo_typeof_str_concat (__eo_typeof s2) (__eo_typeof s3)))
      hLhsNotStuck with ⟨T, hConcatTy⟩
  have hOuter := eo_typeof_str_concat_args_seq
    (__eo_typeof s1) (__eo_typeof_str_concat (__eo_typeof s2) (__eo_typeof s3))
    T hConcatTy
  have hInner := eo_typeof_str_concat_args_seq (__eo_typeof s2) (__eo_typeof s3)
    T hOuter.2
  exact ⟨T, hOuter.1, hInner.1, hInner.2, hElim⟩

public theorem cmd_step_str_len_concat_rec_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_len_concat_rec args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_len_concat_rec args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_len_concat_rec args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_len_concat_rec args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  cases premises with
                  | nil =>
                      have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
                      have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.1
                      have hA3Trans : RuleProofs.eo_has_smt_translation a3 := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.2.1
                      have hA1NotStuck : a1 ≠ Term.Stuck :=
                        RuleProofs.term_ne_stuck_of_has_smt_translation a1 hA1Trans
                      have hA2NotStuck : a2 ≠ Term.Stuck :=
                        RuleProofs.term_ne_stuck_of_has_smt_translation a2 hA2Trans
                      have hA3NotStuck : a3 ≠ Term.Stuck :=
                        RuleProofs.term_ne_stuck_of_has_smt_translation a3 hA3Trans
                      change
                        __eo_typeof (__eo_prog_str_len_concat_rec a1 a2 a3) =
                          Term.Bool at hResultTy
                      rcases typeof_args_of_prog_bool a1 a2 a3
                          hA1NotStuck hA2NotStuck hA3NotStuck hResultTy with
                        ⟨T, hA1Ty, hA2Ty, hA3Ty, hElim⟩
                      have hProps :
                          StepRuleProperties M (premiseTermList s CIndexList.nil)
                            (__eo_prog_str_len_concat_rec a1 a2 a3) := by
                        refine ⟨?_,
                          RuleProofs.eo_has_smt_translation_of_has_bool_type _
                            (typed___eo_prog_str_len_concat_rec_impl a1 a2 a3
                              hA1Trans hA2Trans hA3Trans hA1Ty hA2Ty hA3Ty hElim)⟩
                        intro _hTrue
                        exact facts___eo_prog_str_len_concat_rec_impl M hM a1 a2 a3
                          hA1Trans hA2Trans hA3Trans hA1Ty hA2Ty hA3Ty hElim
                      change StepRuleProperties M [] (__eo_prog_str_len_concat_rec a1 a2 a3)
                      simpa [premiseTermList] using hProps
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
