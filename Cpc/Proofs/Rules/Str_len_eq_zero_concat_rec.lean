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

private abbrev lenZeroConcatTail (s2 s3 : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat s2) s3

private abbrev lenZeroConcatConcat (s1 s2 s3 : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat s1) (lenZeroConcatTail s2 s3)

private abbrev lenZeroConcatLhs (s1 s2 s3 : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len (lenZeroConcatConcat s1 s2 s3)))
    (Term.Numeral 0)

private abbrev lenZeroConcatEmptyEq (s1 A : Term) : Term :=
  Term.Apply (Term.Apply Term.eq s1) (__seq_empty A)

private abbrev lenZeroConcatTailLenEq (s2 s3 : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply Term.str_len (__str_nary_elim (lenZeroConcatTail s2 s3))))
    (Term.Numeral 0)

private abbrev lenZeroConcatRhs (s1 s2 s3 A : Term) : Term :=
  Term.Apply (Term.Apply Term.and (lenZeroConcatEmptyEq s1 A))
    (Term.Apply (Term.Apply Term.and (lenZeroConcatTailLenEq s2 s3))
      (Term.Boolean true))

private abbrev lenZeroConcatConclusion (s1 s2 s3 A : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (lenZeroConcatLhs s1 s2 s3))
    (lenZeroConcatRhs s1 s2 s3 A)

private theorem term_apply_ne_stuck (f a : Term) :
    Term.Apply f a ≠ Term.Stuck := by
  intro h
  cases h

private theorem seq_empty_seq_ne_stuck (T : Term) :
    __seq_empty (Term.Apply Term.Seq T) ≠ Term.Stuck := by
  cases T <;> simp [__seq_empty, Term.Seq]
  case UOp op =>
    cases op <;> simp [__seq_empty, Term.Seq]

private theorem mk_apply_eq (f a : Term)
    (hF : f ≠ Term.Stuck) (hA : a ≠ Term.Stuck) :
    __eo_mk_apply f a = Term.Apply f a := by
  cases f <;> cases a <;> simp [__eo_mk_apply] at hF hA ⊢

private theorem mk_apply_stuck_right (f : Term) :
    __eo_mk_apply f Term.Stuck = Term.Stuck := by
  cases f <;> simp [__eo_mk_apply]

private theorem mk_apply_stuck_left (a : Term) :
    __eo_mk_apply Term.Stuck a = Term.Stuck := by
  cases a <;> simp [__eo_mk_apply]

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

private theorem eo_typeof_seq_empty_seq_of_ne_stuck
    (T : Term)
    (h : __eo_typeof (__seq_empty (Term.Apply Term.Seq T)) ≠ Term.Stuck) :
    __eo_typeof (__seq_empty (Term.Apply Term.Seq T)) =
      Term.Apply Term.Seq T := by
  by_cases hChar : T = Term.Char
  · subst T
    rfl
  · have hDefault :
        __seq_empty (Term.Apply Term.Seq T) =
          Term.seq_empty (Term.Apply Term.Seq T) := by
      cases T <;> simp [__seq_empty] at hChar ⊢
      case UOp op =>
        cases op <;> simp [__seq_empty] at hChar ⊢
    rw [hDefault] at h
    rw [hDefault]
    change
      __eo_typeof_seq_empty
          (__eo_typeof_Seq (__eo_typeof T))
          (Term.Apply Term.Seq T) =
        Term.Apply Term.Seq T
    change
      __eo_typeof_seq_empty
          (__eo_typeof_Seq (__eo_typeof T))
          (Term.Apply Term.Seq T) ≠ Term.Stuck at h
    cases hTy : __eo_typeof T <;>
      simp [__eo_typeof_Seq, __eo_typeof_seq_empty,
        __eo_disamb_type_seq_empty, hTy] at h ⊢

private theorem eo_typeof_eq_bool_of_ne_stuck (A B : Term)
    (h : __eo_typeof_eq A B ≠ Term.Stuck) :
    __eo_typeof_eq A B = Term.Bool := by
  cases A <;> cases B <;>
    simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
      native_not] at h ⊢
  all_goals
    assumption

private theorem eo_typeof_and_left_bool_of_ne_stuck (A B : Term)
    (h : __eo_typeof (Term.Apply (Term.Apply Term.and A) B) ≠ Term.Stuck) :
    __eo_typeof A = Term.Bool := by
  change __eo_typeof_or (__eo_typeof A) (__eo_typeof B) ≠ Term.Stuck at h
  cases hA : __eo_typeof A <;> cases hB : __eo_typeof B <;>
    simp [__eo_typeof_or, hA, hB] at h ⊢

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

private theorem smtx_typeof_seq_empty_typeof_of_smt_type_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
      SmtType.Seq T := by
  exact smt_typeof_seq_empty_typeof x T hxTy
    (seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf x T hxTy
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy).1
      (smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy).2)

private theorem smtx_eval_str_concat_term_eq_raw
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_concat x y) =
      __smtx_model_eval_str_concat
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_boolean_term_eq (M : SmtModel) (b : Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

private theorem smtx_model_eval_str_len_zero_eq_seq_empty
    (sx : SmtSeq) (T : SmtType)
    (hTy : __smtx_typeof_seq_value sx = SmtType.Seq T) :
    __smtx_model_eval_eq
        (__smtx_model_eval_str_len (SmtValue.Seq sx))
        (SmtValue.Numeral 0) =
      __smtx_model_eval_eq
        (SmtValue.Seq sx) (SmtValue.Seq (SmtSeq.empty T)) := by
  cases sx with
  | empty U =>
      simp [__smtx_typeof_seq_value] at hTy
      subst U
      simp [__smtx_model_eval_str_len, __smtx_model_eval_eq, native_seq_len,
        native_veq, native_unpack_seq]
  | cons v vs =>
      simp [__smtx_model_eval_str_len, __smtx_model_eval_eq, native_seq_len,
        native_veq, native_unpack_seq]
      intro h
      have hPos : (0 : Int) < (native_unpack_seq vs).length + 1 := by
        have hNonneg : (0 : Int) <= (native_unpack_seq vs).length := by
          exact Int.natCast_nonneg _
        omega
      rw [h] at hPos
      omega

private theorem native_len_append_zero_and
    (xs ys : List SmtValue) :
    decide (((Int.ofNat xs.length : Int) + Int.ofNat ys.length) = 0) =
      (decide ((Int.ofNat xs.length : Int) = 0) &&
        (decide ((Int.ofNat ys.length : Int) = 0) && true)) := by
  by_cases hx : (Int.ofNat xs.length : Int) = 0
  · by_cases hy : (Int.ofNat ys.length : Int) = 0
    · have hxNil : xs = [] := List.eq_nil_of_length_eq_zero (Int.ofNat_eq_zero.mp hx)
      have hyNil : ys = [] := List.eq_nil_of_length_eq_zero (Int.ofNat_eq_zero.mp hy)
      simp [hxNil, hyNil]
    · have hsum :
          ¬ ((Int.ofNat xs.length : Int) + Int.ofNat ys.length) = 0 := by
        intro hsum
        have hyZero : (Int.ofNat ys.length : Int) = 0 := by
          rw [hx] at hsum
          simpa using hsum
        exact hy hyZero
      have hxNil : xs = [] := List.eq_nil_of_length_eq_zero (Int.ofNat_eq_zero.mp hx)
      have hyNotNil : ys ≠ [] := by
        intro hyNil
        exact hy (by simp [hyNil])
      simp [hxNil, hyNotNil, hsum]
  · have hsum :
        ¬ ((Int.ofNat xs.length : Int) + Int.ofNat ys.length) = 0 := by
      intro hsum
      have hNat : xs.length + ys.length = 0 := by
        apply Int.ofNat_eq_zero.mp
        rw [Int.natCast_add]
        exact hsum
      exact hx (Int.ofNat_eq_zero.mpr (Nat.add_eq_zero_iff.mp hNat).1)
    have hxNotNil : xs ≠ [] := by
      intro hxNil
      exact hx (by simp [hxNil])
    simpa [hxNotNil] using hsum

private theorem native_len_append_zero_and_nil
    (xs ys : List SmtValue) :
    decide (((Int.ofNat xs.length : Int) + Int.ofNat ys.length) = 0) =
      (decide (xs = []) && decide (ys = [])) := by
  simpa using native_len_append_zero_and xs ys

private theorem smtx_model_eval_len_append_zero_eq_and
    (sx sy : SmtSeq) (T : SmtType)
    (hTy : __smtx_typeof_seq_value sx = SmtType.Seq T) :
    __smtx_model_eval_eq
        (__smtx_model_eval_str_len
          (SmtValue.Seq
            (native_pack_seq (__smtx_elem_typeof_seq_value sx)
              (native_unpack_seq sx ++ native_unpack_seq sy))))
        (SmtValue.Numeral 0) =
      __smtx_model_eval_and
        (__smtx_model_eval_eq (SmtValue.Seq sx)
          (SmtValue.Seq (SmtSeq.empty T)))
        (__smtx_model_eval_and
          (__smtx_model_eval_eq
            (__smtx_model_eval_str_len (SmtValue.Seq sy))
            (SmtValue.Numeral 0))
          (SmtValue.Boolean true)) := by
  rw [← smtx_model_eval_str_len_zero_eq_seq_empty sx T hTy]
  simp [__smtx_model_eval_str_len, __smtx_model_eval_eq,
    __smtx_model_eval_and, native_seq_len, Smtm.native_unpack_pack_seq,
    native_veq, SmtEval.native_and]
  exact native_len_append_zero_and_nil (native_unpack_seq sx) (native_unpack_seq sy)

private theorem prog_str_len_eq_zero_concat_rec_eq_of_ne_stuck
    (s1 s2 s3 T : Term)
    (hS1 : s1 ≠ Term.Stuck) (hS2 : s2 ≠ Term.Stuck)
    (hS3 : s3 ≠ Term.Stuck)
    (hElim : __str_nary_elim (lenZeroConcatTail s2 s3) ≠ Term.Stuck) :
    __eo_prog_str_len_eq_zero_concat_rec s1 s2 s3 (Term.Apply Term.Seq T) =
      lenZeroConcatConclusion s1 s2 s3 (Term.Apply Term.Seq T) := by
  simp [__eo_prog_str_len_eq_zero_concat_rec, hS1, hS2, hS3,
    lenZeroConcatConclusion, lenZeroConcatLhs, lenZeroConcatRhs,
    lenZeroConcatEmptyEq, lenZeroConcatTailLenEq, lenZeroConcatConcat,
    lenZeroConcatTail, __str_nary_elim, hElim, mk_apply_eq,
    term_apply_ne_stuck, seq_empty_seq_ne_stuck]

private theorem prog_str_len_eq_zero_concat_rec_stuck_of_elim_stuck
    (s1 s2 s3 T : Term)
    (hS1 : s1 ≠ Term.Stuck) (hS2 : s2 ≠ Term.Stuck)
    (hS3 : s3 ≠ Term.Stuck)
    (hElim : __str_nary_elim (lenZeroConcatTail s2 s3) = Term.Stuck) :
    __eo_prog_str_len_eq_zero_concat_rec s1 s2 s3 (Term.Apply Term.Seq T) =
      Term.Stuck := by
  simp [__eo_prog_str_len_eq_zero_concat_rec, hS1, hS2, hS3,
    lenZeroConcatTail, __str_nary_elim, hElim, mk_apply_stuck_left,
    mk_apply_stuck_right]

private theorem typed___eo_prog_str_len_eq_zero_concat_rec_impl
    (s1 s2 s3 T : Term)
    (hS1Trans : RuleProofs.eo_has_smt_translation s1)
    (hS2Trans : RuleProofs.eo_has_smt_translation s2)
    (hS3Trans : RuleProofs.eo_has_smt_translation s3)
    (hS1Ty : __eo_typeof s1 = Term.Apply Term.Seq T)
    (hS2Ty : __eo_typeof s2 = Term.Apply Term.Seq T)
    (hS3Ty : __eo_typeof s3 = Term.Apply Term.Seq T)
    (hElim : __str_nary_elim (lenZeroConcatTail s2 s3) ≠ Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_len_eq_zero_concat_rec s1 s2 s3 (Term.Apply Term.Seq T)) := by
  let A := Term.Apply Term.Seq T
  let tail := lenZeroConcatTail s2 s3
  let lhs := lenZeroConcatLhs s1 s2 s3
  let emptyEq := lenZeroConcatEmptyEq s1 A
  let tailLenEq := lenZeroConcatTailLenEq s2 s3
  let rhs := lenZeroConcatRhs s1 s2 s3 A
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
  have hConcatTy :
      __smtx_typeof (__eo_to_smt (lenZeroConcatConcat s1 s2 s3)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt s1) (__eo_to_smt tail)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hS1SmtTy, hTailTy, __smtx_typeof_seq_op_2, native_ite, native_Teq]
  have hConcatLenTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply Term.str_len (lenZeroConcatConcat s1 s2 s3))) =
        SmtType.Int := by
    have hRawConcatTy :
        __smtx_typeof (SmtTerm.str_concat (__eo_to_smt s1) (__eo_to_smt tail)) =
          SmtType.Seq (__eo_to_smt_type T) := by
      simpa [tail, lenZeroConcatTail] using hConcatTy
    change __smtx_typeof
        (SmtTerm.str_len (SmtTerm.str_concat (__eo_to_smt s1) (__eo_to_smt tail))) =
      SmtType.Int
    rw [typeof_str_len_eq]
    simp [hRawConcatTy, __smtx_typeof_seq_op_1_ret]
  have hZeroTy :
      __smtx_typeof (__eo_to_smt (Term.Numeral 0)) = SmtType.Int := by
    change __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int
    rw [__smtx_typeof.eq_def]
  have hLhsTy : RuleProofs.eo_has_bool_type lhs :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (Term.Apply Term.str_len (lenZeroConcatConcat s1 s2 s3)) (Term.Numeral 0)
      (by rw [hConcatLenTy, hZeroTy]) (by rw [hConcatLenTy]; simp)
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (__seq_empty A)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    have hEmptyTy' :=
      smtx_typeof_seq_empty_typeof_of_smt_type_seq s1
        (__eo_to_smt_type T) hS1SmtTy
    simpa [A, hS1Ty] using hEmptyTy'
  have hEmptyEqTy : RuleProofs.eo_has_bool_type emptyEq :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type s1 (__seq_empty A)
      (by rw [hS1SmtTy, hEmptyTy]) (by rw [hS1SmtTy]; simp)
  have hElimTy : __smtx_typeof (__eo_to_smt (__str_nary_elim tail)) =
      SmtType.Seq (__eo_to_smt_type T) :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck tail (__eo_to_smt_type T)
      hTailTy hElim
  have hLenElimTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply Term.str_len (__str_nary_elim tail))) =
        SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.str_len (__eo_to_smt (__str_nary_elim tail))) = SmtType.Int
    rw [typeof_str_len_eq]
    simp [hElimTy, __smtx_typeof_seq_op_1_ret]
  have hTailLenEqTy : RuleProofs.eo_has_bool_type tailLenEq :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (Term.Apply Term.str_len (__str_nary_elim tail)) (Term.Numeral 0)
      (by rw [hLenElimTy, hZeroTy]) (by rw [hLenElimTy]; simp)
  have hInnerTy :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.and tailLenEq) (Term.Boolean true)) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args tailLenEq
      (Term.Boolean true) hTailLenEqTy RuleProofs.eo_has_bool_type_true
  have hRhsTy : RuleProofs.eo_has_bool_type rhs := by
    exact RuleProofs.eo_has_bool_type_and_of_bool_args emptyEq
      (Term.Apply (Term.Apply Term.and tailLenEq) (Term.Boolean true))
      hEmptyEqTy hInnerTy
  have hBoolEq :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hS1NotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1Trans
  have hS2NotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation s2 hS2Trans
  have hS3NotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation s3 hS3Trans
  have hProg :
      __eo_prog_str_len_eq_zero_concat_rec s1 s2 s3 A =
        Term.Apply (Term.Apply Term.eq lhs) rhs := by
    simpa [A, lhs, rhs, lenZeroConcatConclusion] using
      prog_str_len_eq_zero_concat_rec_eq_of_ne_stuck s1 s2 s3 T
        hS1NotStuck hS2NotStuck hS3NotStuck hElim
  rw [hProg]
  exact hBoolEq

private theorem facts___eo_prog_str_len_eq_zero_concat_rec_impl
    (M : SmtModel) (hM : model_wf M) (s1 s2 s3 T : Term)
    (hS1Trans : RuleProofs.eo_has_smt_translation s1)
    (hS2Trans : RuleProofs.eo_has_smt_translation s2)
    (hS3Trans : RuleProofs.eo_has_smt_translation s3)
    (hS1Ty : __eo_typeof s1 = Term.Apply Term.Seq T)
    (hS2Ty : __eo_typeof s2 = Term.Apply Term.Seq T)
    (hS3Ty : __eo_typeof s3 = Term.Apply Term.Seq T)
    (hElim : __str_nary_elim (lenZeroConcatTail s2 s3) ≠ Term.Stuck) :
    eo_interprets M
      (__eo_prog_str_len_eq_zero_concat_rec s1 s2 s3 (Term.Apply Term.Seq T))
      true := by
  let A := Term.Apply Term.Seq T
  let tail := lenZeroConcatTail s2 s3
  let lhs := lenZeroConcatLhs s1 s2 s3
  let emptyEq := lenZeroConcatEmptyEq s1 A
  let tailLenEq := lenZeroConcatTailLenEq s2 s3
  let rhs := lenZeroConcatRhs s1 s2 s3 A
  have hS1NotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1Trans
  have hS2NotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation s2 hS2Trans
  have hS3NotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation s3 hS3Trans
  have hProg :
      __eo_prog_str_len_eq_zero_concat_rec s1 s2 s3 A =
        Term.Apply (Term.Apply Term.eq lhs) rhs := by
    simpa [A, lhs, rhs, lenZeroConcatConclusion] using
      prog_str_len_eq_zero_concat_rec_eq_of_ne_stuck s1 s2 s3 T
        hS1NotStuck hS2NotStuck hS3NotStuck hElim
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    have hTypedProg :=
      typed___eo_prog_str_len_eq_zero_concat_rec_impl s1 s2 s3 T
        hS1Trans hS2Trans hS3Trans hS1Ty hS2Ty hS3Ty hElim
    rw [hProg] at hTypedProg
    exact hTypedProg
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
  have hS1SeqTy :
      __smtx_typeof_seq_value ss1 = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hS1Eval, __smtx_typeof_seq_value, __smtx_typeof_value] using hS1EvalTy
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
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt (__seq_empty A)) =
        SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type T)) := by
    have hEmptyEval' :=
      eval_seq_empty_typeof M s1 (__eo_to_smt_type T) hS1SmtTy
    simpa [A, hS1Ty] using hEmptyEval'
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
        (SmtTerm.eq
          (SmtTerm.str_len
            (SmtTerm.str_concat (__eo_to_smt s1) (__eo_to_smt tail)))
          (SmtTerm.Numeral 0)) =
      __smtx_model_eval M
        (SmtTerm.and
          (SmtTerm.eq (__eo_to_smt s1) (__eo_to_smt (__seq_empty A)))
          (SmtTerm.and
            (SmtTerm.eq
              (SmtTerm.str_len (__eo_to_smt (__str_nary_elim tail)))
              (SmtTerm.Numeral 0))
            (SmtTerm.Boolean true)))
    rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq,
      smtx_eval_str_concat_term_eq_raw, hS1Eval, hTailEval]
    rw [show __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0 by
      rw [__smtx_model_eval.eq_def]]
    rw [smtx_eval_and_term_eq, smtx_eval_eq_term_eq, hS1Eval, hEmptyEval]
    rw [smtx_eval_and_term_eq, smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq,
      hElimEval]
    rw [show __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0 by
      rw [__smtx_model_eval.eq_def]]
    rw [smtx_eval_boolean_term_eq, hElimSeqEq]
    exact smtx_model_eval_len_append_zero_eq_and ss1 tailSeq (__eo_to_smt_type T)
      hS1SeqTy
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

private theorem typeof_args_of_prog_bool
    (s1 s2 s3 A : Term)
    (hS1 : s1 ≠ Term.Stuck) (hS2 : s2 ≠ Term.Stuck)
    (hS3 : s3 ≠ Term.Stuck)
    (hTy : __eo_typeof (__eo_prog_str_len_eq_zero_concat_rec s1 s2 s3 A) =
      Term.Bool) :
    ∃ T,
      A = Term.Apply Term.Seq T ∧
      __eo_typeof s1 = Term.Apply Term.Seq T ∧
      __eo_typeof s2 = Term.Apply Term.Seq T ∧
      __eo_typeof s3 = Term.Apply Term.Seq T ∧
      __str_nary_elim (lenZeroConcatTail s2 s3) ≠ Term.Stuck := by
  have hProgNotStuck :
      __eo_prog_str_len_eq_zero_concat_rec s1 s2 s3 A ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  have hASeq : ∃ T, A = Term.Apply Term.Seq T := by
    cases A <;>
      simp [__eo_prog_str_len_eq_zero_concat_rec, hS1, hS2, hS3] at hProgNotStuck ⊢
    case Apply f x =>
      cases f <;>
        simp [__eo_prog_str_len_eq_zero_concat_rec, hS1, hS2, hS3] at hProgNotStuck ⊢
      case UOp op =>
        cases op <;>
          simp [__eo_prog_str_len_eq_zero_concat_rec, hS1, hS2, hS3] at hProgNotStuck ⊢
  rcases hASeq with ⟨T, hA⟩
  subst A
  have hElim : __str_nary_elim (lenZeroConcatTail s2 s3) ≠ Term.Stuck := by
    intro hElim
    have hProgStuck :
        __eo_prog_str_len_eq_zero_concat_rec s1 s2 s3 (Term.Apply Term.Seq T) =
          Term.Stuck :=
      prog_str_len_eq_zero_concat_rec_stuck_of_elim_stuck s1 s2 s3 T
        hS1 hS2 hS3 hElim
    rw [hProgStuck] at hTy
    change Term.Stuck = Term.Bool at hTy
    cases hTy
  rw [prog_str_len_eq_zero_concat_rec_eq_of_ne_stuck s1 s2 s3 T
    hS1 hS2 hS3 hElim] at hTy
  change __eo_typeof_eq
      (__eo_typeof (lenZeroConcatLhs s1 s2 s3))
      (__eo_typeof (lenZeroConcatRhs s1 s2 s3 (Term.Apply Term.Seq T))) =
      Term.Bool at hTy
  have hLhsNotStuck :
      __eo_typeof (lenZeroConcatLhs s1 s2 s3) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy).1
  change __eo_typeof_eq
      (__eo_typeof_str_len
        (__eo_typeof_str_concat (__eo_typeof s1)
          (__eo_typeof_str_concat (__eo_typeof s2) (__eo_typeof s3))))
      (__eo_typeof (Term.Numeral 0)) ≠ Term.Stuck at hLhsNotStuck
  have hLenNotStuck :
      __eo_typeof_str_len
        (__eo_typeof_str_concat (__eo_typeof s1)
          (__eo_typeof_str_concat (__eo_typeof s2) (__eo_typeof s3))) ≠
        Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ <|
      eo_typeof_eq_bool_of_ne_stuck _ _ hLhsNotStuck).1
  rcases eo_typeof_str_len_arg_seq_of_ne_stuck
      (__eo_typeof_str_concat (__eo_typeof s1)
        (__eo_typeof_str_concat (__eo_typeof s2) (__eo_typeof s3)))
      hLenNotStuck with ⟨U, hConcatTy⟩
  have hOuter := eo_typeof_str_concat_args_seq
    (__eo_typeof s1) (__eo_typeof_str_concat (__eo_typeof s2) (__eo_typeof s3))
    U hConcatTy
  have hInner := eo_typeof_str_concat_args_seq (__eo_typeof s2) (__eo_typeof s3)
    U hOuter.2
  have hRhsNotStuck :
      __eo_typeof (lenZeroConcatRhs s1 s2 s3 (Term.Apply Term.Seq T)) ≠
        Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy).2
  have hEmptyEqTy :
      __eo_typeof (lenZeroConcatEmptyEq s1 (Term.Apply Term.Seq T)) =
        Term.Bool :=
    eo_typeof_and_left_bool_of_ne_stuck
      (lenZeroConcatEmptyEq s1 (Term.Apply Term.Seq T))
      (Term.Apply (Term.Apply Term.and (lenZeroConcatTailLenEq s2 s3))
        (Term.Boolean true))
      hRhsNotStuck
  have hEmptyTy :
      __eo_typeof (__seq_empty (Term.Apply Term.Seq T)) =
        Term.Apply Term.Seq T := by
    have hOps :=
      RuleProofs.eo_typeof_eq_bool_operands_not_stuck
        (__eo_typeof s1) (__eo_typeof (__seq_empty (Term.Apply Term.Seq T)))
        hEmptyEqTy
    exact eo_typeof_seq_empty_seq_of_ne_stuck T hOps.2
  have hS1TyT : __eo_typeof s1 = Term.Apply Term.Seq T := by
    have hTypesEq :=
      RuleProofs.eo_typeof_eq_bool_operands_eq
        (__eo_typeof s1) (__eo_typeof (__seq_empty (Term.Apply Term.Seq T)))
        hEmptyEqTy
    simpa [hEmptyTy] using hTypesEq
  have hUT : U = T := by
    rw [hOuter.1] at hS1TyT
    exact (Term.Apply.inj hS1TyT).2
  subst U
  exact ⟨T, rfl, hS1TyT, hInner.1, hInner.2, hElim⟩

public theorem cmd_step_str_len_eq_zero_concat_rec_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_len_eq_zero_concat_rec args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_len_eq_zero_concat_rec args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_len_eq_zero_concat_rec args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_len_eq_zero_concat_rec args premises ≠
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
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons A args =>
                  cases args with
                  | nil =>
                      cases premises with
                      | nil =>
                          have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk, argTranslationOkMasked] using
                              hCmdTrans.1
                          have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk, argTranslationOkMasked] using
                              hCmdTrans.2.1
                          have hA3Trans : RuleProofs.eo_has_smt_translation a3 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk, argTranslationOkMasked] using
                              hCmdTrans.2.2.1
                          have hA1NotStuck : a1 ≠ Term.Stuck :=
                            RuleProofs.term_ne_stuck_of_has_smt_translation a1
                              hA1Trans
                          have hA2NotStuck : a2 ≠ Term.Stuck :=
                            RuleProofs.term_ne_stuck_of_has_smt_translation a2
                              hA2Trans
                          have hA3NotStuck : a3 ≠ Term.Stuck :=
                            RuleProofs.term_ne_stuck_of_has_smt_translation a3
                              hA3Trans
                          change
                            __eo_typeof
                              (__eo_prog_str_len_eq_zero_concat_rec a1 a2 a3 A) =
                              Term.Bool at hResultTy
                          rcases typeof_args_of_prog_bool a1 a2 a3 A
                              hA1NotStuck hA2NotStuck hA3NotStuck hResultTy with
                            ⟨T, hA, hA1Ty, hA2Ty, hA3Ty, hElim⟩
                          subst A
                          have hProps :
                              StepRuleProperties M (premiseTermList s CIndexList.nil)
                                (__eo_prog_str_len_eq_zero_concat_rec a1 a2 a3
                                  (Term.Apply Term.Seq T)) := by
                            refine ⟨?_,
                              RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                (typed___eo_prog_str_len_eq_zero_concat_rec_impl
                                  a1 a2 a3 T hA1Trans hA2Trans hA3Trans
                                  hA1Ty hA2Ty hA3Ty hElim)⟩
                            intro _hTrue
                            exact facts___eo_prog_str_len_eq_zero_concat_rec_impl
                              M hM a1 a2 a3 T hA1Trans hA2Trans hA3Trans
                              hA1Ty hA2Ty hA3Ty hElim
                          change StepRuleProperties M []
                            (__eo_prog_str_len_eq_zero_concat_rec a1 a2 a3
                              (Term.Apply Term.Seq T))
                          simpa [premiseTermList] using hProps
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
