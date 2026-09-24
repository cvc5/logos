module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
public import Cpc.Proofs.RuleSupport.StringSupport
import all Cpc.Proofs.RuleSupport.StringSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev containsCharPremise (x : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len x))
    (Term.Numeral 1)

private abbrev containsCharEmpty (T : Term) : Term :=
  __seq_empty (Term.Apply Term.Seq T)

private abbrev containsCharLhs (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.str_contains x) y

private abbrev containsCharEmptyEq (y T : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (containsCharEmpty T)) y

private abbrev containsCharSelfEq (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.eq x) y

private abbrev containsCharRhs (x y T : Term) : Term :=
  Term.Apply (Term.Apply Term.or (containsCharEmptyEq y T))
    (Term.Apply (Term.Apply Term.or (containsCharSelfEq x y))
      (Term.Boolean false))

private abbrev containsCharConclusion (x y T : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (containsCharLhs x y))
    (containsCharRhs x y T)

private abbrev containsCharGeneratedRhs (x y T : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply Term.or
      (__eo_mk_apply
        (__eo_mk_apply Term.eq (containsCharEmpty T)) y))
    (Term.Apply (Term.Apply Term.or (containsCharSelfEq x y))
      (Term.Boolean false))

private abbrev containsCharGeneratedConclusion (x y T : Term) : Term :=
  __eo_mk_apply (Term.Apply Term.eq (containsCharLhs x y))
    (containsCharGeneratedRhs x y T)

private theorem term_apply_ne_stuck (f a : Term) :
    Term.Apply f a ≠ Term.Stuck := by
  intro h
  cases h

private theorem seq_empty_seq_ne_stuck (T : Term) :
    __seq_empty (Term.Apply Term.Seq T) ≠ Term.Stuck := by
  cases T <;> simp [__seq_empty, Term.Seq]
  case UOp op =>
    cases op <;> simp [__seq_empty, Term.Seq]

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

private theorem contains_char_empty_eq_type_bool_of_rhs_ne_stuck
    (x y T : Term)
    (h : __eo_typeof (containsCharRhs x y T) ≠ Term.Stuck) :
    __eo_typeof (containsCharEmptyEq y T) = Term.Bool := by
  change __eo_typeof_or (__eo_typeof (containsCharEmptyEq y T))
      (__eo_typeof
        (Term.Apply (Term.Apply Term.or (containsCharSelfEq x y))
          (Term.Boolean false))) ≠
    Term.Stuck at h
  cases hEmptyEqTy : __eo_typeof (containsCharEmptyEq y T) <;>
    simp [__eo_typeof_or, hEmptyEqTy] at h ⊢

private theorem contains_char_type_arg_eq
    (y U T : Term)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq U)
    (hEmptyEqTy : __eo_typeof (containsCharEmptyEq y T) = Term.Bool) :
    U = T := by
  change __eo_typeof_eq (__eo_typeof (containsCharEmpty T))
      (__eo_typeof y) = Term.Bool at hEmptyEqTy
  have hOps :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (containsCharEmpty T)) (__eo_typeof y) hEmptyEqTy
  have hEmptyTy :
      __eo_typeof (containsCharEmpty T) = Term.Apply Term.Seq T := by
    exact eo_typeof_seq_empty_seq_of_ne_stuck T hOps.1
  rw [hEmptyTy, hYTy] at hEmptyEqTy
  change __eo_requires
      (__eo_eq (Term.Apply Term.Seq T) (Term.Apply Term.Seq U))
      (Term.Boolean true) Term.Bool =
    Term.Bool at hEmptyEqTy
  have hReqNe :
      __eo_requires
          (__eo_eq (Term.Apply Term.Seq T) (Term.Apply Term.Seq U))
          (Term.Boolean true) Term.Bool ≠ Term.Stuck := by
    rw [hEmptyEqTy]
    simp
  have hSeqEq :
      Term.Apply Term.Seq U = Term.Apply Term.Seq T :=
    RuleProofs.eq_of_requires_eq_true_not_stuck
      (Term.Apply Term.Seq T) (Term.Apply Term.Seq U) Term.Bool hReqNe
  cases hSeqEq
  rfl

private theorem mk_apply_eq (f a : Term)
    (hF : f ≠ Term.Stuck) (hA : a ≠ Term.Stuck) :
    __eo_mk_apply f a = Term.Apply f a := by
  cases f <;> cases a <;> simp [__eo_mk_apply] at hF hA ⊢

private theorem generated_conclusion_eq
    (x y T : Term) (hY : y ≠ Term.Stuck) :
    containsCharGeneratedConclusion x y T =
      containsCharConclusion x y T := by
  have hEmpty : containsCharEmpty T ≠ Term.Stuck :=
    seq_empty_seq_ne_stuck T
  have hEqHead :
      __eo_mk_apply Term.eq (containsCharEmpty T) =
        Term.Apply Term.eq (containsCharEmpty T) := by
    exact mk_apply_eq Term.eq (containsCharEmpty T) (by simp) hEmpty
  have hEmptyEq :
      __eo_mk_apply
          (__eo_mk_apply Term.eq (containsCharEmpty T)) y =
        containsCharEmptyEq y T := by
    rw [hEqHead]
    exact mk_apply_eq (Term.Apply Term.eq (containsCharEmpty T)) y
      (term_apply_ne_stuck Term.eq (containsCharEmpty T)) hY
  have hEmptyEqNotStuck : containsCharEmptyEq y T ≠ Term.Stuck :=
    term_apply_ne_stuck (Term.Apply Term.eq (containsCharEmpty T)) y
  have hOrHead :
      __eo_mk_apply Term.or
          (__eo_mk_apply
            (__eo_mk_apply Term.eq (containsCharEmpty T)) y) =
        Term.Apply Term.or (containsCharEmptyEq y T) := by
    rw [hEmptyEq]
    exact mk_apply_eq Term.or (containsCharEmptyEq y T) (by simp)
      hEmptyEqNotStuck
  have hInnerOrNotStuck :
      Term.Apply (Term.Apply Term.or (containsCharSelfEq x y))
          (Term.Boolean false) ≠ Term.Stuck :=
    term_apply_ne_stuck (Term.Apply Term.or (containsCharSelfEq x y))
      (Term.Boolean false)
  have hRhs :
      containsCharGeneratedRhs x y T =
        containsCharRhs x y T := by
    dsimp [containsCharGeneratedRhs, containsCharRhs]
    rw [hOrHead]
    exact mk_apply_eq (Term.Apply Term.or (containsCharEmptyEq y T))
      (Term.Apply (Term.Apply Term.or (containsCharSelfEq x y))
        (Term.Boolean false))
      (term_apply_ne_stuck Term.or (containsCharEmptyEq y T))
      hInnerOrNotStuck
  have hRhsNotStuck : containsCharRhs x y T ≠ Term.Stuck := by
    dsimp [containsCharRhs]
    exact term_apply_ne_stuck (Term.Apply Term.or (containsCharEmptyEq y T))
      (Term.Apply (Term.Apply Term.or (containsCharSelfEq x y))
        (Term.Boolean false))
  dsimp [containsCharGeneratedConclusion, containsCharConclusion]
  rw [hRhs]
  exact mk_apply_eq (Term.Apply Term.eq (containsCharLhs x y))
    (containsCharRhs x y T)
    (term_apply_ne_stuck Term.eq (containsCharLhs x y)) hRhsNotStuck

private theorem eo_typeof_str_contains_args_of_ne_stuck
    (A B : Term)
    (h : __eo_typeof_str_contains A B ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U := by
  cases A <;> simp [__eo_typeof_str_contains] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_contains] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_contains] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_contains] at h ⊢
        case Apply g y =>
          cases g <;> simp [__eo_typeof_str_contains] at h ⊢
          case UOp opg =>
            cases opg <;> simp [__eo_typeof_str_contains] at h ⊢
            case Seq =>
              have hyx : y = x :=
                RuleProofs.eq_of_requires_eq_true_not_stuck x y Term.Bool h
              exact hyx

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

private theorem smtx_eval_str_contains_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_contains x y) =
      __smtx_model_eval_str_contains
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_boolean_term_eq (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

private theorem smtx_eval_numeral_term_eq (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def]

private theorem native_seq_indexof_rec_nil
    (xs : List SmtValue) (i fuel : Nat)
    (hFuel : fuel ≠ 0) :
    native_seq_indexof_rec xs [] i fuel = Int.ofNat i := by
  cases fuel with
  | zero => exact False.elim (hFuel rfl)
  | succ fuel =>
      rw [Smtm.native_seq_indexof_rec.eq_def]
      simp [native_seq_prefix_eq]

private theorem native_seq_indexof_nil_zero (xs : List SmtValue) :
    native_seq_indexof xs [] 0 = 0 := by
  unfold native_seq_indexof
  simp [native_seq_indexof_rec_nil]

private theorem native_seq_contains_nil (xs : List SmtValue) :
    native_seq_contains xs [] = true := by
  unfold native_seq_contains
  rw [native_seq_indexof_nil_zero]
  simp

private theorem native_seq_contains_singleton_singleton
    (x y : SmtValue) :
    native_seq_contains [x] [y] = native_veq x y := by
  by_cases hxy : x = y
  · subst y
    simpa [native_veq] using native_seq_contains_self [x]
  · unfold native_seq_contains
    unfold native_seq_indexof
    have hyx : ¬ y = x := by
      intro hyx
      exact hxy hyx.symm
    simp [native_seq_indexof_rec, native_seq_prefix_eq, native_veq, hxy, hyx]

private theorem native_seq_contains_singleton_long
    (x y z : SmtValue) (zs : List SmtValue) :
    native_seq_contains [x] (y :: z :: zs) = false := by
  unfold native_seq_contains
  unfold native_seq_indexof
  simp

private theorem native_seq_contains_len_one_pack
    (T : SmtType) (xs ys : List SmtValue)
    (hLen : xs.length = 1) :
    native_seq_contains xs ys =
      SmtEval.native_or
        (native_veq (SmtValue.Seq (SmtSeq.empty T))
          (SmtValue.Seq (native_pack_seq T ys)))
        (SmtEval.native_or
          (native_veq (SmtValue.Seq (native_pack_seq T xs))
            (SmtValue.Seq (native_pack_seq T ys))) false) := by
  cases xs with
  | nil =>
      simp at hLen
  | cons x xsTail =>
      cases xsTail with
      | nil =>
          cases ys with
          | nil =>
              simp [native_seq_contains_nil, native_veq, native_pack_seq,
                SmtEval.native_or]
          | cons y ysTail =>
              cases ysTail with
              | nil =>
                  rw [native_seq_contains_singleton_singleton x y]
                  by_cases hxy : x = y
                  · subst y
                    simp [native_veq, native_pack_seq, SmtEval.native_or]
                  · simp [native_veq, native_pack_seq, SmtEval.native_or,
                      hxy]
              | cons z zs =>
                  rw [native_seq_contains_singleton_long x y z zs]
                  simp [native_veq, native_pack_seq, SmtEval.native_or]
      | cons z zs =>
          simp at hLen

private theorem prog_str_contains_char_info
    (x y A P : Term)
    (hProg : __eo_prog_str_contains_char x y A (Proof.pf P) ≠
      Term.Stuck) :
    ∃ T x0,
      A = Term.Apply Term.Seq T ∧
      P = containsCharPremise x0 ∧
      x0 = x ∧
      __eo_prog_str_contains_char x y A (Proof.pf P) =
        containsCharGeneratedConclusion x y T := by
  unfold __eo_prog_str_contains_char at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    have hx :=
      RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    subst_vars
    refine ⟨_, _, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_contains_char, __eo_requires, __eo_eq,
      SmtEval.native_ite, native_teq, SmtEval.native_not,
      containsCharGeneratedConclusion, containsCharGeneratedRhs,
      containsCharLhs, containsCharEmpty, containsCharSelfEq]

private theorem typed___eo_prog_str_contains_char_impl
    (x y P T : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hProgGen :
      __eo_prog_str_contains_char x y (Term.Apply Term.Seq T) (Proof.pf P) =
        containsCharGeneratedConclusion x y T) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_contains_char x y (Term.Apply Term.Seq T) (Proof.pf P)) := by
  let lhs := containsCharLhs x y
  let empty := containsCharEmpty T
  let emptyEq := containsCharEmptyEq y T
  let selfEq := containsCharSelfEq x y
  let rhs := containsCharRhs x y T
  have hYNotStuck : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hProgEq :
      __eo_prog_str_contains_char x y (Term.Apply Term.Seq T) (Proof.pf P) =
        containsCharConclusion x y T := by
    rw [hProgGen, generated_conclusion_eq x y T hYNotStuck]
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt empty) =
        SmtType.Seq (__eo_to_smt_type T) := by
    have hEmptyTy' :=
      smtx_typeof_seq_empty_typeof_of_smt_type_seq x
        (__eo_to_smt_type T) hXSmtTy
    simpa [empty, containsCharEmpty, hXTy] using hEmptyTy'
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y)) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hXSmtTy, hYSmtTy, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hEmptyEqTy : RuleProofs.eo_has_bool_type emptyEq := by
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type empty y
      (by rw [hEmptyTy, hYSmtTy]) (by rw [hEmptyTy]; simp)
  have hSelfEqTy : RuleProofs.eo_has_bool_type selfEq := by
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type x y
      (by rw [hXSmtTy, hYSmtTy]) (by rw [hXSmtTy]; simp)
  have hInnerTy :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.or selfEq) (Term.Boolean false)) := by
    exact RuleProofs.eo_has_bool_type_or_of_bool_args selfEq
      (Term.Boolean false) hSelfEqTy RuleProofs.eo_has_bool_type_false
  have hRhsTy : RuleProofs.eo_has_bool_type rhs := by
    exact RuleProofs.eo_has_bool_type_or_of_bool_args emptyEq
      (Term.Apply (Term.Apply Term.or selfEq) (Term.Boolean false))
      hEmptyEqTy hInnerTy
  have hBoolEq :
      RuleProofs.eo_has_bool_type (containsCharConclusion x y T) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBoolEq

private theorem facts___eo_prog_str_contains_char_impl
    (M : SmtModel) (hM : model_wf M) (x y P T : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hPrem : eo_interprets M (containsCharPremise x) true)
    (hProgGen :
      __eo_prog_str_contains_char x y (Term.Apply Term.Seq T) (Proof.pf P) =
        containsCharGeneratedConclusion x y T) :
    eo_interprets M
      (__eo_prog_str_contains_char x y (Term.Apply Term.Seq T) (Proof.pf P))
      true := by
  let lhs := containsCharLhs x y
  let rhs := containsCharRhs x y T
  let empty := containsCharEmpty T
  let emptyEq := containsCharEmptyEq y T
  let selfEq := containsCharSelfEq x y
  have hYNotStuck : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hProgEq :
      __eo_prog_str_contains_char x y (Term.Apply Term.Seq T) (Proof.pf P) =
        containsCharConclusion x y T := by
    rw [hProgGen, generated_conclusion_eq x y T hYNotStuck]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (containsCharConclusion x y T) := by
    simpa [hProgEq] using
      typed___eo_prog_str_contains_char_impl x y P T hXTrans hYTrans
        hXTy hYTy hProgGen
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hXEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        rw [hXSmtTy]
        simp)
  have hYEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hYSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt y) (by
        unfold term_has_non_none_type
        rw [hYSmtTy]
        simp)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  rcases seq_value_canonical hYEvalTy with ⟨sy, hYEval⟩
  have hXSeqTy :
      __smtx_typeof_seq_value sx = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hXEval] using hXEvalTy
  have hYSeqTy :
      __smtx_typeof_seq_value sy = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hYEval] using hYEvalTy
  have hXElem : __smtx_elem_typeof_seq_value sx = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hXSeqTy
  have hYElem : __smtx_elem_typeof_seq_value sy = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hYSeqTy
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt empty) =
        SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type T)) := by
    have hEmptyEval' :=
      eval_seq_empty_typeof M x (__eo_to_smt_type T) hXSmtTy
    simpa [empty, containsCharEmpty, hXTy] using hEmptyEval'
  have hXLenOne : (native_unpack_seq sx).length = 1 := by
    have hXLenOneInt : native_seq_len (native_unpack_seq sx) = 1 := by
      rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
      cases hPrem with
      | intro_true _ hEval =>
          change __smtx_model_eval M
              (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x))
                (SmtTerm.Numeral 1)) =
            SmtValue.Boolean true at hEval
          rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hXEval,
            smtx_eval_numeral_term_eq] at hEval
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_veq] using hEval
    have hLenInt : ((native_unpack_seq sx).length : Int) = 1 := by
      simpa [native_seq_len] using hXLenOneInt
    omega
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval M
        (SmtTerm.or
          (SmtTerm.eq (__eo_to_smt empty) (__eo_to_smt y))
          (SmtTerm.or
            (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y))
            (SmtTerm.Boolean false)))
    rw [smtx_eval_str_contains_term_eq, smtx_eval_or_term_eq,
      smtx_eval_eq_term_eq, smtx_eval_or_term_eq, smtx_eval_eq_term_eq,
      hEmptyEval, hXEval, hYEval, smtx_eval_boolean_term_eq]
    rw [← native_pack_unpack_seq sx, ← native_pack_unpack_seq sy]
    rw [hXElem, hYElem]
    simp [__smtx_model_eval_str_contains, __smtx_model_eval_eq,
      __smtx_model_eval_or, SmtEval.native_or, Smtm.native_unpack_pack_seq,
      native_seq_contains_len_one_pack (__eo_to_smt_type T)
        (native_unpack_seq sx) (native_unpack_seq sy) hXLenOne]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_contains_char_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_char args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_contains_char args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_char args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_contains_char args premises ≠
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
          | cons A args =>
              cases args with
              | nil =>
                  cases premises with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons n premises =>
                      cases premises with
                      | nil =>
                          let P := __eo_state_proven_nth s n
                          have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk, argTranslationOkMasked] using
                              hCmdTrans.1
                          have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk, argTranslationOkMasked] using
                              hCmdTrans.2.1
                          change __eo_typeof
                              (__eo_prog_str_contains_char a1 a2 A (Proof.pf P)) =
                            Term.Bool at hResultTy
                          have hProgRule :
                              __eo_prog_str_contains_char a1 a2 A (Proof.pf P) ≠
                                Term.Stuck :=
                            term_ne_stuck_of_typeof_bool hResultTy
                          rcases prog_str_contains_char_info a1 a2 A P hProgRule with
                            ⟨T, x0, hATyArg, hPremShape, hx0, hProgGen⟩
                          subst A
                          subst x0
                          let lhs := containsCharLhs a1 a2
                          rw [hProgGen] at hResultTy
                          have hA2NotStuck : a2 ≠ Term.Stuck :=
                            RuleProofs.term_ne_stuck_of_has_smt_translation a2
                              hA2Trans
                          rw [generated_conclusion_eq a1 a2 T hA2NotStuck]
                            at hResultTy
                          change __eo_typeof_eq (__eo_typeof lhs)
                              (__eo_typeof (containsCharRhs a1 a2 T)) =
                            Term.Bool at hResultTy
                          have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                            (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                              (__eo_typeof lhs)
                              (__eo_typeof (containsCharRhs a1 a2 T))
                              hResultTy).1
                          have hArgTypes :
                              ∃ U, __eo_typeof a1 = Term.Apply Term.Seq U ∧
                                __eo_typeof a2 = Term.Apply Term.Seq U := by
                            change __eo_typeof_str_contains (__eo_typeof a1)
                                (__eo_typeof a2) ≠ Term.Stuck at hLhsNotStuck
                            exact eo_typeof_str_contains_args_of_ne_stuck
                              (__eo_typeof a1) (__eo_typeof a2) hLhsNotStuck
                          rcases hArgTypes with ⟨U, hA1TyU, hA2TyU⟩
                          have hRhsNotStuck :
                              __eo_typeof (containsCharRhs a1 a2 T) ≠
                                Term.Stuck :=
                            (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                              (__eo_typeof lhs)
                              (__eo_typeof (containsCharRhs a1 a2 T))
                              hResultTy).2
                          have hEmptyEqTy :
                              __eo_typeof (containsCharEmptyEq a2 T) =
                                Term.Bool :=
                            contains_char_empty_eq_type_bool_of_rhs_ne_stuck
                              a1 a2 T hRhsNotStuck
                          have hUT : U = T := by
                            exact contains_char_type_arg_eq a2 U T hA2TyU
                              hEmptyEqTy
                          subst U
                          have hProps :
                              StepRuleProperties M
                                (premiseTermList s (CIndexList.cons n CIndexList.nil))
                                (__eo_prog_str_contains_char a1 a2
                                  (Term.Apply Term.Seq T) (Proof.pf P)) := by
                            refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (typed___eo_prog_str_contains_char_impl a1 a2 P T
                                hA1Trans hA2Trans hA1TyU hA2TyU hProgGen)⟩
                            intro hTrue
                            have hPremRaw : eo_interprets M P true :=
                              hTrue P (by simp [P, premiseTermList])
                            have hPrem :
                                eo_interprets M (containsCharPremise a1) true := by
                              simpa [hPremShape] using hPremRaw
                            exact facts___eo_prog_str_contains_char_impl M hM
                              a1 a2 P T hA1Trans hA2Trans hA1TyU hA2TyU
                              hPrem hProgGen
                          change StepRuleProperties M [P]
                            (__eo_prog_str_contains_char a1 a2
                              (Term.Apply Term.Seq T) (Proof.pf P))
                          simpa [premiseTermList] using hProps
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
