module

public import Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
import all Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
public import Cpc.Proofs.RuleSupport.StrConcatUnifySupport
import all Cpc.Proofs.RuleSupport.StrConcatUnifySupport
public import Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
import all Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
public import Cpc.Proofs.RuleSupport.StringRewriteSupport
import all Cpc.Proofs.RuleSupport.StringRewriteSupport
public import Cpc.Proofs.RuleSupport.StrOverlapSupport
import all Cpc.Proofs.RuleSupport.StrOverlapSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev stripCharTail (t ts : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat t) ts

private abbrev stripCharFlatTail (t ts : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.str_concat)
    (stripCharTail t ts)

private abbrev stripCharWhole (c t ts : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat c) (stripCharTail t ts)

private abbrev stripCharLenPremise (c : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len c))
    (Term.Numeral 1)

private abbrev stripCharPrefixPremise (c t ts s : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.str_prefixof s) (stripCharWhole c t ts)))
    (Term.Boolean false)

private abbrev stripCharContainsPremise (c t ts s : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.str_contains (stripCharWhole c t ts)) s))
    (Term.Boolean true)

private abbrev stripCharIdx (x s : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_indexof x) s) (Term.Numeral 0)

private abbrev stripCharRhs (t ts s : Term) : Term :=
  Term.Apply (Term.Apply Term.plus (Term.Numeral 1))
    (Term.Apply
      (Term.Apply Term.plus (stripCharIdx (stripCharFlatTail t ts) s))
      (Term.Numeral 0))

private abbrev stripCharConclusion (c t ts s : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (stripCharIdx (stripCharWhole c t ts) s))
    (stripCharRhs t ts s)

private abbrev stripCharGeneratedIdx (t ts s : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_indexof)
        (stripCharFlatTail t ts)) s)
    (Term.Numeral 0)

private abbrev stripCharGeneratedRhs (t ts s : Term) : Term :=
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.plus) (stripCharGeneratedIdx t ts s))
      (Term.Numeral 0))

private abbrev stripCharGeneratedConclusion (c t ts s : Term) : Term :=
  __eo_mk_apply
    (Term.Apply (Term.UOp UserOp.eq)
      (stripCharIdx (stripCharWhole c t ts) s))
    (stripCharGeneratedRhs t ts s)

private theorem mk_apply_eq (f a : Term)
    (hF : f ≠ Term.Stuck) (hA : a ≠ Term.Stuck) :
    __eo_mk_apply f a = Term.Apply f a := by
  cases f <;> cases a <;> simp [__eo_mk_apply] at hF hA ⊢

private theorem generated_flat_ne_stuck
    (c t ts s : Term)
    (hGenerated :
      stripCharGeneratedConclusion c t ts s ≠ Term.Stuck) :
    stripCharFlatTail t ts ≠ Term.Stuck := by
  have hRhs : stripCharGeneratedRhs t ts s ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hGenerated
  have hInner := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hRhs
  have hPlusHead := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hInner
  have hIdx : stripCharGeneratedIdx t ts s ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hPlusHead
  have hIdx2 := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hIdx
  have hIdx1 := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hIdx2
  exact eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hIdx1

private theorem generated_conclusion_eq
    (c t ts s : Term)
    (hFlat : stripCharFlatTail t ts ≠ Term.Stuck)
    (hS : s ≠ Term.Stuck) :
    stripCharGeneratedConclusion c t ts s =
      stripCharConclusion c t ts s := by
  have hIdx1 :
      __eo_mk_apply (Term.UOp UserOp.str_indexof) (stripCharFlatTail t ts) =
        Term.Apply (Term.UOp UserOp.str_indexof) (stripCharFlatTail t ts) :=
    mk_apply_eq _ _ (by simp) hFlat
  have hIdx : stripCharGeneratedIdx t ts s =
      stripCharIdx (stripCharFlatTail t ts) s := by
    rw [stripCharGeneratedIdx, hIdx1, mk_apply_eq _ _ (by simp) hS]
    exact mk_apply_eq _ _ (by simp) (by simp)
  have hRhs : stripCharGeneratedRhs t ts s = stripCharRhs t ts s := by
    have hInner :
        __eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.plus)
              (stripCharIdx (stripCharFlatTail t ts) s))
            (Term.Numeral 0) =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.plus)
              (stripCharIdx (stripCharFlatTail t ts) s))
            (Term.Numeral 0) := by
      have hP1 :
          __eo_mk_apply (Term.UOp UserOp.plus)
              (stripCharIdx (stripCharFlatTail t ts) s) =
            Term.Apply (Term.UOp UserOp.plus)
              (stripCharIdx (stripCharFlatTail t ts) s) :=
        mk_apply_eq _ _ (by simp) (by simp)
      rw [hP1]
      exact mk_apply_eq _ _ (by simp) (by simp)
    rw [stripCharGeneratedRhs, hIdx, hInner]
    exact mk_apply_eq _ _ (by simp) (by simp)
  rw [stripCharGeneratedConclusion, hRhs]
  exact mk_apply_eq _ _ (by simp) (by simp)

private theorem eo_and_eq_true_parts
    (A B : Term)
    (h : __eo_and A B = Term.Boolean true) :
    A = Term.Boolean true ∧ B = Term.Boolean true := by
  cases A <;> cases B <;> simp [__eo_and, native_and] at h ⊢
  case Boolean.Boolean => exact h
  case Binary.Binary w₁ n₁ w₂ n₂ =>
    by_cases hw : w₁ = w₂ <;>
      simp [__eo_requires, hw, native_teq, native_ite,
        SmtEval.native_not] at h

private theorem prog_str_indexof_strip_char_pre_info
    (c t ts s P₁ P₂ P₃ : Term)
    (hProg :
      __eo_prog_str_indexof_strip_char_pre c t ts s
          (Proof.pf P₁) (Proof.pf P₂) (Proof.pf P₃) ≠ Term.Stuck) :
    P₁ = stripCharLenPremise c ∧
      P₂ = stripCharPrefixPremise c t ts s ∧
      P₃ = stripCharContainsPremise c t ts s ∧
      __eo_prog_str_indexof_strip_char_pre c t ts s
          (Proof.pf P₁) (Proof.pf P₂) (Proof.pf P₃) =
        stripCharGeneratedConclusion c t ts s := by
  unfold __eo_prog_str_indexof_strip_char_pre at hProg
  split at hProg <;> try contradiction
  next heq₁ heq₂ heq₃ =>
    cases heq₁
    cases heq₂
    cases heq₃
    have hGuard := support_eo_requires_cond_eq_of_non_stuck hProg
    have h8 := eo_and_eq_true_parts _ _ hGuard
    have h7 := eo_and_eq_true_parts _ _ h8.1
    have h6 := eo_and_eq_true_parts _ _ h7.1
    have h5 := eo_and_eq_true_parts _ _ h6.1
    have h4 := eo_and_eq_true_parts _ _ h5.1
    have h3 := eo_and_eq_true_parts _ _ h4.1
    have h2 := eo_and_eq_true_parts _ _ h3.1
    have h1 := eo_and_eq_true_parts _ _ h2.1
    have e1 := RuleProofs.eq_of_eo_eq_true _ _ h1.1
    have e2 := RuleProofs.eq_of_eo_eq_true _ _ h1.2
    have e3 := RuleProofs.eq_of_eo_eq_true _ _ h2.2
    have e4 := RuleProofs.eq_of_eo_eq_true _ _ h3.2
    have e5 := RuleProofs.eq_of_eo_eq_true _ _ h4.2
    have e6 := RuleProofs.eq_of_eo_eq_true _ _ h5.2
    have e7 := RuleProofs.eq_of_eo_eq_true _ _ h6.2
    have e8 := RuleProofs.eq_of_eo_eq_true _ _ h7.2
    have e9 := RuleProofs.eq_of_eo_eq_true _ _ h8.2
    subst_vars
    refine ⟨rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_indexof_strip_char_pre, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, stripCharGeneratedConclusion,
      stripCharGeneratedRhs, stripCharGeneratedIdx, stripCharWhole,
      stripCharTail, stripCharIdx, stripCharFlatTail]

private theorem native_seq_indexof_strip_char
    (c : SmtValue) (rest pat : List SmtValue)
    (hPre : native_seq_prefix_eq pat (c :: rest) = false)
    (hCont : native_seq_contains (c :: rest) pat = true) :
    native_seq_indexof (c :: rest) pat 0 =
      native_zplus 1 (native_zplus (native_seq_indexof rest pat 0) 0) := by
  have hContIdx : 0 ≤ native_seq_indexof (c :: rest) pat 0 := by
    simpa [native_seq_contains] using hCont
  rw [native_seq_indexof_eq_rec] at hContIdx ⊢
  rw [native_seq_indexof_eq_rec]
  simp only [Int.lt_irrefl, ↓reduceIte, Int.toNat_zero, List.drop_zero,
    Nat.zero_add, List.length_cons] at hContIdx ⊢
  by_cases hB : pat.length ≤ rest.length + 1
  · simp only [hB, ↓reduceDIte] at hContIdx ⊢
    have hStep : ∀ fuel : Nat,
        native_seq_indexof_rec (c :: rest) pat 0 (fuel + 1) =
          native_seq_indexof_rec rest pat 1 fuel := by
      intro fuel
      rw [native_seq_indexof_rec.eq_def]
      simp [hPre]
    rw [hStep] at hContIdx ⊢
    by_cases hB2 : pat.length ≤ rest.length
    · simp only [hB2, ↓reduceDIte]
      have hFuelEq : rest.length + 1 - pat.length =
          rest.length - pat.length + 1 := by omega
      rw [hFuelEq] at hContIdx ⊢
      have hOff := RuleProofs.native_seq_indexof_rec_offset rest pat 0 1
        (rest.length - pat.length + 1)
      simp only [Nat.zero_add] at hOff
      rw [hOff] at hContIdx ⊢
      by_cases hNeg :
          native_seq_indexof_rec rest pat 0 (rest.length - pat.length + 1) =
            -1
      · simp only [hNeg, ↓reduceIte] at hContIdx
        exact absurd hContIdx (by decide)
      · simp only [hNeg, ↓reduceIte]
        simp only [native_zplus, Int.add_zero]
        exact Int.add_comm _ _
    · have hZero : rest.length + 1 - pat.length = 0 := by omega
      rw [hZero] at hContIdx
      simp [native_seq_indexof_rec] at hContIdx
  · simp only [hB, ↓reduceDIte] at hContIdx
    exact absurd hContIdx (by decide)

private theorem native_seq_prefix_eq_false_of_eval
    (ss sw : SmtSeq) (U : SmtType)
    (hSsElem : __smtx_elem_typeof_seq_value ss = U)
    (hSwElem : __smtx_elem_typeof_seq_value sw = U)
    (hEval :
      __smtx_model_eval_str_prefixof (SmtValue.Seq ss) (SmtValue.Seq sw) =
        SmtValue.Boolean false) :
    native_seq_prefix_eq (native_unpack_seq ss) (native_unpack_seq sw) =
      false := by
  cases hP : native_seq_prefix_eq (native_unpack_seq ss)
      (native_unpack_seq sw) with
  | false => rfl
  | true =>
      exfalso
      have hApp := native_seq_prefix_eq_append_drop _ _ hP
      have hLe := native_seq_prefix_eq_length_le _ _ hP
      have hExtract :
          native_seq_extract (native_unpack_seq sw) 0
              (Int.ofNat (native_unpack_seq ss).length) =
            native_unpack_seq ss := by
        rw [native_seq_extract_zero_nat _ _ hLe]
        conv => lhs; rw [← hApp]
        simp
      have hPack : native_pack_seq (__smtx_elem_typeof_seq_value sw)
          (native_unpack_seq ss) = ss := by
        rw [hSwElem, ← hSsElem]
        exact native_pack_unpack_seq ss
      have hTrue :
          __smtx_model_eval_str_prefixof (SmtValue.Seq ss)
              (SmtValue.Seq sw) = SmtValue.Boolean true := by
        simp [__smtx_model_eval_str_prefixof, __smtx_model_eval_str_len,
          __smtx_model_eval_str_substr, native_seq_len]
        change __smtx_model_eval_eq (SmtValue.Seq ss)
            (SmtValue.Seq
              (native_pack_seq (__smtx_elem_typeof_seq_value sw)
                (native_seq_extract (native_unpack_seq sw) 0
                  (Int.ofNat (native_unpack_seq ss).length)))) = _
        rw [hExtract, hPack]
        simp [__smtx_model_eval_eq, native_veq]
      rw [hTrue] at hEval
      cases hEval

private theorem typed___eo_prog_str_indexof_strip_char_pre_impl
    (c t ts s T : Term)
    (hCTrans : RuleProofs.eo_has_smt_translation c)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hTsTrans : RuleProofs.eo_has_smt_translation ts)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hCTy : __eo_typeof c = Term.Apply Term.Seq T)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hTsTy : __eo_typeof ts = Term.Apply Term.Seq T)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hFlatNe : stripCharFlatTail t ts ≠ Term.Stuck) :
    RuleProofs.eo_has_bool_type (stripCharConclusion c t ts s) := by
  have hCSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq c T hCTrans hCTy
  have hTSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hTsSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq ts T hTsTrans hTsTy
  have hSSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hTailTy : __smtx_typeof (__eo_to_smt (stripCharTail t ts)) =
      SmtType.Seq (__eo_to_smt_type T) :=
    smt_typeof_str_concat_of_seq t ts (__eo_to_smt_type T) hTSmtTy hTsSmtTy
  have hFlatTy : __smtx_typeof (__eo_to_smt (stripCharFlatTail t ts)) =
      SmtType.Seq (__eo_to_smt_type T) :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck
      (stripCharTail t ts) (__eo_to_smt_type T) hTailTy hFlatNe
  have hWholeTy : __smtx_typeof (__eo_to_smt (stripCharWhole c t ts)) =
      SmtType.Seq (__eo_to_smt_type T) :=
    smt_typeof_str_concat_of_seq c (stripCharTail t ts) (__eo_to_smt_type T)
      hCSmtTy hTailTy
  have hZeroTy : __smtx_typeof (__eo_to_smt (Term.Numeral 0)) =
      SmtType.Int := by rfl
  have hLhsTy := StringRewriteSupport.smt_typeof_str_indexof_of_seq
    (stripCharWhole c t ts) s (Term.Numeral 0) (__eo_to_smt_type T)
    hWholeTy hSSmtTy hZeroTy
  have hIdxTy := StringRewriteSupport.smt_typeof_str_indexof_of_seq
    (stripCharFlatTail t ts) s (Term.Numeral 0) (__eo_to_smt_type T)
    hFlatTy hSSmtTy hZeroTy
  have hRhsTy : __smtx_typeof (__eo_to_smt (stripCharRhs t ts s)) =
      SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.plus (SmtTerm.Numeral 1)
          (SmtTerm.plus
            (__eo_to_smt (stripCharIdx (stripCharFlatTail t ts) s))
            (SmtTerm.Numeral 0))) = SmtType.Int
    rw [typeof_plus_eq, typeof_plus_eq, hIdxTy]
    rfl
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)

private theorem facts___eo_prog_str_indexof_strip_char_pre_impl
    (M : SmtModel) (hM : model_wf M)
    (c t ts s T : Term)
    (hCTrans : RuleProofs.eo_has_smt_translation c)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hTsTrans : RuleProofs.eo_has_smt_translation ts)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hCTy : __eo_typeof c = Term.Apply Term.Seq T)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hTsTy : __eo_typeof ts = Term.Apply Term.Seq T)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hFlatNe : stripCharFlatTail t ts ≠ Term.Stuck)
    (hPrem₁ : eo_interprets M (stripCharLenPremise c) true)
    (hPrem₂ : eo_interprets M (stripCharPrefixPremise c t ts s) true)
    (hPrem₃ : eo_interprets M (stripCharContainsPremise c t ts s) true) :
    eo_interprets M (stripCharConclusion c t ts s) true := by
  let tail := stripCharTail t ts
  let flat := stripCharFlatTail t ts
  let whole := stripCharWhole c t ts
  let lhs := stripCharIdx whole s
  let rhs := stripCharRhs t ts s
  let U := __eo_to_smt_type T
  have hBool : RuleProofs.eo_has_bool_type (stripCharConclusion c t ts s) :=
    typed___eo_prog_str_indexof_strip_char_pre_impl c t ts s T
      hCTrans hTTrans hTsTrans hSTrans hCTy hTTy hTsTy hSTy hFlatNe
  have hCSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq c T hCTrans hCTy
  have hTSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hTsSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq ts T hTsTrans hTsTy
  have hSSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.Seq U :=
    smt_typeof_str_concat_of_seq t ts U hTSmtTy hTsSmtTy
  have hFlatTy : __smtx_typeof (__eo_to_smt flat) = SmtType.Seq U :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck tail U hTailTy hFlatNe
  have hWholeTy : __smtx_typeof (__eo_to_smt whole) = SmtType.Seq U :=
    smt_typeof_str_concat_of_seq c tail U hCSmtTy hTailTy
  have hCEvalTy := smt_model_eval_preserves_type M hM (__eo_to_smt c)
    (SmtType.Seq U) hCSmtTy (seq_ne_none _) (type_inhabited_seq _)
  have hTEvalTy := smt_model_eval_preserves_type M hM (__eo_to_smt t)
    (SmtType.Seq U) hTSmtTy (seq_ne_none _) (type_inhabited_seq _)
  have hTsEvalTy := smt_model_eval_preserves_type M hM (__eo_to_smt ts)
    (SmtType.Seq U) hTsSmtTy (seq_ne_none _) (type_inhabited_seq _)
  have hSEvalTy := smt_model_eval_preserves_type M hM (__eo_to_smt s)
    (SmtType.Seq U) hSSmtTy (seq_ne_none _) (type_inhabited_seq _)
  have hFlatEvalTy := smt_model_eval_preserves_type M hM (__eo_to_smt flat)
    (SmtType.Seq U) hFlatTy (seq_ne_none _) (type_inhabited_seq _)
  have hWholeEvalTy := smt_model_eval_preserves_type M hM
    (__eo_to_smt whole) (SmtType.Seq U) hWholeTy (seq_ne_none _)
    (type_inhabited_seq _)
  rcases seq_value_canonical hCEvalTy with ⟨sc, hCEval⟩
  rcases seq_value_canonical hTEvalTy with ⟨st, hTEval⟩
  rcases seq_value_canonical hTsEvalTy with ⟨sts, hTsEval⟩
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases seq_value_canonical hFlatEvalTy with ⟨sflat, hFlatEval⟩
  rcases seq_value_canonical hWholeEvalTy with ⟨sw, hWholeEval⟩
  have hSSeqTy : __smtx_typeof_seq_value ss = SmtType.Seq U := by
    simpa [__smtx_typeof_value, hSEval] using hSEvalTy
  have hWSeqTy : __smtx_typeof_seq_value sw = SmtType.Seq U := by
    simpa [__smtx_typeof_value, hWholeEval] using hWholeEvalTy
  have hSElem : __smtx_elem_typeof_seq_value ss = U :=
    elem_typeof_seq_value_of_typeof_seq_value hSSeqTy
  have hWElem : __smtx_elem_typeof_seq_value sw = U :=
    elem_typeof_seq_value_of_typeof_seq_value hWSeqTy
  let stail := native_pack_seq (__smtx_elem_typeof_seq_value st)
    (native_unpack_seq st ++ native_unpack_seq sts)
  have hTailEval : __smtx_model_eval M (__eo_to_smt tail) =
      SmtValue.Seq stail := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (__eo_to_smt t) (__eo_to_smt ts)) = _
    rw [StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      hTEval, hTsEval]
    rfl
  have hFlatTailRel := smt_value_rel_str_nary_elim M hM tail U hTailTy
    hFlatNe
  have hFlatTailEq : sflat = stail := by
    have hSeqRel : RuleProofs.smt_seq_rel sflat stail := by
      change RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt flat))
          (__smtx_model_eval M (__eo_to_smt tail)) at hFlatTailRel
      rw [hFlatEval, hTailEval] at hFlatTailRel
      exact hFlatTailRel
    exact (RuleProofs.smt_seq_rel_iff_eq sflat stail).1 hSeqRel
  have hFlatUnpack : native_unpack_seq sflat =
      native_unpack_seq st ++ native_unpack_seq sts := by
    rw [hFlatTailEq]
    simp [stail, Smtm.native_unpack_pack_seq]
  have hWholeEval' : __smtx_model_eval M (__eo_to_smt whole) =
      SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sc)
        (native_unpack_seq sc ++ native_unpack_seq stail)) := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (__eo_to_smt c) (__eo_to_smt tail)) = _
    rw [StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      hCEval, hTailEval]
    rfl
  have hWUnpack : native_unpack_seq sw =
      native_unpack_seq sc ++ native_unpack_seq sflat := by
    rw [hWholeEval] at hWholeEval'
    injection hWholeEval' with hSw
    rw [hSw, Smtm.native_unpack_pack_seq, hFlatTailEq]
  have hCLen : (native_unpack_seq sc).length = 1 := by
    have hCLenInt : native_seq_len (native_unpack_seq sc) = 1 := by
      rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem₁
      cases hPrem₁ with
      | intro_true _ hEval =>
          change __smtx_model_eval M
              (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt c))
                (SmtTerm.Numeral 1)) =
            SmtValue.Boolean true at hEval
          rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hCEval,
            StrEqReplSupport.smtx_eval_numeral_term_eq] at hEval
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_veq] using hEval
    have hCast : ((native_unpack_seq sc).length : Int) = 1 := by
      simpa [native_seq_len] using hCLenInt
    omega
  have hPrefixFalse :
      __smtx_model_eval_str_prefixof (SmtValue.Seq ss) (SmtValue.Seq sw) =
        SmtValue.Boolean false := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem₂
    cases hPrem₂ with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.str_prefixof (__eo_to_smt s) (__eo_to_smt whole))
              (SmtTerm.Boolean false)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, StrEqReplSupport.smtx_eval_str_prefixof_term_eq,
          hSEval, hWholeEval, StrEqReplSupport.smtx_eval_boolean_term_eq]
          at hEval
        generalize hV : __smtx_model_eval_str_prefixof (SmtValue.Seq ss)
          (SmtValue.Seq sw) = v at hEval
        cases v <;> simp [__smtx_model_eval_eq, native_veq] at hEval
        all_goals first | rfl | (subst_vars; rfl)
  have hContTrue :
      native_seq_contains (native_unpack_seq sw) (native_unpack_seq ss) =
        true := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem₃
    cases hPrem₃ with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.str_contains (__eo_to_smt whole) (__eo_to_smt s))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq,
          StrContainsReplCharSupport.smtx_eval_str_contains_term_eq,
          hSEval, hWholeEval, StrEqReplSupport.smtx_eval_boolean_term_eq]
          at hEval
        simpa [__smtx_model_eval_str_contains, __smtx_model_eval_eq,
          native_veq] using hEval
  have hPre := native_seq_prefix_eq_false_of_eval ss sw U hSElem hWElem
    hPrefixFalse
  obtain ⟨c0, hC0⟩ : ∃ c0, native_unpack_seq sc = [c0] := by
    cases h : native_unpack_seq sc with
    | nil => rw [h] at hCLen; simp at hCLen
    | cons x xs =>
        cases xs with
        | nil => exact ⟨x, rfl⟩
        | cons _ _ => rw [h] at hCLen; simp at hCLen
  rw [hWUnpack, hC0] at hPre hContTrue
  have hIdx := native_seq_indexof_strip_char c0 (native_unpack_seq sflat)
    (native_unpack_seq ss) hPre hContTrue
  have hEvalEq : __smtx_model_eval M (__eo_to_smt lhs) =
      __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_indexof (__eo_to_smt whole) (__eo_to_smt s)
          (SmtTerm.Numeral 0)) =
      __smtx_model_eval M
        (SmtTerm.plus (SmtTerm.Numeral 1)
          (SmtTerm.plus
            (SmtTerm.str_indexof (__eo_to_smt flat) (__eo_to_smt s)
              (SmtTerm.Numeral 0))
            (SmtTerm.Numeral 0)))
    rw [StringRewriteSupport.smtx_eval_str_indexof_term_eq,
      StrSubstrContainsSupport.smtx_eval_plus_term_eq,
      StrSubstrContainsSupport.smtx_eval_plus_term_eq,
      StringRewriteSupport.smtx_eval_str_indexof_term_eq,
      hWholeEval, hFlatEval, hSEval,
      StrEqReplSupport.smtx_eval_numeral_term_eq,
      StrEqReplSupport.smtx_eval_numeral_term_eq]
    simp only [__smtx_model_eval_str_indexof, __smtx_model_eval_plus]
    rw [hWUnpack, hC0, List.singleton_append, hIdx]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_indexof_strip_char_pre_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_strip_char_pre args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_indexof_strip_char_pre args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_strip_char_pre args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_indexof_strip_char_pre
          args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons c args =>
  cases args with
  | nil => exact absurd rfl hProg
  | cons t args =>
  cases args with
  | nil => exact absurd rfl hProg
  | cons ts args =>
  cases args with
  | nil => exact absurd rfl hProg
  | cons x args =>
  cases args with
  | cons _ _ => exact absurd rfl hProg
  | nil =>
  cases premises with
  | nil => exact absurd rfl hProg
  | cons i₁ premises =>
  cases premises with
  | nil => exact absurd rfl hProg
  | cons i₂ premises =>
  cases premises with
  | nil => exact absurd rfl hProg
  | cons i₃ premises =>
  cases premises with
  | cons _ _ => exact absurd rfl hProg
  | nil =>
  let P₁ := __eo_state_proven_nth s i₁
  let P₂ := __eo_state_proven_nth s i₂
  let P₃ := __eo_state_proven_nth s i₃
  have hCTrans : RuleProofs.eo_has_smt_translation c := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
  have hTTrans : RuleProofs.eo_has_smt_translation t := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.1
  have hTsTrans : RuleProofs.eo_has_smt_translation ts := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.2.1
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.2.2.1
  change __eo_typeof
      (__eo_prog_str_indexof_strip_char_pre c t ts x
        (Proof.pf P₁) (Proof.pf P₂) (Proof.pf P₃)) = Term.Bool at hResultTy
  have hRuleProg :
      __eo_prog_str_indexof_strip_char_pre c t ts x
          (Proof.pf P₁) (Proof.pf P₂) (Proof.pf P₃) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rcases prog_str_indexof_strip_char_pre_info c t ts x P₁ P₂ P₃ hRuleProg with
    ⟨hP₁, hP₂, hP₃, hProgGenerated⟩
  have hGeneratedNe :
      stripCharGeneratedConclusion c t ts x ≠ Term.Stuck := by
    rw [← hProgGenerated]
    exact hRuleProg
  have hFlatNe := generated_flat_ne_stuck c t ts x hGeneratedNe
  have hXNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hProgEq :
      __eo_prog_str_indexof_strip_char_pre c t ts x
          (Proof.pf P₁) (Proof.pf P₂) (Proof.pf P₃) =
        stripCharConclusion c t ts x := by
    rw [hProgGenerated, generated_conclusion_eq c t ts x hFlatNe hXNe]
  rw [hProgEq] at hResultTy
  have hOps :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (stripCharIdx (stripCharWhole c t ts) x))
      (__eo_typeof (stripCharRhs t ts x)) hResultTy
  have hLhsNN := hOps.1
  change __eo_typeof_str_indexof
      (__eo_typeof (stripCharWhole c t ts)) (__eo_typeof x)
      (__eo_typeof (Term.Numeral 0)) ≠ Term.Stuck at hLhsNN
  rcases StringRewriteSupport.eo_typeof_str_indexof_args_of_ne_stuck
      _ _ _ hLhsNN with ⟨T, hWholeTy, hXTy, _hZeroTy⟩
  have hWholeArgs :=
    StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
      c (stripCharTail t ts) T hWholeTy
  have hTailArgs :=
    StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
      t ts T hWholeArgs.2
  change StepRuleProperties M [P₁, P₂, P₃]
    (__eo_prog_str_indexof_strip_char_pre c t ts x
      (Proof.pf P₁) (Proof.pf P₂) (Proof.pf P₃))
  rw [hProgEq]
  refine ⟨?_, ?_⟩
  · intro hTrue
    have hPrem₁ : eo_interprets M (stripCharLenPremise c) true := by
      simpa [hP₁] using hTrue P₁ (by simp)
    have hPrem₂ : eo_interprets M (stripCharPrefixPremise c t ts x) true := by
      simpa [hP₂] using hTrue P₂ (by simp)
    have hPrem₃ :
        eo_interprets M (stripCharContainsPremise c t ts x) true := by
      simpa [hP₃] using hTrue P₃ (by simp)
    exact facts___eo_prog_str_indexof_strip_char_pre_impl
      M hM c t ts x T hCTrans hTTrans hTsTrans hXTrans
      hWholeArgs.1 hTailArgs.1 hTailArgs.2 hXTy hFlatNe hPrem₁ hPrem₂ hPrem₃
  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
      (typed___eo_prog_str_indexof_strip_char_pre_impl
        c t ts x T hCTrans hTTrans hTsTrans hXTrans
        hWholeArgs.1 hTailArgs.1 hTailArgs.2 hXTy hFlatNe)
