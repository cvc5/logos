module

public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport
public import Cpc.Proofs.RuleSupport.StringSupport
import all Cpc.Proofs.RuleSupport.StringSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.RegexSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

local notation "native_str_in_re" => RuleProofs.native_str_in_re

private theorem native_unpack_string_length_eq (ss : SmtSeq) :
    (native_unpack_string ss).length = (native_unpack_seq ss).length := by
  simp [native_unpack_string]

private theorem native_unpack_pack_string (s : native_String) :
    native_unpack_string (native_pack_string s) = s := by
  unfold native_unpack_string native_pack_string
  rw [_root_.native_unpack_pack_seq]
  induction s with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [impl_native_ssm_char_of_value, ih]

private theorem native_str_to_code_singleton_bounds
    {xs : native_String}
    (hValid : native_string_valid xs = true)
    (hLen : xs.length = 1) :
    0 ≤ native_str_to_code xs ∧ native_str_to_code xs < 196608 := by
  cases xs with
  | nil =>
      simp at hLen
  | cons c cs =>
      cases cs with
      | nil =>
          simp [native_string_valid] at hValid
          have hc : c < 196608 := by simpa [native_char_valid] using hValid
          simp [native_str_to_code, native_char_valid, hc]
          exact Int.ofNat_lt.mpr hc
      | cons d ds =>
          simp at hLen

private theorem native_str_to_code_non_singleton
    (xs : native_String)
    (hLen : xs.length ≠ 1) :
    native_str_to_code xs = -1 := by
  cases xs with
  | nil =>
      simp [native_str_to_code]
  | cons c cs =>
      cases cs with
      | nil =>
          exfalso
          exact hLen (by simp)
      | cons d ds =>
          simp [native_str_to_code]

private theorem native_str_to_code_from_code_of_valid
    {n : native_Int}
    (hn0 : 0 ≤ n) (hnHi : n < 196608) :
    native_str_to_code (native_str_from_code n) = n := by
  have hNatLt : Int.toNat n < 196608 := by
    exact (Int.toNat_lt hn0).mpr hnHi
  simp [native_str_from_code, native_str_to_code, native_char_valid, hn0,
    hNatLt, Int.toNat_of_nonneg hn0]

private theorem native_str_from_code_invalid
    {n : native_Int}
    (hBad : ¬ (0 ≤ n ∧ n < 196608)) :
    native_str_from_code n = [] := by
  unfold native_str_from_code
  by_cases hn0 : 0 ≤ n
  · have hNatLtFalse : ¬ Int.toNat n < 196608 := by
      intro hNatLt
      have hnHi : n < 196608 := (Int.toNat_lt hn0).mp hNatLt
      exact hBad ⟨hn0, hnHi⟩
    have hGuard :
        (0 ≤ n && native_char_valid (Int.toNat n)) = false := by
      simp [hn0, native_char_valid, hNatLtFalse]
    rw [hGuard]
    rfl
  · have hGuard :
        (0 ≤ n && native_char_valid (Int.toNat n)) = false := by
      simp [hn0]
    rw [hGuard]
    rfl

private theorem native_str_to_int_ge_neg_one
    (s : native_String) :
    (-1 : Int) ≤ native_str_to_int s := by
  cases s with
  | nil =>
      simp [native_str_to_int]
  | cons c cs =>
      by_cases hDigits : List.all (c :: cs) impl_native_char_is_digit = true
      · simp [native_str_to_int, hDigits]
      · simp [native_str_to_int, hDigits]

private theorem smt_typeof_seq_empty_typeof_of_smt_type_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
      SmtType.Seq T := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  have hSeqWF : __smtx_type_wf (SmtType.Seq T) = true := by
    have hGood :=
      smt_term_result_seq_components_wf_of_non_none (__eo_to_smt x) hTrans
    rw [hxTy] at hGood
    simpa [type_result_seq_components_wf] using hGood
  by_cases hSpecial :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  · rw [hSpecial]
    change __smtx_typeof (SmtTerm.String (native_string_lit "")) = SmtType.Seq T
    rw [__smtx_typeof.eq_4]
    rw [hSpecial] at hA
    simp [TranslationProofs.eo_to_smt_type_seq,
      TranslationProofs.eo_to_smt_type_char] at hA
    exact hA
  ·
    by_cases hStuck : __eo_typeof x = Term.Stuck
    · rw [hStuck] at hA
      simp [__eo_to_smt_type] at hA
    · have hDefault :
          __seq_empty (__eo_typeof x) = Term.UOp1 UserOp1.seq_empty (__eo_typeof x) := by
        cases hTy : __eo_typeof x <;>
          simp [__seq_empty, hTy] at hStuck hSpecial ⊢
        case Apply f a =>
          cases f <;> simp at hSpecial ⊢
          case UOp op =>
            cases op <;> simp at hSpecial ⊢
            case Seq =>
              cases a <;> simp at hSpecial ⊢
              case UOp op' =>
                cases op' <;> simp at hSpecial ⊢
      rw [hDefault]
      change
        __smtx_typeof (__eo_to_smt_seq_empty
          (__eo_to_smt_type (__eo_typeof x))) = SmtType.Seq T
      rw [hA]
      change __smtx_typeof (SmtTerm.seq_empty T) = SmtType.Seq T
      simp [__smtx_typeof, __smtx_typeof_guard_wf, native_ite, hSeqWF]

private theorem smt_typeof_nil_str_concat_typeof_of_smt_type_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof
        (__eo_to_smt (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x))) =
      SmtType.Seq T := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  rw [strConcat_nil_eq_seq_empty_of_type hA]
  exact smt_typeof_seq_empty_typeof_of_smt_type_seq x T hxTy

private theorem nil_str_concat_typeof_ne_stuck_of_smt_type_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x) ≠ Term.Stuck := by
  intro h
  have hNilTy :=
    smt_typeof_nil_str_concat_typeof_of_smt_type_seq x T hxTy
  rw [h] at hNilTy
  change __smtx_typeof SmtTerm.None = SmtType.Seq T at hNilTy
  rw [TranslationProofs.smtx_typeof_none] at hNilTy
  cases hNilTy

private theorem eval_nil_str_concat_typeof_of_smt_type_seq
    (M : SmtModel) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_model_eval M
        (__eo_to_smt (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x))) =
      SmtValue.Seq (SmtSeq.empty T) := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  rw [strConcat_nil_eq_seq_empty_of_type hA]
  exact eval_seq_empty_typeof M x T hxTy

private theorem native_re_find_idx_aux_bound
    {r : SmtRegLan} :
    (xs : List SmtValue) -> (idx : Nat) -> {found len : Nat} ->
      impl_native_re_find_idx_aux r xs idx = some (found, len) ->
      idx ≤ found ∧ found ≤ idx + xs.length
  | xs, idx, found, len, hFind => by
      unfold impl_native_re_find_idx_aux at hFind
      split at hFind
      · cases hFind
        omega
      · cases xs with
        | nil =>
            cases hFind
        | cons _ cs =>
            have h := native_re_find_idx_aux_bound cs (idx + 1) hFind
            rcases h with ⟨hLo, hHi⟩
            constructor
            · omega
            · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hHi

private theorem native_str_indexof_re_eq_neg_one_or_ge
    (s : List SmtValue) (r : SmtRegLan) (i : native_Int) :
    native_str_indexof_re s r i = -1 ∨ i ≤ native_str_indexof_re s r i := by
  unfold native_str_indexof_re
  by_cases hi : i < 0
  · simp [hi]
  · have hi0 : 0 ≤ i := int_nonneg_of_not_neg hi
    by_cases hStart : Int.toNat i ≤ s.length
    · simp only [if_neg hi, if_pos hStart]
      cases hFind : native_re_find_idx_from r s
          (Int.toNat i) with
      | none =>
          simp
      | some p =>
          cases p with
          | mk found len =>
              right
              unfold native_re_find_idx_from at hFind
              have hBound := native_re_find_idx_aux_bound
                (s.drop (Int.toNat i))
                  (Int.toNat i) hFind
              have hLeFound : i ≤ (found : Int) := by
                calc
                i = (Int.toNat i : Int) := (Int.toNat_of_nonneg hi0).symm
                _ ≤ (found : Int) := Int.ofNat_le.mpr hBound.1
              exact hLeFound
    · simp [hi, hStart]

private theorem native_str_indexof_re_le_len
    (s : List SmtValue) (r : SmtRegLan) (i : native_Int) :
    native_str_indexof_re s r i ≤ Int.ofNat s.length := by
  unfold native_str_indexof_re
  by_cases hi : i < 0
  · simp [hi]
  · by_cases hStart : Int.toNat i ≤ s.length
    · simp only [if_neg hi, if_pos hStart]
      cases hFind : native_re_find_idx_from r s
          (Int.toNat i) with
      | none =>
          simp
      | some p =>
          cases p with
          | mk found len =>
              unfold native_re_find_idx_from at hFind
              have hBound := native_re_find_idx_aux_bound
                (s.drop (Int.toNat i))
                  (Int.toNat i) hFind
              have hDropLen :
                  (s.drop (Int.toNat i)).length =
                    s.length - Int.toNat i := by
                simp [List.length_drop]
              have hFoundLe : found ≤ s.length := by
                omega
              exact Int.ofNat_le.mpr hFoundLe
    · simp [hi, hStart]

private theorem int_eval_of_int_type
    (M : SmtModel) (hM : model_wf M) (t : Term) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Int ->
    ∃ z : native_Int, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Numeral z := by
  intro hTy
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by simp [term_has_non_none_type, hTy])
  exact int_value_canonical (by simpa [hTy] using hEvalTy)

private theorem seq_eval_of_seq_type
    (M : SmtModel) (hM : model_wf M) (t : Term) (T : SmtType) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ->
    ∃ ss, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq ss := by
  intro hTy
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by simp [term_has_non_none_type, hTy])
  exact seq_value_canonical (by simpa [hTy] using hEvalTy)

private theorem reglan_eval_of_reglan_type
    (M : SmtModel) (hM : model_wf M) (t : Term) :
    __smtx_typeof (__eo_to_smt t) = SmtType.RegLan ->
    ∃ r, __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan r := by
  intro hTy
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by simp [term_has_non_none_type, hTy])
  exact reglan_value_canonical (by simpa [hTy] using hEvalTy)

private abbrev nativeListInRe := RuleProofs.nativeListInRe

/- The definitions and algebraic proofs in this block are retained as historical
   context.  RegexSupport now owns these facts; the wrappers following the block
   keep the local call sites independent of that implementation move.

private theorem nativeListInRe_empty :
    (xs : List native_Char) -> nativeListInRe xs SmtRegLan.empty = false
  | [] => by rfl
  | _ :: xs => by
      exact nativeListInRe_empty xs

private theorem native_re_nullable_mk_union (r s : SmtRegLan) :
    native_re_nullable (native_re_mk_union r s) =
      (native_re_nullable r || native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_union, native_re_union, native_re_nullable]
  all_goals
    split <;> simp_all [native_re_nullable]

private theorem native_re_mk_union_self (r : SmtRegLan) :
    native_re_mk_union r r = r := by
  cases r <;> simp [native_re_mk_union, native_re_union]

private theorem native_re_mk_union_eq_union_of_ne
    (r s : SmtRegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ s ->
    native_re_mk_union r s = SmtRegLan.union r s := by
  intro hr hs hrs
  cases r <;> cases s <;>
    simp [native_re_mk_union, native_re_union] at hr hs ⊢
  all_goals
    try exact False.elim (hrs rfl)
    try
      intro h
      subst h
      exact False.elim (hrs rfl)
    try
      intro h1 h2
      subst h1
      subst h2
      exact False.elim (hrs rfl)

private theorem nativeListInRe_mk_union :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      nativeListInRe xs (native_re_mk_union r s) =
        (nativeListInRe xs r || nativeListInRe xs s)
  | [], r, s => by
      simp [nativeListInRe, native_re_nullable_mk_union]
  | c :: cs, r, s => by
      by_cases hr : r = SmtRegLan.empty
      · subst r
        simp [native_re_mk_union, native_re_union, nativeListInRe_empty]
      ·
        by_cases hs : s = SmtRegLan.empty
        · subst s
          simp [native_re_mk_union, native_re_union, nativeListInRe_empty]
        ·
          by_cases hEq : r = s
          · subst s
            rw [native_re_mk_union_self]
            simp [nativeListInRe]
          · rw [native_re_mk_union_eq_union_of_ne r s hr hs hEq]
            simp [nativeListInRe, native_re_deriv]
            exact nativeListInRe_mk_union cs
              (native_re_deriv c r) (native_re_deriv c s)

private theorem native_re_mk_inter_self (r : SmtRegLan) :
    native_re_mk_inter r r = r := by
  cases r <;> simp [native_re_mk_inter, native_re_inter]

private theorem native_re_mk_inter_eq_inter_of_ne
    (r s : SmtRegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ s ->
    native_re_mk_inter r s = SmtRegLan.inter r s := by
  intro hr hs hrs
  cases r <;> cases s <;>
    simp [native_re_mk_inter, native_re_inter] at hr hs ⊢
  all_goals
    try exact False.elim (hrs rfl)
    try
      intro h
      subst h
      exact False.elim (hrs rfl)
    try
      intro h1 h2
      subst h1
      subst h2
      exact False.elim (hrs rfl)

private theorem native_re_nullable_mk_inter (r s : SmtRegLan) :
    native_re_nullable (native_re_mk_inter r s) =
      (native_re_nullable r && native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_inter, native_re_inter, native_re_nullable]
  all_goals
    split <;> simp_all [native_re_nullable]

private theorem nativeListInRe_mk_inter :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      nativeListInRe xs (native_re_mk_inter r s) =
        (nativeListInRe xs r && nativeListInRe xs s)
  | [], r, s => by
      simp [nativeListInRe, native_re_nullable_mk_inter]
  | c :: cs, r, s => by
      by_cases hr : r = SmtRegLan.empty
      · subst r
        simp [native_re_mk_inter, native_re_inter, nativeListInRe_empty]
      ·
        by_cases hs : s = SmtRegLan.empty
        · subst s
          simp [native_re_mk_inter, native_re_inter, nativeListInRe_empty]
        ·
          by_cases hEq : r = s
          · subst s
            rw [native_re_mk_inter_self]
            simp [nativeListInRe]
          · rw [native_re_mk_inter_eq_inter_of_ne r s hr hs hEq]
            simp [nativeListInRe, native_re_deriv]
            exact nativeListInRe_mk_inter cs
              (native_re_deriv c r) (native_re_deriv c s)

private theorem native_re_nullable_mk_concat (r s : SmtRegLan) :
    native_re_nullable (native_re_mk_concat r s) =
      (native_re_nullable r && native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_concat, native_re_concat, native_re_nullable]


private theorem nativeListInRe_mk_concat_empty_right
    (xs : List native_Char) (r : SmtRegLan) :
    nativeListInRe xs (native_re_mk_concat r SmtRegLan.empty) = false := by
  cases r <;>
    simp [native_re_mk_concat, native_re_concat, nativeListInRe_empty]


private theorem nativeListInRe_mk_concat_epsilon_right
    (xs : List native_Char) (r : SmtRegLan) :
    nativeListInRe xs (native_re_mk_concat r SmtRegLan.epsilon) =
      nativeListInRe xs r := by
  cases r <;>
    simp [native_re_mk_concat, native_re_concat, nativeListInRe_empty]

private theorem native_re_mk_concat_eq_concat_of_ne
    (r s : SmtRegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ SmtRegLan.epsilon ->
    s ≠ SmtRegLan.epsilon ->
    native_re_mk_concat r s = SmtRegLan.concat r s := by
  intro hrEmpty hsEmpty hrEps hsEps
  cases r <;> cases s <;>
    simp [native_re_mk_concat, native_re_concat] at
      hrEmpty hsEmpty hrEps hsEps ⊢

private theorem nativeListInRe_deriv_mk_concat
    (xs : List native_Char) (c : native_Char) (r s : SmtRegLan) :
    nativeListInRe xs (native_re_deriv c (native_re_mk_concat r s)) =
      nativeListInRe xs
        (native_re_mk_union
          (native_re_mk_concat (native_re_deriv c r) s)
          (if native_re_nullable r then native_re_deriv c s else SmtRegLan.empty)) := by
  by_cases hrEmpty : r = SmtRegLan.empty
  · subst r
    simp [native_re_mk_concat, native_re_concat, native_re_deriv,
      native_re_nullable,
      nativeListInRe_mk_union, nativeListInRe_empty]
  ·
    by_cases hsEmpty : s = SmtRegLan.empty
    · subst s
      have hL :
          nativeListInRe xs
            (native_re_deriv c (native_re_mk_concat r SmtRegLan.empty)) =
            false := by
        simp [native_re_mk_concat, native_re_concat, native_re_deriv,
          nativeListInRe_empty]
      rw [hL]
      rw [nativeListInRe_mk_union]
      rw [nativeListInRe_mk_concat_empty_right]
      simp [native_re_deriv, nativeListInRe_empty]
    ·
      by_cases hrEps : r = SmtRegLan.epsilon
      · subst r
        simp [native_re_mk_concat, native_re_concat, native_re_deriv,
          native_re_nullable,
          nativeListInRe_mk_union, nativeListInRe_empty]
      ·
        by_cases hsEps : s = SmtRegLan.epsilon
        · subst s
          have hMk : native_re_mk_concat r SmtRegLan.epsilon = r := by
            cases r <;>
              simp [native_re_mk_concat, native_re_concat] at hrEmpty hrEps ⊢
          rw [hMk]
          rw [nativeListInRe_mk_union]
          rw [nativeListInRe_mk_concat_epsilon_right]
          simp [native_re_deriv, nativeListInRe_empty]
        · have hMk :=
            native_re_mk_concat_eq_concat_of_ne r s hrEmpty hsEmpty hrEps hsEps
          rw [hMk]
          simp [native_re_deriv, nativeListInRe_mk_union]

private def nativeListInReConcat :
    List native_Char -> SmtRegLan -> SmtRegLan -> native_Bool
  | [], r, s => native_re_nullable r && native_re_nullable s
  | c :: cs, r, s =>
      (native_re_nullable r && nativeListInRe (c :: cs) s) ||
        nativeListInReConcat cs (native_re_deriv c r) s

private theorem nativeListInRe_mk_concat :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      nativeListInRe xs (native_re_mk_concat r s) =
        nativeListInReConcat xs r s
  | [], r, s => by
      simp [nativeListInRe, nativeListInReConcat,
        native_re_nullable_mk_concat]
  | c :: cs, r, s => by
      change
        nativeListInRe cs
            (native_re_deriv c (native_re_mk_concat r s)) =
          ((native_re_nullable r &&
              nativeListInRe cs (native_re_deriv c s)) ||
            nativeListInReConcat cs (native_re_deriv c r) s)
      rw [nativeListInRe_deriv_mk_concat cs c r s]
      rw [nativeListInRe_mk_union]
      rw [nativeListInRe_mk_concat cs (native_re_deriv c r) s]
      cases hNullable : native_re_nullable r <;>
        simp [nativeListInRe_empty, Bool.or_comm]

private theorem nativeListInReConcat_true_iff_exists_append :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      nativeListInReConcat xs r s = true ↔
        ∃ xs₁ xs₂ : List native_Char,
          xs₁ ++ xs₂ = xs ∧
            nativeListInRe xs₁ r = true ∧
            nativeListInRe xs₂ s = true
  | [], r, s => by
      constructor
      · intro h
        simp [nativeListInReConcat, Bool.and_eq_true] at h
        exact ⟨[], [], by rfl, by simpa [nativeListInRe] using h.1,
          by simpa [nativeListInRe] using h.2⟩
      · intro h
        rcases h with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        cases xs₁ with
        | nil =>
            cases xs₂ with
            | nil =>
                simp [nativeListInReConcat, nativeListInRe] at hLeft hRight ⊢
                simp [hLeft, hRight]
            | cons _ _ =>
                simp at hAppend
        | cons _ _ =>
            simp at hAppend
  | c :: cs, r, s => by
      constructor
      · intro h
        simp [nativeListInReConcat, Bool.or_eq_true, Bool.and_eq_true] at h
        rcases h with hHead | hTail
        · exact ⟨[], c :: cs, by rfl,
            by simpa [nativeListInRe] using hHead.1, hHead.2⟩
        · have hTailExists :=
            (nativeListInReConcat_true_iff_exists_append cs
              (native_re_deriv c r) s).1 hTail
          rcases hTailExists with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
          exact ⟨c :: xs₁, xs₂, by simp [hAppend],
            by simpa [nativeListInRe] using hLeft, hRight⟩
      · intro h
        rcases h with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        cases xs₁ with
        | nil =>
            cases xs₂ with
            | nil =>
                simp at hAppend
            | cons _ _ =>
                cases hAppend
                have hNullable : native_re_nullable r = true := by
                  simpa [nativeListInRe] using hLeft
                simp [nativeListInReConcat, hNullable, hRight]
        | cons _ ds =>
            cases hAppend
            have hLeftDeriv :
                nativeListInRe ds (native_re_deriv c r) = true := by
              simpa [nativeListInRe] using hLeft
            have hTail :
                nativeListInReConcat (ds ++ xs₂) (native_re_deriv c r) s =
                  true :=
              (nativeListInReConcat_true_iff_exists_append (ds ++ xs₂)
                (native_re_deriv c r) s).2
                ⟨ds, xs₂, by rfl, hLeftDeriv, hRight⟩
            simp [nativeListInReConcat, hTail]

private theorem nativeListInRe_mk_concat_true_iff_exists_append
    (xs : List native_Char) (r s : SmtRegLan) :
    nativeListInRe xs (native_re_mk_concat r s) = true ↔
      ∃ xs₁ xs₂ : List native_Char,
        xs₁ ++ xs₂ = xs ∧
          nativeListInRe xs₁ r = true ∧
          nativeListInRe xs₂ s = true := by
  rw [nativeListInRe_mk_concat xs r s]
  exact nativeListInReConcat_true_iff_exists_append xs r s

-/

private theorem nativeListInRe_empty
    (xs : List native_Char) :
    nativeListInRe xs SmtRegLan.empty = false :=
  RuleProofs.nativeListInRe_empty xs

private theorem nativeListInRe_mk_union
    (xs : List native_Char) (r s : SmtRegLan) :
    nativeListInRe xs (native_re_mk_union r s) =
      (nativeListInRe xs r || nativeListInRe xs s) :=
  RuleProofs.nativeListInRe_mk_union xs r s

private theorem nativeListInRe_mk_inter
    (xs : List native_Char) (r s : SmtRegLan) :
    nativeListInRe xs (native_re_mk_inter r s) =
      (nativeListInRe xs r && nativeListInRe xs s) :=
  RuleProofs.nativeListInRe_mk_inter xs r s

private theorem nativeListInRe_mk_concat_true_iff_exists_append
    (xs : List native_Char) (r s : SmtRegLan) :
    nativeListInRe xs (native_re_mk_concat r s) = true ↔
      ∃ xs₁ xs₂ : List native_Char,
        xs₁ ++ xs₂ = xs ∧
          nativeListInRe xs₁ r = true ∧
          nativeListInRe xs₂ s = true :=
  RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append xs r s

private theorem native_str_in_re_mk_union
    (str : native_String) (r s : SmtRegLan) :
    native_str_in_re str (native_re_mk_union r s) =
      (native_str_in_re str r || native_str_in_re str s) := by
  by_cases hValid : native_string_valid str = true
  · simpa [RuleProofs.native_str_in_re, hValid, nativeListInRe] using
      nativeListInRe_mk_union str r s
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [RuleProofs.native_str_in_re, hInvalid]

private theorem native_str_in_re_mk_inter
    (str : native_String) (r s : SmtRegLan) :
    native_str_in_re str (native_re_mk_inter r s) =
      (native_str_in_re str r && native_str_in_re str s) := by
  by_cases hValid : native_string_valid str = true
  · simpa [RuleProofs.native_str_in_re, hValid, nativeListInRe] using
      nativeListInRe_mk_inter str r s
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [RuleProofs.native_str_in_re, hInvalid]

private theorem native_str_in_re_union_true
    {str : native_String} {r s : SmtRegLan}
    (h : native_str_in_re str (native_re_union r s) = true) :
    native_str_in_re str r = true ∨ native_str_in_re str s = true := by
  rw [native_str_in_re_mk_union] at h
  simpa [Bool.or_eq_true] using h

private theorem native_str_in_re_inter_true
    {str : native_String} {r s : SmtRegLan}
    (h : native_str_in_re str (native_re_inter r s) = true) :
    native_str_in_re str r = true ∧ native_str_in_re str s = true := by
  rw [native_str_in_re_mk_inter] at h
  simpa [Bool.and_eq_true] using h

private theorem native_string_valid_of_str_in_re_true
    {str : native_String} {r : SmtRegLan}
    (h : native_str_in_re str r = true) :
    native_string_valid str = true := by
  by_cases hValid : native_string_valid str = true
  · exact hValid
  · have hInvalid : native_string_valid str = false := by
      cases hv : native_string_valid str <;> simp [hv] at hValid ⊢
    simp [RuleProofs.native_str_in_re, hInvalid] at h

private theorem nativeListInRe_of_str_in_re_true
    {str : native_String} {r : SmtRegLan}
    (h : native_str_in_re str r = true) :
    nativeListInRe str r = true := by
  have hValid := native_string_valid_of_str_in_re_true h
  simpa [RuleProofs.native_str_in_re, hValid, nativeListInRe] using h

private theorem native_str_in_re_true_of_valid_list
    {str : native_String} {r : SmtRegLan}
    (hValid : native_string_valid str = true)
    (hList : nativeListInRe str r = true) :
    native_str_in_re str r = true := by
  simpa [RuleProofs.native_str_in_re, hValid, nativeListInRe] using hList

private theorem native_string_valid_left_of_append_valid
    {xs ys : native_String}
    (hValid : native_string_valid (xs ++ ys) = true) :
    native_string_valid xs = true := by
  simp [native_string_valid] at hValid
  simpa [native_string_valid] using hValid.1

private theorem native_string_valid_right_of_append_valid
    {xs ys : native_String}
    (hValid : native_string_valid (xs ++ ys) = true) :
    native_string_valid ys = true := by
  simp [native_string_valid] at hValid
  simpa [native_string_valid] using hValid.2

private theorem native_str_in_re_concat_true
    {str : native_String} {r s : SmtRegLan}
    (h : native_str_in_re str (native_re_concat r s) = true) :
    ∃ xs ys : native_String,
      xs ++ ys = str ∧
        native_str_in_re xs r = true ∧
        native_str_in_re ys s = true := by
  have hValid := native_string_valid_of_str_in_re_true h
  have hList :
      nativeListInRe str (native_re_mk_concat r s) = true := by
    exact nativeListInRe_of_str_in_re_true h
  rcases (nativeListInRe_mk_concat_true_iff_exists_append str r s).1 hList with
    ⟨xs, ys, hAppend, hLeft, hRight⟩
  have hAppendValid : native_string_valid (xs ++ ys) = true := by
    rw [hAppend]
    exact hValid
  have hXsValid := native_string_valid_left_of_append_valid hAppendValid
  have hYsValid := native_string_valid_right_of_append_valid hAppendValid
  exact ⟨xs, ys, hAppend,
    native_str_in_re_true_of_valid_list hXsValid hLeft,
    native_str_in_re_true_of_valid_list hYsValid hRight⟩

private theorem native_str_in_re_empty_false (str : native_String) :
    native_str_in_re str SmtRegLan.empty = false := by
  by_cases hValid : native_string_valid str = true
  · simpa [RuleProofs.native_str_in_re, hValid, nativeListInRe] using
      nativeListInRe_empty str
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [RuleProofs.native_str_in_re, hInvalid]

private theorem native_re_nullable_fold_empty_false (xs : List native_Char) :
    native_re_nullable
        (xs.foldl (fun acc c => native_re_deriv c acc) SmtRegLan.empty) =
      false := by
  rw [← RuleProofs.nativeListInRe_eq_model_fold]
  exact nativeListInRe_empty xs

private theorem native_str_in_re_epsilon_length
    {str : native_String}
    (h : native_str_in_re str SmtRegLan.epsilon = true) :
    str.length = 0 := by
  cases str with
  | nil => rfl
  | cons c cs =>
      have hList := nativeListInRe_of_str_in_re_true h
      change nativeListInRe cs SmtRegLan.empty = true at hList
      rw [nativeListInRe_empty] at hList
      simp at hList

private theorem native_str_in_re_char_length
    {str : native_String} {c : SmtValue}
    (h : native_str_in_re str (SmtRegLan.char c) = true) :
    str.length = 1 := by
  cases str with
  | nil =>
      have hList := nativeListInRe_of_str_in_re_true h
      simp [RuleProofs.nativeListInRe, native_re_nullable] at hList
  | cons d ds =>
      cases ds with
      | nil => rfl
      | cons e es =>
          have hList := nativeListInRe_of_str_in_re_true h
          simp only [RuleProofs.nativeListInRe, native_re_deriv] at hList
          split at hList <;>
            simp [native_re_deriv,
              nativeListInRe_empty] at hList

private theorem native_str_in_re_range_atom_length
    {str : native_String} {lo hi : SmtValue}
    (h : native_str_in_re str (SmtRegLan.range lo hi) = true) :
    str.length = 1 := by
  cases str with
  | nil =>
      have hList := nativeListInRe_of_str_in_re_true h
      simp [RuleProofs.nativeListInRe, native_re_nullable] at hList
  | cons d ds =>
      cases ds with
      | nil => rfl
      | cons e es =>
          have hList := nativeListInRe_of_str_in_re_true h
          simp only [RuleProofs.nativeListInRe, native_re_deriv] at hList
          split at hList <;>
            simp [native_re_deriv,
              nativeListInRe_empty] at hList

private theorem native_str_in_re_allchar_length
    {str : native_String}
    (h : native_str_in_re str native_re_allchar = true) :
    str.length = 1 := by
  cases str with
  | nil =>
      have hList := nativeListInRe_of_str_in_re_true h
      simp [native_re_allchar, RuleProofs.nativeListInRe,
        native_re_nullable] at hList
  | cons d ds =>
      cases ds with
      | nil => rfl
      | cons e es =>
          have hList := nativeListInRe_of_str_in_re_true h
          simp only [native_re_allchar, RuleProofs.nativeListInRe,
            native_re_deriv] at hList
          split at hList <;>
            simp [native_re_deriv,
              nativeListInRe_empty] at hList

private theorem native_str_in_re_range_length
    {str : native_String} {lo hi : List SmtValue}
    (h : native_str_in_re str (native_re_range lo hi) = true) :
    str.length = 1 := by
  cases lo with
  | nil =>
      simp [native_re_range, native_str_in_re_empty_false] at h
  | cons lo0 los =>
      cases los with
      | nil =>
          cases hi with
          | nil =>
              simp [native_re_range, native_str_in_re_empty_false] at h
          | cons hi0 his =>
              cases his with
              | nil =>
                  exact native_str_in_re_range_atom_length h
              | cons _ _ =>
                  simp [native_re_range, native_str_in_re_empty_false] at h
      | cons _ _ =>
          simp [native_re_range, native_str_in_re_empty_false] at h

private theorem native_str_in_re_re_of_list_length :
    (pat : List SmtValue) -> {str : native_String} ->
      native_str_in_re str (impl_native_re_of_list pat) = true ->
      str.length = pat.length
  | [], str, h => by
      exact native_str_in_re_epsilon_length h
  | c :: cs, str, h => by
      rcases native_str_in_re_concat_true
          (r := SmtRegLan.char c) (s := impl_native_re_of_list cs)
          (by simpa [native_re_concat, impl_native_re_of_list] using h) with
        ⟨s1, s2, hAppend, hLeft, hRight⟩
      have hLeftLen := native_str_in_re_char_length hLeft
      have hRightLen := native_str_in_re_re_of_list_length cs hRight
      rw [← hAppend]
      simp [hLeftLen, hRightLen]
      omega

private theorem native_str_in_re_str_to_re_length
    {str : native_String} {pat : List SmtValue}
    (h : native_str_in_re str (native_str_to_re pat) = true) :
    str.length = pat.length := by
  simpa [native_str_to_re] using native_str_in_re_re_of_list_length pat h

private theorem model_eval_re_concat_reglan
    (M : SmtModel) (t1 t2 : SmtTerm) {rr : SmtRegLan}
    (h :
      __smtx_model_eval M (SmtTerm.re_concat t1 t2) =
        SmtValue.RegLan rr) :
    ∃ r1 r2 : SmtRegLan,
      __smtx_model_eval M t1 = SmtValue.RegLan r1 ∧
        __smtx_model_eval M t2 = SmtValue.RegLan r2 ∧
        rr = native_re_concat r1 r2 := by
  cases h1 : __smtx_model_eval M t1 <;>
    cases h2 : __smtx_model_eval M t2 <;>
    simp [__smtx_model_eval, __smtx_model_eval_re_concat, h1, h2] at h
  case RegLan.RegLan r1 r2 =>
    cases h
    exact ⟨r1, r2, rfl, rfl, rfl⟩

private theorem model_eval_re_union_reglan
    (M : SmtModel) (t1 t2 : SmtTerm) {rr : SmtRegLan}
    (h :
      __smtx_model_eval M (SmtTerm.re_union t1 t2) =
        SmtValue.RegLan rr) :
    ∃ r1 r2 : SmtRegLan,
      __smtx_model_eval M t1 = SmtValue.RegLan r1 ∧
        __smtx_model_eval M t2 = SmtValue.RegLan r2 ∧
        rr = native_re_union r1 r2 := by
  cases h1 : __smtx_model_eval M t1 <;>
    cases h2 : __smtx_model_eval M t2 <;>
    simp [__smtx_model_eval, __smtx_model_eval_re_union, h1, h2] at h
  case RegLan.RegLan r1 r2 =>
    cases h
    exact ⟨r1, r2, rfl, rfl, rfl⟩

private theorem model_eval_re_inter_reglan
    (M : SmtModel) (t1 t2 : SmtTerm) {rr : SmtRegLan}
    (h :
      __smtx_model_eval M (SmtTerm.re_inter t1 t2) =
        SmtValue.RegLan rr) :
    ∃ r1 r2 : SmtRegLan,
      __smtx_model_eval M t1 = SmtValue.RegLan r1 ∧
        __smtx_model_eval M t2 = SmtValue.RegLan r2 ∧
        rr = native_re_inter r1 r2 := by
  cases h1 : __smtx_model_eval M t1 <;>
    cases h2 : __smtx_model_eval M t2 <;>
    simp [__smtx_model_eval, __smtx_model_eval_re_inter, h1, h2] at h
  case RegLan.RegLan r1 r2 =>
    cases h
    exact ⟨r1, r2, rfl, rfl, rfl⟩

private theorem model_eval_re_range_reglan
    (M : SmtModel) (t1 t2 : SmtTerm) {rr : SmtRegLan}
    (h :
      __smtx_model_eval M (SmtTerm.re_range t1 t2) =
        SmtValue.RegLan rr) :
    ∃ s1 s2 : SmtSeq,
      __smtx_model_eval M t1 = SmtValue.Seq s1 ∧
        __smtx_model_eval M t2 = SmtValue.Seq s2 ∧
        rr = native_re_range (native_unpack_seq s1) (native_unpack_seq s2) := by
  cases h1 : __smtx_model_eval M t1 <;>
    cases h2 : __smtx_model_eval M t2 <;>
    simp [__smtx_model_eval, __smtx_model_eval_re_range, h1, h2] at h
  case Seq.Seq s1 s2 =>
    cases h
    exact ⟨s1, s2, rfl, rfl, rfl⟩


private theorem eo_add_numeral_or_stuck
    (a b : Term)
    (ha : (∃ n : native_Int, a = Term.Numeral n) ∨ a = Term.Stuck)
    (hb : (∃ n : native_Int, b = Term.Numeral n) ∨ b = Term.Stuck) :
    (∃ n : native_Int, __eo_add a b = Term.Numeral n) ∨
      __eo_add a b = Term.Stuck := by
  rcases ha with ⟨n0, rfl⟩ | rfl
  · rcases hb with ⟨n1, rfl⟩ | rfl
    · left
      exact ⟨native_zplus n0 n1, rfl⟩
    · right
      rfl
  · right
    rfl

private theorem eo_requires_same_numeral_or_stuck
    (a b : Term)
    (ha : (∃ n : native_Int, a = Term.Numeral n) ∨ a = Term.Stuck)
    (hb : (∃ n : native_Int, b = Term.Numeral n) ∨ b = Term.Stuck) :
    (∃ n : native_Int, __eo_requires a b b = Term.Numeral n) ∨
      __eo_requires a b b = Term.Stuck := by
  rcases hb with ⟨nb, rfl⟩ | rfl
  · rcases ha with ⟨na, rfl⟩ | rfl
    · by_cases hEq : na = nb
      · subst na
        left
        exact ⟨nb, by
          simp [__eo_requires, native_teq, native_ite, native_not]⟩
      · right
        simp [__eo_requires, native_teq, native_ite, hEq]
    · right
      simp [__eo_requires, native_teq, native_ite]
  · right
    cases a <;> simp [__eo_requires, native_teq, native_ite, native_not]

private theorem eo_ite_numeral_or_stuck
    (c a b : Term)
    (ha : (∃ n : native_Int, a = Term.Numeral n) ∨ a = Term.Stuck)
    (hb : (∃ n : native_Int, b = Term.Numeral n) ∨ b = Term.Stuck) :
    (∃ n : native_Int, __eo_ite c a b = Term.Numeral n) ∨
      __eo_ite c a b = Term.Stuck := by
  unfold __eo_ite
  cases hTrue : native_teq c (Term.Boolean true)
  · cases hFalse : native_teq c (Term.Boolean false)
    · right
      simp [native_ite]
    · simpa [native_ite, hTrue, hFalse] using hb
  · simpa [native_ite, hTrue] using ha

private theorem eo_requires_stuck_stuck (a : Term) :
    __eo_requires a Term.Stuck Term.Stuck = Term.Stuck := by
  cases a <;> simp [__eo_requires, native_teq, native_ite, native_not]

private theorem eo_ite_stuck_stuck (c : Term) :
    __eo_ite c Term.Stuck Term.Stuck = Term.Stuck := by
  unfold __eo_ite
  cases native_teq c (Term.Boolean true) <;>
    cases native_teq c (Term.Boolean false) <;>
    simp [native_ite]

theorem str_fixed_len_re_numeral_or_stuck :
    (r : Term) ->
      (∃ n : native_Int, __str_fixed_len_re r = Term.Numeral n) ∨
        __str_fixed_len_re r = Term.Stuck
  | Term.UOp op => by
      cases op <;> simp [__str_fixed_len_re]
  | Term.UOp1 _ _ => by right; rfl
  | Term.UOp2 _ _ _ => by right; rfl
  | Term.UOp3 _ _ _ _ => by right; rfl
  | Term.__eo_List => by right; rfl
  | Term.__eo_List_nil => by right; rfl
  | Term.__eo_List_cons => by right; rfl
  | Term.Bool => by right; rfl
  | Term.Boolean _ => by right; rfl
  | Term.Numeral _ => by right; rfl
  | Term.Rational _ => by right; rfl
  | Term.String _ => by right; rfl
  | Term.Binary _ _ => by right; rfl
  | Term.Type => by right; rfl
  | Term.Stuck => by right; rfl
  | Term.Apply f x => by
      cases f
      case UOp op =>
        cases op <;> simp [__str_fixed_len_re, __eo_len]
        case str_to_re =>
          cases x <;> simp
      case Apply g y =>
        cases g
        case UOp op =>
          cases op <;> simp [__str_fixed_len_re]
          case re_concat =>
            exact eo_add_numeral_or_stuck
              (__str_fixed_len_re y) (__str_fixed_len_re x)
              (str_fixed_len_re_numeral_or_stuck y)
              (str_fixed_len_re_numeral_or_stuck x)
          case re_union =>
            exact eo_ite_numeral_or_stuck
              (__eo_eq x (Term.UOp UserOp.re_none))
              (__str_fixed_len_re y)
              (__eo_requires (__str_fixed_len_re x) (__str_fixed_len_re y)
                (__str_fixed_len_re y))
              (str_fixed_len_re_numeral_or_stuck y)
              (eo_requires_same_numeral_or_stuck
                (__str_fixed_len_re x) (__str_fixed_len_re y)
                (str_fixed_len_re_numeral_or_stuck x)
                (str_fixed_len_re_numeral_or_stuck y))
          case re_inter =>
            exact eo_ite_numeral_or_stuck
              (__eo_eq x (Term.UOp UserOp.re_all))
              (__str_fixed_len_re y)
              (__eo_requires (__str_fixed_len_re x) (__str_fixed_len_re y)
                (__str_fixed_len_re y))
              (str_fixed_len_re_numeral_or_stuck y)
              (eo_requires_same_numeral_or_stuck
                (__str_fixed_len_re x) (__str_fixed_len_re y)
                (str_fixed_len_re_numeral_or_stuck x)
                (str_fixed_len_re_numeral_or_stuck y))
        all_goals
          right
          rfl
      all_goals
        right
        rfl
  | Term.FunType => by right; rfl
  | Term.Var _ _ => by right; rfl
  | Term.DatatypeType _ _ => by right; rfl
  | Term.DatatypeTypeRef _ => by right; rfl
  | Term.DtcAppType _ _ => by right; rfl
  | Term.DtCons _ _ _ => by right; rfl
  | Term.DtSel _ _ _ _ => by right; rfl
  | Term.USort _ => by right; rfl
  | Term.UConst _ _ => by right; rfl
termination_by r => sizeOf r

theorem str_fixed_len_re_numeral_of_ne_stuck
    (r : Term)
    (h : __str_fixed_len_re r ≠ Term.Stuck) :
    ∃ n : native_Int, __str_fixed_len_re r = Term.Numeral n := by
  rcases str_fixed_len_re_numeral_or_stuck r with hNum | hStuck
  · exact hNum
  · exact False.elim (h hStuck)

theorem str_fixed_len_re_sound (M : SmtModel) :
    (r : Term) -> (str : native_String) -> (rr : SmtRegLan) ->
      (n : native_Int) ->
      __str_fixed_len_re r = Term.Numeral n ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rr ->
      native_str_in_re str rr = true ->
      Int.ofNat str.length = n
  | Term.UOp op, str, rr, n, hFixed, hEval, hIn => by
      cases op <;> simp [__str_fixed_len_re] at hFixed
      case re_allchar =>
        cases hFixed
        simp [__smtx_model_eval] at hEval
        cases hEval
        have hLen := native_str_in_re_allchar_length hIn
        simp [hLen]
  | Term.UOp1 _ _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.UOp2 _ _ _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.UOp3 _ _ _ _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.__eo_List, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.__eo_List_nil, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.__eo_List_cons, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.Bool, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.Boolean _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.Numeral _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.Rational _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.String _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.Binary _ _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.Type, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.Stuck, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.Apply f x, str, rr, n, hFixed, hEval, hIn => by
      cases f
      case UOp op =>
        cases op <;> simp [__str_fixed_len_re, __eo_len] at hFixed
        case str_to_re =>
          cases x <;> simp  at hFixed
          case String pat =>
            cases hFixed
            change
              __smtx_model_eval M
                  (SmtTerm.str_to_re (SmtTerm.String pat)) =
                SmtValue.RegLan rr at hEval
            simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
              ] at hEval
            cases hEval
            have hLen := native_str_in_re_str_to_re_length hIn
            simp [native_str_len, hLen, native_pack_string,
              Smtm.native_unpack_pack_seq]
          case Binary =>
            cases hFixed
            change
              __smtx_model_eval M
                  (SmtTerm.str_to_re (SmtTerm.Binary _ _)) =
                SmtValue.RegLan rr at hEval
            simp [__smtx_model_eval, __smtx_model_eval_str_to_re] at hEval
      case Apply g y =>
        cases g
        case UOp op =>
          cases op <;> simp [__str_fixed_len_re] at hFixed
          case re_concat =>
            rcases str_fixed_len_re_numeral_or_stuck y with
              ⟨n0, h0⟩ | h0
            · rcases str_fixed_len_re_numeral_or_stuck x with
                ⟨n1, h1⟩ | h1
              · have hSum : native_zplus n0 n1 = n := by
                  simpa [__str_fixed_len_re, h0, h1, __eo_add] using hFixed
                rcases model_eval_re_concat_reglan M (__eo_to_smt y)
                    (__eo_to_smt x) hEval with
                  ⟨rr0, rr1, hEval0, hEval1, rfl⟩
                rcases native_str_in_re_concat_true hIn with
                  ⟨s0, s1, hAppend, hIn0, hIn1⟩
                have hLen0 :=
                  str_fixed_len_re_sound M y s0 rr0 n0 h0 hEval0 hIn0
                have hLen1 :=
                  str_fixed_len_re_sound M x s1 rr1 n1 h1 hEval1 hIn1
                rw [← hAppend]
                calc
                  Int.ofNat (s0 ++ s1).length =
                      Int.ofNat s0.length + Int.ofNat s1.length := by simp
                  _ = n0 + n1 := by rw [hLen0, hLen1]
                  _ = n := by simpa [native_zplus] using hSum
              · simp [h0, h1, __eo_add] at hFixed
            · simp [h0, __eo_add] at hFixed
          case re_range =>
            cases hFixed
            rcases model_eval_re_range_reglan M (__eo_to_smt y)
                (__eo_to_smt x) hEval with
              ⟨_slo, _shi, _hLoEval, _hHiEval, rfl⟩
            have hLen := native_str_in_re_range_length hIn
            simp [hLen]
          case re_union =>
            rcases str_fixed_len_re_numeral_or_stuck y with
              ⟨n0, h0⟩ | h0
            ·
              by_cases hNone : (x = Term.UOp UserOp.re_none)
              · subst x
                have hn : n0 = n := by
                  simpa [__str_fixed_len_re, h0, __eo_eq, __eo_ite,
                    native_teq, native_ite] using hFixed
                subst n
                rcases model_eval_re_union_reglan M (__eo_to_smt y)
                    SmtTerm.re_none hEval with
                  ⟨rr0, rr1, hEval0, hEval1, hRr⟩
                have hR1 : rr1 = native_re_none := by
                  simpa [__smtx_model_eval, native_re_none] using hEval1.symm
                subst rr1
                rw [hRr] at hIn
                rcases native_str_in_re_union_true hIn with hIn0 | hIn1
                · exact str_fixed_len_re_sound M y str rr0 n0 h0 hEval0 hIn0
                · rw [native_re_none, native_str_in_re_empty_false] at hIn1
                  cases hIn1
              ·
                by_cases hStuck : x = Term.Stuck
                · subst x
                  simp [__eo_eq, __eo_ite,
                    native_teq, native_ite] at hFixed
                · have hNone' : ¬ Term.UOp UserOp.re_none = x := by
                    intro h
                    exact hNone h.symm
                  rcases str_fixed_len_re_numeral_or_stuck x with
                    ⟨n1, h1⟩ | h1
                  ·
                    by_cases hLenEq : n1 = n0
                    · subst n1
                      have hn : n0 = n := by
                        simpa [__str_fixed_len_re, h0, h1, __eo_eq,
                          __eo_ite, __eo_requires, native_teq, native_ite,
                          native_not, hNone, hNone', hStuck] using hFixed
                      subst n
                      rcases model_eval_re_union_reglan M (__eo_to_smt y)
                          (__eo_to_smt x) hEval with
                        ⟨rr0, rr1, hEval0, hEval1, rfl⟩
                      rcases native_str_in_re_union_true hIn with hIn0 | hIn1
                      · exact str_fixed_len_re_sound M y str rr0 n0 h0 hEval0 hIn0
                      · exact str_fixed_len_re_sound M x str rr1 n0 h1 hEval1 hIn1
                    · simp [h0, h1, __eo_eq, __eo_ite,
                        __eo_requires, native_teq, native_ite, hNone', hLenEq] at hFixed
                  · simp [h0, h1, __eo_eq, __eo_ite,
                      __eo_requires, native_teq, native_ite, hNone'] at hFixed
            · simp [h0, eo_requires_stuck_stuck, eo_ite_stuck_stuck] at hFixed
          case re_inter =>
            rcases str_fixed_len_re_numeral_or_stuck y with
              ⟨n0, h0⟩ | h0
            ·
              by_cases hAll : (x = Term.UOp UserOp.re_all)
              · subst x
                have hn : n0 = n := by
                  simpa [__str_fixed_len_re, h0, __eo_eq, __eo_ite,
                    native_teq, native_ite] using hFixed
                subst n
                rcases model_eval_re_inter_reglan M (__eo_to_smt y)
                    SmtTerm.re_all hEval with
                  ⟨rr0, rr1, hEval0, hEval1, hRr⟩
                have hR1 : rr1 = native_re_all := by
                  simpa [__smtx_model_eval, native_re_all] using hEval1.symm
                subst rr1
                rw [hRr] at hIn
                have hIn0 := (native_str_in_re_inter_true hIn).1
                exact str_fixed_len_re_sound M y str rr0 n0 h0 hEval0 hIn0
              ·
                by_cases hStuck : x = Term.Stuck
                · subst x
                  simp [__eo_eq, __eo_ite,
                    native_teq, native_ite] at hFixed
                · have hAll' : ¬ Term.UOp UserOp.re_all = x := by
                    intro h
                    exact hAll h.symm
                  rcases str_fixed_len_re_numeral_or_stuck x with
                    ⟨n1, h1⟩ | h1
                  ·
                    by_cases hLenEq : n1 = n0
                    · subst n1
                      have hn : n0 = n := by
                        simpa [__str_fixed_len_re, h0, h1, __eo_eq,
                          __eo_ite, __eo_requires, native_teq, native_ite,
                          native_not, hAll, hAll', hStuck] using hFixed
                      subst n
                      rcases model_eval_re_inter_reglan M (__eo_to_smt y)
                          (__eo_to_smt x) hEval with
                        ⟨rr0, rr1, hEval0, _hEval1, rfl⟩
                      have hIn0 := (native_str_in_re_inter_true hIn).1
                      exact str_fixed_len_re_sound M y str rr0 n0 h0 hEval0 hIn0
                    · simp [h0, h1, __eo_eq, __eo_ite,
                        __eo_requires, native_teq, native_ite, hAll', hLenEq] at hFixed
                  · simp [h0, h1, __eo_eq, __eo_ite,
                      __eo_requires, native_teq, native_ite, hAll'] at hFixed
            · simp [h0, eo_requires_stuck_stuck, eo_ite_stuck_stuck] at hFixed
        all_goals simp [__str_fixed_len_re] at hFixed
      all_goals simp [__str_fixed_len_re] at hFixed
  | Term.FunType, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.Var _ _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.DatatypeType _ _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.DatatypeTypeRef _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.DtcAppType _ _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.DtCons _ _ _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.DtSel _ _ _ _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.USort _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.UConst _ _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
termination_by r _ _ _ _ _ _ => sizeOf r

theorem string_eager_reduction_has_bool_type
    (a : Term)
    (hATrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof (__eo_prog_string_eager_reduction a) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_string_eager_reduction a) := by
  cases a <;> simp [__eo_prog_string_eager_reduction, __mk_str_eager_reduction] at hTy ⊢
  all_goals try cases hTy
  case Apply f x =>
    cases f <;> try simp  at hTy ⊢
    all_goals try cases hTy
    case UOp op =>
      cases op <;> try simp  at hTy ⊢
      all_goals try cases hTy
      case str_to_code =>
        apply RuleProofs.eo_typeof_bool_implies_has_bool_type
        · unfold RuleProofs.eo_has_smt_translation at hATrans ⊢
          have hsTy :
              __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
            seq_char_arg_of_non_none (op := SmtTerm.str_to_code)
              (typeof_str_to_code_eq (__eo_to_smt x))
              (by simpa [term_has_non_none_type, __eo_to_smt, __smtx_typeof] using hATrans)
          change
            __smtx_typeof
              (SmtTerm.ite
                (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x)) (SmtTerm.Numeral 1))
                (SmtTerm.and
                  (SmtTerm.geq (SmtTerm.str_to_code (__eo_to_smt x)) (SmtTerm.Numeral 0))
                  (SmtTerm.and
                    (SmtTerm.lt (SmtTerm.str_to_code (__eo_to_smt x))
                      (SmtTerm.Numeral 196608))
                    (SmtTerm.Boolean true)))
                (SmtTerm.eq (SmtTerm.str_to_code (__eo_to_smt x))
                  (SmtTerm.Numeral (-1 : native_Int)))) ≠ SmtType.None
          simp [hsTy, __smtx_typeof_seq_op_1_ret,
            __smtx_typeof_arith_overload_op_2_ret,
            __smtx_typeof_eq, __smtx_typeof_guard, __smtx_typeof_ite,
            __smtx_typeof, native_ite, native_Teq]
        · simpa [__eo_prog_string_eager_reduction, __mk_str_eager_reduction] using hTy
      case str_from_code =>
        apply RuleProofs.eo_typeof_bool_implies_has_bool_type
        · unfold RuleProofs.eo_has_smt_translation at hATrans ⊢
          have hnTy : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
            int_arg_of_non_none_ret (op := SmtTerm.str_from_code)
              (typeof_str_from_code_eq (__eo_to_smt x))
              (by simpa [term_has_non_none_type, __eo_to_smt, __smtx_typeof] using hATrans)
          change
            __smtx_typeof
              (SmtTerm.ite
                (SmtTerm.and (SmtTerm.leq (SmtTerm.Numeral 0) (__eo_to_smt x))
                  (SmtTerm.and (SmtTerm.lt (__eo_to_smt x) (SmtTerm.Numeral 196608))
                    (SmtTerm.Boolean true)))
                (SmtTerm.eq (__eo_to_smt x)
                  (SmtTerm.str_to_code
                    (SmtTerm._at_purify (SmtTerm.str_from_code (__eo_to_smt x)))))
                (SmtTerm.eq
                  (SmtTerm._at_purify (SmtTerm.str_from_code (__eo_to_smt x)))
                  (SmtTerm.String []))) ≠ SmtType.None
          simp [hnTy, __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq,
            __smtx_typeof_guard, __smtx_typeof_ite, __smtx_typeof,
            native_ite, native_Teq, native_string_valid]
        · simpa [__eo_prog_string_eager_reduction, __mk_str_eager_reduction] using hTy
      case str_to_int =>
        apply RuleProofs.eo_typeof_bool_implies_has_bool_type
        · unfold RuleProofs.eo_has_smt_translation at hATrans ⊢
          have hsTy :
              __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
            seq_char_arg_of_non_none (op := SmtTerm.str_to_int)
              (typeof_str_to_int_eq (__eo_to_smt x))
              (by simpa [term_has_non_none_type, __eo_to_smt, __smtx_typeof] using hATrans)
          change
            __smtx_typeof
                (SmtTerm.geq (SmtTerm.str_to_int (__eo_to_smt x))
                  (SmtTerm.Numeral (-1 : native_Int))) ≠ SmtType.None
          rw [typeof_geq_eq, typeof_str_to_int_eq]
          rw [__smtx_typeof.eq_2]
          simp [hsTy, __smtx_typeof_arith_overload_op_2_ret, native_ite,
            native_Teq]
        · simpa [__eo_prog_string_eager_reduction, __mk_str_eager_reduction] using hTy
    case Apply f y =>
      cases f <;> try simp  at hTy ⊢
      all_goals try cases hTy
      case UOp op =>
        cases op <;> try simp  at hTy ⊢
        all_goals try cases hTy
        case str_contains =>
          apply RuleProofs.eo_typeof_bool_implies_has_bool_type
          · unfold RuleProofs.eo_has_smt_translation at hATrans ⊢
            rcases seq_binop_args_of_non_none_ret (op := SmtTerm.str_contains)
                (R := SmtType.Bool)
                (typeof_str_contains_eq (__eo_to_smt y) (__eo_to_smt x))
                (by simpa [term_has_non_none_type, __eo_to_smt, __smtx_typeof] using hATrans) with
              ⟨T, hyTy, hxTy⟩
            let pre :=
              Term.Apply (Term.UOp UserOp._at_purify)
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_substr) y)
                    (Term.Numeral 0))
                  (Term.Apply
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_indexof) y) x)
                    (Term.Numeral 0)))
            have hPreTy :
                __smtx_typeof (__eo_to_smt pre) = SmtType.Seq T := by
              change
                __smtx_typeof
                  (SmtTerm._at_purify
                    (SmtTerm.str_substr (__eo_to_smt y) (SmtTerm.Numeral 0)
                      (SmtTerm.str_indexof (__eo_to_smt y) (__eo_to_smt x)
                        (SmtTerm.Numeral 0)))) = SmtType.Seq T
              simp [__smtx_typeof, hyTy, hxTy, __smtx_typeof_str_indexof,
                __smtx_typeof_str_substr,
                native_ite, native_Teq]
            have hNilNe :
                __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre) ≠
                  Term.Stuck := by
              exact nil_str_concat_typeof_ne_stuck_of_smt_type_seq pre T hPreTy
            have hNilNe' :
                __eo_nil (Term.UOp UserOp.str_concat)
                    (__eo_typeof
                      (Term.Apply (Term.UOp UserOp._at_purify)
                        (Term.Apply
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_substr) y)
                            (Term.Numeral 0))
                          (Term.Apply
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.str_indexof) y) x)
                            (Term.Numeral 0))))) ≠
                  Term.Stuck := by
              simpa [pre] using hNilNe
            have hNilTy' :
                __smtx_typeof
                    (__eo_to_smt
                      (__eo_nil (Term.UOp UserOp.str_concat)
                        (__eo_typeof
                          (Term.Apply (Term.UOp UserOp._at_purify)
                            (Term.Apply
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp.str_substr) y)
                                (Term.Numeral 0))
                              (Term.Apply
                                (Term.Apply
                                  (Term.Apply (Term.UOp UserOp.str_indexof) y) x)
                                (Term.Numeral 0))))))) =
                  SmtType.Seq T := by
              simpa [pre] using
                smt_typeof_nil_str_concat_typeof_of_smt_type_seq pre T hPreTy
            simp only [__eo_mk_apply]
            change
              __smtx_typeof
                (SmtTerm.ite
                  (SmtTerm.str_contains (__eo_to_smt y) (__eo_to_smt x))
                  (SmtTerm.eq (__eo_to_smt y)
                    (SmtTerm.str_concat
                      (SmtTerm._at_purify
                        (SmtTerm.str_substr (__eo_to_smt y) (SmtTerm.Numeral 0)
                          (SmtTerm.str_indexof (__eo_to_smt y) (__eo_to_smt x)
                            (SmtTerm.Numeral 0))))
                      (SmtTerm.str_concat (__eo_to_smt x)
                        (SmtTerm.str_concat
                          (SmtTerm._at_purify
                            (SmtTerm.str_substr (__eo_to_smt y)
                              (SmtTerm.plus
                                (SmtTerm.str_len
                                  (SmtTerm._at_purify
                                    (SmtTerm.str_substr (__eo_to_smt y)
                                      (SmtTerm.Numeral 0)
                                      (SmtTerm.str_indexof (__eo_to_smt y)
                                        (__eo_to_smt x) (SmtTerm.Numeral 0)))))
                                (SmtTerm.plus (SmtTerm.str_len (__eo_to_smt x))
                                  (SmtTerm.Numeral 0)))
                              (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt y))
                                (SmtTerm.plus
                                  (SmtTerm.str_len
                                    (SmtTerm._at_purify
                                      (SmtTerm.str_substr (__eo_to_smt y)
                                        (SmtTerm.Numeral 0)
                                        (SmtTerm.str_indexof (__eo_to_smt y)
                                          (__eo_to_smt x) (SmtTerm.Numeral 0)))))
                                  (SmtTerm.plus (SmtTerm.str_len (__eo_to_smt x))
                                    (SmtTerm.Numeral 0))))))
                          (__eo_to_smt
                            (__eo_nil (Term.UOp UserOp.str_concat)
                              (__eo_typeof
                                (Term.Apply (Term.UOp UserOp._at_purify)
                                  (Term.Apply
                                    (Term.Apply
                                      (Term.Apply (Term.UOp UserOp.str_substr) y)
                                      (Term.Numeral 0))
                                    (Term.Apply
                                      (Term.Apply
                                        (Term.Apply (Term.UOp UserOp.str_indexof) y)
                                        x)
                                      (Term.Numeral 0)))))))))))
                  (SmtTerm.not (SmtTerm.eq (__eo_to_smt y) (__eo_to_smt x)))) ≠
                SmtType.None
            simp [hyTy, hxTy, __smtx_typeof_str_indexof,
              __smtx_typeof_str_substr,
              __smtx_typeof_seq_op_2, __smtx_typeof_seq_op_2_ret,
              __smtx_typeof_seq_op_1_ret, __smtx_typeof_arith_overload_op_2,
              __smtx_typeof_eq, __smtx_typeof_guard, __smtx_typeof_ite,
              __smtx_typeof, native_ite, native_Teq, hNilTy']
          · simpa [__eo_prog_string_eager_reduction, __mk_str_eager_reduction] using hTy
        case str_in_re =>
          apply RuleProofs.eo_typeof_bool_implies_has_bool_type
          · unfold RuleProofs.eo_has_smt_translation at hATrans ⊢
            have hOrigNN :
                term_has_non_none_type
                  (SmtTerm.str_in_re (__eo_to_smt y) (__eo_to_smt x)) := by
              unfold term_has_non_none_type
              exact hATrans
            have hArgs :=
              seq_char_reglan_args_of_non_none
                (op := SmtTerm.str_in_re)
                (typeof_str_in_re_eq (__eo_to_smt y) (__eo_to_smt x))
                hOrigNN
            have hyTy : __smtx_typeof (__eo_to_smt y) =
                SmtType.Seq SmtType.Char := hArgs.1
            have hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
              hArgs.2
            let fixed := __str_fixed_len_re x
            let rhsEo :=
              __eo_mk_apply
                (Term.Apply (Term.UOp UserOp.eq)
                  (Term.Apply (Term.UOp UserOp.str_len) y))
                fixed
            let gen :=
              __eo_mk_apply
                (Term.Apply (Term.UOp UserOp.imp)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) y) x))
                rhsEo
            have hGenTy : __eo_typeof gen = Term.Bool := by
              simpa [gen, rhsEo, fixed, __eo_prog_string_eager_reduction,
                __mk_str_eager_reduction] using hTy
            have hGenNe : gen ≠ Term.Stuck := by
              intro h
              rw [h] at hGenTy
              change Term.Stuck = Term.Bool at hGenTy
              cases hGenTy
            have hRhsNe : rhsEo ≠ Term.Stuck :=
              eo_mk_apply_arg_ne_stuck_of_ne_stuck
                (Term.Apply (Term.UOp UserOp.imp)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) y) x))
                rhsEo hGenNe
            have hFixedNe : fixed ≠ Term.Stuck :=
              eo_mk_apply_arg_ne_stuck_of_ne_stuck
                (Term.Apply (Term.UOp UserOp.eq)
                  (Term.Apply (Term.UOp UserOp.str_len) y))
                fixed hRhsNe
            rcases str_fixed_len_re_numeral_of_ne_stuck x hFixedNe with
              ⟨n, hFixed⟩
            simp only [__eo_mk_apply, hFixed]
            change
              __smtx_typeof
                  (SmtTerm.imp
                    (SmtTerm.str_in_re (__eo_to_smt y) (__eo_to_smt x))
                    (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt y))
                      (SmtTerm.Numeral n))) ≠
                SmtType.None
            simp [hyTy, hxTy,
              __smtx_typeof_seq_op_1_ret, __smtx_typeof_eq,
              __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
          · simpa [__eo_prog_string_eager_reduction, __mk_str_eager_reduction] using hTy
      case Apply f z =>
        cases f <;> try simp  at hTy ⊢
        all_goals try cases hTy
        case UOp op =>
          cases op <;> try simp  at hTy ⊢
          all_goals try cases hTy
          case str_indexof =>
            apply RuleProofs.eo_typeof_bool_implies_has_bool_type
            · unfold RuleProofs.eo_has_smt_translation at hATrans ⊢
              rcases str_indexof_args_of_non_none
                  (by simpa [term_has_non_none_type, __eo_to_smt, __smtx_typeof] using hATrans) with
                ⟨T, hzTy, hyTy, hxTy⟩
              change
                __smtx_typeof
                  (SmtTerm.and
                    (SmtTerm.or
                      (SmtTerm.eq
                        (SmtTerm.str_indexof (__eo_to_smt z) (__eo_to_smt y)
                          (__eo_to_smt x))
                        (SmtTerm.Numeral (-1 : native_Int)))
                      (SmtTerm.or
                        (SmtTerm.geq
                          (SmtTerm.str_indexof (__eo_to_smt z) (__eo_to_smt y)
                            (__eo_to_smt x))
                          (__eo_to_smt x))
                        (SmtTerm.Boolean false)))
                    (SmtTerm.and
                      (SmtTerm.leq
                        (SmtTerm.str_indexof (__eo_to_smt z) (__eo_to_smt y)
                          (__eo_to_smt x))
                        (SmtTerm.str_len (__eo_to_smt z)))
                      (SmtTerm.Boolean true))) ≠ SmtType.None
              simp [hzTy, hyTy, hxTy, __smtx_typeof_str_indexof,
                __smtx_typeof_seq_op_1_ret, __smtx_typeof_arith_overload_op_2_ret,
                __smtx_typeof_eq, __smtx_typeof_guard, __smtx_typeof,
                native_ite, native_Teq]
            · simpa [__eo_prog_string_eager_reduction, __mk_str_eager_reduction] using hTy
          case str_indexof_re =>
            apply RuleProofs.eo_typeof_bool_implies_has_bool_type
            · unfold RuleProofs.eo_has_smt_translation at hATrans ⊢
              rcases str_indexof_re_args_of_non_none
                  (by simpa [term_has_non_none_type, __eo_to_smt, __smtx_typeof] using hATrans) with
                ⟨hzTy, hyTy, hxTy⟩
              change
                __smtx_typeof
                  (SmtTerm.and
                    (SmtTerm.or
                      (SmtTerm.eq
                        (SmtTerm.str_indexof_re (__eo_to_smt z) (__eo_to_smt y)
                          (__eo_to_smt x))
                        (SmtTerm.Numeral (-1 : native_Int)))
                      (SmtTerm.or
                        (SmtTerm.geq
                          (SmtTerm.str_indexof_re (__eo_to_smt z) (__eo_to_smt y)
                            (__eo_to_smt x))
                          (__eo_to_smt x))
                        (SmtTerm.Boolean false)))
                    (SmtTerm.and
                      (SmtTerm.leq
                        (SmtTerm.str_indexof_re (__eo_to_smt z) (__eo_to_smt y)
                          (__eo_to_smt x))
                        (SmtTerm.str_len (__eo_to_smt z)))
                      (SmtTerm.Boolean true))) ≠ SmtType.None
              simp [hzTy, hyTy, hxTy, __smtx_typeof_seq_op_1_ret,
                __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq,
                __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
            · simpa [__eo_prog_string_eager_reduction, __mk_str_eager_reduction] using hTy

theorem string_eager_reduction_true
    (M : SmtModel) (hM : model_wf M)
    (a : Term)
    (hBool : RuleProofs.eo_has_bool_type (__eo_prog_string_eager_reduction a)) :
    eo_interprets M (__eo_prog_string_eager_reduction a) true := by
  cases a <;> simp [__eo_prog_string_eager_reduction, __mk_str_eager_reduction] at hBool ⊢
  all_goals try
    exact False.elim (RuleProofs.term_ne_stuck_of_has_bool_type _ hBool rfl)
  case Apply f x =>
    cases f <;> try simp  at hBool ⊢
    all_goals try
      exact False.elim (RuleProofs.term_ne_stuck_of_has_bool_type _ hBool rfl)
    case UOp op =>
      cases op <;> try simp  at hBool ⊢
      all_goals try
        exact False.elim (RuleProofs.term_ne_stuck_of_has_bool_type _ hBool rfl)
      case str_to_code =>
        let tx := __eo_to_smt x
        let code := SmtTerm.str_to_code tx
        let thenTerm :=
          SmtTerm.and (SmtTerm.geq code (SmtTerm.Numeral 0))
            (SmtTerm.and (SmtTerm.lt code (SmtTerm.Numeral 196608))
              (SmtTerm.Boolean true))
        let elseTerm := SmtTerm.eq code (SmtTerm.Numeral (-1 : native_Int))
        let cond := SmtTerm.eq (SmtTerm.str_len tx) (SmtTerm.Numeral 1)
        have hFormulaTy :
            __smtx_typeof (SmtTerm.ite cond thenTerm elseTerm) = SmtType.Bool := by
          simpa [RuleProofs.eo_has_bool_type, tx, code, thenTerm, elseTerm, cond, __eo_to_smt, __smtx_typeof]
            using hBool
        have hFormulaNN : term_has_non_none_type (SmtTerm.ite cond thenTerm elseTerm) := by
          unfold term_has_non_none_type
          rw [hFormulaTy]
          simp
        rcases ite_args_of_non_none hFormulaNN with
          ⟨T, _hCondTy, hThenTy, _hElseTy, hTNN⟩
        have hThenNN : term_has_non_none_type thenTerm := by
          unfold term_has_non_none_type
          rw [hThenTy]
          exact hTNN
        have hGeqTy :
            __smtx_typeof (SmtTerm.geq code (SmtTerm.Numeral 0)) = SmtType.Bool :=
          (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
            (typeof_and_eq (SmtTerm.geq code (SmtTerm.Numeral 0))
              (SmtTerm.and (SmtTerm.lt code (SmtTerm.Numeral 196608))
                (SmtTerm.Boolean true))) hThenNN).1
        have hGeqNN : term_has_non_none_type
            (SmtTerm.geq code (SmtTerm.Numeral 0)) := by
          unfold term_has_non_none_type
          rw [hGeqTy]
          simp
        have hCodeTy : __smtx_typeof code = SmtType.Int := by
          rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq)
              (typeof_geq_eq code (SmtTerm.Numeral 0)) hGeqNN with
            hInt | hReal
          · exact hInt.1
          · have hNumTy : __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int := by
              rw [__smtx_typeof.eq_2]
            rw [hNumTy] at hReal
            cases hReal.2
        have hCodeNN : term_has_non_none_type code := by
          unfold term_has_non_none_type
          rw [hCodeTy]
          simp
        have hsTy : __smtx_typeof tx = SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_to_code)
            (typeof_str_to_code_eq tx) hCodeNN
        rcases seq_eval_of_seq_type M hM x SmtType.Char (by simpa [tx] using hsTy) with
          ⟨ss, hSEval⟩
        have hEvalTy :
            __smtx_typeof_value (__smtx_model_eval M tx) = __smtx_typeof tx :=
          Smtm.smt_model_eval_preserves_type_of_non_none M hM tx
            (by simp [term_has_non_none_type, hsTy])
        have hSeqTy :
            __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
          simpa [tx, hSEval, hsTy, __smtx_typeof_seq_value, __smtx_typeof_value] using hEvalTy
        have hValid :
            native_string_valid (native_unpack_string ss) = true :=
          native_unpack_string_valid_of_typeof_seq_char hSeqTy
        apply RuleProofs.eo_interprets_of_bool_eval M _ true hBool
        change __smtx_model_eval M (SmtTerm.ite cond thenTerm elseTerm) =
          SmtValue.Boolean true
        by_cases hLen : (native_unpack_seq ss).length = 1
        · have hLenString : (native_unpack_string ss).length = 1 := by
            simpa [native_unpack_string_length_eq ss] using hLen
          rcases native_str_to_code_singleton_bounds hValid hLenString with
            ⟨hLo, hHi⟩
          simp [tx, code, thenTerm, elseTerm, cond, __smtx_model_eval, hSEval,
            __smtx_model_eval_str_len, __smtx_model_eval_str_to_code,
            __smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_geq,
            __smtx_model_eval_leq, __smtx_model_eval_lt, __smtx_model_eval_and,
            native_seq_len, native_veq, native_zleq, native_zlt, native_and,
            hLen, hLo, hHi]
        · have hLenString : (native_unpack_string ss).length ≠ 1 := by
            intro h
            exact hLen (by simpa [native_unpack_string_length_eq ss] using h)
          have hCode : native_str_to_code (native_unpack_string ss) = -1 :=
            native_str_to_code_non_singleton (native_unpack_string ss) hLenString
          have hLenInt :
              (Int.ofNat (native_unpack_seq ss).length) ≠ (1 : Int) := by
            intro hEq
            exact hLen (Int.ofNat.inj hEq)
          have hCondFalse :
              (decide ((Int.ofNat (native_unpack_seq ss).length : Int) = 1)) = false := by
            exact decide_eq_false hLenInt
          simp [tx, code, thenTerm, elseTerm, cond, __smtx_model_eval, hSEval,
            __smtx_model_eval_str_len, __smtx_model_eval_str_to_code,
            __smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_geq,
            __smtx_model_eval_leq, __smtx_model_eval_lt, __smtx_model_eval_and,
            native_seq_len, native_veq, native_zleq, native_zlt, native_and,
            hCode]
          cases hCond :
              decide ((Int.ofNat (native_unpack_seq ss).length : Int) = 1) with
          | false =>
              rfl
          | true =>
              exact False.elim (hLenInt (of_decide_eq_true hCond))
      case str_from_code =>
        let tx := __eo_to_smt x
        let strFrom := SmtTerm._at_purify (SmtTerm.str_from_code tx)
        let cond :=
          SmtTerm.and (SmtTerm.leq (SmtTerm.Numeral 0) tx)
            (SmtTerm.and (SmtTerm.lt tx (SmtTerm.Numeral 196608))
              (SmtTerm.Boolean true))
        let thenTerm := SmtTerm.eq tx (SmtTerm.str_to_code strFrom)
        let elseTerm := SmtTerm.eq strFrom (SmtTerm.String [])
        have hFormulaTy :
            __smtx_typeof (SmtTerm.ite cond thenTerm elseTerm) = SmtType.Bool := by
          simpa [RuleProofs.eo_has_bool_type, tx, strFrom, cond, thenTerm, elseTerm, __eo_to_smt, __smtx_typeof]
            using hBool
        have hFormulaNN : term_has_non_none_type (SmtTerm.ite cond thenTerm elseTerm) := by
          unfold term_has_non_none_type
          rw [hFormulaTy]
          simp
        rcases ite_args_of_non_none hFormulaNN with
          ⟨T, hCondTy, _hThenTy, _hElseTy, _hTNN⟩
        have hCondNN : term_has_non_none_type cond := by
          unfold term_has_non_none_type
          rw [hCondTy]
          simp
        have hLeqTy :
            __smtx_typeof (SmtTerm.leq (SmtTerm.Numeral 0) tx) = SmtType.Bool :=
          (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
            (typeof_and_eq (SmtTerm.leq (SmtTerm.Numeral 0) tx)
              (SmtTerm.and (SmtTerm.lt tx (SmtTerm.Numeral 196608))
                (SmtTerm.Boolean true))) hCondNN).1
        have hLeqNN :
            term_has_non_none_type (SmtTerm.leq (SmtTerm.Numeral 0) tx) := by
          unfold term_has_non_none_type
          rw [hLeqTy]
          simp
        have hxTy : __smtx_typeof tx = SmtType.Int := by
          rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.leq)
              (typeof_leq_eq (SmtTerm.Numeral 0) tx) hLeqNN with
            hInt | hReal
          · exact hInt.2
          · have hNumTy : __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int := by
              rw [__smtx_typeof.eq_2]
            rw [hNumTy] at hReal
            cases hReal.1
        rcases int_eval_of_int_type M hM x (by simpa [tx] using hxTy) with
          ⟨z, hXEval⟩
        apply RuleProofs.eo_interprets_of_bool_eval M _ true hBool
        change __smtx_model_eval M (SmtTerm.ite cond thenTerm elseTerm) =
          SmtValue.Boolean true
        by_cases hz0 : 0 ≤ z
        ·
          by_cases hzHi : z < 196608
          · have hCode :
                native_str_to_code (native_str_from_code z) = z :=
              native_str_to_code_from_code_of_valid hz0 hzHi
            simp [tx, strFrom, cond, thenTerm, elseTerm, __smtx_model_eval, hXEval,
              __smtx_model_eval_ite, __smtx_model_eval_eq,
              __smtx_model_eval__at_purify, __smtx_model_eval_str_from_code,
              __smtx_model_eval_str_to_code, __smtx_model_eval_leq,
              __smtx_model_eval_lt, __smtx_model_eval_and, native_zleq,
              native_zlt, native_and, native_veq, native_unpack_pack_string,
              hz0, hzHi, hCode]
          · have hBad : ¬ (0 ≤ z ∧ z < 196608) := by
              intro h
              exact hzHi h.2
            have hFrom : native_str_from_code z = [] :=
              native_str_from_code_invalid hBad
            simp [tx, strFrom, cond, thenTerm, elseTerm, __smtx_model_eval, hXEval,
              __smtx_model_eval_ite, __smtx_model_eval_eq,
              __smtx_model_eval__at_purify, __smtx_model_eval_str_from_code,
              __smtx_model_eval_str_to_code, __smtx_model_eval_leq,
              __smtx_model_eval_lt, __smtx_model_eval_and, native_zleq,
              native_zlt, native_and, native_veq, hz0, hzHi, hFrom]
        · have hBad : ¬ (0 ≤ z ∧ z < 196608) := by
            intro h
            exact hz0 h.1
          have hFrom : native_str_from_code z = [] :=
            native_str_from_code_invalid hBad
          simp [tx, strFrom, cond, thenTerm, elseTerm, __smtx_model_eval, hXEval,
            __smtx_model_eval_ite, __smtx_model_eval_eq,
            __smtx_model_eval__at_purify, __smtx_model_eval_str_from_code,
            __smtx_model_eval_str_to_code, __smtx_model_eval_leq,
            __smtx_model_eval_lt, __smtx_model_eval_and, native_zleq,
            native_zlt, native_and, native_veq, hz0, hFrom]
      case str_to_int =>
        have hFormulaTy :
            __smtx_typeof
              (SmtTerm.geq (SmtTerm.str_to_int (__eo_to_smt x))
                (SmtTerm.Numeral (-1 : native_Int))) = SmtType.Bool := by
          simpa [RuleProofs.eo_has_bool_type, __eo_to_smt, __smtx_typeof] using hBool
        have hNN :
            term_has_non_none_type
              (SmtTerm.geq (SmtTerm.str_to_int (__eo_to_smt x))
                (SmtTerm.Numeral (-1 : native_Int))) := by
          unfold term_has_non_none_type
          rw [hFormulaTy]
          simp
        have hStrToIntTy :
            __smtx_typeof (SmtTerm.str_to_int (__eo_to_smt x)) = SmtType.Int := by
          rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq)
              (typeof_geq_eq (SmtTerm.str_to_int (__eo_to_smt x))
                (SmtTerm.Numeral (-1 : native_Int))) hNN with
            hInt | hReal
          · exact hInt.1
          · have hNumTy :
                __smtx_typeof (SmtTerm.Numeral (-1 : native_Int)) = SmtType.Int := by
              rw [__smtx_typeof.eq_2]
            rw [hNumTy] at hReal
            cases hReal.2
        have hStrToIntNN :
            term_has_non_none_type (SmtTerm.str_to_int (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [hStrToIntTy]
          simp
        have hsTy :
            __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_to_int)
            (typeof_str_to_int_eq (__eo_to_smt x)) hStrToIntNN
        rcases seq_eval_of_seq_type M hM x SmtType.Char hsTy with ⟨ss, hSEval⟩
        apply RuleProofs.eo_interprets_of_bool_eval M _ true hBool
        change
          __smtx_model_eval M
              (SmtTerm.geq (SmtTerm.str_to_int (__eo_to_smt x))
                (SmtTerm.Numeral (-1 : native_Int))) =
            SmtValue.Boolean true
        have hGe :
            (-1 : Int) ≤ native_str_to_int (native_unpack_string ss) :=
          native_str_to_int_ge_neg_one (native_unpack_string ss)
        simp [__smtx_model_eval, hSEval, __smtx_model_eval_str_to_int, __smtx_model_eval_geq,
          __smtx_model_eval_leq, native_zleq, hGe]
    case Apply f y =>
      cases f <;> try simp  at hBool ⊢
      all_goals try
        exact False.elim (RuleProofs.term_ne_stuck_of_has_bool_type _ hBool rfl)
      case UOp op =>
        cases op <;> try simp  at hBool ⊢
        all_goals try
          exact False.elim (RuleProofs.term_ne_stuck_of_has_bool_type _ hBool rfl)
        case str_contains =>
          let condEo := Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) y) x
          let pre :=
            Term.Apply (Term.UOp UserOp._at_purify)
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_substr) y)
                  (Term.Numeral 0))
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_indexof) y) x)
                  (Term.Numeral 0)))
          let start :=
            Term.Apply
              (Term.Apply (Term.UOp UserOp.plus)
                (Term.Apply (Term.UOp UserOp.str_len) pre))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.plus)
                  (Term.Apply (Term.UOp UserOp.str_len) x))
                (Term.Numeral 0))
          let suffix :=
            Term.Apply (Term.UOp UserOp._at_purify)
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_substr) y) start)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.neg)
                    (Term.Apply (Term.UOp UserOp.str_len) y))
                  start))
          let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre)
          let rhs3 := __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) suffix) nil
          let rhs2 := __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) rhs3
          let rhs1 := __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) pre) rhs2
          let thenEo := __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) y) rhs1
          let iteHead := __eo_mk_apply (Term.Apply (Term.UOp UserOp.ite) condEo) thenEo
          let elseEo :=
            Term.Apply (Term.UOp UserOp.not)
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x)
          let gen := __eo_mk_apply iteHead elseEo
          have hGenBool : RuleProofs.eo_has_bool_type gen := by
            simpa [gen, iteHead, thenEo, rhs1, rhs2, rhs3, nil, suffix, start,
              pre, condEo, elseEo] using hBool
          have hGenNe : gen ≠ Term.Stuck :=
            RuleProofs.term_ne_stuck_of_has_bool_type gen hGenBool
          have hIteHeadNe : iteHead ≠ Term.Stuck :=
            eo_mk_apply_fun_ne_stuck_of_ne_stuck iteHead elseEo hGenNe
          have hThenNe : thenEo ≠ Term.Stuck :=
            eo_mk_apply_arg_ne_stuck_of_ne_stuck
              (Term.Apply (Term.UOp UserOp.ite) condEo) thenEo hIteHeadNe
          have hRhs1Ne : rhs1 ≠ Term.Stuck :=
            eo_mk_apply_arg_ne_stuck_of_ne_stuck
              (Term.Apply (Term.UOp UserOp.eq) y) rhs1 hThenNe
          have hRhs2Ne : rhs2 ≠ Term.Stuck :=
            eo_mk_apply_arg_ne_stuck_of_ne_stuck
              (Term.Apply (Term.UOp UserOp.str_concat) pre) rhs2 hRhs1Ne
          have hRhs3Ne : rhs3 ≠ Term.Stuck :=
            eo_mk_apply_arg_ne_stuck_of_ne_stuck
              (Term.Apply (Term.UOp UserOp.str_concat) x) rhs3 hRhs2Ne
          have hNilNe : nil ≠ Term.Stuck :=
            eo_mk_apply_arg_ne_stuck_of_ne_stuck
              (Term.Apply (Term.UOp UserOp.str_concat) suffix) nil hRhs3Ne
          let ty := __eo_to_smt y
          let tx := __eo_to_smt x
          let idx := SmtTerm.str_indexof ty tx (SmtTerm.Numeral 0)
          let pfx := SmtTerm._at_purify (SmtTerm.str_substr ty (SmtTerm.Numeral 0) idx)
          let cut :=
            SmtTerm.plus (SmtTerm.str_len pfx)
              (SmtTerm.plus (SmtTerm.str_len tx) (SmtTerm.Numeral 0))
          let suffixS := SmtTerm._at_purify
            (SmtTerm.str_substr ty cut (SmtTerm.neg (SmtTerm.str_len ty) cut))
          let nilS := __eo_to_smt nil
          let rhs :=
            SmtTerm.str_concat pfx
              (SmtTerm.str_concat tx (SmtTerm.str_concat suffixS nilS))
          let cond := SmtTerm.str_contains ty tx
          let formula :=
            SmtTerm.ite cond (SmtTerm.eq ty rhs)
              (SmtTerm.not (SmtTerm.eq ty tx))
          have hFormulaTy : __smtx_typeof formula = SmtType.Bool := by
            unfold RuleProofs.eo_has_bool_type at hGenBool
            simpa [gen, iteHead, thenEo, rhs1, rhs2, rhs3, nil, suffix, start, pre, condEo, elseEo, formula, cond, rhs, nilS, suffixS, cut, pfx, idx, ty, tx, __eo_mk_apply, hNilNe, __eo_nil, __eo_to_smt, __eo_typeof, __smtx_typeof] using hGenBool
          have hFormulaNN : term_has_non_none_type formula := by
            unfold term_has_non_none_type
            rw [hFormulaTy]
            simp
          rcases ite_args_of_non_none hFormulaNN with
            ⟨_R, hCondTy, _hThenTy, _hElseTy, _hRNN⟩
          have hCondNN : term_has_non_none_type cond := by
            unfold term_has_non_none_type
            rw [hCondTy]
            simp
          rcases seq_binop_args_of_non_none_ret (op := SmtTerm.str_contains)
              (R := SmtType.Bool) (typeof_str_contains_eq ty tx) hCondNN with
            ⟨U, hyTy, hxTy⟩
          rcases seq_eval_of_seq_type M hM y U (by simpa [ty] using hyTy) with
            ⟨sy, hYEval⟩
          rcases seq_eval_of_seq_type M hM x U (by simpa [tx] using hxTy) with
            ⟨sx, hXEval⟩
          let ys := native_unpack_seq sy
          let xs := native_unpack_seq sx
          let idxVal := native_seq_indexof ys xs 0
          have hYEvalTy :
              __smtx_typeof_value (__smtx_model_eval M ty) = __smtx_typeof ty :=
            Smtm.smt_model_eval_preserves_type_of_non_none M hM ty
              (by simp [term_has_non_none_type, hyTy])
          have hSyTy : __smtx_typeof_seq_value sy = SmtType.Seq U := by
            rw [hYEval] at hYEvalTy
            simpa [__smtx_typeof_value, hyTy] using hYEvalTy
          have hElemY : __smtx_elem_typeof_seq_value sy = U :=
            elem_typeof_seq_value_of_typeof_seq_value hSyTy
          have hPreTy :
              __smtx_typeof (__eo_to_smt pre) = SmtType.Seq U := by
            change __smtx_typeof pfx = SmtType.Seq U
            simp [pfx, idx, ty, tx, hyTy, hxTy, __smtx_typeof,
              __smtx_typeof_str_indexof, __smtx_typeof_str_substr,
              native_ite, native_Teq]
          have hNilEval : __smtx_model_eval M nilS =
              SmtValue.Seq (SmtSeq.empty U) := by
            simpa [nilS, nil] using
              eval_nil_str_concat_typeof_of_smt_type_seq M pre U hPreTy
          apply RuleProofs.eo_interprets_of_bool_eval M _ true hBool
          simp only [nil, pre, __eo_mk_apply]
          change __smtx_model_eval M formula = SmtValue.Boolean true
          by_cases hContains : native_seq_contains ys xs = true
          · have hIdxNonneg : 0 ≤ idxVal := by
              simpa [idxVal, native_seq_contains] using hContains
            have hSplit :
                native_seq_extract ys 0 idxVal ++ xs ++
                    native_seq_extract ys (idxVal + Int.ofNat xs.length)
                      (Int.ofNat ys.length - (idxVal + Int.ofNat xs.length)) =
                  ys :=
              native_seq_indexof_zero_decomp ys xs hIdxNonneg
            have hPrefixLen :
                Int.ofNat (native_seq_extract ys 0 idxVal).length = idxVal := by
              simpa [idxVal] using
                native_seq_extract_prefix_length_of_indexof_nonneg ys xs hIdxNonneg
            have hStartEq :
                Int.ofNat (native_seq_extract ys 0 idxVal).length +
                    Int.ofNat xs.length =
                  idxVal + Int.ofNat xs.length := by
              rw [hPrefixLen]
            have hLenEq :
                Int.ofNat ys.length +
                    -((Int.ofNat (native_seq_extract ys 0 idxVal).length) +
                      Int.ofNat xs.length) =
                  Int.ofNat ys.length - (idxVal + Int.ofNat xs.length) := by
              rw [hPrefixLen]
              simp [Int.sub_eq_add_neg]
            have hPackSy : native_pack_seq U ys = sy := by
              dsimp [ys]
              rw [← hElemY]
              exact native_pack_unpack_seq sy
            simp [formula, cond, rhs, nilS, suffixS, cut, pfx, idx, ty, tx,
              ys, xs, __smtx_model_eval, hYEval, hXEval, hNilEval,
              __smtx_model_eval_ite, __smtx_model_eval_str_contains,
              __smtx_model_eval_eq, __smtx_model_eval_str_concat,
              __smtx_model_eval_str_substr, __smtx_model_eval_str_indexof,
              __smtx_model_eval_str_len, __smtx_model_eval_plus,
              __smtx_model_eval__, __smtx_model_eval__at_purify, native_seq_concat,
              _root_.native_unpack_pack_seq, elem_typeof_pack_seq, native_seq_len,
              hElemY, hContains, native_zplus, native_zneg, native_veq]
            apply Eq.trans hPackSy.symm
            apply congrArg (native_pack_seq U)
            dsimp [ys, xs, idxVal] at hSplit hStartEq hLenEq ⊢
            rw [hStartEq]
            simpa [native_unpack_seq, List.append_assoc, Int.sub_eq_add_neg] using hSplit.symm
          · have hContainsFalse : native_seq_contains ys xs = false := by
              cases h : native_seq_contains ys xs
              · rfl
              · exact False.elim (hContains (by simp [h]))
            have hSyNeSx : sy ≠ sx := by
              intro hEq
              have hLists : ys = xs := by
                simp [ys, xs, hEq]
              have hSelf := native_seq_contains_self xs
              have hFalseSelf : native_seq_contains xs xs = false := by
                simpa [ys, xs, hLists] using hContainsFalse
              rw [hSelf] at hFalseSelf
              cases hFalseSelf
            have hValNe : SmtValue.Seq sy ≠ SmtValue.Seq sx := by
              intro hEq
              cases hEq
              exact hSyNeSx rfl
            have hEqFalse : native_veq (SmtValue.Seq sy) (SmtValue.Seq sx) = false := by
              simp [native_veq, hValNe]
            simp [formula, cond, rhs, nilS, suffixS, cut, pfx, idx, ty, tx,
              ys, xs, __smtx_model_eval, hYEval, hXEval,
              __smtx_model_eval_ite, __smtx_model_eval_str_contains,
              __smtx_model_eval_eq, __smtx_model_eval_not, native_not,
              native_veq, hContainsFalse]
            exact hSyNeSx
        case str_in_re =>
          let fixed := __str_fixed_len_re x
          let rhsEo :=
            __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.str_len) y))
              fixed
          let gen :=
            __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.imp)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) y) x))
              rhsEo
          have hGenBool : RuleProofs.eo_has_bool_type gen := by
            simpa [gen, rhsEo, fixed] using hBool
          have hGenNe : gen ≠ Term.Stuck :=
            RuleProofs.term_ne_stuck_of_has_bool_type gen hGenBool
          have hRhsNe : rhsEo ≠ Term.Stuck :=
            eo_mk_apply_arg_ne_stuck_of_ne_stuck
              (Term.Apply (Term.UOp UserOp.imp)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) y) x))
              rhsEo hGenNe
          have hFixedNe : fixed ≠ Term.Stuck :=
            eo_mk_apply_arg_ne_stuck_of_ne_stuck
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.str_len) y))
              fixed hRhsNe
          rcases str_fixed_len_re_numeral_of_ne_stuck x hFixedNe with
            ⟨n, hFixed⟩
          let ty := __eo_to_smt y
          let tx := __eo_to_smt x
          let lhs := SmtTerm.str_in_re ty tx
          let rhs := SmtTerm.eq (SmtTerm.str_len ty) (SmtTerm.Numeral n)
          let formula := SmtTerm.imp lhs rhs
          have hFormulaTy : __smtx_typeof formula = SmtType.Bool := by
            unfold RuleProofs.eo_has_bool_type at hGenBool
            simpa [gen, rhsEo, fixed, formula, lhs, rhs, ty, tx, hFixed,
              __eo_mk_apply, __eo_to_smt] using hGenBool
          have hFormulaNN : term_has_non_none_type formula := by
            unfold term_has_non_none_type
            rw [hFormulaTy]
            simp
          have hLhsTy : __smtx_typeof lhs = SmtType.Bool :=
            (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
              (typeof_imp_eq lhs rhs) hFormulaNN).1
          have hLhsNN : term_has_non_none_type lhs := by
            unfold term_has_non_none_type
            rw [hLhsTy]
            simp
          have hArgs :=
            seq_char_reglan_args_of_non_none
              (op := SmtTerm.str_in_re) (typeof_str_in_re_eq ty tx) hLhsNN
          have hyTy : __smtx_typeof ty = SmtType.Seq SmtType.Char := hArgs.1
          have hxTy : __smtx_typeof tx = SmtType.RegLan := hArgs.2
          rcases seq_eval_of_seq_type M hM y SmtType.Char
              (by simpa [ty] using hyTy) with
            ⟨sy, hYEval⟩
          rcases reglan_eval_of_reglan_type M hM x
              (by simpa [tx] using hxTy) with
            ⟨rx, hXEval⟩
          have hYEvalTy :
              __smtx_typeof_value (__smtx_model_eval M ty) = __smtx_typeof ty :=
            Smtm.smt_model_eval_preserves_type_of_non_none M hM ty
              (by simp [term_has_non_none_type, hyTy])
          have hSyTy :
              __smtx_typeof_seq_value sy = SmtType.Seq SmtType.Char := by
            simpa [ty, hYEval, hyTy, __smtx_typeof_value] using hYEvalTy
          have hUnpack :=
            native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSyTy
          apply RuleProofs.eo_interprets_of_bool_eval M _ true hBool
          simp only [__eo_mk_apply, hFixed]
          change __smtx_model_eval M formula = SmtValue.Boolean true
          by_cases hIn : native_str_in_re (native_unpack_string sy) rx = true
          · have hInModel :
                Smtm.native_str_in_re (native_unpack_seq sy) rx = true := by
              rw [hUnpack, ← RuleProofs.native_str_in_re_eq_model]
              exact hIn
            have hFixedLen :
                Int.ofNat (native_unpack_string sy).length = n :=
              str_fixed_len_re_sound M x (native_unpack_string sy) rx n
                hFixed hXEval hIn
            have hFixedLenSeq : native_seq_len (native_unpack_seq sy) = n := by
              simpa [native_seq_len, native_unpack_string_length_eq sy] using
                hFixedLen
            simp [formula, lhs, rhs, ty, tx, __smtx_model_eval, hYEval, hXEval,
              __smtx_model_eval_imp, __smtx_model_eval_str_in_re,
              __smtx_model_eval_str_len, __smtx_model_eval_eq,
              __smtx_model_eval_or, __smtx_model_eval_not, native_or,
              native_not, native_veq, hInModel, hFixedLenSeq]
          · have hInFalse :
                native_str_in_re (native_unpack_string sy) rx = false := by
              cases h : native_str_in_re (native_unpack_string sy) rx
              · rfl
              · exact False.elim (hIn (by simp [h]))
            have hInModel :
                Smtm.native_str_in_re (native_unpack_seq sy) rx = false := by
              rw [hUnpack, ← RuleProofs.native_str_in_re_eq_model]
              exact hInFalse
            simp [formula, lhs, rhs, ty, tx, __smtx_model_eval, hYEval, hXEval,
              __smtx_model_eval_imp, __smtx_model_eval_str_in_re,
              __smtx_model_eval_str_len, __smtx_model_eval_eq,
              __smtx_model_eval_or, __smtx_model_eval_not, native_or,
              native_not, native_veq, hInModel]
      case Apply f z =>
        cases f <;> try simp  at hBool ⊢
        all_goals try
          exact False.elim (RuleProofs.term_ne_stuck_of_has_bool_type _ hBool rfl)
        case UOp op =>
          cases op <;> try simp  at hBool ⊢
          all_goals try
            exact False.elim (RuleProofs.term_ne_stuck_of_has_bool_type _ hBool rfl)
          case str_indexof =>
            let tz := __eo_to_smt z
            let ty := __eo_to_smt y
            let tx := __eo_to_smt x
            let idx := SmtTerm.str_indexof tz ty tx
            let leftTerm :=
              SmtTerm.or (SmtTerm.eq idx (SmtTerm.Numeral (-1 : native_Int)))
                (SmtTerm.or (SmtTerm.geq idx tx) (SmtTerm.Boolean false))
            let rightTerm :=
              SmtTerm.and (SmtTerm.leq idx (SmtTerm.str_len tz))
                (SmtTerm.Boolean true)
            have hFormulaTy :
                __smtx_typeof (SmtTerm.and leftTerm rightTerm) = SmtType.Bool := by
              exact hBool
            have hFormulaNN :
                term_has_non_none_type (SmtTerm.and leftTerm rightTerm) := by
              unfold term_has_non_none_type
              rw [hFormulaTy]
              simp
            have hRightTy : __smtx_typeof rightTerm = SmtType.Bool :=
              (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
                (typeof_and_eq leftTerm rightTerm) hFormulaNN).2
            have hRightNN : term_has_non_none_type rightTerm := by
              unfold term_has_non_none_type
              rw [hRightTy]
              simp
            have hLeqTy :
                __smtx_typeof (SmtTerm.leq idx (SmtTerm.str_len tz)) =
                  SmtType.Bool :=
              (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
                (typeof_and_eq (SmtTerm.leq idx (SmtTerm.str_len tz))
                  (SmtTerm.Boolean true)) hRightNN).1
            have hLeqNN :
                term_has_non_none_type (SmtTerm.leq idx (SmtTerm.str_len tz)) := by
              unfold term_has_non_none_type
              rw [hLeqTy]
              simp
            have hIdxTy : __smtx_typeof idx = SmtType.Int := by
              rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.leq)
                  (typeof_leq_eq idx (SmtTerm.str_len tz)) hLeqNN with
                hInt | hReal
              · exact hInt.1
              · have hLenNN : term_has_non_none_type (SmtTerm.str_len tz) := by
                  unfold term_has_non_none_type
                  rw [hReal.2]
                  simp
                rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
                    (typeof_str_len_eq tz) hLenNN with ⟨U, hSeq⟩
                have hLenTy :
                    __smtx_typeof (SmtTerm.str_len tz) = SmtType.Int := by
                  rw [typeof_str_len_eq]
                  simp [__smtx_typeof_seq_op_1_ret, hSeq]
                rw [hLenTy] at hReal
                cases hReal.2
            have hIdxNN : term_has_non_none_type idx := by
              unfold term_has_non_none_type
              rw [hIdxTy]
              simp
            rcases str_indexof_args_of_non_none (by simpa [idx] using hIdxNN) with
              ⟨U, hzTy, hyTy, hxTy⟩
            rcases seq_eval_of_seq_type M hM z U (by simpa [tz] using hzTy) with
              ⟨sz, hZEval⟩
            rcases seq_eval_of_seq_type M hM y U (by simpa [ty] using hyTy) with
              ⟨sy, hYEval⟩
            rcases int_eval_of_int_type M hM x (by simpa [tx] using hxTy) with
              ⟨n, hXEval⟩
            let idxVal :=
              native_seq_indexof (native_unpack_seq sz) (native_unpack_seq sy) n
            have hIdxOr :
                idxVal = -1 ∨ n ≤ idxVal :=
              native_seq_indexof_eq_neg_one_or_ge
                (native_unpack_seq sz) (native_unpack_seq sy) n
            have hIdxLe :
                idxVal ≤ Int.ofNat (native_unpack_seq sz).length :=
              native_seq_indexof_le_len
                (native_unpack_seq sz) (native_unpack_seq sy) n
            apply RuleProofs.eo_interprets_of_bool_eval M _ true hBool
            change __smtx_model_eval M (SmtTerm.and leftTerm rightTerm) =
              SmtValue.Boolean true
            rcases hIdxOr with hIdxEq | hIdxGe
            · simp [tz, ty, tx, idx, idxVal, leftTerm, rightTerm, __smtx_model_eval,
                hZEval, hYEval, hXEval, __smtx_model_eval_str_indexof,
                __smtx_model_eval_str_len, __smtx_model_eval_eq,
                __smtx_model_eval_geq, __smtx_model_eval_leq,
                __smtx_model_eval_or, __smtx_model_eval_and, native_seq_len,
                native_veq, native_zleq, native_or, native_and, hIdxEq]
            · simp [tz, ty, tx, idx, idxVal, leftTerm, rightTerm, __smtx_model_eval,
                hZEval, hYEval, hXEval, __smtx_model_eval_str_indexof,
                __smtx_model_eval_str_len, __smtx_model_eval_eq,
                __smtx_model_eval_geq, __smtx_model_eval_leq,
                __smtx_model_eval_or, __smtx_model_eval_and, native_seq_len,
              native_veq, native_zleq, native_or, native_and, hIdxGe]
              simpa [idxVal] using hIdxLe
          case str_indexof_re =>
            let tz := __eo_to_smt z
            let ty := __eo_to_smt y
            let tx := __eo_to_smt x
            let idx := SmtTerm.str_indexof_re tz ty tx
            let leftTerm :=
              SmtTerm.or (SmtTerm.eq idx (SmtTerm.Numeral (-1 : native_Int)))
                (SmtTerm.or (SmtTerm.geq idx tx) (SmtTerm.Boolean false))
            let rightTerm :=
              SmtTerm.and (SmtTerm.leq idx (SmtTerm.str_len tz))
                (SmtTerm.Boolean true)
            have hFormulaTy :
                __smtx_typeof (SmtTerm.and leftTerm rightTerm) = SmtType.Bool := by
              exact hBool
            have hFormulaNN :
                term_has_non_none_type (SmtTerm.and leftTerm rightTerm) := by
              unfold term_has_non_none_type
              rw [hFormulaTy]
              simp
            have hRightTy : __smtx_typeof rightTerm = SmtType.Bool :=
              (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
                (typeof_and_eq leftTerm rightTerm) hFormulaNN).2
            have hRightNN : term_has_non_none_type rightTerm := by
              unfold term_has_non_none_type
              rw [hRightTy]
              simp
            have hLeqTy :
                __smtx_typeof (SmtTerm.leq idx (SmtTerm.str_len tz)) =
                  SmtType.Bool :=
              (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
                (typeof_and_eq (SmtTerm.leq idx (SmtTerm.str_len tz))
                  (SmtTerm.Boolean true)) hRightNN).1
            have hLeqNN :
                term_has_non_none_type (SmtTerm.leq idx (SmtTerm.str_len tz)) := by
              unfold term_has_non_none_type
              rw [hLeqTy]
              simp
            have hIdxTy : __smtx_typeof idx = SmtType.Int := by
              rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.leq)
                  (typeof_leq_eq idx (SmtTerm.str_len tz)) hLeqNN with
                hInt | hReal
              · exact hInt.1
              · have hLenNN : term_has_non_none_type (SmtTerm.str_len tz) := by
                  unfold term_has_non_none_type
                  rw [hReal.2]
                  simp
                rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
                    (typeof_str_len_eq tz) hLenNN with ⟨U, hSeq⟩
                have hLenTy :
                    __smtx_typeof (SmtTerm.str_len tz) = SmtType.Int := by
                  rw [typeof_str_len_eq]
                  simp [__smtx_typeof_seq_op_1_ret, hSeq]
                rw [hLenTy] at hReal
                cases hReal.2
            have hIdxNN : term_has_non_none_type idx := by
              unfold term_has_non_none_type
              rw [hIdxTy]
              simp
            rcases str_indexof_re_args_of_non_none (by simpa [idx] using hIdxNN) with
              ⟨hzTy, hyTy, hxTy⟩
            rcases seq_eval_of_seq_type M hM z SmtType.Char (by simpa [tz] using hzTy) with
              ⟨sz, hZEval⟩
            rcases reglan_eval_of_reglan_type M hM y (by simpa [ty] using hyTy) with
              ⟨ry, hYEval⟩
            rcases int_eval_of_int_type M hM x (by simpa [tx] using hxTy) with
              ⟨n, hXEval⟩
            let idxVal := native_str_indexof_re (native_unpack_seq sz) ry n
            have hIdxOr :
                idxVal = -1 ∨ n ≤ idxVal :=
              native_str_indexof_re_eq_neg_one_or_ge (native_unpack_seq sz) ry n
            have hIdxLe :
                idxVal ≤ Int.ofNat (native_unpack_seq sz).length :=
              native_str_indexof_re_le_len (native_unpack_seq sz) ry n
            apply RuleProofs.eo_interprets_of_bool_eval M _ true hBool
            change __smtx_model_eval M (SmtTerm.and leftTerm rightTerm) =
              SmtValue.Boolean true
            rcases hIdxOr with hIdxEq | hIdxGe
            · simp [tz, ty, tx, idx, idxVal, leftTerm, rightTerm, __smtx_model_eval,
                hZEval, hYEval, hXEval, __smtx_model_eval_str_indexof_re,
                __smtx_model_eval_str_len, __smtx_model_eval_eq,
                __smtx_model_eval_geq, __smtx_model_eval_leq,
                __smtx_model_eval_or, __smtx_model_eval_and, native_seq_len,
                native_veq, native_zleq, native_or, native_and, hIdxEq]
            · simp [tz, ty, tx, idx, idxVal, leftTerm, rightTerm, __smtx_model_eval,
                hZEval, hYEval, hXEval, __smtx_model_eval_str_indexof_re,
                __smtx_model_eval_str_len, __smtx_model_eval_eq,
                __smtx_model_eval_geq, __smtx_model_eval_leq,
                __smtx_model_eval_or, __smtx_model_eval_and, native_seq_len,
                native_veq, native_zleq, native_or, native_and, hIdxGe]
              simpa [idxVal] using hIdxLe
