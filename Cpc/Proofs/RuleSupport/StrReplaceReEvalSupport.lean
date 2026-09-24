module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.RegexSupport
public import Cpc.Proofs.RuleSupport.CongSupport
import all Cpc.Proofs.RuleSupport.CongSupport
public import Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Cpc.SmtModel

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

private theorem str_replace_re_args_smt_types_of_has_translation
    (s r t : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) s) r) t) ->
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char := by
  intro hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.str_replace_re (__eo_to_smt s) (__eo_to_smt r) (__eo_to_smt t)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) s) r) t)) ≠
      SmtType.None
    exact hTrans
  exact str_replace_re_args_of_non_none (op := SmtTerm.str_replace_re)
    (typeof_str_replace_re_eq (__eo_to_smt s) (__eo_to_smt r) (__eo_to_smt t)) hNN

theorem eq_has_bool_type_of_translation
    (x y : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) := by
  unfold RuleProofs.eo_has_bool_type
  have hNN :
      term_has_non_none_type
        (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) ≠
      SmtType.None
    exact hTrans
  exact Smtm.eq_term_typeof_of_non_none hNN

theorem seq_eval_of_type
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char) :
    ∃ ss : SmtSeq,
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq ss ∧
      __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char ∧
      native_string_valid (native_unpack_string ss) = true := by
  have hPres :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq SmtType.Char := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTy]
        simp)
  rcases seq_value_canonical hPres with ⟨ss, hss⟩
  have hSeqTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
    simpa [__smtx_typeof_value, hss] using hPres
  exact ⟨ss, hss, hSeqTy, native_unpack_string_valid_of_typeof_seq_char hSeqTy⟩

theorem reglan_eval_of_type
    (M : SmtModel) (hM : model_wf M) (r : Term)
    (hTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan) :
    ∃ rv : SmtRegLan,
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv := by
  have hPres :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hTy]
        simp)
  exact reglan_value_canonical hPres

private theorem native_re_prefix_match_go_isSome_iff_exists
    (r : SmtRegLan) :
  ∀ (xs : native_String) (n : Nat),
      native_string_valid xs = true ->
      ((Smtm.impl_native_re_prefix_match_len_go r xs n).isSome = true ↔
        ∃ pre : native_String, (∃ post : native_String,
          (pre ++ post = xs ∧ RuleProofs.nativeListInRe pre r = true))) := by
  intro xs n
  induction xs generalizing r n with
  | nil =>
      refine (fun hValid : native_string_valid [] = true => ?_)
      simp only [impl_native_string_to_values, List.map]
      rw [Smtm.impl_native_re_prefix_match_len_go.eq_1]
      cases hNull : native_re_nullable r
      · simp [hNull, RuleProofs.nativeListInRe]
      · simp [hNull, RuleProofs.nativeListInRe]
  | cons c cs ih =>
      refine (fun hValid : native_string_valid (c :: cs) = true => ?_)
      have hParts : native_char_valid c = true ∧ native_string_valid cs = true := by
        simpa [native_string_valid] using hValid
      rcases hParts with ⟨hc, hcs⟩
      simp only [impl_native_string_to_values, List.map]
      rw [Smtm.impl_native_re_prefix_match_len_go.eq_2]
      cases hNull : native_re_nullable r
      · simp
        constructor
        · intro h
          rcases (ih (native_re_deriv c r) (n + 1) hcs).1 h with
            ⟨pre, post, hAppend, hIn⟩
          refine Exists.intro (c :: pre) ?_
          constructor
          · exact ⟨post, by simp [hAppend]⟩
          · simpa [RuleProofs.nativeListInRe] using hIn
        · intro h
          rcases h with ⟨pre, hPost, hIn⟩
          cases pre with
          | nil =>
              have hNullable : native_re_nullable r = true := by
                simpa [RuleProofs.nativeListInRe] using hIn
              simp [hNull] at hNullable
          | cons d ds =>
              rcases hPost with ⟨post, hAppend⟩
              cases hAppend
              have hTailIn :
                  RuleProofs.nativeListInRe ds (native_re_deriv c r) = true := by
                simpa [RuleProofs.nativeListInRe] using hIn
              exact (ih (native_re_deriv c r) (n + 1) hcs).2
                ⟨ds, post, by rfl, hTailIn⟩
      · simp
        refine Exists.intro [] ?_
        constructor
        · exact ⟨c :: cs, by simp⟩
        · simpa [RuleProofs.nativeListInRe] using hNull

private theorem native_re_prefix_match_isSome_iff_exists
    (r : SmtRegLan) (xs : native_String)
    (hValid : native_string_valid xs = true) :
    (native_re_prefix_match_len? r xs).isSome = true ↔
      ∃ pre : native_String, (∃ post : native_String,
        (pre ++ post = xs ∧ RuleProofs.nativeListInRe pre r = true)) := by
  rw [Smtm.native_re_prefix_match_len?.eq_1]
  have h := native_re_prefix_match_go_isSome_iff_exists r xs 0
  exact h hValid

private theorem nativeListInRe_concat_all_true_iff_exists
    (r : SmtRegLan) (xs : native_String)
    (hValid : native_string_valid xs = true) :
    RuleProofs.nativeListInRe xs (native_re_concat r native_re_all) = true ↔
      ∃ pre : native_String, (∃ post : native_String,
        (pre ++ post = xs ∧ RuleProofs.nativeListInRe pre r = true)) := by
  constructor
  · intro h
    rcases
      (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append xs r native_re_all).1
        (by have hsimpa := h; (try simp [native_re_concat] at hsimpa ⊢); exact hsimpa) with
      ⟨pre, post, hAppend, hLeft, _hRight⟩
    exact ⟨pre, post, hAppend, hLeft⟩
  · intro h
    rcases h with ⟨pre, post, hAppend, hLeft⟩
    have hAppendValid : native_string_valid (pre ++ post) = true := by
      simpa [hAppend] using hValid
    have hRight : RuleProofs.nativeListInRe post native_re_all = true := by
      have hAll : post.all native_char_valid = true := by
        have hAllAppend : (pre ++ post).all native_char_valid = true := by
          simpa [native_string_valid] using hAppendValid
        have hAllParts :
            pre.all native_char_valid = true ∧ post.all native_char_valid = true := by
          simpa [List.all_append, Bool.and_eq_true] using hAllAppend
        exact hAllParts.2
      exact RuleProofs.nativeListInRe_re_all post hAll
    have hsimpa :=
      (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append xs r native_re_all).2
        ⟨pre, post, hAppend, hLeft, hRight⟩
    try simp [native_re_concat] at hsimpa ⊢
    exact hsimpa

private theorem native_re_prefix_match_isSome_iff_concat_all
    (r : SmtRegLan) (xs : native_String)
    (hValid : native_string_valid xs = true) :
    (native_re_prefix_match_len? r xs).isSome = true ↔
      RuleProofs.nativeListInRe xs (native_re_concat r native_re_all) = true := by
  rw [native_re_prefix_match_isSome_iff_exists r xs hValid,
    nativeListInRe_concat_all_true_iff_exists r xs hValid]

private theorem native_str_in_re_concat_all_eq_prefix_isSome
    (r : SmtRegLan) (xs : native_String)
    (hValid : native_string_valid xs = true) :
    native_str_in_re xs (native_re_concat r native_re_all) =
      (native_re_prefix_match_len? r xs).isSome := by
  have hIff := native_re_prefix_match_isSome_iff_concat_all r xs hValid
  have hNative :
      native_str_in_re xs (native_re_concat r native_re_all) =
        RuleProofs.nativeListInRe xs (native_re_concat r native_re_all) := by
    simp [native_str_in_re, hValid]
  rw [hNative]
  cases hPref : (native_re_prefix_match_len? r xs).isSome <;>
    cases hIn : RuleProofs.nativeListInRe xs (native_re_concat r native_re_all) <;>
      simp [hPref, hIn] at hIff ⊢

def replace_re_search_re (r : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r)
    (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) (Term.UOp UserOp.re_all))
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))

theorem replace_re_search_re_eval
    (M : SmtModel) (r : Term) (rv : SmtRegLan)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv) :
    __smtx_typeof (__eo_to_smt (replace_re_search_re r)) = SmtType.RegLan ∧
      __smtx_model_eval M (__eo_to_smt (replace_re_search_re r)) =
        SmtValue.RegLan (native_re_concat rv native_re_all) := by
  constructor
  · change __smtx_typeof
        (SmtTerm.re_concat (__eo_to_smt r)
          (SmtTerm.re_concat SmtTerm.re_all
            (SmtTerm.str_to_re (SmtTerm.String [])))) =
      SmtType.RegLan
    simp [__smtx_typeof, hRTy, native_ite,
      native_Teq, native_string_valid]
  · change __smtx_model_eval M
        (SmtTerm.re_concat (__eo_to_smt r)
          (SmtTerm.re_concat SmtTerm.re_all
            (SmtTerm.str_to_re (SmtTerm.String [])))) =
      SmtValue.RegLan (native_re_concat rv native_re_all)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat,
      __smtx_model_eval_str_to_re, hREval,
      native_re_concat,
      native_re_all]
    cases rv <;> simp [native_str_to_re,
      impl_native_re_of_list]

theorem str_first_match_rec_smallest_eq_go
    (M : SmtModel) (hM : model_wf M) :
    ∀ (xs : native_String) (r : Term) (rv : SmtRegLan) (n : Nat),
      native_string_valid xs = true ->
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
      __str_first_match_rec_smallest (substrWord xs 0 xs.length) r
          (Term.Numeral (Int.ofNat n)) ≠ Term.Stuck ->
      __str_first_match_rec_smallest (substrWord xs 0 xs.length) r
          (Term.Numeral (Int.ofNat n)) =
        match Smtm.impl_native_re_prefix_match_len_go rv xs n with
        | some endIdx => Term.Numeral (Int.ofNat endIdx)
        | none => Term.Stuck
  | [], r, rv, n, hValid, hRTy, hREval, hNe => by
      have hRNe : r ≠ Term.Stuck := by
        intro hR
        subst r
        change __smtx_model_eval M SmtTerm.None = SmtValue.RegLan rv at hREval
        simp [__smtx_model_eval] at hREval
      have hStep :
          __str_first_match_rec_smallest
              (substrWord ([] : native_String) 0 ([] : native_String).length) r
              (Term.Numeral (Int.ofNat n)) =
            __eo_requires (__re_nullable r) (Term.Boolean true)
              (Term.Numeral (Int.ofNat n)) := by
        change
          __str_first_match_rec_smallest (Term.String []) r
              (Term.Numeral (Int.ofNat n)) =
            __eo_requires (__re_nullable r) (Term.Boolean true)
              (Term.Numeral (Int.ofNat n))
        exact
          Eo.__str_first_match_rec_smallest.eq_4 r
            (Term.Numeral (Int.ofNat n)) hRNe (by simp)
      have hNeReq :
          __eo_requires (__re_nullable r) (Term.Boolean true)
              (Term.Numeral (Int.ofNat n)) ≠ Term.Stuck := by
        intro hReqStuck
        exact hNe (hStep.trans hReqStuck)
      have hReq :
          __re_nullable r = Term.Boolean true :=
        eo_requires_eq_of_ne_stuck (__re_nullable r) (Term.Boolean true)
          (Term.Numeral (Int.ofNat n)) hNeReq
      have hNullNe : __re_nullable r ≠ Term.Stuck :=
        eo_requires_left_ne_stuck_of_ne_stuck (__re_nullable r)
          (Term.Boolean true) (Term.Numeral (Int.ofNat n)) hNeReq
      have hReqResult :
          __eo_requires (__re_nullable r) (Term.Boolean true)
              (Term.Numeral (Int.ofNat n)) =
            Term.Numeral (Int.ofNat n) :=
        eo_requires_result_eq_of_ne_stuck (__re_nullable r)
          (Term.Boolean true) (Term.Numeral (Int.ofNat n)) hNeReq
      have hNullEq :
          __re_nullable r = Term.Boolean (native_re_nullable rv) := by
        have h :=
          str_eval_str_in_re_rec_substrWord_eq M hM [] r rv
            (by simp [native_string_valid]) hRTy hREval (by
              simpa [substrWord, str_eval_empty_eq_nullable] using hNullNe)
        have hsimpa := h
        try simp [substrWord, str_eval_empty_eq_nullable] at hsimpa ⊢
        exact hsimpa
      cases hNull : native_re_nullable rv
      · have hFalse : False := by
          rw [hNull] at hNullEq
          rw [hReq] at hNullEq
          cases hNullEq
        exact False.elim hFalse
      · simp only [impl_native_string_to_values, List.map]
        rw [Smtm.impl_native_re_prefix_match_len_go.eq_1]
        simp [hNull]
        exact hStep.trans hReqResult
  | c :: cs, r, rv, n, hValid, hRTy, hREval, hNe => by
      rcases native_string_valid_cons_parts hValid with ⟨hc, hcs⟩
      simp [substrWord, extractString_zero_cons] at hNe ⊢
      rw [substrWord_cons_tail c cs] at hNe ⊢
      have hRNe : r ≠ Term.Stuck := by
        intro hR
        subst r
        change __smtx_model_eval M SmtTerm.None = SmtValue.RegLan rv at hREval
        simp [__smtx_model_eval] at hREval
      have hAdd :
          __eo_add (Term.Numeral (Int.ofNat n)) (Term.Numeral 1) =
            Term.Numeral (Int.ofNat (n + 1)) := by
        simp [__eo_add, native_zplus]
      have hStep :
          __str_first_match_rec_smallest
              (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                (substrWord cs 0 cs.length)) r (Term.Numeral (Int.ofNat n)) =
            __eo_ite (__re_nullable r) (Term.Numeral (Int.ofNat n))
              (__str_first_match_rec_smallest (substrWord cs 0 cs.length)
                (__derivative (Term.String [c]) r)
                (Term.Numeral (Int.ofNat (n + 1)))) := by
        rw [Eo.__str_first_match_rec_smallest.eq_3 r
          (Term.Numeral (Int.ofNat n)) (Term.String [c])
          (substrWord cs 0 cs.length) hRNe (by simp)]
        rw [hAdd]
      have hNeIte :
          __eo_ite (__re_nullable r) (Term.Numeral (Int.ofNat n))
              (__str_first_match_rec_smallest (substrWord cs 0 cs.length)
                (__derivative (Term.String [c]) r)
                (Term.Numeral (Int.ofNat (n + 1)))) ≠ Term.Stuck := by
        intro hStuck
        exact hNe (hStep.trans hStuck)
      refine hStep.trans ?_
      have hNullNe : __re_nullable r ≠ Term.Stuck := by
        intro hNullStuck
        rw [hNullStuck] at hNeIte
        simp [__eo_ite, native_teq, native_ite] at hNeIte
      have hNullEq :
          __re_nullable r = Term.Boolean (native_re_nullable rv) := by
        have h :=
          str_eval_str_in_re_rec_substrWord_eq M hM [] r rv
            (by simp [native_string_valid]) hRTy hREval (by
              simpa [substrWord, str_eval_empty_eq_nullable] using hNullNe)
        have hsimpa := h
        try simp [substrWord, str_eval_empty_eq_nullable] at hsimpa ⊢
        exact hsimpa
      cases hNull : native_re_nullable rv
      · rw [hNull] at hNullEq
        rw [hNullEq] at hNeIte ⊢
        simp [__eo_ite, native_teq, native_ite] at hNeIte ⊢
        have hDerNe : __derivative (Term.String [c]) r ≠ Term.Stuck := by
          intro hDer
          rw [hDer] at hNeIte
          have hStuck :
              __str_first_match_rec_smallest (substrWord cs 0 cs.length)
                  Term.Stuck (Term.Numeral (Int.ofNat n + 1)) =
                Term.Stuck :=
            Eo.__str_first_match_rec_smallest.eq_1
              (substrWord cs 0 cs.length) (Term.Numeral (Int.ofNat n + 1))
          exact hNeIte hStuck
        rcases
          smtx_model_eval_derivative_single_rel M hM c hc r rv hRTy hREval
            hDerNe with
          ⟨drv, hDerEval, hDerTy, hDerRel⟩
        have hNeTail :
            __str_first_match_rec_smallest (substrWord cs 0 cs.length)
                (__derivative (Term.String [c]) r)
                (Term.Numeral (Int.ofNat (n + 1))) ≠ Term.Stuck := by
          simpa using hNeIte
        have hTail :=
          str_first_match_rec_smallest_eq_go M hM cs
            (__derivative (Term.String [c]) r) drv (n + 1)
            hcs hDerTy hDerEval hNeTail
        have hTail' :
            __str_first_match_rec_smallest (substrWord cs 0 cs.length)
                (__derivative (Term.String [c]) r)
                (Term.Numeral (Int.ofNat n + 1)) =
              match Smtm.impl_native_re_prefix_match_len_go drv cs (n + 1) with
              | some endIdx => Term.Numeral (Int.ofNat endIdx)
              | none => Term.Stuck := by
          simpa using hTail
        change
          __str_first_match_rec_smallest (substrWord cs 0 cs.length)
              (__derivative (Term.String [c]) r)
              (Term.Numeral (Int.ofNat n + 1)) =
            match Smtm.impl_native_re_prefix_match_len_go rv (c :: cs) n with
            | some endIdx => Term.Numeral (Int.ofNat endIdx)
            | none => Term.Stuck
        rw [hTail']
        have hGoCong :
            Smtm.impl_native_re_prefix_match_len_go drv cs (n + 1) =
              Smtm.impl_native_re_prefix_match_len_go
                (native_re_deriv c rv) cs (n + 1) :=
          CongSupport.native_re_prefix_match_len_go_congr_valid_ext_of_str_ext cs drv
            (native_re_deriv c rv) (n + 1) hcs (by
              intro ys hys
              change RuleProofs.native_str_in_re ys drv =
                RuleProofs.native_str_in_re ys (native_re_deriv c rv)
              rw [RuleProofs.native_str_in_re_eq_model,
                RuleProofs.native_str_in_re_eq_model]
              exact smt_value_rel_reglan_valid_eq hDerRel hys)
        rw [Smtm.impl_native_re_prefix_match_len_go.eq_2]
        simp [hNull]
        rw [← hGoCong]
      · rw [hNull] at hNullEq
        rw [hNullEq]
        rw [Smtm.impl_native_re_prefix_match_len_go.eq_2]
        simp [__eo_ite, native_teq, native_ite, hNull]

theorem str_eval_prefix_condition_eq
    (M : SmtModel) (hM : model_wf M)
    (xs : native_String) (rs : Term) (rv : SmtRegLan)
    (hValid : native_string_valid xs = true)
    (hRsTy : __smtx_typeof (__eo_to_smt rs) = SmtType.RegLan)
    (hRsEval :
      __smtx_model_eval M (__eo_to_smt rs) =
        SmtValue.RegLan (native_re_concat rv native_re_all))
    (hCondNe :
      __str_eval_str_in_re_rec (substrWord xs 0 xs.length) rs ≠ Term.Stuck) :
    __str_eval_str_in_re_rec (substrWord xs 0 xs.length) rs =
      Term.Boolean ((native_re_prefix_match_len? rv xs).isSome) := by
  have hEval :=
    str_eval_str_in_re_rec_substrWord_eq M hM xs rs
      (native_re_concat rv native_re_all) hValid hRsTy hRsEval hCondNe
  rw [hEval]
  rw [← RuleProofs.native_str_in_re_eq_model]
  rw [native_str_in_re_concat_all_eq_prefix_isSome rv xs hValid]

private theorem native_string_valid_of_string_type
    {str : native_String}
    (hTy : __smtx_typeof (__eo_to_smt (Term.String str)) =
      SmtType.Seq SmtType.Char) :
    native_string_valid str = true := by
  change __smtx_typeof (SmtTerm.String str) = SmtType.Seq SmtType.Char at hTy
  cases hValid : native_string_valid str <;>
    simp [__smtx_typeof, native_ite, hValid] at hTy ⊢

private theorem list_typed_char_pack_unpack :
    ∀ {xs : List SmtValue},
      list_typed SmtType.Char xs ->
        xs.map (fun v => SmtValue.Char (impl_native_ssm_char_of_value v)) = xs
  | [], _ => rfl
  | v :: vs, hxs => by
      rcases hxs with ⟨hv, hvs⟩
      rcases char_value_canonical hv with ⟨c, hvc, _hc⟩
      rw [hvc]
      simpa [impl_native_ssm_char_of_value] using list_typed_char_pack_unpack hvs

theorem native_pack_seq_char_append_unpack_string
    (pre suf : native_String) (ss : SmtSeq)
    (hTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    native_pack_seq SmtType.Char
        (pre.map SmtValue.Char ++ native_unpack_seq ss ++ suf.map SmtValue.Char) =
      native_pack_string (pre ++ native_unpack_string ss ++ suf) := by
  have hTyped : list_typed SmtType.Char (native_unpack_seq ss) :=
    typed_unpack_seq_of_typeof_seq_value hTy
  have hMap :
      (native_unpack_seq ss).map
          (fun v => SmtValue.Char (impl_native_ssm_char_of_value v)) =
        native_unpack_seq ss :=
    list_typed_char_pack_unpack hTyped
  have hMap' :
      List.map SmtValue.Char
          (List.map impl_native_ssm_char_of_value (native_unpack_seq ss)) =
        native_unpack_seq ss := by
    have hsimpa := hMap
    try simp [List.map_map] at hsimpa ⊢
    exact hsimpa
  unfold native_pack_string native_unpack_string
  simp only [List.map_append]
  rw [hMap']

private theorem native_str_substr_prefix_take
    (s : native_String) (idx : Nat) :
    native_str_substr s 0 (Int.ofNat idx) = s.take idx := by
  cases s with
  | nil =>
      simp [native_str_substr, native_str_len]
  | cons c cs =>
      cases idx with
      | zero =>
          simp [native_str_substr, native_str_len]
      | succ k =>
          by_cases hk : k ≤ cs.length
          · have hki : (↑k : Int) ≤ (↑cs.length : Int) :=
              Int.ofNat_le.mpr hk
            have hMinInt :
                min (↑k : Int) (↑cs.length : Int) = (↑k : Int) :=
              Int.min_eq_left hki
            simp [native_str_substr, native_str_len]
            rw [hMinInt]
            simp
          · have hkge : cs.length ≤ k := Nat.le_of_not_ge hk
            have hki : (↑cs.length : Int) ≤ (↑k : Int) :=
              Int.ofNat_le.mpr hkge
            have hMinInt :
                min (↑k : Int) (↑cs.length : Int) = (↑cs.length : Int) :=
              Int.min_eq_right hki
            have hTake : cs.take k = cs := List.take_of_length_le hkge
            simp [native_str_substr, native_str_len]
            rw [hMinInt]
            simp [hTake]

private theorem native_str_substr_suffix_drop
    (s : native_String) (start : Nat) :
    native_str_substr s (Int.ofNat start)
        (Int.ofNat s.length - Int.ofNat start + 1) =
      s.drop start := by
  unfold native_str_substr native_str_len
  by_cases hlt : start < s.length
  · have hltInt : (↑start : Int) < ↑s.length := Int.ofNat_lt.mpr hlt
    have hnot1 : ¬((↑start : Int) < 0) := by omega
    have hnot2 : ¬((↑s.length : Int) - ↑start + 1 <= 0) := by omega
    have hnot3 : ¬((↑start : Int) >= ↑s.length) := by omega
    simp [hnot1, hnot2, hnot3]
    have hMin :
        min ((↑s.length : Int) - ↑start + 1)
            ((↑s.length : Int) - ↑start) =
          (↑s.length : Int) - ↑start := by
      apply Int.min_eq_right
      omega
    rw [hMin]
    have hToNat :
        Int.toNat ((↑s.length : Int) - ↑start) = s.length - start := by
      apply Int.ofNat.inj
      change (↑(((↑s.length : Int) - ↑start).toNat) : Int) =
        ↑(s.length - start)
      rw [Int.toNat_of_nonneg]
      · rw [Int.ofNat_sub (Nat.le_of_lt hlt)]
      · omega
    rw [hToNat]
    exact List.take_of_length_le (by rw [List.length_drop]; omega)
  · have hge : s.length ≤ start := Nat.le_of_not_gt hlt
    have hdrop : s.drop start = [] := List.drop_eq_nil_of_le hge
    simp [hdrop]

private theorem smtx_model_eval_str_concat_replacement
    (M : SmtModel) (t : Term) (repl : SmtSeq)
    (pre suf : native_String)
    (hTEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq repl)
    (hReplTy : __smtx_typeof_seq_value repl = SmtType.Seq SmtType.Char) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat) (Term.String pre))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat) t)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) (Term.String suf))
                (Term.String []))))) =
      SmtValue.Seq
        (native_pack_string (pre ++ native_unpack_string repl ++ suf)) := by
  change __smtx_model_eval M
      (SmtTerm.str_concat (SmtTerm.String pre)
        (SmtTerm.str_concat (__eo_to_smt t)
          (SmtTerm.str_concat (SmtTerm.String suf) (SmtTerm.String [])))) =
    SmtValue.Seq
      (native_pack_string (pre ++ native_unpack_string repl ++ suf))
  have hElem : __smtx_elem_typeof_seq_value repl = SmtType.Char :=
    elem_typeof_seq_value_of_typeof_seq_value hReplTy
  simp [__smtx_model_eval, __smtx_model_eval_str_concat, hTEval,
    native_seq_concat, native_pack_string, Smtm.native_unpack_pack_seq,
    elem_typeof_pack_seq, hElem]
  simpa [native_pack_string, native_unpack_string, List.map_append,
    List.append_assoc] using
    native_pack_seq_char_append_unpack_string pre suf repl hReplTy

private def replace_re_match_pair (idx endIdx : Nat) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp._at__at_pair)
      (Term.Numeral (Int.ofNat idx)))
    (Term.Numeral (Int.ofNat endIdx))

private def replace_re_no_match_pair : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp._at__at_pair)
      (Term.Numeral (-1 : native_Int)))
    (Term.Numeral (-1 : native_Int))

private theorem str_first_match_rec_eq_find_aux
    (M : SmtModel) (hM : model_wf M) :
    ∀ (xs : native_String) (r rs : Term) (rv : SmtRegLan) (n : Nat),
      native_string_valid xs = true ->
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
      __smtx_typeof (__eo_to_smt rs) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt rs) =
        SmtValue.RegLan (native_re_concat rv native_re_all) ->
      __str_first_match_rec (substrWord xs 0 xs.length) r rs
          (Term.Numeral (Int.ofNat n)) ≠ Term.Stuck ->
      __str_first_match_rec (substrWord xs 0 xs.length) r rs
          (Term.Numeral (Int.ofNat n)) =
        match impl_native_re_find_idx_aux rv xs n with
        | some (idx, len) => replace_re_match_pair idx (idx + len)
        | none => replace_re_no_match_pair
  | [], r, rs, rv, n, hValid, hRTy, hREval, hRsTy, hRsEval, hNe => by
      have hRNe : r ≠ Term.Stuck := by
        intro hR
        subst r
        change __smtx_model_eval M SmtTerm.None = SmtValue.RegLan rv at hREval
        simp [__smtx_model_eval] at hREval
      have hRsNe : rs ≠ Term.Stuck := by
        intro hRs
        subst rs
        change __smtx_model_eval M SmtTerm.None =
          SmtValue.RegLan (native_re_concat rv native_re_all) at hRsEval
        simp [__smtx_model_eval] at hRsEval
      have hStep :
          __str_first_match_rec
              (substrWord ([] : native_String) 0 ([] : native_String).length) r rs
              (Term.Numeral (Int.ofNat n)) =
            __eo_ite (__str_eval_str_in_re_rec (Term.String []) rs)
              (__eo_mk_apply
                ((Term.UOp UserOp._at__at_pair).Apply
                  (Term.Numeral (Int.ofNat n)))
                (__eo_add (Term.Numeral (Int.ofNat n))
                  (__str_first_match_rec_smallest (Term.String []) r
                    (Term.Numeral 0))))
              replace_re_no_match_pair := by
        change
          __str_first_match_rec (Term.String []) r rs
              (Term.Numeral (Int.ofNat n)) =
            __eo_ite (__str_eval_str_in_re_rec (Term.String []) rs)
              (__eo_mk_apply
                ((Term.UOp UserOp._at__at_pair).Apply
                  (Term.Numeral (Int.ofNat n)))
                (__eo_add (Term.Numeral (Int.ofNat n))
                  (__str_first_match_rec_smallest (Term.String []) r
                    (Term.Numeral 0))))
              replace_re_no_match_pair
        simpa [replace_re_no_match_pair] using
          Eo.__str_first_match_rec.eq_5 r rs
            (Term.Numeral (Int.ofNat n)) hRNe hRsNe (by simp)
      have hNeIte :
          __eo_ite (__str_eval_str_in_re_rec (Term.String []) rs)
              (__eo_mk_apply
                ((Term.UOp UserOp._at__at_pair).Apply
                  (Term.Numeral (Int.ofNat n)))
                (__eo_add (Term.Numeral (Int.ofNat n))
                  (__str_first_match_rec_smallest (Term.String []) r
                    (Term.Numeral 0))))
              replace_re_no_match_pair ≠ Term.Stuck := by
        intro hStuck
        exact hNe (hStep.trans hStuck)
      have hCondNe : __str_eval_str_in_re_rec (Term.String []) rs ≠ Term.Stuck := by
        intro hCond
        rw [hCond] at hNeIte
        simp [__eo_ite, native_teq, native_ite] at hNeIte
      have hCondEq :
          __str_eval_str_in_re_rec (Term.String []) rs =
            Term.Boolean ((native_re_prefix_match_len? rv ([] : native_String)).isSome) := by
        simpa [substrWord] using
          str_eval_prefix_condition_eq M hM [] rs rv
            (by simp [native_string_valid]) hRsTy hRsEval
            (by simpa [substrWord] using hCondNe)
      cases hPref : native_re_prefix_match_len? rv ([] : native_String) with
      | none =>
          simp only [impl_native_string_to_values, List.map] at hPref
          refine hStep.trans ?_
          rw [hCondEq]
          simp only [impl_native_string_to_values, List.map]
          rw [Smtm.impl_native_re_find_idx_aux.eq_1]
          simp [hPref, __eo_ite, native_teq, native_ite]
      | some len =>
          simp only [impl_native_string_to_values, List.map] at hPref
          have hBranchNe :
              __eo_mk_apply
                  ((Term.UOp UserOp._at__at_pair).Apply
                    (Term.Numeral (Int.ofNat n)))
                  (__eo_add (Term.Numeral (Int.ofNat n))
                    (__str_first_match_rec_smallest (Term.String []) r
                      (Term.Numeral 0))) ≠ Term.Stuck := by
            rw [hCondEq] at hNeIte
            simp [hPref, __eo_ite, native_teq, native_ite] at hNeIte
            exact hNeIte
          have hSmallNe :
              __str_first_match_rec_smallest (Term.String []) r
                  (Term.Numeral 0) ≠ Term.Stuck := by
            intro hSmall
            rw [hSmall] at hBranchNe
            simp [__eo_add, __eo_mk_apply] at hBranchNe
          have hSmall :=
            str_first_match_rec_smallest_eq_go M hM [] r rv 0
              (by simp [native_string_valid]) hRTy hREval
              (by simpa [substrWord] using hSmallNe)
          have hGoPref :
              Smtm.impl_native_re_prefix_match_len_go rv ([] : native_String) 0 =
                some len := by
            simpa [Smtm.native_re_prefix_match_len?.eq_1] using hPref
          have hSmall' :
              __str_first_match_rec_smallest (Term.String []) r
                  (Term.Numeral 0) =
                match Smtm.impl_native_re_prefix_match_len_go rv ([] : native_String) 0 with
                | some endIdx => Term.Numeral (Int.ofNat endIdx)
                | none => Term.Stuck := by
            simpa [substrWord] using hSmall
          refine hStep.trans ?_
          rw [hCondEq]
          simp only [impl_native_string_to_values, List.map]
          rw [Smtm.impl_native_re_find_idx_aux.eq_1]
          simp [hPref, __eo_ite, native_teq, native_ite]
          rw [hSmall', hGoPref]
          simp [replace_re_match_pair, __eo_add, native_zplus, __eo_mk_apply]
  | c :: cs, r, rs, rv, n, hValid, hRTy, hREval, hRsTy, hRsEval, hNe => by
      rcases native_string_valid_cons_parts hValid with ⟨hc, hcs⟩
      simp [substrWord, extractString_zero_cons] at hNe ⊢
      rw [substrWord_cons_tail c cs] at hNe ⊢
      have hRNe : r ≠ Term.Stuck := by
        intro hR
        subst r
        change __smtx_model_eval M SmtTerm.None = SmtValue.RegLan rv at hREval
        simp [__smtx_model_eval] at hREval
      have hRsNe : rs ≠ Term.Stuck := by
        intro hRs
        subst rs
        change __smtx_model_eval M SmtTerm.None =
          SmtValue.RegLan (native_re_concat rv native_re_all) at hRsEval
        simp [__smtx_model_eval] at hRsEval
      have hAdd :
          __eo_add (Term.Numeral (Int.ofNat n)) (Term.Numeral 1) =
            Term.Numeral (Int.ofNat (n + 1)) := by
        simp [__eo_add, native_zplus]
      have hStep :
          __str_first_match_rec
              (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                (substrWord cs 0 cs.length)) r rs
              (Term.Numeral (Int.ofNat n)) =
            __eo_ite
              (__str_eval_str_in_re_rec
                (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                  (substrWord cs 0 cs.length)) rs)
              (__eo_mk_apply
                ((Term.UOp UserOp._at__at_pair).Apply
                  (Term.Numeral (Int.ofNat n)))
                (__eo_add (Term.Numeral (Int.ofNat n))
                  (__str_first_match_rec_smallest
                    (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                      (substrWord cs 0 cs.length)) r (Term.Numeral 0))))
              (__str_first_match_rec (substrWord cs 0 cs.length) r rs
                (Term.Numeral (Int.ofNat (n + 1)))) := by
        rw [Eo.__str_first_match_rec.eq_4 r rs
          (Term.Numeral (Int.ofNat n)) (Term.String [c])
          (substrWord cs 0 cs.length) hRNe hRsNe (by simp)]
        rw [hAdd]
      have hNeIte :
          __eo_ite
              (__str_eval_str_in_re_rec
                (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                  (substrWord cs 0 cs.length)) rs)
              (__eo_mk_apply
                ((Term.UOp UserOp._at__at_pair).Apply
                  (Term.Numeral (Int.ofNat n)))
                (__eo_add (Term.Numeral (Int.ofNat n))
                  (__str_first_match_rec_smallest
                    (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                      (substrWord cs 0 cs.length)) r (Term.Numeral 0))))
              (__str_first_match_rec (substrWord cs 0 cs.length) r rs
                (Term.Numeral (Int.ofNat (n + 1)))) ≠ Term.Stuck := by
        intro hStuck
        exact hNe (hStep.trans hStuck)
      have hCondNe :
          __str_eval_str_in_re_rec
              (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                (substrWord cs 0 cs.length)) rs ≠ Term.Stuck := by
        intro hCond
        rw [hCond] at hNeIte
        simp [__eo_ite, native_teq, native_ite] at hNeIte
      have hCondEq :
          __str_eval_str_in_re_rec
              (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                (substrWord cs 0 cs.length)) rs =
            Term.Boolean ((native_re_prefix_match_len? rv (c :: cs)).isSome) := by
        have h :=
          str_eval_prefix_condition_eq M hM (c :: cs) rs rv
            hValid hRsTy hRsEval (by
              simpa [substrWord, extractString_zero_cons,
                substrWord_cons_tail] using hCondNe)
        simpa [substrWord, extractString_zero_cons,
          substrWord_cons_tail] using h
      cases hPref : native_re_prefix_match_len? rv (c :: cs) with
      | some len =>
          have hBranchNe :
              __eo_mk_apply
                  ((Term.UOp UserOp._at__at_pair).Apply
                    (Term.Numeral (Int.ofNat n)))
                  (__eo_add (Term.Numeral (Int.ofNat n))
                    (__str_first_match_rec_smallest
                      (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                        (substrWord cs 0 cs.length)) r (Term.Numeral 0))) ≠
                Term.Stuck := by
            rw [hCondEq] at hNeIte
            simp [hPref, __eo_ite, native_teq, native_ite] at hNeIte
            exact hNeIte
          have hSmallNe :
              __str_first_match_rec_smallest
                  (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                    (substrWord cs 0 cs.length)) r (Term.Numeral 0) ≠
                Term.Stuck := by
            intro hSmall
            rw [hSmall] at hBranchNe
            simp [__eo_add, __eo_mk_apply] at hBranchNe
          have hSmall :=
            str_first_match_rec_smallest_eq_go M hM (c :: cs) r rv 0
              hValid hRTy hREval (by
                simpa [substrWord, extractString_zero_cons,
                  substrWord_cons_tail] using hSmallNe)
          have hGoPref :
              Smtm.impl_native_re_prefix_match_len_go rv (c :: cs) 0 =
                some len := by
            simpa [Smtm.native_re_prefix_match_len?.eq_1] using hPref
          have hSmall' :
              __str_first_match_rec_smallest
                  (((Term.UOp UserOp.str_concat).Apply (Term.String [c])).Apply
                    (substrWord cs 0 cs.length)) r (Term.Numeral 0) =
                match Smtm.impl_native_re_prefix_match_len_go rv (c :: cs) 0 with
                | some endIdx => Term.Numeral (Int.ofNat endIdx)
                | none => Term.Stuck := by
            simpa [substrWord, extractString_zero_cons,
              substrWord_cons_tail] using hSmall
          refine hStep.trans ?_
          rw [hCondEq]
          rw [Smtm.impl_native_re_find_idx_aux.eq_2]
          simp [hPref, __eo_ite, native_teq, native_ite]
          rw [hSmall', hGoPref]
          simp [replace_re_match_pair, __eo_add, native_zplus, __eo_mk_apply]
      | none =>
          have hTailNe :
              __str_first_match_rec (substrWord cs 0 cs.length) r rs
                  (Term.Numeral (Int.ofNat (n + 1))) ≠ Term.Stuck := by
            rw [hCondEq] at hNeIte
            simp [hPref, __eo_ite, native_teq, native_ite] at hNeIte
            exact hNeIte
          have hTail :=
            str_first_match_rec_eq_find_aux M hM cs r rs rv (n + 1)
              hcs hRTy hREval hRsTy hRsEval hTailNe
          refine hStep.trans ?_
          rw [hCondEq]
          rw [Smtm.impl_native_re_find_idx_aux.eq_2]
          simp [hPref, __eo_ite, native_teq, native_ite]
          exact hTail

private theorem str_eval_replace_re_no_match_eval
    (M : SmtModel) (str : native_String) (r t : Term)
    (hRNe : r ≠ Term.Stuck) (hTNe : t ≠ Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt
          (__str_eval_replace_re (Term.String str) r t
            replace_re_no_match_pair)) =
      SmtValue.Seq (native_pack_string str) := by
  rw [show
      __str_eval_replace_re (Term.String str) r t replace_re_no_match_pair =
        Term.String str by
    simpa [replace_re_no_match_pair] using
      Eo.__str_eval_replace_re.eq_4 (Term.String str) r t
        (by simp) hRNe hTNe]
  change __smtx_model_eval M (SmtTerm.String str) =
    SmtValue.Seq (native_pack_string str)
  exact __smtx_model_eval.eq_4 M str

private theorem str_eval_replace_re_pair_eval
    (M : SmtModel) (str : native_String) (r t : Term)
    (idx len : Nat) (repl : SmtSeq)
    (hTEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq repl)
    (hReplTy : __smtx_typeof_seq_value repl = SmtType.Seq SmtType.Char)
    (hRNe : r ≠ Term.Stuck) (hTNe : t ≠ Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt
          (__str_eval_replace_re (Term.String str) r t
            (replace_re_match_pair idx (idx + len)))) =
      SmtValue.Seq
        (native_pack_string
          (str.take idx ++ native_unpack_string repl ++ str.drop (idx + len))) := by
  have hNotNoMatch :
      Term.Numeral (Int.ofNat (idx + len)) = Term.Numeral (-1 : native_Int) ->
        Term.Numeral (Int.ofNat idx) = Term.Numeral (-1 : native_Int) ->
          False := by
    intro hEp _hSp
    cases hEp
  rw [show
      __str_eval_replace_re (Term.String str) r t
          (replace_re_match_pair idx (idx + len)) =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat)
            (__eo_extract (Term.String str) (Term.Numeral 0)
              (__eo_add (Term.Numeral (Int.ofNat idx))
                (Term.Numeral (-1 : native_Int)))))
          (__eo_mk_apply
            ((Term.UOp UserOp.str_concat).Apply t)
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.str_concat)
                (__eo_extract (Term.String str)
                  (Term.Numeral (Int.ofNat (idx + len)))
                  (__eo_len (Term.String str))))
              (Term.String []))) by
    simpa [replace_re_match_pair] using
      Eo.__str_eval_replace_re.eq_5 (Term.String str) r t
        (Term.Numeral (Int.ofNat idx))
        (Term.Numeral (Int.ofNat (idx + len)))
        hNotNoMatch (by simp) hRNe hTNe]
  simp [__eo_add, native_zplus,
    __eo_mk_apply, __eo_extract, __eo_len, native_str_len, native_zneg]
  have hPrefixArg : ((↑idx : Int) + -1 + 1) = (↑idx : Int) := by
    omega
  have hStartArg : ((↑idx : Int) + ↑len) = (↑(idx + len) : Int) := by
    rw [Int.natCast_add]
  rw [hPrefixArg, hStartArg]
  rw [show native_str_substr str 0 (↑idx : Int) = str.take idx by
    exact native_str_substr_prefix_take str idx]
  rw [show
      native_str_substr str (↑(idx + len) : Int)
          ((↑str.length : Int) + -↑(idx + len) + 1) =
        str.drop (idx + len) by
    have hsimpa := native_str_substr_suffix_drop str (idx + len); (try simp at hsimpa ⊢); exact hsimpa]
  simpa [List.append_assoc] using
    smtx_model_eval_str_concat_replacement M t repl (str.take idx)
      (str.drop (idx + len)) hTEval hReplTy

private theorem replace_re_match_ne_stuck_of_eval_ne_stuck
    (s r t m : Term)
    (hNe : __str_eval_replace_re s r t m ≠ Term.Stuck) :
    m ≠ Term.Stuck := by
  intro hm
  subst m
  cases s <;> cases r <;> cases t <;>
    simp [__str_eval_replace_re] at hNe

private theorem str_eval_replace_re_eval_eq
    (M : SmtModel) (hM : model_wf M)
    (str : native_String) (r t side : Term) (rv : SmtRegLan) (repl : SmtSeq)
    (hSTy : __smtx_typeof (__eo_to_smt (Term.String str)) =
      SmtType.Seq SmtType.Char)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hTEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq repl)
    (hReplTy : __smtx_typeof_seq_value repl = SmtType.Seq SmtType.Char)
    (hSide :
      side =
        __str_eval_replace_re (Term.String str) r t
          (__eo_requires (__eo_is_str (Term.String str)) (Term.Boolean true)
            (__str_first_match_rec (__str_flatten (__str_nary_intro (Term.String str))) r
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) (Term.UOp UserOp.re_all))
                  (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
              (Term.Numeral 0))))
    (hSideNe : side ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt side) =
      SmtValue.Seq
        (native_pack_seq SmtType.Char
          (native_str_replace_re (impl_native_string_to_values str) rv
            (native_unpack_seq repl))) := by
  have hStrValid : native_string_valid str = true :=
    native_string_valid_of_string_type hSTy
  have hRNe : r ≠ Term.Stuck := by
    intro hR
    subst r
    change __smtx_model_eval M SmtTerm.None = SmtValue.RegLan rv at hREval
    simp [__smtx_model_eval] at hREval
  have hTNe : t ≠ Term.Stuck := by
    intro hT
    subst t
    change __smtx_model_eval M SmtTerm.None = SmtValue.Seq repl at hTEval
    simp [__smtx_model_eval] at hTEval
  let rs := replace_re_search_re r
  let rawFlat :=
    __str_first_match_rec (__str_flatten (__str_nary_intro (Term.String str)))
      r rs (Term.Numeral 0)
  let matchTerm :=
    __eo_requires (__eo_is_str (Term.String str)) (Term.Boolean true) rawFlat
  have hSideEq' :
      side =
        __str_eval_replace_re (Term.String str) r t matchTerm := by
    simpa [matchTerm, rawFlat, rs, replace_re_search_re] using hSide
  have hSideNeDef :
      __str_eval_replace_re (Term.String str) r t matchTerm ≠ Term.Stuck := by
    intro hStuck
    exact hSideNe (hSideEq'.trans hStuck)
  have hMatchTermNe : matchTerm ≠ Term.Stuck :=
    replace_re_match_ne_stuck_of_eval_ne_stuck
      (Term.String str) r t matchTerm hSideNeDef
  have hMatchTermEq : matchTerm = rawFlat := by
    simp [matchTerm, rawFlat, __eo_requires, __eo_is_str,
      __eo_is_str_internal, native_ite, native_teq, native_not,
      SmtEval.native_and]
  have hRawFlatNe : rawFlat ≠ Term.Stuck := by
    simpa [hMatchTermEq] using hMatchTermNe
  have hFlatten :
      __str_flatten (__str_nary_intro (Term.String str)) =
        substrWord str 0 str.length := by
    cases str with
    | nil =>
        simpa [substrWord] using str_flatten_nary_intro_empty
    | cons c cs =>
        exact str_flatten_nary_intro_cons c cs
  have hRawFlatEqSub :
      rawFlat =
        __str_first_match_rec (substrWord str 0 str.length) r rs
          (Term.Numeral 0) := by
    simp [rawFlat, hFlatten]
  have hRawSubNe :
      __str_first_match_rec (substrWord str 0 str.length) r rs
          (Term.Numeral 0) ≠ Term.Stuck := by
    intro hStuck
    exact hRawFlatNe (hRawFlatEqSub.trans hStuck)
  have hSearch := replace_re_search_re_eval M r rv hRTy hREval
  have hRsTy : __smtx_typeof (__eo_to_smt rs) = SmtType.RegLan := by
    simpa [rs] using hSearch.1
  have hRsEval :
      __smtx_model_eval M (__eo_to_smt rs) =
        SmtValue.RegLan (native_re_concat rv native_re_all) := by
    simpa [rs] using hSearch.2
  have hMatchEval :=
    str_first_match_rec_eq_find_aux M hM str r rs rv 0
      hStrValid hRTy hREval hRsTy hRsEval hRawSubNe
  rw [hSideEq']
  rw [hMatchTermEq, hRawFlatEqSub]
  cases hFind : impl_native_re_find_idx_aux rv str 0 with
  | none =>
      have hRaw :
          __str_first_match_rec (substrWord str 0 str.length) r rs
              (Term.Numeral 0) =
            replace_re_no_match_pair := by
        simpa [hFind] using hMatchEval
      rw [hRaw]
      rw [str_eval_replace_re_no_match_eval M str r t hRNe hTNe]
      simp only [native_str_replace_re, native_re_find_idx_from, List.drop_zero]
      rw [hFind]
      rfl
  | some found =>
      rcases found with ⟨idx, len⟩
      have hRaw :
          __str_first_match_rec (substrWord str 0 str.length) r rs
              (Term.Numeral 0) =
            replace_re_match_pair idx (idx + len) := by
        simpa [hFind] using hMatchEval
      rw [hRaw]
      rw [str_eval_replace_re_pair_eval M str r t idx len repl
        hTEval hReplTy hRNe hTNe]
      simp only [native_str_replace_re, native_re_find_idx_from, List.drop_zero]
      rw [hFind]
      simp [native_pack_string, impl_native_string_to_values,
        native_unpack_seq_eq_string_to_values_of_typeof_seq_char hReplTy,
        List.map_append, List.append_assoc]

private theorem str_replace_re_eval_valid_properties
    (M : SmtModel) (hM : model_wf M)
    (s r t u : Term)
    (hArgTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) s) r) t))
          u))
    (hProgNe :
      __eo_prog_str_replace_re_eval
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) s) r) t))
          u) ≠ Term.Stuck) :
    StepRuleProperties M []
      (__eo_prog_str_replace_re_eval
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) s) r) t))
          u)) := by
  let lhs := Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) s) r) t
  let body := Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) u
  let matchRaw :=
    __str_first_match_rec (__str_flatten (__str_nary_intro s)) r
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r)
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) (Term.UOp UserOp.re_all))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
      (Term.Numeral 0)
  let matchTerm := __eo_requires (__eo_is_str s) (Term.Boolean true) matchRaw
  let side := __str_eval_replace_re s r t matchTerm
  change __eo_requires side u body ≠ Term.Stuck at hProgNe
  have hSideEqU : side = u :=
    eo_requires_eq_of_ne_stuck side u body hProgNe
  have hResult :
      __eo_requires side u body = body :=
    eo_requires_result_eq_of_ne_stuck side u body hProgNe
  have hSideNe : side ≠ Term.Stuck :=
    eo_requires_left_ne_stuck_of_ne_stuck side u body hProgNe
  have hMatchNe : matchTerm ≠ Term.Stuck :=
    replace_re_match_ne_stuck_of_eval_ne_stuck s r t matchTerm hSideNe
  have hStrReq : __eo_is_str s = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck (__eo_is_str s) (Term.Boolean true)
      matchRaw hMatchNe
  rcases eo_is_str_eq_true_cases s hStrReq with ⟨str, rfl⟩
  subst u
  have hArgTrans' :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) (Term.String str)) r)
              t))
          side) := by
    simpa [lhs, body, side] using hArgTrans
  let lhs' :=
    Term.Apply
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) (Term.String str)) r) t
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs') side) :=
    eq_has_bool_type_of_translation lhs' side (by simpa [lhs'] using hArgTrans')
  rcases
      RuleProofs.eq_operands_have_smt_translation_of_eq_has_smt_translation lhs' side
        (by simpa [lhs'] using hArgTrans') with
    ⟨hLhsTrans, _hSideTrans⟩
  rcases str_replace_re_args_smt_types_of_has_translation (Term.String str) r t
      (by simpa [lhs'] using hLhsTrans) with
    ⟨hSTy, hRTy, hTTy⟩
  rcases reglan_eval_of_type M hM r hRTy with ⟨rv, hREval⟩
  rcases seq_eval_of_type M hM t hTTy with
    ⟨repl, hTEval, hReplTy, _hReplValid⟩
  have hLeftEval :
      __smtx_model_eval M (__eo_to_smt lhs') =
        SmtValue.Seq
          (native_pack_seq SmtType.Char
            (native_str_replace_re (impl_native_string_to_values str) rv
              (native_unpack_seq repl))) := by
    change __smtx_model_eval M
        (SmtTerm.str_replace_re (SmtTerm.String str) (__eo_to_smt r) (__eo_to_smt t)) =
      SmtValue.Seq
        (native_pack_seq SmtType.Char
          (native_str_replace_re (impl_native_string_to_values str) rv
            (native_unpack_seq repl)))
    rw [__smtx_model_eval.eq_101, __smtx_model_eval.eq_4, hREval, hTEval]
    simp [__smtx_model_eval_str_replace_re,
      native_pack_string, impl_native_string_to_values,
      Smtm.native_unpack_pack_seq, elem_typeof_pack_seq]
  have hSideDef :
      side =
        __str_eval_replace_re (Term.String str) r t
          (__eo_requires (__eo_is_str (Term.String str)) (Term.Boolean true)
            (__str_first_match_rec (__str_flatten (__str_nary_intro (Term.String str))) r
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r)
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) (Term.UOp UserOp.re_all))
                  (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
              (Term.Numeral 0))) := by
    rfl
  have hSideEval :
      __smtx_model_eval M (__eo_to_smt side) =
        SmtValue.Seq
          (native_pack_seq SmtType.Char
            (native_str_replace_re (impl_native_string_to_values str) rv
              (native_unpack_seq repl))) :=
    str_eval_replace_re_eval_eq M hM str r t side rv repl hSTy hRTy hREval
      hTEval hReplTy hSideDef hSideNe
  have hResult' :
      __eo_prog_str_replace_re_eval
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) (Term.String str)) r)
              t))
          side) =
        Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs') side := by
    have hsimpa := hResult
    try simp [lhs, body, matchRaw, matchTerm, side, lhs'] at hsimpa ⊢
    exact hsimpa
  refine ⟨?_, ?_⟩
  · intro _hPremises
    rw [hResult']
    exact RuleProofs.eo_interprets_eq_of_rel M lhs' side hEqBool <| by
      rw [hLeftEval, hSideEval]
      exact RuleProofs.smt_value_rel_refl
        (SmtValue.Seq
          (native_pack_seq SmtType.Char
            (native_str_replace_re (impl_native_string_to_values str) rv
              (native_unpack_seq repl))))
  · rw [hResult']
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
      (by simpa [lhs'] using hEqBool)

theorem str_replace_re_eval_arg_properties
    (M : SmtModel) (hM : model_wf M) :
    (a1 : Term) ->
    RuleProofs.eo_has_smt_translation a1 ->
    __eo_prog_str_replace_re_eval a1 ≠ Term.Stuck ->
    StepRuleProperties M [] (__eo_prog_str_replace_re_eval a1)
  | a1, hTrans, hNe => by
      cases a1 with
      | Apply eqApp u =>
          cases eqApp with
          | Apply eqOp lhs =>
              cases eqOp with
              | UOp eqOpName =>
                  cases eqOpName with
                  | eq =>
                      cases lhs with
                      | Apply replApp t =>
                          cases replApp with
                          | Apply replApp' r =>
                              cases replApp' with
                              | Apply replOp s =>
                                  cases replOp with
                                  | UOp replOpName =>
                                      cases replOpName with
                                      | str_replace_re =>
                                          exact str_replace_re_eval_valid_properties M hM s r t u
                                            hTrans hNe
                                      | _ =>
                                          change Term.Stuck ≠ Term.Stuck at hNe
                                          exact False.elim (hNe rfl)
                                  | _ =>
                                      change Term.Stuck ≠ Term.Stuck at hNe
                                      exact False.elim (hNe rfl)
                              | _ =>
                                  change Term.Stuck ≠ Term.Stuck at hNe
                                  exact False.elim (hNe rfl)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hNe
                              exact False.elim (hNe rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hNe
                          exact False.elim (hNe rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hNe
                      exact False.elim (hNe rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hNe
                  exact False.elim (hNe rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hNe
              exact False.elim (hNe rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hNe
          exact False.elim (hNe rfl)

end RuleProofs
