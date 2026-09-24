module

public import Cpc.Proofs.RuleSupport.StrReplaceReEvalSupport
import all Cpc.Proofs.RuleSupport.StrReplaceReEvalSupport
public import Cpc.Proofs.RuleSupport.StrConcatSupport
import all Cpc.Proofs.RuleSupport.StrConcatSupport
import all Cpc.SmtModel

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

private theorem str_replace_re_all_args_smt_types_of_has_translation
    (s r t : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) s) r) t) ->
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char := by
  intro hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.str_replace_re_all (__eo_to_smt s) (__eo_to_smt r) (__eo_to_smt t)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) s) r) t)) ≠
      SmtType.None
    exact hTrans
  exact str_replace_re_args_of_non_none (op := SmtTerm.str_replace_re_all)
    (typeof_str_replace_re_all_eq (__eo_to_smt s) (__eo_to_smt r) (__eo_to_smt t)) hNN

private def replace_re_all_nonempty_re (r : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.re_inter)
        (Term.Apply (Term.UOp UserOp.re_comp)
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
      (Term.UOp UserOp.re_all))

private def filteredRe (rv : SmtRegLan) : SmtRegLan :=
  native_re_inter rv
    (native_re_inter (native_re_comp (native_str_to_re [])) native_re_all)

/-- Proof-level string view of the model's value-list replacement recursion. -/
private def impl_native_re_replace_all_nonempty_list_aux :
    Nat -> SmtRegLan -> native_String -> native_String -> native_String
  | 0, _r, _replacement, xs => xs
  | _fuel + 1, _r, _replacement, [] => []
  | fuel + 1, r, replacement, c :: cs =>
      match Smtm.native_re_positive_prefix_match_len? r
          (impl_native_string_to_values (c :: cs)) with
      | some (n + 1) =>
          replacement ++
            impl_native_re_replace_all_nonempty_list_aux fuel r replacement
              ((c :: cs).drop (n + 1))
      | _ =>
          c :: impl_native_re_replace_all_nonempty_list_aux fuel r replacement cs

private def impl_native_re_replace_all_nonempty_list
    (r : SmtRegLan) (replacement xs : native_String) : native_String :=
  impl_native_re_replace_all_nonempty_list_aux (xs.length + 1) r replacement xs

private def native_str_replace_re_all
    (s : native_String) (r : SmtRegLan) (replacement : native_String) :
    native_String :=
  impl_native_re_replace_all_nonempty_list r replacement s

private theorem native_string_to_values_replace_all_aux :
    ∀ (fuel : Nat) (r : SmtRegLan) (replacement xs : native_String),
      impl_native_string_to_values
          (impl_native_re_replace_all_nonempty_list_aux fuel r replacement xs) =
        Smtm.impl_native_re_replace_all_nonempty_list_aux fuel r
          (impl_native_string_to_values replacement) (impl_native_string_to_values xs)
  | 0, _r, _replacement, _xs => rfl
  | fuel + 1, r, replacement, [] => by
      simp [impl_native_re_replace_all_nonempty_list_aux,
        Smtm.impl_native_re_replace_all_nonempty_list_aux,
        Smtm.native_re_positive_prefix_match_len?, impl_native_string_to_values]
  | fuel + 1, r, replacement, c :: cs => by
      rw [impl_native_re_replace_all_nonempty_list_aux.eq_3]
      simp only [Smtm.impl_native_re_replace_all_nonempty_list_aux,
        impl_native_string_to_values, List.map_cons]
      cases hPref : Smtm.native_re_positive_prefix_match_len? r
          (SmtValue.Char c :: List.map SmtValue.Char cs) with
      | none =>
          simpa only [impl_native_string_to_values, List.map_cons] using
            congrArg (fun tail => SmtValue.Char c :: tail)
              (native_string_to_values_replace_all_aux fuel r replacement cs)
      | some n =>
          cases n with
          | zero =>
              simpa only [impl_native_string_to_values, List.map_cons] using
                congrArg (fun tail => SmtValue.Char c :: tail)
                  (native_string_to_values_replace_all_aux fuel r replacement cs)
          | succ n =>
              have hsimpa :=
                congrArg (fun tail => List.map SmtValue.Char replacement ++ tail)
                  (native_string_to_values_replace_all_aux fuel r replacement
                    (cs.drop n))
              try simp only [impl_native_string_to_values, List.map_append, List.map_drop] at hsimpa ⊢
              exact hsimpa

private theorem native_string_to_values_str_replace_re_all
    (s : native_String) (r : SmtRegLan) (replacement : native_String) :
    impl_native_string_to_values (native_str_replace_re_all s r replacement) =
      Smtm.native_str_replace_re_all (impl_native_string_to_values s) r
        (impl_native_string_to_values replacement) := by
  unfold native_str_replace_re_all impl_native_re_replace_all_nonempty_list
  unfold Smtm.native_str_replace_re_all
  unfold Smtm.impl_native_re_replace_all_nonempty_list
  simpa [impl_native_string_to_values] using
    native_string_to_values_replace_all_aux (s.length + 1) r replacement s

private theorem native_str_replace_re_all_string_valid
    (s replacement : native_String) (r : SmtRegLan)
    (hs : native_string_valid s = true)
    (hreplacement : native_string_valid replacement = true) :
    native_string_valid (native_str_replace_re_all s r replacement) = true := by
  have hTyped :
      list_typed SmtType.Char
        (impl_native_string_to_values (native_str_replace_re_all s r replacement)) := by
    rw [native_string_to_values_str_replace_re_all]
    exact Smtm.native_str_replace_re_all_valid r
      (char_values_of_string_typed s hs)
      (char_values_of_string_typed replacement hreplacement)
  simpa [impl_native_string_to_values, Function.comp_def,
    impl_native_ssm_char_of_value] using
    native_string_valid_of_list_typed_char hTyped

private theorem replace_re_all_nonempty_re_eval
    (M : SmtModel) (r : Term) (rv : SmtRegLan)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv) :
    __smtx_typeof (__eo_to_smt (replace_re_all_nonempty_re r)) = SmtType.RegLan ∧
      __smtx_model_eval M (__eo_to_smt (replace_re_all_nonempty_re r)) =
        SmtValue.RegLan (filteredRe rv) := by
  constructor
  · change __smtx_typeof
        (SmtTerm.re_inter (__eo_to_smt r)
          (SmtTerm.re_inter
            (SmtTerm.re_comp (SmtTerm.str_to_re (SmtTerm.String [])))
            SmtTerm.re_all)) =
      SmtType.RegLan
    simp [__smtx_typeof, hRTy, native_ite, native_Teq, native_string_valid]
  · change __smtx_model_eval M
        (SmtTerm.re_inter (__eo_to_smt r)
          (SmtTerm.re_inter
            (SmtTerm.re_comp (SmtTerm.str_to_re (SmtTerm.String [])))
            SmtTerm.re_all)) =
      SmtValue.RegLan (filteredRe rv)
    simp [filteredRe, __smtx_model_eval, __smtx_model_eval_re_inter,
      __smtx_model_eval_re_comp, __smtx_model_eval_str_to_re, hREval,
      ]

private theorem filteredRe_nullable_false (rv : SmtRegLan) :
    native_re_nullable (filteredRe rv) = false := by
  unfold filteredRe
  rw [RuleProofs.native_re_nullable_mk_inter]
  rw [RuleProofs.native_re_nullable_mk_inter]
  simp [native_re_comp, native_str_to_re,
    impl_native_re_of_list, native_re_all, native_re_nullable]

private theorem native_str_in_re_deriv_eq_cons
    (c : native_Char) (r : SmtRegLan) (ys : native_String)
    (hc : native_char_valid c = true)
    (hys : native_string_valid ys = true) :
    native_str_in_re ys (native_re_deriv c r) =
      native_str_in_re (c :: ys) r := by
  have hCons : native_string_valid (c :: ys) = true :=
    native_string_valid_cons hc hys
  simp [native_str_in_re, RuleProofs.nativeListInRe, hys, hCons]

private theorem native_re_prefix_match_len_go_shift :
    ∀ (xs : native_String) (r : SmtRegLan) (n : Nat),
      impl_native_re_prefix_match_len_go r xs n =
        (native_re_prefix_match_len? r xs).map (fun m => m + n)
  | [], r, n => by
      simp only [impl_native_string_to_values, List.map]
      rw [Smtm.impl_native_re_prefix_match_len_go.eq_1,
        Smtm.native_re_prefix_match_len?.eq_1,
        Smtm.impl_native_re_prefix_match_len_go.eq_1]
      cases native_re_nullable r <;> simp
  | c :: cs, r, n => by
      simp only [impl_native_string_to_values, List.map]
      rw [Smtm.impl_native_re_prefix_match_len_go.eq_2,
        Smtm.native_re_prefix_match_len?.eq_1,
        Smtm.impl_native_re_prefix_match_len_go.eq_2]
      cases hNull : native_re_nullable r <;> simp
      have hShiftN :=
        native_re_prefix_match_len_go_shift cs (native_re_deriv c r) (n + 1)
      have hShiftOne :=
        native_re_prefix_match_len_go_shift cs (native_re_deriv c r) 1
      simp only [impl_native_string_to_values] at hShiftN hShiftOne
      rw [hShiftN, hShiftOne]
      cases hPref : native_re_prefix_match_len? (native_re_deriv c r) cs <;>
        simp [impl_native_string_to_values] at hPref <;>
        simp [hPref, Nat.add_comm,
          Nat.add_left_comm]

private theorem native_re_prefix_match_len_eq_positive_of_not_nullable
    (r : SmtRegLan) (xs : native_String)
    (hNull : native_re_nullable r = false) :
    native_re_prefix_match_len? r xs =
      native_re_positive_prefix_match_len? r xs := by
  cases xs with
  | nil =>
      simp only [impl_native_string_to_values, List.map]
      rw [Smtm.native_re_prefix_match_len?.eq_1,
        Smtm.impl_native_re_prefix_match_len_go.eq_1]
      simp [native_re_positive_prefix_match_len?, hNull]
  | cons c cs =>
      simp only [impl_native_string_to_values, List.map]
      rw [Smtm.native_re_prefix_match_len?.eq_1,
        Smtm.impl_native_re_prefix_match_len_go.eq_2]
      simp [hNull]
      have hShift :=
        native_re_prefix_match_len_go_shift cs (native_re_deriv c r) 1
      simp only [impl_native_string_to_values] at hShift
      rw [hShift]
      cases hPref : native_re_prefix_match_len? (native_re_deriv c r) cs <;>
        simp [impl_native_string_to_values] at hPref <;>
        simp [hPref, native_re_positive_prefix_match_len?]

private theorem native_re_positive_prefix_match_len_congr_nonempty
    (r r' : SmtRegLan) :
    ∀ xs : native_String,
      native_string_valid xs = true ->
      (∀ ys : native_String,
        ys ≠ [] ->
        native_string_valid ys = true ->
          native_str_in_re ys r = native_str_in_re ys r') ->
      native_re_positive_prefix_match_len? r xs =
        native_re_positive_prefix_match_len? r' xs
  | [], _hValid, _hExt => rfl
  | c :: cs, hValid, hExt => by
      rcases native_string_valid_cons_parts hValid with ⟨hc, hcs⟩
      have hDerExt :
          ∀ ys : native_String,
            native_string_valid ys = true ->
              native_str_in_re ys (native_re_deriv c r) =
                native_str_in_re ys (native_re_deriv c r') := by
        intro ys hys
        rw [native_str_in_re_deriv_eq_cons c r ys hc hys,
          native_str_in_re_deriv_eq_cons c r' ys hc hys]
        exact hExt (c :: ys) (by simp) (native_string_valid_cons hc hys)
      have hGo :=
        CongSupport.native_re_prefix_match_len_go_congr_valid_ext_of_str_ext
          cs (native_re_deriv c r) (native_re_deriv c r') 0 hcs (by
            intro ys hys
            change RuleProofs.native_str_in_re ys (native_re_deriv c r) =
              RuleProofs.native_str_in_re ys (native_re_deriv c r')
            exact hDerExt ys hys)
      simp only [impl_native_string_to_values] at hGo
      simp only [impl_native_string_to_values, List.map,
        Smtm.native_re_positive_prefix_match_len?]
      rw [Smtm.native_re_prefix_match_len?.eq_1,
        Smtm.native_re_prefix_match_len?.eq_1, hGo]

private theorem native_re_replace_all_nonempty_list_aux_congr_nonempty :
    ∀ (fuel : Nat) (xs replacement : native_String) (r r' : SmtRegLan),
      native_string_valid xs = true ->
      (∀ ys : native_String,
        ys ≠ [] ->
        native_string_valid ys = true ->
          native_str_in_re ys r = native_str_in_re ys r') ->
      impl_native_re_replace_all_nonempty_list_aux fuel r replacement xs =
        impl_native_re_replace_all_nonempty_list_aux fuel r' replacement xs
  | 0, _xs, _replacement, _r, _r', _hValid, _hExt => rfl
  | fuel + 1, [], replacement, r, r', _hValid, _hExt => by
      rw [impl_native_re_replace_all_nonempty_list_aux.eq_2,
        impl_native_re_replace_all_nonempty_list_aux.eq_2]
  | fuel + 1, c :: cs, replacement, r, r', hValid, hExt => by
      rcases native_string_valid_cons_parts hValid with ⟨_hc, hcs⟩
      have hPref :=
        native_re_positive_prefix_match_len_congr_nonempty r r' (c :: cs)
          hValid hExt
      rw [impl_native_re_replace_all_nonempty_list_aux.eq_3,
        impl_native_re_replace_all_nonempty_list_aux.eq_3, hPref]
      cases hMatch : native_re_positive_prefix_match_len? r'
          (impl_native_string_to_values (c :: cs)) with
      | none =>
          simp
          rw [native_re_replace_all_nonempty_list_aux_congr_nonempty
            fuel cs replacement r r' hcs hExt]
      | some n =>
          cases n with
          | zero =>
              simp
              rw [native_re_replace_all_nonempty_list_aux_congr_nonempty
                fuel cs replacement r r' hcs hExt]
          | succ n =>
              simp
              exact native_re_replace_all_nonempty_list_aux_congr_nonempty
                fuel (List.drop n cs) replacement r r'
                  (Smtm.native_string_valid_drop n hcs) hExt

private theorem native_str_replace_re_all_congr_nonempty
    (s : native_String) (r r' : SmtRegLan) (replacement : native_String)
    (hValid : native_string_valid s = true)
    (hExt :
      ∀ ys : native_String,
        ys ≠ [] ->
        native_string_valid ys = true ->
          native_str_in_re ys r = native_str_in_re ys r') :
    native_str_replace_re_all s r replacement =
      native_str_replace_re_all s r' replacement := by
  unfold native_str_replace_re_all impl_native_re_replace_all_nonempty_list
  exact native_re_replace_all_nonempty_list_aux_congr_nonempty
    (s.length + 1) s replacement r r' hValid hExt

private theorem native_str_in_re_empty_re_of_nonempty
    {ys : native_String}
    (hNe : ys ≠ [])
    (hValid : native_string_valid ys = true) :
    native_str_in_re ys (native_str_to_re []) = false := by
  cases ys with
  | nil => exact False.elim (hNe rfl)
  | cons c cs =>
      simpa [native_str_in_re, hValid, native_str_to_re, impl_native_re_of_list,
        RuleProofs.nativeListInRe, native_re_deriv] using
        RuleProofs.nativeListInRe_empty cs

private theorem native_str_replace_re_all_filtered_eq
    (s : native_String) (rv : SmtRegLan) (replacement : native_String)
    (hValid : native_string_valid s = true) :
    native_str_replace_re_all s (filteredRe rv) replacement =
      native_str_replace_re_all s rv replacement := by
  apply native_str_replace_re_all_congr_nonempty _ _ _ _ hValid
  intro ys hNe hValid
  have hEmpty := native_str_in_re_empty_re_of_nonempty hNe hValid
  have hAll := RuleProofs.native_str_in_re_re_all ys hValid
  rw [filteredRe, RuleProofs.native_str_in_re_re_inter,
    RuleProofs.native_str_in_re_re_inter, RuleProofs.native_str_in_re_re_comp]
  simp [hValid, hEmpty, hAll]

private theorem native_re_replace_all_nonempty_list_aux_nil
    (fuel : Nat) (r : SmtRegLan) (replacement : native_String) :
    impl_native_re_replace_all_nonempty_list_aux fuel r replacement [] = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rw [impl_native_re_replace_all_nonempty_list_aux.eq_2]

private theorem str_concat_string_eval
    (M : SmtModel) (x y : native_String) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String x))
            (Term.String y))) =
      SmtValue.Seq (native_pack_string (x ++ y)) := by
  change __smtx_model_eval M
      (SmtTerm.str_concat (SmtTerm.String x) (SmtTerm.String y)) =
    SmtValue.Seq (native_pack_string (x ++ y))
  simp [__smtx_model_eval, __smtx_model_eval_str_concat,
    native_seq_concat, native_pack_string, Smtm.native_unpack_pack_seq,
    elem_typeof_pack_seq, List.map_append]

private theorem str_concat_eval_string_left
    (M : SmtModel) (x y : Term) (sx sy : native_String)
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Seq (native_pack_string sy))
    (hx : x = Term.String sx) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y)) =
      SmtValue.Seq (native_pack_string (sx ++ sy)) := by
  subst x
  change __smtx_model_eval M
      (SmtTerm.str_concat (SmtTerm.String sx) (__eo_to_smt y)) =
    SmtValue.Seq (native_pack_string (sx ++ sy))
  simp [__smtx_model_eval, __smtx_model_eval_str_concat, hy,
    native_seq_concat, native_pack_string, Smtm.native_unpack_pack_seq,
    elem_typeof_pack_seq, List.map_append]

private theorem str_concat_eval_replacement_left
    (M : SmtModel) (t y : Term) (repl : SmtSeq) (sy : native_String)
    (hTEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq repl)
    (hReplTy : __smtx_typeof_seq_value repl = SmtType.Seq SmtType.Char)
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Seq (native_pack_string sy)) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) y)) =
      SmtValue.Seq (native_pack_string (native_unpack_string repl ++ sy)) := by
  change __smtx_model_eval M
      (SmtTerm.str_concat (__eo_to_smt t) (__eo_to_smt y)) =
    SmtValue.Seq (native_pack_string (native_unpack_string repl ++ sy))
  have hElem : __smtx_elem_typeof_seq_value repl = SmtType.Char :=
    elem_typeof_seq_value_of_typeof_seq_value hReplTy
  simp [__smtx_model_eval, __smtx_model_eval_str_concat, hTEval, hy,
    native_seq_concat, native_pack_string, Smtm.native_unpack_pack_seq, hElem]
  simpa [native_pack_string, List.append_assoc] using
    native_pack_seq_char_append_unpack_string [] sy repl hReplTy

private theorem str_eval_replace_re_all_rec_properties
    (M : SmtModel) (hM : model_wf M) :
    ∀ (xs acc : native_String) (fuel skip : Nat)
      (r : Term) (rv : SmtRegLan) (t : Term) (repl : SmtSeq),
      native_string_valid xs = true ->
      native_string_valid acc = true ->
      xs.length + 1 ≤ fuel + skip ->
      native_re_nullable rv = false ->
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
      __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char ->
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq repl ->
      __smtx_typeof_seq_value repl = SmtType.Seq SmtType.Char ->
      __str_eval_replace_re_all_rec (substrWord xs 0 xs.length) (Term.String acc)
          r t (Term.Numeral (Int.ofNat skip)) ≠ Term.Stuck ->
        __eo_is_list (Term.UOp UserOp.str_concat)
            (__str_eval_replace_re_all_rec (substrWord xs 0 xs.length) (Term.String acc)
              r t (Term.Numeral (Int.ofNat skip))) =
          Term.Boolean true ∧
        __smtx_typeof
            (__eo_to_smt
              (__str_eval_replace_re_all_rec (substrWord xs 0 xs.length) (Term.String acc)
                r t (Term.Numeral (Int.ofNat skip)))) =
          SmtType.Seq SmtType.Char ∧
        __smtx_model_eval M
            (__eo_to_smt
              (__str_eval_replace_re_all_rec (substrWord xs 0 xs.length) (Term.String acc)
                r t (Term.Numeral (Int.ofNat skip)))) =
          SmtValue.Seq
            (native_pack_string
              (acc ++ impl_native_re_replace_all_nonempty_list_aux fuel rv
                (native_unpack_string repl) (xs.drop skip)))
  | [], acc, fuel, skip, r, rv, t, repl, _hValid, hAccValid, _hFuel, _hNull,
      _hRTy, hREval, _hTTy, hTEval, _hReplTy, _hRawNe => by
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
      have hAux : impl_native_re_replace_all_nonempty_list_aux fuel rv
          (native_unpack_string repl) ([] : native_String) = [] :=
        native_re_replace_all_nonempty_list_aux_nil fuel rv (native_unpack_string repl)
      by_cases hAcc : acc = []
      · subst acc
        have hRawEq :
            __str_eval_replace_re_all_rec
                (substrWord ([] : native_String) 0 ([] : native_String).length)
                (Term.String []) r t (Term.Numeral (Int.ofNat skip)) =
              Term.String [] := by
          change __str_eval_replace_re_all_rec (Term.String [])
              (Term.String []) r t (Term.Numeral (Int.ofNat skip)) =
            Term.String []
          rw [Eo.__str_eval_replace_re_all_rec.eq_5
            (Term.String []) r t (Term.Numeral (Int.ofNat skip))
            (by simp) hRNe hTNe (by simp)]
          simp [__eo_eq, __eo_ite, native_ite, native_teq]
        rw [hRawEq]
        constructor
        · simp [__eo_is_list, __eo_get_nil_rec, __eo_requires, __eo_is_list_nil,
            __eo_is_list_nil_str_concat, __eo_is_ok, __eo_eq, native_ite,
            native_teq, SmtEval.native_not]
        constructor
        · change __smtx_typeof (SmtTerm.String []) = SmtType.Seq SmtType.Char
          simp [__smtx_typeof, native_string_valid, native_ite]
        · simp only [List.drop_nil, List.nil_append]
          rw [native_re_replace_all_nonempty_list_aux_nil]
          change __smtx_model_eval M (SmtTerm.String []) =
            SmtValue.Seq (native_pack_string [])
          simp [__smtx_model_eval, native_pack_string]
      · have hEqFalse :
            __eo_eq (Term.String acc) (Term.String []) = Term.Boolean false := by
          simp [__eo_eq, native_teq, hAcc]
        have hRawEq :
            __str_eval_replace_re_all_rec
                (substrWord ([] : native_String) 0 ([] : native_String).length)
                (Term.String acc) r t (Term.Numeral (Int.ofNat skip)) =
              Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String acc))
                (Term.String []) := by
          change __str_eval_replace_re_all_rec (Term.String [])
              (Term.String acc) r t (Term.Numeral (Int.ofNat skip)) =
            Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String acc))
              (Term.String [])
          rw [Eo.__str_eval_replace_re_all_rec.eq_5
            (Term.String acc) r t (Term.Numeral (Int.ofNat skip))
            (by simp) hRNe hTNe (by simp)]
          simp [hEqFalse, __eo_ite, native_ite, native_teq]
        rw [hRawEq]
        constructor
        · simp [__eo_is_list, __eo_get_nil_rec, __eo_requires, __eo_is_list_nil,
            __eo_is_list_nil_str_concat, __eo_is_ok, __eo_eq, native_ite,
            native_teq, SmtEval.native_not]
        constructor
        · change __smtx_typeof
              (SmtTerm.str_concat (SmtTerm.String acc) (SmtTerm.String [])) =
            SmtType.Seq SmtType.Char
          have hAccAll : ∀ x ∈ acc, native_char_valid x = true := by
            simpa [native_string_valid, List.all_eq_true] using hAccValid
          have hAccList : List.all acc native_char_valid = true := by
            simpa [native_string_valid] using hAccValid
          simp only [__smtx_typeof, native_string_valid]
          rw [hAccList]
          simp [__smtx_typeof_seq_op_2, native_ite, native_Teq]
        · rw [str_concat_string_eval M acc []]
          simp [hAux]
  | c :: cs, acc, fuel, skip, r, rv, t, repl, hValid, hAccValid, hFuel, hNull,
      hRTy, hREval, hTTy, hTEval, hReplTy, hRawNe => by
      rcases native_string_valid_cons_parts hValid with ⟨hc, hcs⟩
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
      cases skip with
      | succ k =>
          have hAdd :
              __eo_add (Term.Numeral (Int.ofNat (k + 1)))
                  (Term.Numeral (-1 : native_Int)) =
                Term.Numeral (Int.ofNat k) := by
            change Term.Numeral ((Int.ofNat (k + 1)) + (-1 : Int)) =
              Term.Numeral (Int.ofNat k)
            congr
            simpa [Int.ofNat_eq_natCast, Int.natCast_succ]
              using Int.add_neg_cancel_right (Int.ofNat k) 1
          have hRawEq :
              __str_eval_replace_re_all_rec
                  (substrWord (c :: cs) 0 (c :: cs).length) (Term.String acc)
                  r t (Term.Numeral (Int.ofNat (k + 1))) =
                __str_eval_replace_re_all_rec (substrWord cs 0 cs.length)
                  (Term.String acc) r t (Term.Numeral (Int.ofNat k)) := by
            have hSub :
                substrWord (c :: cs) 0 (c :: cs).length =
                  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                    (substrWord cs 0 cs.length) := by
              simp [substrWord, extractString_zero_cons]
              rw [substrWord_cons_tail c cs]
            rw [hSub]
            rw [Eo.__str_eval_replace_re_all_rec.eq_7
              (Term.String acc) r t (Term.Numeral (Int.ofNat (k + 1)))
              (Term.String [c]) (substrWord cs 0 cs.length)
              (by simp) hRNe hTNe (by simp) (by
                intro h
                injection h with hInt
                have hNonzero : Int.ofNat (k + 1) ≠ 0 := by
                  rw [Int.ofNat_eq_natCast]
                  exact Int.natCast_ne_zero.mpr (Nat.succ_ne_zero k)
                exact hNonzero hInt)]
            rw [hAdd]
          have hTailNe :
              __str_eval_replace_re_all_rec (substrWord cs 0 cs.length)
                  (Term.String acc) r t (Term.Numeral (Int.ofNat k)) ≠
                Term.Stuck := by
            intro hStuck
            exact hRawNe (hRawEq.trans hStuck)
          have hFuelTail : cs.length + 1 ≤ fuel + k := by
            have hFuel' : (cs.length + 1) + 1 ≤ (fuel + k) + 1 := by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hFuel
            exact Nat.succ_le_succ_iff.mp hFuel'
          have hIH :=
            str_eval_replace_re_all_rec_properties M hM cs acc fuel k r rv t repl
              hcs hAccValid hFuelTail hNull hRTy hREval hTTy hTEval hReplTy hTailNe
          rw [hRawEq]
          simpa using hIH
      | zero =>
          cases fuel with
          | zero =>
              have : False := by
                simp at hFuel
              exact False.elim this
          | succ fuel' =>
              simp [substrWord, extractString_zero_cons] at hRawNe ⊢
              rw [substrWord_cons_tail c cs] at hRawNe ⊢
              let word :=
                Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                  (substrWord cs 0 cs.length)
              let rs := replace_re_search_re r
              let cond := __str_eval_str_in_re_rec word rs
              let small := __str_first_match_rec_smallest word r (Term.Numeral 0)
              let v1 := __eo_ite cond small (Term.Numeral (-1 : native_Int))
              let noMatch :=
                __str_eval_replace_re_all_rec (substrWord cs 0 cs.length)
                  (__eo_concat (Term.String acc) (Term.String [c])) r t (Term.Numeral 0)
              let matchBranch :=
                __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String acc))
                  (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                    (__str_eval_replace_re_all_rec (substrWord cs 0 cs.length)
                      (Term.String []) r t
                      (__eo_add v1 (Term.Numeral (-1 : native_Int)))))
              have hRawStep :
                  __str_eval_replace_re_all_rec word (Term.String acc) r t
                      (Term.Numeral 0) =
                    __eo_ite (__eo_eq v1 (Term.Numeral (-1 : native_Int)))
                      noMatch matchBranch := by
                rw [Eo.__str_eval_replace_re_all_rec.eq_6
                  (Term.String acc) r t (Term.String [c])
                  (substrWord cs 0 cs.length)
                  (by simp) hRNe hTNe]
                rfl
              have hRawNeWord :
                  __str_eval_replace_re_all_rec word (Term.String acc) r t
                      (Term.Numeral 0) ≠ Term.Stuck := by
                simpa [word] using hRawNe
              have hCondNe : cond ≠ Term.Stuck := by
                intro hCond
                have hv1 : v1 = Term.Stuck := by
                  simp [v1, hCond, native_ite, native_teq]
                have hEq : __eo_eq v1 (Term.Numeral (-1 : native_Int)) = Term.Stuck := by
                  simp [hv1, __eo_eq]
                have hStuck :
                    __str_eval_replace_re_all_rec word (Term.String acc) r t
                        (Term.Numeral 0) = Term.Stuck := by
                  rw [hRawStep, hEq]
                  simp [__eo_ite, native_ite, native_teq]
                exact hRawNeWord hStuck
              have hSearch := replace_re_search_re_eval M r rv hRTy hREval
              have hCondEq :
                  cond =
                    Term.Boolean ((native_re_prefix_match_len? rv (c :: cs)).isSome) := by
                have h :=
                  str_eval_prefix_condition_eq M hM (c :: cs) rs rv hValid
                    (by simpa [rs] using hSearch.1)
                    (by simpa [rs] using hSearch.2)
                    (by simpa [word, substrWord, extractString_zero_cons,
                      substrWord_cons_tail] using hCondNe)
                simpa [cond, word, substrWord, extractString_zero_cons,
                  substrWord_cons_tail] using h
              have hPrefixPositive :
                  native_re_prefix_match_len? rv (c :: cs) =
                    native_re_positive_prefix_match_len? rv (c :: cs) :=
                native_re_prefix_match_len_eq_positive_of_not_nullable rv (c :: cs) hNull
              cases hPref : native_re_positive_prefix_match_len? rv (c :: cs) with
              | none =>
                  have hCondFalse : cond = Term.Boolean false := by
                    rw [hCondEq, hPrefixPositive, hPref]
                    simp
                  have hv1 : v1 = Term.Numeral (-1 : native_Int) := by
                    simp [v1, hCondFalse, native_ite, native_teq]
                  have hEqTrue :
                      __eo_eq v1 (Term.Numeral (-1 : native_Int)) =
                        Term.Boolean true := by
                    simp [hv1, __eo_eq, native_teq]
                  have hRawNo :
                      __str_eval_replace_re_all_rec word (Term.String acc) r t
                          (Term.Numeral 0) = noMatch := by
                    rw [hRawStep, hEqTrue]
                    simp [__eo_ite, native_ite, native_teq]
                  have hNoNe : noMatch ≠ Term.Stuck := by
                    intro hStuck
                    exact hRawNeWord (hRawNo.trans hStuck)
                  have hAccCharValid :
                      native_string_valid (acc ++ [c]) = true := by
                    exact native_string_valid_append hAccValid
                      (native_string_valid_cons hc (by simp [native_string_valid]))
                  have hNoMatchTerm :
                      noMatch =
                        __str_eval_replace_re_all_rec (substrWord cs 0 cs.length)
                          (Term.String (acc ++ [c])) r t (Term.Numeral 0) := by
                    simp [noMatch, __eo_concat, native_str_concat]
                  have hFuelTail : cs.length + 1 ≤ fuel' + 0 := by
                    simpa using hFuel
                  have hIH :=
                    str_eval_replace_re_all_rec_properties M hM cs (acc ++ [c])
                      fuel' 0 r rv t repl hcs hAccCharValid hFuelTail hNull hRTy
                      hREval hTTy hTEval hReplTy (by
                        simpa [hNoMatchTerm] using hNoNe)
                  have hAuxUnfold :
                      impl_native_re_replace_all_nonempty_list_aux (fuel' + 1) rv
                          (native_unpack_string repl) (c :: cs) =
                        c :: impl_native_re_replace_all_nonempty_list_aux fuel' rv
                          (native_unpack_string repl) cs := by
                    have hPref' :
                        native_re_positive_prefix_match_len? rv
                            (impl_native_string_to_values (c :: cs)) = none := by
                      simpa [impl_native_string_to_values] using hPref
                    rw [impl_native_re_replace_all_nonempty_list_aux.eq_3, hPref']
                  rw [hRawNo, hNoMatchTerm]
                  constructor
                  · exact hIH.1
                  constructor
                  · exact hIH.2.1
                  · have hIHEval :
                        __smtx_model_eval M
                            (__eo_to_smt
                              (__str_eval_replace_re_all_rec
                                (substrWord cs 0 cs.length) (Term.String (acc ++ [c]))
                                r t (Term.Numeral 0))) =
                          SmtValue.Seq
                            (native_pack_string
                              (acc ++ [c] ++
                                impl_native_re_replace_all_nonempty_list_aux fuel' rv
                                  (native_unpack_string repl) (List.drop 0 cs))) := by
                      simpa using hIH.2.2
                    rw [hIHEval, hAuxUnfold]
                    simp [List.append_assoc]
              | some len =>
                  cases len with
                  | zero =>
                      simp [native_re_positive_prefix_match_len?] at hPref
                      cases hDerPref :
                          native_re_prefix_match_len? (native_re_deriv c rv) cs <;>
                        simp [hDerPref] at hPref
                  | succ n =>
                      have hCondTrue : cond = Term.Boolean true := by
                        rw [hCondEq, hPrefixPositive, hPref]
                        simp
                      have hSmallNe : small ≠ Term.Stuck := by
                        intro hSmall
                        have hv1 : v1 = Term.Stuck := by
                          simp [v1, hCondTrue, hSmall, native_ite, native_teq]
                        have hEq : __eo_eq v1 (Term.Numeral (-1 : native_Int)) = Term.Stuck := by
                          simp [hv1, __eo_eq]
                        have hStuck :
                            __str_eval_replace_re_all_rec word (Term.String acc) r t
                                (Term.Numeral 0) = Term.Stuck := by
                          rw [hRawStep, hEq]
                          simp [__eo_ite, native_ite, native_teq]
                        exact hRawNeWord hStuck
                      have hSmallEq :
                          small = Term.Numeral (Int.ofNat (n + 1)) := by
                        have hSmallEval :=
                          str_first_match_rec_smallest_eq_go M hM (c :: cs) r rv 0
                            hValid hRTy hREval (by
                              simpa [small, word, substrWord, extractString_zero_cons,
                                substrWord_cons_tail] using hSmallNe)
                        have hGo :
                            impl_native_re_prefix_match_len_go rv (c :: cs) 0 =
                              some (n + 1) := by
                          have hPrefixSome :
                              native_re_prefix_match_len? rv (c :: cs) =
                                some (n + 1) := by
                            rw [hPrefixPositive, hPref]
                          simpa [Smtm.native_re_prefix_match_len?.eq_1]
                            using hPrefixSome
                        simpa [small, word, substrWord, extractString_zero_cons,
                          substrWord_cons_tail, hGo] using hSmallEval
                      have hv1 : v1 = Term.Numeral (Int.ofNat (n + 1)) := by
                        simp [v1, hCondTrue, hSmallEq, native_ite,
                          native_teq]
                      have hEqFalse :
                          __eo_eq v1 (Term.Numeral (-1 : native_Int)) =
                            Term.Boolean false := by
                        have hNe : Int.ofNat (n + 1) ≠ (-1 : Int) := by
                          simp only [Int.ofNat_eq_natCast, Int.natCast_add,
                            Int.natCast_one]
                          omega
                        have hNe' : (-1 : Int) ≠ Int.ofNat (n + 1) := hNe.symm
                        have hNe'' : (-1 : Int) ≠ Int.ofNat n + 1 := by
                          simpa [Int.ofNat_eq_natCast, Int.natCast_succ] using hNe'
                        have hNeNat : (-1 : Int) ≠ (n : Int) + 1 := by
                          simpa [Int.ofNat_eq_natCast] using hNe''
                        simp [hv1, __eo_eq, native_teq,
                          hNeNat]
                      have hSkip :
                          __eo_add v1 (Term.Numeral (-1 : native_Int)) =
                            Term.Numeral (Int.ofNat n) := by
                        rw [hv1]
                        change Term.Numeral ((Int.ofNat (n + 1)) + (-1 : Int)) =
                          Term.Numeral (Int.ofNat n)
                        congr
                        simpa [Int.ofNat_eq_natCast, Int.natCast_succ]
                          using Int.add_neg_cancel_right (Int.ofNat n) 1
                      have hRawMatch :
                          __str_eval_replace_re_all_rec word (Term.String acc) r t
                              (Term.Numeral 0) = matchBranch := by
                        rw [hRawStep, hEqFalse]
                        simp [__eo_ite, native_ite, native_teq]
                      have hMatchNe : matchBranch ≠ Term.Stuck := by
                        intro hStuck
                        exact hRawNeWord (hRawMatch.trans hStuck)
                      let tail :=
                        __str_eval_replace_re_all_rec (substrWord cs 0 cs.length)
                          (Term.String []) r t (Term.Numeral (Int.ofNat n))
                      have hMatchBranchMk :
                          matchBranch =
                            __eo_mk_apply
                              (Term.Apply (Term.UOp UserOp.str_concat) (Term.String acc))
                              (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                                tail) := by
                        simp [matchBranch, tail, hSkip]
                      have hInnerNe :
                          __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                              tail ≠ Term.Stuck :=
                        eo_mk_apply_arg_ne_stuck_of_ne_stuck
                          (Term.Apply (Term.UOp UserOp.str_concat) (Term.String acc))
                          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) t) tail)
                          (by simpa [hMatchBranchMk] using hMatchNe)
                      have hTailNe : tail ≠ Term.Stuck := by
                        exact eo_mk_apply_arg_ne_stuck_of_ne_stuck
                          (Term.Apply (Term.UOp UserOp.str_concat) t) tail hInnerNe
                      have hMatchBranchEq :
                          matchBranch =
                            Term.Apply
                              (Term.Apply (Term.UOp UserOp.str_concat) (Term.String acc))
                              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) tail) := by
                        have hOuterMkNe :
                            __eo_mk_apply
                                (Term.Apply (Term.UOp UserOp.str_concat) (Term.String acc))
                                (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                                  tail) ≠ Term.Stuck := by
                          simpa [hMatchBranchMk] using hMatchNe
                        have hInnerEq :
                            __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                                tail =
                              Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                                tail :=
                          eo_mk_apply_eq_apply_of_ne_stuck
                            (Term.Apply (Term.UOp UserOp.str_concat) t) tail hInnerNe
                        have hOuterMkNe' :
                            __eo_mk_apply
                                (Term.Apply (Term.UOp UserOp.str_concat) (Term.String acc))
                                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                                  tail) ≠ Term.Stuck := by
                          simpa [← hInnerEq] using hOuterMkNe
                        rw [hMatchBranchMk]
                        rw [hInnerEq]
                        rw [eo_mk_apply_eq_apply_of_ne_stuck
                          (Term.Apply (Term.UOp UserOp.str_concat) (Term.String acc))
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) tail)
                          hOuterMkNe']
                      have hFuelTail : cs.length + 1 ≤ fuel' + n := by
                        have hBase : cs.length + 1 ≤ fuel' := by
                          have hFuel' : (cs.length + 1) + 1 ≤ fuel' + 1 := by
                            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hFuel
                          exact Nat.succ_le_succ_iff.mp hFuel'
                        exact Nat.le_trans hBase (Nat.le_add_right fuel' n)
                      have hIH :=
                        str_eval_replace_re_all_rec_properties M hM cs [] fuel' n
                          r rv t repl hcs (by simp [native_string_valid])
                          hFuelTail hNull hRTy hREval hTTy hTEval hReplTy hTailNe
                      have hAuxUnfold :
                          impl_native_re_replace_all_nonempty_list_aux (fuel' + 1) rv
                              (native_unpack_string repl) (c :: cs) =
                            native_unpack_string repl ++
                              impl_native_re_replace_all_nonempty_list_aux fuel' rv
                                (native_unpack_string repl) (cs.drop n) := by
                        have hPref' :
                            native_re_positive_prefix_match_len? rv
                                (impl_native_string_to_values (c :: cs)) =
                              some (n + 1) := by
                          simpa [impl_native_string_to_values] using hPref
                        rw [impl_native_re_replace_all_nonempty_list_aux.eq_3, hPref']
                        rfl
                      rw [hRawMatch, hMatchBranchEq]
                      constructor
                      · apply strConcat_is_list_cons_true_of_tail_list
                        apply strConcat_is_list_cons_true_of_tail_list
                        exact hIH.1
                      constructor
                      · have hTailTy := hIH.2.1
                        have hInnerTy :
                            __smtx_typeof
                                (__eo_to_smt
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) tail)) =
                              SmtType.Seq SmtType.Char :=
                          strConcat_typeof_concat_of_seq t tail
                            SmtType.Char hTTy hTailTy
                        exact strConcat_typeof_concat_of_seq
                          (Term.String acc)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) tail)
                          SmtType.Char
                          (by
                            change __smtx_typeof (SmtTerm.String acc) =
                              SmtType.Seq SmtType.Char
                            simp [__smtx_typeof, hAccValid, native_ite])
                          hInnerTy
                      · have hTailEval := hIH.2.2
                        have hInnerEval :
                            __smtx_model_eval M
                                (__eo_to_smt
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) tail)) =
                              SmtValue.Seq
                                (native_pack_string
                                  (native_unpack_string repl ++
                                    impl_native_re_replace_all_nonempty_list_aux fuel' rv
                                      (native_unpack_string repl) (cs.drop n))) := by
                          simpa using
                            str_concat_eval_replacement_left M t tail repl
                              (impl_native_re_replace_all_nonempty_list_aux fuel' rv
                                (native_unpack_string repl) (cs.drop n))
                              hTEval hReplTy (by have hsimpa := hTailEval; (try simp at hsimpa ⊢); exact hsimpa)
                        have hOuter :
                            __smtx_model_eval M
                                (__eo_to_smt
                                  (Term.Apply
                                    (Term.Apply (Term.UOp UserOp.str_concat)
                                      (Term.String acc))
                                    (Term.Apply
                                      (Term.Apply (Term.UOp UserOp.str_concat) t)
                                      tail))) =
                              SmtValue.Seq
                                (native_pack_string
                                  (acc ++
                                    (native_unpack_string repl ++
                                      impl_native_re_replace_all_nonempty_list_aux fuel' rv
                                        (native_unpack_string repl) (cs.drop n)))) := by
                          exact
                            str_concat_eval_string_left M (Term.String acc)
                              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t) tail)
                              acc
                              (native_unpack_string repl ++
                                impl_native_re_replace_all_nonempty_list_aux fuel' rv
                                  (native_unpack_string repl) (cs.drop n))
                              hInnerEval rfl
                        rw [hOuter, hAuxUnfold]
                        try simp [List.append_assoc]

private theorem list_singleton_elim_arg_ne_stuck_of_ne_stuck
    (f a : Term)
    (hNe : __eo_list_singleton_elim f a ≠ Term.Stuck) :
    a ≠ Term.Stuck := by
  intro hA
  subst a
  cases f <;> simp [__eo_list_singleton_elim, __eo_is_list, __eo_requires, native_ite, native_teq] at hNe

private theorem term_ne_stuck_of_smt_seq_type_local
    {t : Term} {T : SmtType}
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T) :
    t ≠ Term.Stuck := by
  intro h
  subst t
  change __smtx_typeof SmtTerm.None = SmtType.Seq T at hTy
  simp at hTy

private theorem strConcat_singleton_elim_rel
    (M : SmtModel) (hM : model_wf M) (c : Term) (T : SmtType) :
    __eo_is_list (Term.UOp UserOp.str_concat) c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.Seq T ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.str_concat) c)))
      (__smtx_model_eval M (__eo_to_smt c)) := by
  intro hList hcTy
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))))
    (__smtx_model_eval M (__eo_to_smt c))
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg :
              g = Term.UOp UserOp.str_concat :=
            strConcat_is_list_cons_head_eq_of_true g head tail hList
          subst g
          have hTailList :
              __eo_is_list (Term.UOp UserOp.str_concat) tail =
                Term.Boolean true :=
            strConcat_is_list_tail_true_of_cons_self head tail hList
          have hTypes := strConcat_args_of_seq_type head tail T hcTy
          cases hNil : __eo_is_list_nil (Term.UOp UserOp.str_concat) tail
          all_goals
            simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite,
              native_teq]
          case Boolean b =>
            cases b
            · exact RuleProofs.smt_value_rel_refl
                (__smtx_model_eval M (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head) tail)))
            · exact RuleProofs.smt_value_rel_symm
                (__smtx_model_eval M (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) head) tail)))
                (__smtx_model_eval M (__eo_to_smt head))
                (strConcat_smt_value_rel_list_nil_right_empty M hM
                  head tail T hTypes.1 hNil hTypes.2)
          all_goals
            have hTailNe : tail ≠ Term.Stuck :=
              term_ne_stuck_of_smt_seq_type_local hTypes.2
            cases tail <;>
              simp [__eo_is_list_nil, __eo_is_list_nil_str_concat,
                __eo_eq, native_teq] at hNil hTailNe
            case UOp1 op A =>
              cases op <;> simp at hNil
      | _ =>
          simpa [__eo_list_singleton_elim_2] using
            RuleProofs.smt_value_rel_refl _
  | _ =>
      simpa [__eo_list_singleton_elim_2] using
        RuleProofs.smt_value_rel_refl _

private theorem str_replace_re_all_eval_valid_properties
    (M : SmtModel) (hM : model_wf M)
    (s r t u : Term)
    (hArgTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) s) r) t))
          u))
    (hProgNe :
      __eo_prog_str_replace_re_all_eval
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) s) r) t))
          u) ≠ Term.Stuck) :
    StepRuleProperties M []
      (__eo_prog_str_replace_re_all_eval
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) s) r) t))
          u)) := by
  let lhs := Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) s) r) t
  let body := Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) u
  let rNonempty := replace_re_all_nonempty_re r
  let raw :=
    __str_eval_replace_re_all_rec (__str_flatten (__str_nary_intro s)) (Term.String [])
      rNonempty t (Term.Numeral 0)
  let side := __eo_list_singleton_elim (Term.UOp UserOp.str_concat) raw
  let inner := __eo_requires side u body
  change __eo_requires (__eo_is_str s) (Term.Boolean true) inner ≠ Term.Stuck at hProgNe
  have hStrReq : __eo_is_str s = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck (__eo_is_str s) (Term.Boolean true) inner
      hProgNe
  have hInnerNe : inner ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck (__eo_is_str s)
      (Term.Boolean true) inner hProgNe
  change __eo_requires side u body ≠ Term.Stuck at hInnerNe
  have hSideEqU : side = u :=
    eo_requires_eq_of_ne_stuck side u body hInnerNe
  have hInnerResult : inner = body := by
    change __eo_requires side u body = body
    exact eo_requires_result_eq_of_ne_stuck side u body hInnerNe
  have hOuterResult :
      __eo_requires (__eo_is_str s) (Term.Boolean true) inner = inner :=
    eo_requires_result_eq_of_ne_stuck (__eo_is_str s) (Term.Boolean true)
      inner hProgNe
  have hResult :
      __eo_requires (__eo_is_str s) (Term.Boolean true) inner = body := by
    rw [hOuterResult, hInnerResult]
  have hSideNe : side ≠ Term.Stuck :=
    eo_requires_left_ne_stuck_of_ne_stuck side u body hInnerNe
  have hRawNe : raw ≠ Term.Stuck :=
    list_singleton_elim_arg_ne_stuck_of_ne_stuck
      (Term.UOp UserOp.str_concat) raw hSideNe
  subst u
  have hArgTrans' :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) side) := by
    simpa [lhs, body, side] using hArgTrans
  let lhs' := lhs
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs') side) :=
    eq_has_bool_type_of_translation lhs' side (by simpa [lhs'] using hArgTrans')
  rcases
      RuleProofs.eq_operands_have_smt_translation_of_eq_has_smt_translation lhs' side
        (by simpa [lhs'] using hArgTrans') with
    ⟨hLhsTrans, _hSideTrans⟩
  rcases str_replace_re_all_args_smt_types_of_has_translation s r t
      (by simpa [lhs, lhs'] using hLhsTrans) with
    ⟨hSTy, hRTy, hTTy⟩
  rcases seq_eval_of_type M hM s hSTy with ⟨src, hSEval, hSrcTy, hSrcValid⟩
  rcases reglan_eval_of_type M hM r hRTy with ⟨rv, hREval⟩
  rcases seq_eval_of_type M hM t hTTy with
    ⟨repl, hTEval, hReplTy, _hReplValid⟩
  have hLeftEval :
      __smtx_model_eval M (__eo_to_smt lhs') =
        SmtValue.Seq
          (native_pack_string
            (native_str_replace_re_all (native_unpack_string src) rv
              (native_unpack_string repl))) := by
    change __smtx_model_eval M
        (SmtTerm.str_replace_re_all (__eo_to_smt s) (__eo_to_smt r) (__eo_to_smt t)) =
      SmtValue.Seq
        (native_pack_string
          (native_str_replace_re_all (native_unpack_string src) rv
            (native_unpack_string repl)))
    rw [__smtx_model_eval.eq_102, hSEval, hREval, hTEval]
    simp only [__smtx_model_eval_str_replace_re_all]
    have hSrcElem : __smtx_elem_typeof_seq_value src = SmtType.Char :=
      elem_typeof_seq_value_of_typeof_seq_value hSrcTy
    rw [hSrcElem,
      native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSrcTy,
      native_unpack_seq_eq_string_to_values_of_typeof_seq_char hReplTy,
      ← native_string_to_values_str_replace_re_all]
    rfl
  rcases eo_is_str_eq_true_cases s hStrReq with ⟨str, rfl⟩
  change __smtx_model_eval M (SmtTerm.String str) = SmtValue.Seq src at hSEval
  have hSrcEq : src = native_pack_string str := by
    simpa [__smtx_model_eval] using hSEval.symm
  subst src
  have hStrValid : native_string_valid str = true := by
    simpa [RuleProofs.native_unpack_string_pack_string] using hSrcValid
  have hFilteredEval := replace_re_all_nonempty_re_eval M r rv hRTy hREval
  have hFilteredNull : native_re_nullable (filteredRe rv) = false :=
    filteredRe_nullable_false rv
  have hFlatten :
      __str_flatten (__str_nary_intro (Term.String str)) =
        substrWord str 0 str.length := by
    cases str with
    | nil =>
        simpa [substrWord] using str_flatten_nary_intro_empty
    | cons c cs =>
        exact str_flatten_nary_intro_cons c cs
  have hRawNeSub :
      __str_eval_replace_re_all_rec (substrWord str 0 str.length) (Term.String [])
          (replace_re_all_nonempty_re r) t (Term.Numeral 0) ≠ Term.Stuck := by
    simpa [raw, rNonempty, hFlatten] using hRawNe
  have hRec :=
    str_eval_replace_re_all_rec_properties M hM str [] (str.length + 1) 0
      (replace_re_all_nonempty_re r) (filteredRe rv) t repl hStrValid
      (by simp [native_string_valid]) (by simp) hFilteredNull
      (by simpa [rNonempty] using hFilteredEval.1)
      (by simpa [rNonempty] using hFilteredEval.2)
      hTTy hTEval hReplTy hRawNeSub
  have hRawList : __eo_is_list (Term.UOp UserOp.str_concat) raw = Term.Boolean true := by
    simpa [raw, rNonempty, hFlatten] using hRec.1
  have hRawTy : __smtx_typeof (__eo_to_smt raw) = SmtType.Seq SmtType.Char := by
    simpa [raw, rNonempty, hFlatten] using hRec.2.1
  have hRawEval :
      __smtx_model_eval M (__eo_to_smt raw) =
        SmtValue.Seq
          (native_pack_string
            (native_str_replace_re_all str (filteredRe rv)
              (native_unpack_string repl))) := by
    simpa [raw, rNonempty, hFlatten, native_str_replace_re_all,
      impl_native_re_replace_all_nonempty_list] using hRec.2.2
  have hSideRel :=
    strConcat_singleton_elim_rel M hM raw SmtType.Char hRawList hRawTy
  have hSideEval :
      __smtx_model_eval M (__eo_to_smt side) =
        SmtValue.Seq
          (native_pack_string
            (native_str_replace_re_all str rv (native_unpack_string repl))) := by
    have hLhsTy :
        __smtx_typeof (__eo_to_smt lhs') = SmtType.Seq SmtType.Char := by
      change __smtx_typeof
          (SmtTerm.str_replace_re_all (SmtTerm.String str) (__eo_to_smt r)
            (__eo_to_smt t)) =
        SmtType.Seq SmtType.Char
      have hStrAll : ∀ x ∈ str, native_char_valid x = true := by
        simpa [native_string_valid, List.all_eq_true] using hStrValid
      simp [__smtx_typeof, hRTy, hTTy, native_string_valid, native_ite,
        native_Teq]
      exact hStrAll
    have hSameTy :=
      (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type lhs' side
        (by simpa [lhs, lhs'] using hEqBool)).1
    have hSideTy : __smtx_typeof (__eo_to_smt side) = SmtType.Seq SmtType.Char := by
      simpa [hLhsTy] using hSameTy.symm
    have hSideValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt side)) =
          SmtType.Seq SmtType.Char := by
      have hNN : term_has_non_none_type (__eo_to_smt side) := by
        unfold term_has_non_none_type
        rw [hSideTy]
        exact seq_ne_none SmtType.Char
      simpa [hSideTy] using
        smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt side) hNN
    have hTargetTy :
        __smtx_typeof_value
            (SmtValue.Seq
              (native_pack_string
                (native_str_replace_re_all str rv (native_unpack_string repl)))) =
          SmtType.Seq SmtType.Char := by
      change __smtx_typeof_seq_value
          (native_pack_string
            (native_str_replace_re_all str rv (native_unpack_string repl))) =
        SmtType.Seq SmtType.Char
      exact typeof_pack_string
        (native_str_replace_re_all str rv (native_unpack_string repl))
        (native_str_replace_re_all_string_valid str (native_unpack_string repl)
          rv hStrValid _hReplValid)
    have hSideRel' :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt side))
          (SmtValue.Seq
            (native_pack_string
              (native_str_replace_re_all str rv (native_unpack_string repl)))) := by
      simpa [side, hRawEval,
        native_str_replace_re_all_filtered_eq str rv (native_unpack_string repl)
          hStrValid]
        using hSideRel
    exact RuleProofs.smt_value_rel_eq_of_type_ne_reglan
      hSideValTy hTargetTy (by simp) hSideRel'
  have hResult' :
      __eo_prog_str_replace_re_all_eval
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) (Term.String str)) r)
              t))
          side) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) (Term.String str)) r)
              t))
          side := by
    have hsimpa := hResult
    try simp [lhs, body, side, inner, raw, rNonempty, replace_re_all_nonempty_re] at hsimpa ⊢
    exact hsimpa
  refine ⟨?_, ?_⟩
  · intro _hPremises
    rw [hResult']
    exact RuleProofs.eo_interprets_eq_of_rel M
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) (Term.String str)) r)
        t)
      side (by simpa [lhs, lhs'] using hEqBool) <| by
        rw [hLeftEval, hSideEval]
        simp [RuleProofs.native_unpack_string_pack_string]
        exact RuleProofs.smt_value_rel_refl
          (SmtValue.Seq
            (native_pack_string
              (native_str_replace_re_all str rv (native_unpack_string repl))))
  · rw [hResult']
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
      (by simpa [lhs, lhs'] using hEqBool)

private theorem str_replace_re_all_eval_arg_properties
    (M : SmtModel) (hM : model_wf M) :
    (a1 : Term) ->
    RuleProofs.eo_has_smt_translation a1 ->
    __eo_prog_str_replace_re_all_eval a1 ≠ Term.Stuck ->
    StepRuleProperties M [] (__eo_prog_str_replace_re_all_eval a1)
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
                                      | str_replace_re_all =>
                                          exact str_replace_re_all_eval_valid_properties M hM s r t u
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

public theorem cmd_step_str_replace_re_all_eval_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_re_all_eval args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_replace_re_all_eval args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_re_all_eval args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_replace_re_all_eval args premises ≠ Term.Stuck :=
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
              change StepRuleProperties M [] (__eo_prog_str_replace_re_all_eval a1)
              exact RuleProofs.str_replace_re_all_eval_arg_properties M hM a1 hA1Trans hProg
