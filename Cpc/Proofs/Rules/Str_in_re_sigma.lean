module

public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.RegexSupport
public import Cpc.Proofs.RuleSupport.RegexValueSupport
import all Cpc.Proofs.RuleSupport.RegexValueSupport
public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace RuleProofs

private theorem native_string_lit_empty :
    native_string_lit "" = ([] : native_String) := by
  simp [native_string_lit]

private def nativeSigmaState (n : Nat) (exact : Bool) (r : SmtRegLan) :
    SmtRegLan :=
  native_re_mk_concat (if exact then nativeSigmaExact n else nativeSigmaAtLeast n) r

private theorem nativeListInRe_sigmaState_allchar
    (xs : List native_Char) (n : Nat) (exact : Bool) (r : SmtRegLan) :
    nativeListInRe xs
        (nativeSigmaState n exact (native_re_concat native_re_allchar r)) =
      nativeListInRe xs (nativeSigmaState (n + 1) exact r) := by
  cases exact
  · change
      nativeListInRe xs
          (native_re_mk_concat (nativeSigmaAtLeast n)
            (native_re_mk_concat native_re_allchar r)) =
        nativeListInRe xs
          (native_re_mk_concat
            (native_re_mk_concat (nativeSigmaAtLeast n) native_re_allchar) r)
    exact (nativeListInRe_mk_concat_assoc xs
      (nativeSigmaAtLeast n) native_re_allchar r).symm
  · change
      nativeListInRe xs
          (native_re_mk_concat (nativeSigmaExact n)
            (native_re_mk_concat native_re_allchar r)) =
        nativeListInRe xs
          (native_re_mk_concat
            (native_re_mk_concat (nativeSigmaExact n) native_re_allchar) r)
    exact (nativeListInRe_mk_concat_assoc xs
      (nativeSigmaExact n) native_re_allchar r).symm

private theorem nativeListInRe_sigmaState_star
    (xs : List native_Char) (n : Nat) (exact : Bool) (r : SmtRegLan) :
    nativeListInRe xs
        (nativeSigmaState n exact (native_re_concat (native_re_mult native_re_allchar) r)) =
      nativeListInRe xs (nativeSigmaState n false r) := by
  cases exact
  · change
      nativeListInRe xs
          (native_re_mk_concat (nativeSigmaAtLeast n)
            (native_re_mk_concat native_re_all r)) =
        nativeListInRe xs (native_re_mk_concat (nativeSigmaAtLeast n) r)
    rw [← nativeListInRe_mk_concat_assoc]
    exact nativeListInRe_mk_concat_congr xs
      (native_re_mk_concat (nativeSigmaAtLeast n) native_re_all)
      (nativeSigmaAtLeast n) r r
      (nativeListInRe_atLeast_concat_re_all_eq_atLeast n) (fun _ => rfl)
  · change
      nativeListInRe xs
          (native_re_mk_concat (nativeSigmaExact n)
            (native_re_mk_concat native_re_all r)) =
        nativeListInRe xs (native_re_mk_concat (nativeSigmaAtLeast n) r)
    rw [← nativeListInRe_mk_concat_assoc]
    exact nativeListInRe_mk_concat_congr xs
      (native_re_mk_concat (nativeSigmaExact n) native_re_all)
      (nativeSigmaAtLeast n) r r
      (nativeListInRe_exact_concat_re_all_eq_atLeast n) (fun _ => rfl)

private theorem nativeListInRe_sigmaState_empty_exact
    (xs : List native_Char) (n : Nat)
    (hValid : native_string_valid xs = true) :
    nativeListInRe xs (nativeSigmaState n true SmtRegLan.epsilon) =
      decide (xs.length = n) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rw [decide_eq_true_iff]
    exact ((nativeListInRe_sigmaExact_true_iff n xs).1 (by
      simpa [nativeSigmaState, nativeListInRe_mk_concat_epsilon_right] using h)
      ).1
  · intro h
    have h' : xs.length = n := of_decide_eq_true h
    have hListValid : xs.all native_char_valid = true := by
      simpa [native_string_valid] using hValid
    have hExact : nativeListInRe xs (nativeSigmaExact n) = true :=
      (nativeListInRe_sigmaExact_true_iff n xs).2 ⟨h', hListValid⟩
    simpa [nativeSigmaState, nativeListInRe_mk_concat_epsilon_right] using hExact

private theorem nativeListInRe_sigmaState_empty_atLeast
    (xs : List native_Char) (n : Nat)
    (hValid : native_string_valid xs = true) :
    nativeListInRe xs (nativeSigmaState n false SmtRegLan.epsilon) =
      decide (n ≤ xs.length) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rw [decide_eq_true_iff]
    exact ((nativeListInRe_sigmaAtLeast_true_iff n xs).1 (by
      simpa [nativeSigmaState, nativeListInRe_mk_concat_epsilon_right] using h)
      ).1
  · intro h
    have h' : n ≤ xs.length := of_decide_eq_true h
    have hListValid : xs.all native_char_valid = true := by
      simpa [native_string_valid] using hValid
    have hAtLeast : nativeListInRe xs (nativeSigmaAtLeast n) = true :=
      (nativeListInRe_sigmaAtLeast_true_iff n xs).2 ⟨h', hListValid⟩
    simpa [nativeSigmaState, nativeListInRe_mk_concat_epsilon_right] using hAtLeast

private theorem native_unpack_string_length_eq (ss : SmtSeq) :
    (native_unpack_string ss).length = (native_unpack_seq ss).length := by
  simp [native_unpack_string]

private theorem native_unpack_string_strlen_eq (ss : SmtSeq) :
    (native_unpack_string ss).length = (native_unpack_seq ss).length := by
  simpa using native_unpack_string_length_eq ss

private theorem str_in_re_sigma_rec_empty_false_eq
    (s : Term) (n : Nat) (hSNe : s ≠ Term.Stuck) :
    __str_mk_str_in_re_sigma_rec s
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String (native_string_lit "")))
        (Term.Numeral (Int.ofNat n)) (Term.Boolean false) =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.geq)
        (Term.Apply (Term.UOp UserOp.str_len) s))
        (Term.Numeral (Int.ofNat n)) := by
  cases hs : s <;>
    first | exact False.elim (hSNe hs) |
      simp [__str_mk_str_in_re_sigma_rec, __eo_ite, native_teq,
        native_ite, native_string_lit]

private theorem str_in_re_sigma_rec_empty_true_eq
    (s : Term) (n : Nat) (hSNe : s ≠ Term.Stuck) :
    __str_mk_str_in_re_sigma_rec s
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String (native_string_lit "")))
        (Term.Numeral (Int.ofNat n)) (Term.Boolean true) =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp UserOp.str_len) s))
        (Term.Numeral (Int.ofNat n)) := by
  cases hs : s <;>
    first | exact False.elim (hSNe hs) |
      simp [__str_mk_str_in_re_sigma_rec, __eo_ite, native_teq,
        native_ite, native_string_lit]

private theorem str_in_re_sigma_rec_str_to_re_nonempty_eq_stuck
    (s : Term) (str : native_String) (n : Nat) (exact : Bool)
    (hStr : str ≠ native_string_lit "") :
    __str_mk_str_in_re_sigma_rec s
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String str))
        (Term.Numeral (Int.ofNat n)) (Term.Boolean exact) =
      Term.Stuck := by
  have hStrNil : str ≠ ([] : native_String) := by
    simpa [native_string_lit_empty] using hStr
  cases s <;> unfold __str_mk_str_in_re_sigma_rec <;>
    simp [hStrNil]

private theorem str_in_re_sigma_rec_allchar_eq
    (s r : Term) (n : Nat) (exact : Bool) (hSNe : s ≠ Term.Stuck) :
    __str_mk_str_in_re_sigma_rec s
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat) (Term.UOp UserOp.re_allchar)) r)
        (Term.Numeral (Int.ofNat n)) (Term.Boolean exact) =
      __str_mk_str_in_re_sigma_rec s r
        (Term.Numeral (Int.ofNat (n + 1))) (Term.Boolean exact) := by
  simp [__str_mk_str_in_re_sigma_rec, __eo_add, native_zplus, Int.natCast_add]

private theorem str_in_re_sigma_rec_star_eq
    (s r : Term) (n : Nat) (exact : Bool) (hSNe : s ≠ Term.Stuck) :
    __str_mk_str_in_re_sigma_rec s
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.re_mult) (Term.UOp UserOp.re_allchar))) r)
        (Term.Numeral (Int.ofNat n)) (Term.Boolean exact) =
      __str_mk_str_in_re_sigma_rec s r
        (Term.Numeral (Int.ofNat n)) (Term.Boolean false) := by
  simp [__str_mk_str_in_re_sigma_rec]

private theorem smtx_model_eval_str_in_re_sigma_rec
    (M : SmtModel) (s : Term) (ss : SmtSeq)
    (hSNe : s ≠ Term.Stuck)
    (hSEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hSsTy : __smtx_typeof_value (SmtValue.Seq ss) =
      SmtType.Seq SmtType.Char)
    (hSSValid : native_string_valid (native_unpack_string ss) = true)
    (r : Term) (rv : SmtRegLan) (n : Nat) (exact : Bool) :
      __str_mk_str_in_re_sigma_rec s r
          (Term.Numeral (Int.ofNat n)) (Term.Boolean exact) ≠ Term.Stuck ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
      __smtx_model_eval M
          (__eo_to_smt
            (__str_mk_str_in_re_sigma_rec s r
              (Term.Numeral (Int.ofNat n)) (Term.Boolean exact))) =
        SmtValue.Boolean
          (nativeListInRe (native_unpack_string ss)
            (nativeSigmaState n exact rv))
:= by
  intro hSide hREval
  cases r with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | str_to_re =>
              cases x with
              | String str =>
                  by_cases hStr : str = native_string_lit ""
                  · subst str
                    have hRv : rv = SmtRegLan.epsilon := by
                      change __smtx_model_eval M (SmtTerm.str_to_re (SmtTerm.String (native_string_lit ""))) =
                          SmtValue.RegLan rv at hREval
                      rw [__smtx_model_eval.eq_107, __smtx_model_eval.eq_4] at hREval
                      have hsimpa := hREval.symm
                      try simp [__smtx_model_eval_str_to_re, native_str_to_re, native_pack_string] at hsimpa ⊢
                      exact hsimpa
                    subst rv
                    cases exact
                    · rw [str_in_re_sigma_rec_empty_false_eq s n hSNe]
                      change
                        __smtx_model_eval M
                            (SmtTerm.geq (SmtTerm.str_len (__eo_to_smt s))
                              (SmtTerm.Numeral (Int.ofNat n))) =
                          SmtValue.Boolean
                            (nativeListInRe (native_unpack_string ss)
                              (nativeSigmaState n false SmtRegLan.epsilon))
                      rw [__smtx_model_eval.eq_20, smtx_eval_str_len_term_eq,
                        __smtx_model_eval.eq_2, hSEval]
                      simp [__smtx_model_eval_geq, __smtx_model_eval_leq,
                        __smtx_model_eval_str_len, native_seq_len, native_zleq,
                        nativeListInRe_sigmaState_empty_atLeast, hSSValid,
                        native_unpack_string_strlen_eq]
                    · rw [str_in_re_sigma_rec_empty_true_eq s n hSNe]
                      change
                        __smtx_model_eval M
                            (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt s))
                              (SmtTerm.Numeral (Int.ofNat n))) =
                          SmtValue.Boolean
                            (nativeListInRe (native_unpack_string ss)
                              (nativeSigmaState n true SmtRegLan.epsilon))
                      rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq,
                        __smtx_model_eval.eq_2, hSEval]
                      simp [__smtx_model_eval_eq, __smtx_model_eval_str_len,
                        native_veq, native_seq_len,
                        nativeListInRe_sigmaState_empty_exact, hSSValid,
                        native_unpack_string_strlen_eq]
                      exact Int.ofNat_inj
                  · exfalso
                    apply hSide
                    exact str_in_re_sigma_rec_str_to_re_nonempty_eq_stuck s str n exact hStr
              | _ =>
                  exfalso
                  apply hSide
                  simpa [__str_mk_str_in_re_sigma_rec]
          | _ =>
              exfalso
              apply hSide
              simpa [__str_mk_str_in_re_sigma_rec]
      | Apply f₁ y =>
          cases f₁ with
          | UOp op =>
              cases op with
              | re_concat =>
                  cases y with
                  | UOp yop =>
                      cases yop with
                      | re_allchar =>
                          change __smtx_model_eval M
                              (SmtTerm.re_concat SmtTerm.re_allchar (__eo_to_smt x)) =
                            SmtValue.RegLan rv at hREval
                          rw [__smtx_model_eval.eq_114, __smtx_model_eval.eq_104] at hREval
                          cases hTailEval : __smtx_model_eval M (__eo_to_smt x) with
                          | RegLan rvTail =>
                              have hRv : rv = native_re_concat native_re_allchar rvTail := by
                                simp [__smtx_model_eval_re_concat, hTailEval] at hREval
                                exact hREval.symm
                              subst rv
                              have hSideTail :
                                  __str_mk_str_in_re_sigma_rec s x
                                      (Term.Numeral (Int.ofNat (n + 1)))
                                      (Term.Boolean exact) ≠
                                    Term.Stuck := by
                                rw [← str_in_re_sigma_rec_allchar_eq s x n exact hSNe]
                                exact hSide
                              have hRec :=
                                smtx_model_eval_str_in_re_sigma_rec M s ss hSNe hSEval
                                  hSsTy hSSValid x rvTail (n + 1) exact hSideTail hTailEval
                              rw [str_in_re_sigma_rec_allchar_eq s x n exact hSNe]
                              simpa [nativeListInRe_sigmaState_allchar] using hRec
                          | _ =>
                              simp [__smtx_model_eval_re_concat, hTailEval] at hREval
                      | _ =>
                          exfalso
                          apply hSide
                          simpa [__str_mk_str_in_re_sigma_rec]
                  | Apply yf yx =>
                      cases yf with
                      | UOp yopf =>
                          cases yopf with
                          | re_mult =>
                              cases yx with
                              | UOp yxop =>
                                  cases yxop with
                                  | re_allchar =>
                                      change __smtx_model_eval M
                                          (SmtTerm.re_concat
                                            (SmtTerm.re_mult SmtTerm.re_allchar)
                                            (__eo_to_smt x)) =
                                        SmtValue.RegLan rv at hREval
                                      rw [__smtx_model_eval.eq_114, __smtx_model_eval.eq_108,
                                        __smtx_model_eval.eq_104] at hREval
                                      cases hTailEval :
                                          __smtx_model_eval M (__eo_to_smt x) with
                                      | RegLan rvTail =>
                                          have hRv :
                                              rv =
                                                native_re_concat
                                                  (native_re_mult native_re_allchar) rvTail := by
                                            simp [__smtx_model_eval_re_concat,
                                              __smtx_model_eval_re_mult,
                                              native_re_mult, native_re_allchar,
                                              hTailEval] at hREval
                                            exact hREval.symm
                                          subst rv
                                          have hSideTail :
                                              __str_mk_str_in_re_sigma_rec s x
                                                  (Term.Numeral (Int.ofNat n))
                                                  (Term.Boolean false) ≠
                                                Term.Stuck := by
                                            rw [← str_in_re_sigma_rec_star_eq s x n exact hSNe]
                                            exact hSide
                                          have hRec :=
                                            smtx_model_eval_str_in_re_sigma_rec M s ss
                                              hSNe hSEval hSsTy hSSValid x rvTail n false
                                              hSideTail hTailEval
                                          rw [str_in_re_sigma_rec_star_eq s x n exact hSNe]
                                          simpa [nativeListInRe_sigmaState_star] using hRec
                                      | _ =>
                                          simp [__smtx_model_eval_re_concat,
                                            hTailEval] at hREval
                                  | _ =>
                                      exfalso
                                      apply hSide
                                      simpa [__str_mk_str_in_re_sigma_rec]
                              | _ =>
                                  exfalso
                                  apply hSide
                                  simpa [__str_mk_str_in_re_sigma_rec]
                          | _ =>
                              exfalso
                              apply hSide
                              simpa [__str_mk_str_in_re_sigma_rec]
                      | _ =>
                          exfalso
                          apply hSide
                          simpa [__str_mk_str_in_re_sigma_rec]
                  | _ =>
                      exfalso
                      apply hSide
                      simpa [__str_mk_str_in_re_sigma_rec]
              | _ =>
                  exfalso
                  apply hSide
                  simpa [__str_mk_str_in_re_sigma_rec]
          | _ =>
              exfalso
              apply hSide
              simpa [__str_mk_str_in_re_sigma_rec]
      | _ =>
          exfalso
          apply hSide
          simpa [__str_mk_str_in_re_sigma_rec]
  | _ =>
      exfalso
      apply hSide
      simpa [__str_mk_str_in_re_sigma_rec]
termination_by r

private theorem eo_requires_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro h
  simp [__eo_requires, native_ite, native_teq] at h
  exact h.1

private theorem eo_requires_result_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    __eo_requires x y z = z := by
  intro h
  have h' := h
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at h'
  rcases h' with ⟨hxy, hxOk, _hz⟩
  subst y
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not, hxOk]

private theorem eo_requires_left_ne_stuck_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x ≠ Term.Stuck := by
  intro h
  have h' := h
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at h'
  rcases h' with ⟨_hxy, hxOk, _hz⟩
  intro hx
  subst x
  have hxNe : y ≠ Term.Stuck := by
    intro hy
    subst y
    simp at hxOk
  exact hxNe hx

private theorem eq_operands_same_smt_type_of_eq_has_smt_translation
    (x y : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
    __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hTrans
  have hEqNN : term_has_non_none_type (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) ≠
      SmtType.None
    exact hTrans
  have hEqTy :
      __smtx_typeof (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool :=
    Smtm.eq_term_typeof_of_non_none hEqNN
  rw [Smtm.typeof_eq_eq] at hEqTy
  exact RuleProofs.smtx_typeof_eq_bool_iff
    (__smtx_typeof (__eo_to_smt x))
    (__smtx_typeof (__eo_to_smt y)) |>.mp hEqTy

private theorem eq_operands_have_smt_translation_of_eq_has_smt_translation
    (x y : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
    RuleProofs.eo_has_smt_translation x ∧
      RuleProofs.eo_has_smt_translation y := by
  intro hTrans
  rcases eq_operands_same_smt_type_of_eq_has_smt_translation x y hTrans with
    ⟨hTy, hNonNone⟩
  constructor
  · simpa [RuleProofs.eo_has_smt_translation] using hNonNone
  · simpa [RuleProofs.eo_has_smt_translation, hTy] using hNonNone

private theorem str_in_re_args_smt_types_of_has_translation
    (s r : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) ->
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
  intro hTrans
  have hNN :
      term_has_non_none_type (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) ≠
      SmtType.None
    exact hTrans
  exact seq_char_reglan_args_of_non_none
    (op := SmtTerm.str_in_re) (typeof_str_in_re_eq (__eo_to_smt s) (__eo_to_smt r)) hNN

private theorem smtx_model_eval_str_in_re_eq_sigma_side
    (M : SmtModel) (s r side : Term) (ss : SmtSeq) (rv : SmtRegLan)
    (hSNe : s ≠ Term.Stuck)
    (hSEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hSsTy : __smtx_typeof_value (SmtValue.Seq ss) =
      SmtType.Seq SmtType.Char)
    (hSSValid : native_string_valid (native_unpack_string ss) = true)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hSide :
      side = __str_mk_str_in_re_sigma_rec s r (Term.Numeral 0) (Term.Boolean true))
    (hSideNe : side ≠ Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) =
      __smtx_model_eval M (__eo_to_smt side) := by
  subst side
  have hSideEval :=
    smtx_model_eval_str_in_re_sigma_rec M s ss hSNe hSEval hSsTy hSSValid r rv
      0 true hSideNe hREval
  change
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) =
      __smtx_model_eval M
        (__eo_to_smt
          (__str_mk_str_in_re_sigma_rec s r
            (Term.Numeral (Int.ofNat 0)) (Term.Boolean true)))
  rw [hSideEval]
  change
    __smtx_model_eval M (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) =
      SmtValue.Boolean
        (nativeListInRe (native_unpack_string ss)
          (nativeSigmaState 0 true rv))
  rw [__smtx_model_eval.eq_119]
  have hState : nativeSigmaState 0 true rv = rv := by
    cases rv <;>
      simp [nativeSigmaState, nativeSigmaExact, native_re_mk_concat,
        native_re_concat]
  rw [hSEval, hREval]
  simp [__smtx_model_eval_str_in_re, hState,
    model_str_in_re_unpack_eq_string_of_value_type ss rv hSsTy,
    native_str_in_re, hSSValid]

private theorem str_in_re_sigma_valid_properties
    (M : SmtModel) (hM : model_wf M)
    (s r b : Term)
    (hArgTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) b))
    (hProgNe :
      __eo_prog_str_in_re_sigma
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) b) ≠
        Term.Stuck) :
    StepRuleProperties M []
      (__eo_prog_str_in_re_sigma
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) b)) := by
  let strIn := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r
  let side := __str_mk_str_in_re_sigma_rec s r (Term.Numeral 0) (Term.Boolean true)
  let body := Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) b
  change __eo_requires side b body ≠ Term.Stuck at hProgNe
  have hReqEq : side = b := eo_requires_eq_of_ne_stuck side b body hProgNe
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
  rcases eq_operands_have_smt_translation_of_eq_has_smt_translation strIn side hEqTrans with
    ⟨hStrInTrans, _hSideTrans⟩
  rcases str_in_re_args_smt_types_of_has_translation s r (by
      simpa [strIn] using hStrInTrans) with
    ⟨hSTy, hRTy⟩
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  rcases seq_value_canonical_with_char_type hSEvalTy with
    ⟨ss, hSEval, hSsTy⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hSSValid : native_string_valid (native_unpack_string ss) = true := by
    apply native_unpack_string_valid_of_typeof_seq_char
    simp only [hSEval] at hSEvalTy
    exact hSEvalTy
  have hSNe : s ≠ Term.Stuck := by
    intro hs
    apply hSideNe
    subst s
    simp [side, __str_mk_str_in_re_sigma_rec]
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt strIn) =
        __smtx_model_eval M (__eo_to_smt side) := by
    exact smtx_model_eval_str_in_re_eq_sigma_side M s r side ss rv hSNe hSEval
      hSsTy hSSValid hREval rfl hSideNe
  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
    (by simpa [strIn, side] using hEqBool)⟩
  intro _hPremises
  exact RuleProofs.eo_interprets_eq_of_rel M strIn side hEqBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt side))

end RuleProofs

public theorem cmd_step_str_in_re_sigma_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_sigma args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_in_re_sigma args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_sigma args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_in_re_sigma args premises ≠ Term.Stuck :=
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
                                                RuleProofs.str_in_re_sigma_valid_properties
                                                  M hM str r b (by
                                                    simpa using hA1Trans) (by
                                                    change
                                                      __eo_prog_str_in_re_sigma
                                                        (Term.Apply
                                                          (Term.Apply (Term.UOp UserOp.eq)
                                                            (Term.Apply
                                                              (Term.Apply
                                                                (Term.UOp UserOp.str_in_re) str) r)) b) ≠
                                                        Term.Stuck at hProg
                                                    exact hProg)
                                              change StepRuleProperties M []
                                                (__eo_prog_str_in_re_sigma
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
