module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.Canonical.Seq
import all Cpc.Proofs.Canonical.Seq

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def eslFormula (U n id : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.UOp UserOp.str_len)
        (Term.UOp3 UserOp3._at_witness_string_length
          (Term.Apply (Term.UOp UserOp.Seq) U) n id)))
    n

private def eslSmtBody (A : SmtType) (k : native_Int) : SmtTerm :=
  SmtTerm.eq
    (SmtTerm.str_len (SmtTerm.Var (native_string_lit "@x") (SmtType.Seq A)))
    (SmtTerm.Numeral k)

private theorem eo_requires_cond_eq_of_non_stuck {x y z : Term}
    (h : __eo_requires x y z ≠ Term.Stuck) :
    x = y := by
  unfold __eo_requires at h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · have hxyFalse : native_teq x y = false := by
      cases hTeq : native_teq x y <;> simp_all
    simp [native_ite, hxyFalse] at h

private theorem eo_requires_result_eq_of_non_stuck {x y z : Term}
    (h : __eo_requires x y z ≠ Term.Stuck) :
    __eo_requires x y z = z := by
  unfold __eo_requires at h ⊢
  by_cases hxy : native_teq x y = true
  · by_cases hx : native_teq x Term.Stuck = true
    · simp [native_ite, hxy, hx, SmtEval.native_not] at h
    · simp [native_ite, hxy, hx, SmtEval.native_not]
  · simp [native_ite, hxy] at h

private theorem eo_requires_result_ne_stuck_of_non_stuck {x y z : Term}
    (h : __eo_requires x y z ≠ Term.Stuck) :
    z ≠ Term.Stuck := by
  intro hz
  exact h (by rw [eo_requires_result_eq_of_non_stuck h, hz])

private theorem eo_gt_numeral_neg_one_eq_true {n : Term} :
    __eo_gt n (Term.Numeral (-1 : native_Int)) = Term.Boolean true ->
    ∃ k : native_Int, n = Term.Numeral k ∧
      native_zlt (-1 : native_Int) k = true := by
  intro h
  cases n <;> simp [__eo_gt] at h
  case Numeral k =>
    exact ⟨k, rfl, by simpa [__eo_gt] using h⟩

private theorem eo_to_smt_nat_is_valid_numeral_of_gt_neg_one
    {k : native_Int}
    (hgt : native_zlt (-1 : native_Int) k = true) :
    __eo_to_smt_nat_is_valid (Term.Numeral k) = true := by
  have hkLt : (-1 : native_Int) < k := by
    simpa [native_zlt] using hgt
  have hkNonneg : (0 : native_Int) <= k :=
    Int.add_one_le_iff.mpr hkLt
  simpa [__eo_to_smt_nat_is_valid, native_zleq] using hkNonneg

private theorem eo_to_smt_nat_is_valid_of_gt_neg_one {n : Term}
    (hgt : __eo_gt n (Term.Numeral (-1 : native_Int)) =
      Term.Boolean true) :
    __eo_to_smt_nat_is_valid n = true := by
  rcases eo_gt_numeral_neg_one_eq_true hgt with ⟨k, rfl, hkGt⟩
  exact eo_to_smt_nat_is_valid_numeral_of_gt_neg_one hkGt

private theorem prog_exists_string_length_eq_formula
    {U id : Term} {k : native_Int}
    (hgt : native_zlt (-1 : native_Int) k = true)
    (hIdGt : __eo_gt id (Term.Numeral (-1 : native_Int)) =
      Term.Boolean true) :
    __eo_prog_exists_string_length
      (Term.Apply (Term.UOp UserOp.Seq) U) (Term.Numeral k) id =
      eslFormula U (Term.Numeral k) id := by
  cases id <;>
    simp_all [eslFormula, __eo_prog_exists_string_length, __eo_requires,
      __eo_gt, native_ite, native_teq, SmtEval.native_not]

private theorem exists_string_length_first_arg_seq
    {s : CState} {a n id : Term}
    (hProg :
      __eo_cmd_step_proven s CRule.exists_string_length
        (CArgList.cons a (CArgList.cons n (CArgList.cons id CArgList.nil)))
        CIndexList.nil ≠ Term.Stuck) :
    ∃ U, a = Term.Apply (Term.UOp UserOp.Seq) U := by
  change __eo_prog_exists_string_length a n id ≠ Term.Stuck at hProg
  by_cases hn : n = Term.Stuck
  · subst n
    exact False.elim (hProg rfl)
  by_cases hid : id = Term.Stuck
  · subst id
    exact False.elim (hProg (by simp [__eo_prog_exists_string_length]))
  cases a with
  | Apply f U =>
      cases f with
      | UOp op =>
          cases op with
          | Seq =>
              exact ⟨U, rfl⟩
          | _ =>
              exfalso
              apply hProg
              simp [__eo_prog_exists_string_length]
      | _ =>
          exfalso
          apply hProg
          simp [__eo_prog_exists_string_length]
  | _ =>
      exfalso
      apply hProg
      simp [__eo_prog_exists_string_length]

private theorem eo_seq_type_eq_of_wf (U : Term)
    (hWF : __smtx_type_wf
      (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U)) = true) :
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U) =
      SmtType.Seq (__eo_to_smt_type U) := by
  rw [TranslationProofs.eo_to_smt_type_seq] at hWF ⊢
  generalize hA : __eo_to_smt_type U = A at hWF ⊢
  cases A <;> simp [__smtx_typeof_guard, native_ite, native_Teq,
    __smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
    native_inhabited_type, native_and] at hWF ⊢

private theorem seq_elem_wf_parts_of_seq_wf {A : SmtType} :
    __smtx_type_wf (SmtType.Seq A) = true ->
    native_inhabited_type A = true ∧
      __smtx_type_wf_rec A = true := by
  intro h
  have hAll :
      native_inhabited_type (SmtType.Seq A) = true ∧
        (native_inhabited_type A = true ∧
          __smtx_type_wf_rec A = true) := by
    simpa [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      native_and] using h
  exact hAll.2

private theorem list_typed_replicate_type_default
    (A : SmtType) (n : Nat)
    (hA : __smtx_typeof_value (__smtx_type_default A) = A) :
    list_typed A (List.replicate n (__smtx_type_default A)) := by
  induction n with
  | zero =>
      simp [list_typed]
  | succ n ih =>
      simp [List.replicate, list_typed, hA, ih]

private theorem eslSmtBody_type (A : SmtType) (k : native_Int)
    (hWF : __smtx_type_wf (SmtType.Seq A) = true) :
    __smtx_typeof (eslSmtBody A k) = SmtType.Bool := by
  have hVarTy :
      __smtx_typeof (SmtTerm.Var (native_string_lit "@x") (SmtType.Seq A)) =
        SmtType.Seq A := by
    rw [smtx_typeof_var_term_eq]
    simp [__smtx_typeof_guard_wf, hWF, native_ite]
  rw [eslSmtBody, typeof_eq_eq, typeof_str_len_eq, __smtx_typeof.eq_2,
    hVarTy]
  simp [__smtx_typeof_seq_op_1_ret, __smtx_typeof_eq,
    __smtx_typeof_guard, native_Teq, native_ite]

private theorem eslSmtBody_eval_default_seq
    (M : SmtModel) (A : SmtType) (k : native_Int)
    (hkNonneg : 0 <= k) :
    __smtx_model_eval
      (native_model_push M (native_string_lit "@x") (SmtType.Seq A)
        (SmtValue.Seq
          (native_pack_seq A (List.replicate (native_int_to_nat k)
            (__smtx_type_default A)))))
      (eslSmtBody A k) = SmtValue.Boolean true := by
  rw [eslSmtBody, smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq,
    smtx_eval_var_term_eq, __smtx_model_eval.eq_2]
  simp [native_model_var_lookup, native_model_push, __smtx_model_eval_str_len,
    Smtm.native_unpack_pack_seq, __smtx_model_eval_eq, native_seq_len,
    native_int_to_nat, SmtEval.native_int_to_nat, Int.toNat_of_nonneg hkNonneg,
    native_veq]

private theorem native_eval_tchoice_body_true_of_exists
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm)
    (hSat : ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push M s T v) body =
          SmtValue.Boolean true) :
    __smtx_model_eval (native_model_push M s T
      (native_eval_choice M s T body)) body =
      SmtValue.Boolean true := by
  classical
  change
    __smtx_model_eval
      (native_model_push M s T
        (if hSat' : ∃ v : SmtValue,
          __smtx_typeof_value v = T ∧
            __smtx_value_canonical v = true ∧
            __smtx_model_eval (native_model_push M s T v) body =
              SmtValue.Boolean true then
          Classical.choose hSat'
        else if hTy : ∃ v : SmtValue, __smtx_typeof_value v = T ∧
            __smtx_value_canonical v then
          Classical.choose hTy
        else SmtValue.NotValue)) body = SmtValue.Boolean true
  simp [hSat]
  exact (Classical.choose_spec hSat).2.2

private theorem eslSmtBody_true_imp_str_len
    (M : SmtModel) (A : SmtType) (k : native_Int) (v : SmtValue)
    (hBody :
      __smtx_model_eval
        (native_model_push M (native_string_lit "@x") (SmtType.Seq A) v)
        (eslSmtBody A k) = SmtValue.Boolean true) :
    __smtx_model_eval_str_len v = SmtValue.Numeral k := by
  rw [eslSmtBody, smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq,
    smtx_eval_var_term_eq, __smtx_model_eval.eq_2] at hBody
  simp [native_model_var_lookup, native_model_push] at hBody
  cases hLen : __smtx_model_eval_str_len v <;>
    simp [hLen, __smtx_model_eval_eq, native_veq] at hBody ⊢ <;>
    simp_all

private theorem eslFormula_has_bool_type
    (U id : Term) (A : SmtType) (k : native_Int)
    (hkGt : native_zlt (-1 : native_Int) k = true)
    (hIdGt : __eo_gt id (Term.Numeral (-1 : native_Int)) =
      Term.Boolean true)
    (hSeqTy : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U) =
      SmtType.Seq A)
    (hSeqWF : __smtx_type_wf (SmtType.Seq A) = true) :
    RuleProofs.eo_has_bool_type (eslFormula U (Term.Numeral k) id) := by
  have hKValid : __eo_to_smt_nat_is_valid (Term.Numeral k) = true :=
    eo_to_smt_nat_is_valid_numeral_of_gt_neg_one hkGt
  have hIdValid : __eo_to_smt_nat_is_valid id = true :=
    eo_to_smt_nat_is_valid_of_gt_neg_one hIdGt
  have hBodyTy : __smtx_typeof (eslSmtBody A k) = SmtType.Bool :=
    eslSmtBody_type A k hSeqWF
  have hChoiceTy :
      __smtx_typeof
        (SmtTerm.choice (native_string_lit "@x") (SmtType.Seq A)
          (eslSmtBody A k)) = SmtType.Seq A := by
    rw [__smtx_typeof.eq_def]
    simp [hBodyTy, __smtx_typeof_guard_wf, hSeqWF, native_Teq, native_ite]
  let wit : Term :=
    Term.UOp3 UserOp3._at_witness_string_length
      (Term.Apply (Term.UOp UserOp.Seq) U) (Term.Numeral k) id
  have hWitTy : __smtx_typeof (__eo_to_smt wit) = SmtType.Seq A := by
    change
      __smtx_typeof
        (native_ite (__eo_to_smt_nat_is_valid (Term.Numeral k))
          (native_ite (__eo_to_smt_nat_is_valid id)
            (SmtTerm.choice (native_string_lit "@x")
              (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U))
              (SmtTerm.eq
                (SmtTerm.str_len (SmtTerm.Var (native_string_lit "@x")
                  (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U))))
                (SmtTerm.Numeral k)))
            SmtTerm.None)
          SmtTerm.None) = SmtType.Seq A
    simpa [hKValid, hIdValid, hSeqTy, native_ite, eslSmtBody] using hChoiceTy
  have hLenTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) wit)) =
        SmtType.Int := by
    change __smtx_typeof (SmtTerm.str_len (__eo_to_smt wit)) = SmtType.Int
    rw [typeof_str_len_eq, hWitTy]
    simp [__smtx_typeof_seq_op_1_ret]
  have hNumTy : __smtx_typeof (__eo_to_smt (Term.Numeral k)) = SmtType.Int := by
    change __smtx_typeof (SmtTerm.Numeral k) = SmtType.Int
    rw [__smtx_typeof.eq_2]
  change RuleProofs.eo_has_bool_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.UOp UserOp.str_len) wit)) (Term.Numeral k))
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UOp UserOp.str_len) wit) (Term.Numeral k)
    (by rw [hLenTy, hNumTy])
    (by rw [hLenTy]; simp)

private theorem eslFormula_true
    (M : SmtModel) (U id : Term) (A : SmtType) (k : native_Int)
    (hIdGt : __eo_gt id (Term.Numeral (-1 : native_Int)) =
      Term.Boolean true)
    (hSeqTy : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U) =
      SmtType.Seq A)
    (hSeqWF : __smtx_type_wf (SmtType.Seq A) = true)
    (hkGt : native_zlt (-1 : native_Int) k = true) :
    eo_interprets M (eslFormula U (Term.Numeral k) id) true := by
  have hKValid : __eo_to_smt_nat_is_valid (Term.Numeral k) = true :=
    eo_to_smt_nat_is_valid_numeral_of_gt_neg_one hkGt
  have hIdValid : __eo_to_smt_nat_is_valid id = true :=
    eo_to_smt_nat_is_valid_of_gt_neg_one hIdGt
  have hkLt : (-1 : native_Int) < k := by
    simpa [native_zlt] using hkGt
  have hkNonneg : (0 : native_Int) <= k := by
    exact Int.add_one_le_iff.mpr hkLt
  have hAParts := seq_elem_wf_parts_of_seq_wf hSeqWF
  have hDef :=
    Smtm.type_default_typed_canonical_of_native_inhabited_type
      A hAParts.1 hAParts.2
  let xs : List SmtValue :=
    List.replicate (native_int_to_nat k) (__smtx_type_default A)
  let w : SmtValue := SmtValue.Seq (native_pack_seq A xs)
  have hWTy : __smtx_typeof_value w = SmtType.Seq A := by
    change __smtx_typeof_seq_value (native_pack_seq A xs) = SmtType.Seq A
    exact Smtm.typeof_seq_value_pack_seq_of_typed
      (list_typed_replicate_type_default A (native_int_to_nat k) hDef.1)
  have hWCanon : __smtx_value_canonical w = true := by
    change __smtx_seq_canonical (native_pack_seq A xs) = true
    apply Smtm.seq_canonical_pack_seq
    intro v hv
    simp [xs] at hv
    simp_all [hDef.2]
  have hBodyEval :
      __smtx_model_eval
        (native_model_push M (native_string_lit "@x") (SmtType.Seq A) w)
        (eslSmtBody A k) = SmtValue.Boolean true := by
    simpa [w, xs] using eslSmtBody_eval_default_seq M A k hkNonneg
  have hSat : ∃ v : SmtValue,
      __smtx_typeof_value v = SmtType.Seq A ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval
          (native_model_push M (native_string_lit "@x") (SmtType.Seq A) v)
          (eslSmtBody A k) = SmtValue.Boolean true :=
    ⟨w, hWTy, hWCanon, hBodyEval⟩
  have hChoiceBody :
      __smtx_model_eval
        (native_model_push M (native_string_lit "@x") (SmtType.Seq A)
          (native_eval_choice M (native_string_lit "@x") (SmtType.Seq A)
            (eslSmtBody A k)))
        (eslSmtBody A k) = SmtValue.Boolean true :=
    native_eval_tchoice_body_true_of_exists M (native_string_lit "@x")
      (SmtType.Seq A) (eslSmtBody A k) hSat
  have hChoiceLen :
      __smtx_model_eval_str_len
        (native_eval_choice M (native_string_lit "@x") (SmtType.Seq A)
          (eslSmtBody A k)) = SmtValue.Numeral k :=
    eslSmtBody_true_imp_str_len M A k
      (native_eval_choice M (native_string_lit "@x") (SmtType.Seq A)
        (eslSmtBody A k)) hChoiceBody
  have hChoiceLen' :
      __smtx_model_eval_str_len
        (native_eval_choice M (native_string_lit "@x") (SmtType.Seq A)
          (SmtTerm.eq
            (SmtTerm.str_len
              (SmtTerm.Var (native_string_lit "@x") (SmtType.Seq A)))
            (SmtTerm.Numeral k))) = SmtValue.Numeral k := by
    exact hChoiceLen
  have hBool : RuleProofs.eo_has_bool_type (eslFormula U (Term.Numeral k) id) :=
    eslFormula_has_bool_type U id A k hkGt hIdGt hSeqTy hSeqWF
  have hEval :
      __smtx_model_eval M (__eo_to_smt (eslFormula U (Term.Numeral k) id)) =
        SmtValue.Boolean true := by
    unfold eslFormula
    change
      __smtx_model_eval M
        (SmtTerm.eq
          (SmtTerm.str_len
            (native_ite
              (__eo_to_smt_nat_is_valid (Term.Numeral k))
              (native_ite
                (__eo_to_smt_nat_is_valid id)
                (SmtTerm.choice (native_string_lit "@x")
                  (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U))
                  (SmtTerm.eq
                    (SmtTerm.str_len
                      (SmtTerm.Var (native_string_lit "@x")
                        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U))))
                    (SmtTerm.Numeral k)))
                SmtTerm.None)
              SmtTerm.None))
          (SmtTerm.Numeral k)) = SmtValue.Boolean true
    rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq,
      __smtx_model_eval.eq_2]
    simp [hKValid, hIdValid, hSeqTy, native_ite,
      smtx_model_eval_choice_eq,
      hChoiceLen', __smtx_model_eval_eq, native_veq]
  exact RuleProofs.eo_interprets_of_bool_eval M _ true hBool hEval

public theorem cmd_step_exists_string_length_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.exists_string_length args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.exists_string_length args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.exists_string_length args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.exists_string_length args premises ≠ Term.Stuck :=
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
      | cons n args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons id args =>
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
                      rcases exists_string_length_first_arg_seq hProg with ⟨U, rfl⟩
                      have hProg' :
                          __eo_prog_exists_string_length
                            (Term.Apply (Term.UOp UserOp.Seq) U) n id ≠
                            Term.Stuck := by
                        change __eo_prog_exists_string_length
                          (Term.Apply (Term.UOp UserOp.Seq) U) n id ≠
                          Term.Stuck at hProg
                        exact hProg
                      have hSeqWF :
                          __smtx_type_wf
                            (__eo_to_smt_type
                              (Term.Apply (Term.UOp UserOp.Seq) U)) = true := by
                        change
                          argTranslationOkMasked ArgTranslationKind.type
                              (Term.Apply (Term.UOp UserOp.Seq) U) ∧
                            argTranslationOkMasked ArgTranslationKind.term n ∧
                              argTranslationOkMasked ArgTranslationKind.term id ∧
                                True at hCmdTrans
                        exact hCmdTrans.1
                      have hnNe : n ≠ Term.Stuck := by
                        intro hn
                        subst n
                        exact hProg' rfl
                      have hIdNe0 : id ≠ Term.Stuck := by
                        intro hid
                        subst id
                        exact hProg' (by simp [__eo_prog_exists_string_length])
                      have hReqEq :
                          __eo_prog_exists_string_length
                            (Term.Apply (Term.UOp UserOp.Seq) U) n id =
                        __eo_requires
                            (__eo_gt n (Term.Numeral (-1 : native_Int)))
                            (Term.Boolean true)
                            (__eo_requires
                              (__eo_gt id (Term.Numeral (-1 : native_Int)))
                              (Term.Boolean true)
                              (eslFormula U n id)) := by
                        simp [eslFormula, __eo_prog_exists_string_length]
                      have hReqNe :
                          __eo_requires
                            (__eo_gt n (Term.Numeral (-1 : native_Int)))
                            (Term.Boolean true)
                            (__eo_requires
                              (__eo_gt id (Term.Numeral (-1 : native_Int)))
                              (Term.Boolean true)
                              (eslFormula U n id)) ≠
                            Term.Stuck := by
                        intro hStuck
                        exact hProg' (by simpa [hReqEq] using hStuck)
                      have hGtTrue :
                          __eo_gt n (Term.Numeral (-1 : native_Int)) =
                            Term.Boolean true :=
                        eo_requires_cond_eq_of_non_stuck hReqNe
                      rcases eo_gt_numeral_neg_one_eq_true hGtTrue with
                        ⟨k, rfl, hkGt⟩
                      have hInnerReqNe :
                          __eo_requires
                            (__eo_gt id (Term.Numeral (-1 : native_Int)))
                            (Term.Boolean true)
                            (eslFormula U (Term.Numeral k) id) ≠
                            Term.Stuck :=
                        eo_requires_result_ne_stuck_of_non_stuck hReqNe
                      have hIdGt :
                          __eo_gt id (Term.Numeral (-1 : native_Int)) =
                            Term.Boolean true :=
                        eo_requires_cond_eq_of_non_stuck hInnerReqNe
                      let A := __eo_to_smt_type U
                      have hSeqTy :
                          __eo_to_smt_type
                            (Term.Apply (Term.UOp UserOp.Seq) U) =
                            SmtType.Seq A := by
                        simpa [A] using eo_seq_type_eq_of_wf U hSeqWF
                      have hSeqWF' :
                          __smtx_type_wf (SmtType.Seq A) = true := by
                        simpa [hSeqTy] using hSeqWF
                      have hFormulaEq :
                          __eo_prog_exists_string_length
                            (Term.Apply (Term.UOp UserOp.Seq) U)
                            (Term.Numeral k) id =
                            eslFormula U (Term.Numeral k) id :=
                        prog_exists_string_length_eq_formula hkGt hIdGt
                      refine ⟨?_, ?_⟩
                      · intro _hPremises
                        change eo_interprets M
                          (__eo_prog_exists_string_length
                            (Term.Apply (Term.UOp UserOp.Seq) U)
                            (Term.Numeral k) id) true
                        rw [hFormulaEq]
                        exact eslFormula_true M U id A k hIdGt
                          hSeqTy hSeqWF' hkGt
                      · change RuleProofs.eo_has_smt_translation
                          (__eo_prog_exists_string_length
                            (Term.Apply (Term.UOp UserOp.Seq) U)
                            (Term.Numeral k) id)
                        rw [hFormulaEq]
                        exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (eslFormula_has_bool_type U id A k hkGt hIdGt
                            hSeqTy hSeqWF')
