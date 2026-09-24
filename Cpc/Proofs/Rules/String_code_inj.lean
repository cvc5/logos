module

public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport
public import Cpc.Proofs.RuleSupport.StringSupport
import all Cpc.Proofs.RuleSupport.StringSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private def sciCode (t : Term) : Term :=
  Term.Apply Term.str_to_code t

private def sciEq (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.eq x) y

private def sciOr (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.or x) y

private def sciNot (x : Term) : Term :=
  Term.Apply Term.not x

private def sciCodeNeg (t : Term) : Term :=
  sciEq (sciCode t) (Term.Numeral (-1 : native_Int))

private def sciCodeEq (t s : Term) : Term :=
  sciEq (sciCode t) (sciCode s)

private def sciFormula (t s : Term) : Term :=
  sciOr (sciCodeNeg t)
    (sciOr (sciNot (sciCodeEq t s))
      (sciOr (sciEq t s) (Term.Boolean false)))

private theorem typeof_or_left_bool (A B : Term) :
    __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) = Term.Bool ->
    __eo_typeof A = Term.Bool := by
  intro h
  change __eo_typeof_or (__eo_typeof A) (__eo_typeof B) = Term.Bool at h
  cases hA : __eo_typeof A <;> cases hB : __eo_typeof B <;>
    simp [__eo_typeof_or, hA, hB] at h ⊢

private theorem typeof_or_right_bool (A B : Term) :
    __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) = Term.Bool ->
    __eo_typeof B = Term.Bool := by
  intro h
  change __eo_typeof_or (__eo_typeof A) (__eo_typeof B) = Term.Bool at h
  cases hA : __eo_typeof A <;> cases hB : __eo_typeof B <;>
    simp [__eo_typeof_or, hA, hB] at h ⊢

private theorem typeof_str_to_code_arg_string (t : Term) :
    __eo_typeof (sciCode t) = Term.UOp UserOp.Int ->
    __eo_typeof t = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  intro h
  unfold sciCode at h
  change __eo_typeof_str_to_code (__eo_typeof t) = Term.UOp UserOp.Int at h
  cases ht : __eo_typeof t <;> simp [__eo_typeof_str_to_code, ht] at h
  case Apply f a =>
    cases f
    all_goals try simp at h
    case UOp op =>
      cases op <;> try simp at h
      case Seq =>
        cases a <;> try simp at h
        case UOp op =>
          cases op <;> try simp at h
          case Char =>
            rfl

private theorem sciFormula_left_arg_string (t s : Term) :
    __eo_typeof (sciFormula t s) = Term.Bool ->
    __eo_typeof t = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  intro hTy
  have hLeft : __eo_typeof (sciCodeNeg t) = Term.Bool := by
    simpa [sciFormula, sciOr] using
      typeof_or_left_bool (sciCodeNeg t)
        (sciOr (sciNot (sciCodeEq t s))
          (sciOr (sciEq t s) (Term.Boolean false))) hTy
  have hCodeTy : __eo_typeof (sciCode t) = Term.UOp UserOp.Int := by
    unfold sciCodeNeg sciEq at hLeft
    change __eo_typeof_eq (__eo_typeof (sciCode t))
      (__eo_typeof (Term.Numeral (-1 : native_Int))) = Term.Bool at hLeft
    change __eo_typeof_eq (__eo_typeof (sciCode t)) (Term.UOp UserOp.Int) =
      Term.Bool at hLeft
    cases hCode : __eo_typeof (sciCode t) <;>
      simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
        native_not, hCode] at hLeft ⊢
    case UOp op =>
      cases op <;>
        simp at hLeft ⊢
  exact typeof_str_to_code_arg_string t hCodeTy

private theorem sciFormula_right_arg_string (t s : Term) :
    __eo_typeof (sciFormula t s) = Term.Bool ->
    __eo_typeof s = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  intro hTy
  have hRight : __eo_typeof
      (sciOr (sciNot (sciCodeEq t s))
        (sciOr (sciEq t s) (Term.Boolean false))) = Term.Bool := by
    simpa [sciFormula, sciOr] using
      typeof_or_right_bool (sciCodeNeg t)
        (sciOr (sciNot (sciCodeEq t s))
          (sciOr (sciEq t s) (Term.Boolean false))) hTy
  have hNot : __eo_typeof (sciNot (sciCodeEq t s)) = Term.Bool := by
    simpa [sciOr] using
      typeof_or_left_bool (sciNot (sciCodeEq t s))
        (sciOr (sciEq t s) (Term.Boolean false)) hRight
  have hCodeEq : __eo_typeof (sciCodeEq t s) = Term.Bool := by
    unfold sciNot at hNot
    change __eo_typeof_not (__eo_typeof (sciCodeEq t s)) = Term.Bool at hNot
    cases h : __eo_typeof (sciCodeEq t s) <;>
      simp [__eo_typeof_not, h] at hNot ⊢
  have hCodeSTy : __eo_typeof (sciCode s) = Term.UOp UserOp.Int := by
    have hTString :
        __eo_typeof t =
          Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
      sciFormula_left_arg_string t s hTy
    have hCodeTTy : __eo_typeof (sciCode t) = Term.UOp UserOp.Int := by
      unfold sciCode
      change __eo_typeof_str_to_code (__eo_typeof t) = Term.UOp UserOp.Int
      rw [hTString]
      rfl
    unfold sciCodeEq sciEq at hCodeEq
    change __eo_typeof_eq (__eo_typeof (sciCode t)) (__eo_typeof (sciCode s)) =
      Term.Bool at hCodeEq
    rw [hCodeTTy] at hCodeEq
    cases hS : __eo_typeof (sciCode s) <;>
      simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
        native_not, hS] at hCodeEq ⊢
    case UOp opT =>
      cases opT <;>
        simp at hCodeEq ⊢
  exact typeof_str_to_code_arg_string s hCodeSTy

private theorem smt_type_seq_char_of_eo_type
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : __eo_typeof t =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char := by
  have hRaw :
      __smtx_typeof (__eo_to_smt t) =
        __eo_to_smt_type
          (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
      (__eo_to_smt t) rfl hTrans hTy
  simpa [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq] using hRaw

private theorem sciCode_type_int
    (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char) :
    __smtx_typeof (__eo_to_smt (sciCode t)) = SmtType.Int := by
  unfold sciCode
  change __smtx_typeof (SmtTerm.str_to_code (__eo_to_smt t)) = SmtType.Int
  rw [typeof_str_to_code_eq, hTy]
  simp [native_ite, native_Teq]

private theorem sciFormula_has_bool_type
    (t s : Term)
    (hT : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hS : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char) :
    RuleProofs.eo_has_bool_type (sciFormula t s) := by
  have hCodeT : __smtx_typeof (__eo_to_smt (sciCode t)) = SmtType.Int :=
    sciCode_type_int t hT
  have hCodeS : __smtx_typeof (__eo_to_smt (sciCode s)) = SmtType.Int :=
    sciCode_type_int s hS
  have hCodeNeg :
      RuleProofs.eo_has_bool_type (sciCodeNeg t) := by
    unfold sciCodeNeg sciEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (sciCode t) (Term.Numeral (-1 : native_Int))
      (by
        rw [hCodeT]
        change SmtType.Int = __smtx_typeof (SmtTerm.Numeral (-1 : native_Int))
        rw [__smtx_typeof.eq_2])
      (by rw [hCodeT]; simp)
  have hCodeEq :
      RuleProofs.eo_has_bool_type (sciCodeEq t s) := by
    unfold sciCodeEq sciEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (sciCode t) (sciCode s) (by rw [hCodeT, hCodeS]) (by rw [hCodeT]; simp)
  have hNotCodeEq :
      RuleProofs.eo_has_bool_type (sciNot (sciCodeEq t s)) := by
    unfold sciNot
    exact RuleProofs.eo_has_bool_type_not_of_bool_arg (sciCodeEq t s) hCodeEq
  have hEq :
      RuleProofs.eo_has_bool_type (sciEq t s) := by
    unfold sciEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type t s
      (by rw [hT, hS]) (by rw [hT]; simp)
  have hEqFalse :
      RuleProofs.eo_has_bool_type (sciOr (sciEq t s) (Term.Boolean false)) := by
    unfold sciOr
    exact RuleProofs.eo_has_bool_type_or_of_bool_args (sciEq t s)
      (Term.Boolean false) hEq RuleProofs.eo_has_bool_type_false
  have hRight :
      RuleProofs.eo_has_bool_type
        (sciOr (sciNot (sciCodeEq t s))
          (sciOr (sciEq t s) (Term.Boolean false))) := by
    unfold sciOr
    exact RuleProofs.eo_has_bool_type_or_of_bool_args
      (sciNot (sciCodeEq t s)) (sciOr (sciEq t s) (Term.Boolean false))
      hNotCodeEq hEqFalse
  unfold sciFormula sciOr
  exact RuleProofs.eo_has_bool_type_or_of_bool_args (sciCodeNeg t)
    (sciOr (sciNot (sciCodeEq t s))
      (sciOr (sciEq t s) (Term.Boolean false))) hCodeNeg hRight

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

private theorem native_pack_string_unpack_string_of_typeof_seq_char
    (ss : SmtSeq)
    (hTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    native_pack_string (native_unpack_string ss) = ss := by
  have hTyped : list_typed SmtType.Char (native_unpack_seq ss) :=
    typed_unpack_seq_of_typeof_seq_value hTy
  have hMap :
      (native_unpack_seq ss).map
          (fun v => SmtValue.Char (impl_native_ssm_char_of_value v)) =
        native_unpack_seq ss :=
    list_typed_char_pack_unpack hTyped
  unfold native_pack_string native_unpack_string
  have hElem : __smtx_elem_typeof_seq_value ss = SmtType.Char :=
    elem_typeof_seq_value_of_typeof_seq_value hTy
  simp only [List.map_map]
  change native_pack_seq SmtType.Char
      ((native_unpack_seq ss).map (fun v => SmtValue.Char (impl_native_ssm_char_of_value v))) =
    ss
  rw [hMap]
  rw [← native_pack_unpack_seq ss, hElem]
  simp [_root_.native_unpack_pack_seq]

private theorem native_str_to_code_inj_of_ne_neg_one
    {xs ys : native_String}
    (hxs : native_string_valid xs = true)
    (hys : native_string_valid ys = true)
    (hCode : native_str_to_code xs = native_str_to_code ys)
    (hNe : native_str_to_code xs ≠ (-1 : native_Int)) :
    xs = ys := by
  cases xs with
  | nil =>
      simp [native_str_to_code] at hNe
  | cons c cs =>
      cases cs with
      | nil =>
          cases ys with
          | nil =>
              have hc : native_char_valid c = true := by
                simpa [native_string_valid] using hxs
              simp [native_str_to_code, hc] at hCode
          | cons d ds =>
              cases ds with
              | nil =>
                  have hc : native_char_valid c = true := by
                    simpa [native_string_valid] using hxs
                  have hd : native_char_valid d = true := by
                    simpa [native_string_valid] using hys
                  have hNat : c = d := by
                    have hInt : Int.ofNat c = Int.ofNat d := by
                      simpa [native_str_to_code, hc, hd] using hCode
                    exact Int.ofNat.inj hInt
                  simp [hNat]
              | cons _ _ =>
                  have hc : native_char_valid c = true := by
                    simpa [native_string_valid] using hxs
                  have hFalse : Int.ofNat c = (-1 : native_Int) := by
                    simpa [native_str_to_code, hc] using hCode
                  have hNonneg : (0 : Int) ≤ Int.ofNat c := Int.natCast_nonneg c
                  exact False.elim (by omega)
      | cons _ _ =>
          simp [native_str_to_code] at hNe

private theorem eval_seq_of_seq_char_type
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char) :
    ∃ ss : SmtSeq,
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq ss ∧
        __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
  have hPres :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq SmtType.Char := by
    simpa [hTy] using
      type_preservation M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTy]
        simp)
  rcases seq_value_canonical hPres with ⟨ss, hEval⟩
  refine ⟨ss, hEval, ?_⟩
  simpa [hEval, __smtx_typeof_value] using hPres

private theorem facts_sciFormula
    (M : SmtModel) (hM : model_wf M) (t s : Term)
    (hT : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hS : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char) :
    eo_interprets M (sciFormula t s) true := by
  have hFormulaBool : RuleProofs.eo_has_bool_type (sciFormula t s) :=
    sciFormula_has_bool_type t s hT hS
  rcases eval_seq_of_seq_char_type M hM t hT with ⟨ts, hEvalT, hTsTy⟩
  rcases eval_seq_of_seq_char_type M hM s hS with ⟨ss, hEvalS, hSsTy⟩
  have hValidT : native_string_valid (native_unpack_string ts) = true :=
    native_unpack_string_valid_of_typeof_seq_char hTsTy
  have hValidS : native_string_valid (native_unpack_string ss) = true :=
    native_unpack_string_valid_of_typeof_seq_char hSsTy
  apply RuleProofs.eo_interprets_of_bool_eval M (sciFormula t s) true hFormulaBool
  change __smtx_model_eval M
      (SmtTerm.or
        (SmtTerm.eq (SmtTerm.str_to_code (__eo_to_smt t))
          (SmtTerm.Numeral (-1 : native_Int)))
        (SmtTerm.or
          (SmtTerm.not
            (SmtTerm.eq (SmtTerm.str_to_code (__eo_to_smt t))
              (SmtTerm.str_to_code (__eo_to_smt s))))
          (SmtTerm.or (SmtTerm.eq (__eo_to_smt t) (__eo_to_smt s))
            (SmtTerm.Boolean false)))) = SmtValue.Boolean true
  by_cases hNeg : native_str_to_code (native_unpack_string ts) = (-1 : native_Int)
  · simp [__smtx_model_eval.eq_8, __smtx_model_eval.eq_7,
      smtx_eval_eq_term_eq, smtx_eval_str_to_code_term_eq,
      __smtx_model_eval.eq_2, __smtx_model_eval.eq_1,
      hEvalT, hEvalS, hNeg, __smtx_model_eval_str_to_code,
      __smtx_model_eval_eq, __smtx_model_eval_or, __smtx_model_eval_not,
      native_veq, SmtEval.native_or, SmtEval.native_not]
  · by_cases hCodes :
        native_str_to_code (native_unpack_string ts) =
          native_str_to_code (native_unpack_string ss)
    · have hString :
          native_unpack_string ts = native_unpack_string ss :=
        native_str_to_code_inj_of_ne_neg_one hValidT hValidS hCodes hNeg
      have hSeq : ts = ss := by
        rw [← native_pack_string_unpack_string_of_typeof_seq_char ts hTsTy,
          ← native_pack_string_unpack_string_of_typeof_seq_char ss hSsTy, hString]
      simp [__smtx_model_eval.eq_8, __smtx_model_eval.eq_7,
        smtx_eval_eq_term_eq, smtx_eval_str_to_code_term_eq,
        __smtx_model_eval.eq_2, __smtx_model_eval.eq_1,
        hEvalT, hEvalS,hSeq, __smtx_model_eval_str_to_code,
        __smtx_model_eval_eq, __smtx_model_eval_or, __smtx_model_eval_not,
        native_veq, SmtEval.native_or, SmtEval.native_not]
    · simp [__smtx_model_eval.eq_8, __smtx_model_eval.eq_7,
        smtx_eval_eq_term_eq, smtx_eval_str_to_code_term_eq,
        __smtx_model_eval.eq_2, __smtx_model_eval.eq_1,
        hEvalT, hEvalS, hNeg, hCodes, __smtx_model_eval_str_to_code,
        __smtx_model_eval_eq, __smtx_model_eval_or, __smtx_model_eval_not,
        native_veq, SmtEval.native_or, SmtEval.native_not]

public theorem cmd_step_string_code_inj_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_code_inj args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.string_code_inj args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_code_inj args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.string_code_inj args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons t args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons u args =>
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
                  let T := t
                  let U := u
                  have hTNe : T ≠ Term.Stuck := by
                    intro h
                    subst h
                    change __eo_prog_string_code_inj Term.Stuck U ≠ Term.Stuck at hProg
                    exact hProg rfl
                  have hUNe : U ≠ Term.Stuck := by
                    intro h
                    subst h
                    change __eo_prog_string_code_inj T Term.Stuck ≠ Term.Stuck at hProg
                    simpa [__eo_prog_string_code_inj, hTNe] using hProg
                  have hProgEq : __eo_prog_string_code_inj T U = sciFormula T U := by
                    simp [__eo_prog_string_code_inj, sciFormula, sciOr, sciCodeNeg,
                      sciCodeEq, sciEq, sciCode, sciNot]
                  have hFormulaTy : __eo_typeof (sciFormula T U) = Term.Bool := by
                    change __eo_typeof (__eo_prog_string_code_inj T U) = Term.Bool at hResultTy
                    simpa [hProgEq] using hResultTy
                  have hTTrans : RuleProofs.eo_has_smt_translation T := by
                    simpa [T, RuleProofs.eo_has_smt_translation, eoHasSmtTranslation,
                      cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
                  have hUTrans : RuleProofs.eo_has_smt_translation U := by
                    simpa [U, RuleProofs.eo_has_smt_translation, eoHasSmtTranslation,
                      cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.1
                  have hTEoTy :
                      __eo_typeof T =
                        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
                    sciFormula_left_arg_string T U hFormulaTy
                  have hUEoTy :
                      __eo_typeof U =
                        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
                    sciFormula_right_arg_string T U hFormulaTy
                  have hTSmt :
                      __smtx_typeof (__eo_to_smt T) = SmtType.Seq SmtType.Char :=
                    smt_type_seq_char_of_eo_type T hTTrans hTEoTy
                  have hUSmt :
                      __smtx_typeof (__eo_to_smt U) = SmtType.Seq SmtType.Char :=
                    smt_type_seq_char_of_eo_type U hUTrans hUEoTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_string_code_inj T U) true
                    rw [hProgEq]
                    exact facts_sciFormula M hM T U hTSmt hUSmt
                  · change RuleProofs.eo_has_smt_translation (__eo_prog_string_code_inj T U)
                    rw [hProgEq]
                    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (sciFormula_has_bool_type T U hTSmt hUSmt)
