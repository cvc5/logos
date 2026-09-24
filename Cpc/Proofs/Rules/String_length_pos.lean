module

public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport
public import Cpc.Proofs.RuleSupport.StringSupport
import all Cpc.Proofs.RuleSupport.StringSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def slpLen (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp.str_len) x

private def slpEq (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

private def slpAnd (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y

private def slpOr (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y

private def slpGt (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.gt) x) y

private def slpFormula (x : Term) : Term :=
  slpOr
    (slpAnd (slpEq (slpLen x) (Term.Numeral 0))
      (slpAnd (slpEq x (__seq_empty (__eo_typeof x))) (Term.Boolean true)))
    (slpOr (slpGt (slpLen x) (Term.Numeral 0)) (Term.Boolean false))

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

private theorem typeof_str_len_arg_seq (x : Term) :
    __eo_typeof (Term.Apply (Term.UOp UserOp.str_len) x) = Term.UOp UserOp.Int ->
    ∃ U, __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) U := by
  intro h
  change __eo_typeof_str_len (__eo_typeof x) = Term.UOp UserOp.Int at h
  cases hX : __eo_typeof x <;> simp [__eo_typeof_str_len, hX] at h
  case Apply f a =>
    cases f <;> try simp at h
    case UOp op =>
      cases op <;> simp at h
      case Seq =>
        exact ⟨a, rfl⟩

private theorem typeof_gt_zero_left_int (x : Term) :
    __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x) (Term.Numeral 0)) =
      Term.Bool ->
    __eo_typeof x = Term.UOp UserOp.Int := by
  intro h
  change __eo_typeof_lt (__eo_typeof x) (__eo_typeof (Term.Numeral 0)) =
    Term.Bool at h
  change __eo_typeof_lt (__eo_typeof x) (Term.UOp UserOp.Int) = Term.Bool at h
  cases hX : __eo_typeof x <;>
    simp [__eo_typeof_lt, __eo_requires, __eo_eq, __is_arith_type,
      hX, native_ite, native_teq, native_not] at h ⊢
  case UOp op =>
    cases op <;>
      simp at h ⊢

private theorem typeof_mk_or_right_bool (A B : Term) :
    __eo_typeof (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.or) A) B) =
      Term.Bool ->
    __eo_typeof B = Term.Bool := by
  intro h
  cases hA : A <;> cases hB : B <;> simp [__eo_mk_apply, hA, hB] at h ⊢
  all_goals
    first
    | exact typeof_or_right_bool _ _ h
    | have hNo : __eo_typeof Term.Stuck ≠ Term.Bool := by native_decide
      exact False.elim (hNo h)

private theorem prog_string_length_pos_arg_seq
    (x : Term) :
    __eo_typeof (__eo_prog_string_length_pos x) = Term.Bool ->
    ∃ U, __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) U := by
  intro hTy
  by_cases hx : x = Term.Stuck
  · subst hx
    have hNo : __eo_typeof Term.Stuck ≠ Term.Bool := by native_decide
    exact False.elim (hNo hTy)
  · unfold __eo_prog_string_length_pos at hTy
    simp at hTy
    have hRight := typeof_mk_or_right_bool _ _ hTy
    have hGtBool := typeof_or_left_bool _ _ hRight
    have hLenInt := typeof_gt_zero_left_int _ hGtBool
    exact typeof_str_len_arg_seq x hLenInt

private theorem prog_string_length_pos_eq_formula
    (x : Term)
    (hx : x ≠ Term.Stuck)
    (hEmpty : __seq_empty (__eo_typeof x) ≠ Term.Stuck) :
    __eo_prog_string_length_pos x = slpFormula x := by
  unfold __eo_prog_string_length_pos slpFormula slpLen slpEq slpAnd slpOr slpGt
  simp [__eo_mk_apply]

private theorem typeof_eo_str_len_of_seq
    (s : Term) (T : SmtType)
    (hSTySeq : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (slpLen s)) = SmtType.Int := by
  unfold slpLen
  change __smtx_typeof (SmtTerm.str_len (__eo_to_smt s)) = SmtType.Int
  rw [typeof_str_len_eq, hSTySeq]
  simp [__smtx_typeof_seq_op_1_ret]

private theorem eval_eo_str_len_of_seq
    (M : SmtModel) (s : Term) (ss : SmtSeq)
    (hEvalS : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss) :
    __smtx_model_eval M (__eo_to_smt (slpLen s)) =
      SmtValue.Numeral (native_seq_len (native_unpack_seq ss)) := by
  unfold slpLen
  change __smtx_model_eval M (SmtTerm.str_len (__eo_to_smt s)) =
    SmtValue.Numeral (native_seq_len (native_unpack_seq ss))
  rw [smtx_eval_str_len_term_eq, hEvalS]
  rfl

private theorem typeof_eo_zero :
    __smtx_typeof (__eo_to_smt (Term.Numeral 0)) = SmtType.Int := by
  change __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int
  rw [__smtx_typeof.eq_2]

private theorem eval_eo_zero (M : SmtModel) :
    __smtx_model_eval M (__eo_to_smt (Term.Numeral 0)) = SmtValue.Numeral 0 := by
  change __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0
  rw [__smtx_model_eval.eq_2]

private theorem eo_has_bool_type_gt_of_int_args (x y : Term)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int) :
    RuleProofs.eo_has_bool_type (slpGt x y) := by
  unfold RuleProofs.eo_has_bool_type slpGt
  change __smtx_typeof (SmtTerm.gt (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool
  rw [typeof_gt_eq, hx, hy]
  simp [__smtx_typeof_arith_overload_op_2_ret]

private theorem smt_typeof_of_prog_string_length_pos
    (x : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hResultTy : __eo_typeof (__eo_prog_string_length_pos x) = Term.Bool) :
    ∃ T, __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
  rcases prog_string_length_pos_arg_seq x hResultTy with ⟨U, hXSeq⟩
  let T := __eo_to_smt_type U
  refine ⟨T, ?_⟩
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
  have hRaw :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof_guard T (SmtType.Seq T) := by
    rw [hTypeMatch, hXSeq]
    change __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U) =
      __smtx_typeof_guard T (SmtType.Seq T)
    rw [TranslationProofs.eo_to_smt_type_seq]
  have hTNonNone : T ≠ SmtType.None := by
    intro hNone
    apply hXTrans
    rw [hRaw, hNone]
    simp [__smtx_typeof_guard, native_ite, native_Teq]
  rw [hRaw]
  simp [__smtx_typeof_guard, hTNonNone, native_ite, native_Teq]

private theorem slpFormula_has_bool_type
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (slpFormula x) := by
  have hLenTy : __smtx_typeof (__eo_to_smt (slpLen x)) = SmtType.Int :=
    typeof_eo_str_len_of_seq x T hxTy
  have hZeroTy : __smtx_typeof (__eo_to_smt (Term.Numeral 0)) = SmtType.Int :=
    typeof_eo_zero
  rcases smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy with
    ⟨hTInh, hTWf⟩
  have hEmptyNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
        SmtType.None :=
    seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf x T hxTy hTInh hTWf
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
        SmtType.Seq T :=
    smt_typeof_seq_empty_typeof x T hxTy hEmptyNN
  have hEqLenBool : RuleProofs.eo_has_bool_type (slpEq (slpLen x) (Term.Numeral 0)) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (slpLen x) (Term.Numeral 0) (by rw [hLenTy, hZeroTy])
      (by rw [hLenTy]; simp)
  have hEqEmptyBool : RuleProofs.eo_has_bool_type
      (slpEq x (__seq_empty (__eo_typeof x))) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      x (__seq_empty (__eo_typeof x)) (by rw [hxTy, hEmptyTy])
      (by rw [hxTy]; simp)
  have hInnerBool : RuleProofs.eo_has_bool_type
      (slpAnd (slpEq x (__seq_empty (__eo_typeof x))) (Term.Boolean true)) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args _ _
      hEqEmptyBool RuleProofs.eo_has_bool_type_true
  have hLeftBool : RuleProofs.eo_has_bool_type
      (slpAnd (slpEq (slpLen x) (Term.Numeral 0))
        (slpAnd (slpEq x (__seq_empty (__eo_typeof x))) (Term.Boolean true))) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hEqLenBool hInnerBool
  have hGtBool : RuleProofs.eo_has_bool_type (slpGt (slpLen x) (Term.Numeral 0)) :=
    eo_has_bool_type_gt_of_int_args (slpLen x) (Term.Numeral 0) hLenTy hZeroTy
  have hRightBool : RuleProofs.eo_has_bool_type
      (slpOr (slpGt (slpLen x) (Term.Numeral 0)) (Term.Boolean false)) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args _ _
      hGtBool RuleProofs.eo_has_bool_type_false
  unfold slpFormula
  exact RuleProofs.eo_has_bool_type_or_of_bool_args _ _ hLeftBool hRightBool

private theorem prog_string_length_pos_has_bool_type
    (x : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hResultTy : __eo_typeof (__eo_prog_string_length_pos x) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_string_length_pos x) := by
  rcases smt_typeof_of_prog_string_length_pos x hXTrans hResultTy with ⟨T, hxTy⟩
  have hxNonStuck : x ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_seq x T hxTy
  have hEmptyNonStuck : __seq_empty (__eo_typeof x) ≠ Term.Stuck :=
    seq_empty_typeof_ne_stuck_of_smt_type_seq x T hxTy
  rw [prog_string_length_pos_eq_formula x hxNonStuck hEmptyNonStuck]
  exact slpFormula_has_bool_type x T hxTy

private theorem slpFormula_true
    (M : SmtModel) (hM : model_wf M)
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    eo_interprets M (slpFormula x) true := by
  have hLenTy : __smtx_typeof (__eo_to_smt (slpLen x)) = SmtType.Int :=
    typeof_eo_str_len_of_seq x T hxTy
  have hZeroTy : __smtx_typeof (__eo_to_smt (Term.Numeral 0)) = SmtType.Int :=
    typeof_eo_zero
  rcases smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T hxTy with
    ⟨hTInh, hTWf⟩
  have hEmptyNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
        SmtType.None :=
    seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf x T hxTy hTInh hTWf
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
        SmtType.Seq T :=
    smt_typeof_seq_empty_typeof x T hxTy hEmptyNN
  have hEqLenBool : RuleProofs.eo_has_bool_type (slpEq (slpLen x) (Term.Numeral 0)) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (slpLen x) (Term.Numeral 0) (by rw [hLenTy, hZeroTy])
      (by rw [hLenTy]; simp)
  have hEqEmptyBool : RuleProofs.eo_has_bool_type
      (slpEq x (__seq_empty (__eo_typeof x))) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      x (__seq_empty (__eo_typeof x)) (by rw [hxTy, hEmptyTy])
      (by rw [hxTy]; simp)
  have hInnerBool : RuleProofs.eo_has_bool_type
      (slpAnd (slpEq x (__seq_empty (__eo_typeof x))) (Term.Boolean true)) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args _ _
      hEqEmptyBool RuleProofs.eo_has_bool_type_true
  have hLeftBool : RuleProofs.eo_has_bool_type
      (slpAnd (slpEq (slpLen x) (Term.Numeral 0))
        (slpAnd (slpEq x (__seq_empty (__eo_typeof x))) (Term.Boolean true))) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hEqLenBool hInnerBool
  have hGtBool : RuleProofs.eo_has_bool_type (slpGt (slpLen x) (Term.Numeral 0)) :=
    eo_has_bool_type_gt_of_int_args (slpLen x) (Term.Numeral 0) hLenTy hZeroTy
  have hRightBool : RuleProofs.eo_has_bool_type
      (slpOr (slpGt (slpLen x) (Term.Numeral 0)) (Term.Boolean false)) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args _ _
      hGtBool RuleProofs.eo_has_bool_type_false
  have hEvalSTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Seq T :=
    smt_model_eval_preserves_type M hM (__eo_to_smt x) (SmtType.Seq T)
      hxTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hEvalSTy with ⟨ss, hEvalS⟩
  cases ss with
  | empty T0 =>
      have hSeqTy : SmtType.Seq T0 = SmtType.Seq T := by
        simpa [__smtx_typeof_value, __smtx_typeof_seq_value, hEvalS] using hEvalSTy
      have hT0 : T0 = T := by
        injection hSeqTy
      have hEvalS_T :
          __smtx_model_eval M (__eo_to_smt x) =
            SmtValue.Seq (SmtSeq.empty T) := by
        simpa [hT0] using hEvalS
      have hLenEval :
          __smtx_model_eval M (__eo_to_smt (slpLen x)) = SmtValue.Numeral 0 := by
        have hRaw := eval_eo_str_len_of_seq M x (SmtSeq.empty T0) hEvalS
        simpa [native_unpack_seq, native_seq_len] using hRaw
      have hEqLenEval :
          __smtx_model_eval M (__eo_to_smt (slpEq (slpLen x) (Term.Numeral 0))) =
            SmtValue.Boolean true := by
        unfold slpEq
        change
          __smtx_model_eval M
              (SmtTerm.eq (__eo_to_smt (slpLen x)) (__eo_to_smt (Term.Numeral 0))) =
            SmtValue.Boolean true
        rw [smtx_eval_eq_term_eq, hLenEval, eval_eo_zero M]
        simp [__smtx_model_eval_eq, native_veq]
      have hEqLenTrue :
          eo_interprets M (slpEq (slpLen x) (Term.Numeral 0)) true :=
        RuleProofs.eo_interprets_of_bool_eval M _ true hEqLenBool hEqLenEval
      have hEmptyEval :
          __smtx_model_eval M (__eo_to_smt (__seq_empty (__eo_typeof x))) =
            SmtValue.Seq (SmtSeq.empty T) :=
        eval_seq_empty_typeof M x T hxTy
      have hEqEmptyTrue :
          eo_interprets M (slpEq x (__seq_empty (__eo_typeof x))) true := by
        exact RuleProofs.eo_interprets_eq_of_rel M x (__seq_empty (__eo_typeof x))
          hEqEmptyBool <| by
            rw [hEvalS_T, hEmptyEval]
            exact RuleProofs.smt_value_rel_refl _
      have hInnerTrue :
          eo_interprets M
            (slpAnd (slpEq x (__seq_empty (__eo_typeof x))) (Term.Boolean true)) true :=
        RuleProofs.eo_interprets_and_intro M _ _
          hEqEmptyTrue (RuleProofs.eo_interprets_true M)
      have hLeftTrue :
          eo_interprets M
            (slpAnd (slpEq (slpLen x) (Term.Numeral 0))
              (slpAnd (slpEq x (__seq_empty (__eo_typeof x))) (Term.Boolean true))) true :=
        RuleProofs.eo_interprets_and_intro M _ _ hEqLenTrue hInnerTrue
      unfold slpFormula
      exact RuleProofs.eo_interprets_or_left_intro M hM _ _ hLeftTrue hRightBool
  | cons v vs =>
      have hLenEval :
          __smtx_model_eval M (__eo_to_smt (slpLen x)) =
            SmtValue.Numeral
              (native_seq_len (native_unpack_seq (SmtSeq.cons v vs))) :=
        eval_eo_str_len_of_seq M x (SmtSeq.cons v vs) hEvalS
      have hGtEval :
          __smtx_model_eval M (__eo_to_smt (slpGt (slpLen x) (Term.Numeral 0))) =
            SmtValue.Boolean true := by
        unfold slpGt
        change
          __smtx_model_eval M
              (SmtTerm.gt (__eo_to_smt (slpLen x)) (__eo_to_smt (Term.Numeral 0))) =
            SmtValue.Boolean true
        simp [__smtx_model_eval, hLenEval, eval_eo_zero M,
          __smtx_model_eval_gt, __smtx_model_eval_lt, native_zlt,
          native_seq_len, native_unpack_seq]
      have hGtTrue :
          eo_interprets M (slpGt (slpLen x) (Term.Numeral 0)) true :=
        RuleProofs.eo_interprets_of_bool_eval M _ true hGtBool hGtEval
      have hRightTrue :
          eo_interprets M
            (slpOr (slpGt (slpLen x) (Term.Numeral 0)) (Term.Boolean false)) true :=
        RuleProofs.eo_interprets_or_left_intro M hM _ _
          hGtTrue RuleProofs.eo_has_bool_type_false
      unfold slpFormula
      exact RuleProofs.eo_interprets_or_right_intro M hM _ _ hLeftBool hRightTrue

private theorem prog_string_length_pos_true
    (M : SmtModel) (hM : model_wf M)
    (x : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hResultTy : __eo_typeof (__eo_prog_string_length_pos x) = Term.Bool) :
    eo_interprets M (__eo_prog_string_length_pos x) true := by
  rcases smt_typeof_of_prog_string_length_pos x hXTrans hResultTy with ⟨T, hxTy⟩
  have hxNonStuck : x ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_seq x T hxTy
  have hEmptyNonStuck : __seq_empty (__eo_typeof x) ≠ Term.Stuck :=
    seq_empty_typeof_ne_stuck_of_smt_type_seq x T hxTy
  rw [prog_string_length_pos_eq_formula x hxNonStuck hEmptyNonStuck]
  exact slpFormula_true M hM x T hxTy

public theorem cmd_step_string_length_pos_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_length_pos args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.string_length_pos args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_length_pos args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.string_length_pos args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons x args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hXTrans : RuleProofs.eo_has_smt_translation x := by
                change eoHasSmtTranslation x ∧ True at hCmdTrans
                exact hCmdTrans.1
              have hResultTy' :
                  __eo_typeof (__eo_prog_string_length_pos x) = Term.Bool := by
                change __eo_typeof (__eo_prog_string_length_pos x) = Term.Bool at hResultTy
                exact hResultTy
              refine ⟨?_, ?_⟩
              · intro _hPremises
                change eo_interprets M (__eo_prog_string_length_pos x) true
                exact prog_string_length_pos_true M hM x hXTrans hResultTy'
              · change RuleProofs.eo_has_smt_translation (__eo_prog_string_length_pos x)
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (prog_string_length_pos_has_bool_type x hXTrans hResultTy')
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
