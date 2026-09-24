module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

/-- From a non-stuck `__eo_typeof_str_lt`, both operands are `Seq Char`. -/
private theorem eo_typeof_str_lt_args_of_ne_stuck
    (T U : Term)
    (h : __eo_typeof_str_lt T U ≠ Term.Stuck) :
    T = Term.Apply Term.Seq Term.Char ∧ U = Term.Apply Term.Seq Term.Char := by
  cases T <;> simp [__eo_typeof_str_lt] at h ⊢
  case Apply f x =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      case Seq =>
        cases x <;> simp at h ⊢
        case UOp opx =>
          cases opx <;> simp at h ⊢
          case Char =>
            cases U <;> simp [__eo_typeof_str_lt] at h ⊢
            case Apply g y =>
              cases g <;> simp at h ⊢
              case UOp opg =>
                cases opg <;> simp at h ⊢
                case Seq =>
                  cases y <;> simp at h ⊢
                  case UOp opy =>
                    cases opy <;> simp at h ⊢

/-- Translates the SMT type of an EO term with `Seq Char` type. -/
private theorem smtx_typeof_of_eo_seq_char
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Apply Term.Seq Term.Char) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Seq SmtType.Char := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  rw [hTy] at hTyRaw
  rw [TranslationProofs.eo_to_smt_type_seq] at hTyRaw
  have hCharNN : __eo_to_smt_type Term.Char ≠ SmtType.None := by decide
  simpa [TranslationProofs.eo_to_smt_type_char] using hTyRaw.trans
    (TranslationProofs.smtx_typeof_guard_of_non_none
      (__eo_to_smt_type Term.Char) (SmtType.Seq (__eo_to_smt_type Term.Char)) hCharNN)

/-- Stable rewrite for evaluating SMT `str_lt` terms. -/
private theorem smtx_eval_str_lt_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_lt x y) =
      __smtx_model_eval_str_lt (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT `str_leq` terms. -/
private theorem smtx_eval_str_leq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_leq x y) =
      __smtx_model_eval_str_leq (__smtx_model_eval M x)
        (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT Boolean literal terms. -/
private theorem smtx_eval_boolean_term_eq
    (M : SmtModel) (b : Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

/-- `str_lt` of a native string with itself is `false` (irreflexivity). -/
private theorem native_str_lt_self (x : native_String) :
    native_str_lt x x = false := by
  simp [native_str_lt]

/-- The semantic model identity behind `str_lt_elim`, at the value level. -/
private theorem str_lt_elim_value_identity (vs vt : SmtValue) :
    __smtx_model_eval_str_lt vs vt =
      __smtx_model_eval_and
        (__smtx_model_eval_not (__smtx_model_eval_eq vs vt))
        (__smtx_model_eval_and
          (__smtx_model_eval_str_leq vs vt)
          (SmtValue.Boolean true)) := by
  cases vs <;> cases vt <;>
    simp [__smtx_model_eval_str_lt, __smtx_model_eval_str_leq,
      __smtx_model_eval_or, __smtx_model_eval_and, __smtx_model_eval_not,
      __smtx_model_eval_eq, native_veq, SmtEval.native_and, SmtEval.native_or,
      SmtEval.native_not]
  case Seq.Seq a b =>
    by_cases hEq : a = b
    · subst b
      simp [native_str_lt_self]
    · simp [hEq, native_veq]

/-- The rewritten right-hand side as an explicit `Term`. -/
private def str_lt_elim_rhs (s t : Term) : Term :=
  Term.Apply (Term.Apply Term.and (Term.Apply Term.not
      (Term.Apply (Term.Apply Term.eq s) t)))
    (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.str_leq s) t))
      (Term.Boolean true))

/-- `__eo_prog_str_lt_elim` on non-stuck arguments equals the explicit rewrite. -/
private theorem prog_str_lt_elim_eq_of_ne_stuck (s t : Term)
    (hs : s ≠ Term.Stuck) (ht : t ≠ Term.Stuck) :
    __eo_prog_str_lt_elim s t =
      Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_lt s) t))
        (str_lt_elim_rhs s t) := by
  cases hS : s <;> cases hT : t <;> first
    | exact False.elim (hs hS)
    | exact False.elim (ht hT)
    | rfl

/-- `str_leq s t` has Boolean type whenever its operands are `Seq Char`. -/
private theorem eo_has_bool_type_str_leq_of_seq_char (s t : Term)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.str_leq s) t) := by
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.str_leq (__eo_to_smt s) (__eo_to_smt t)) =
    SmtType.Bool
  rw [typeof_str_leq_eq]
  simp [hsTy, htTy, native_ite, native_Teq]

/-- `str_lt s t` has Boolean type whenever its operands are `Seq Char`. -/
private theorem eo_has_bool_type_str_lt_of_seq_char (s t : Term)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.str_lt s) t) := by
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.str_lt (__eo_to_smt s) (__eo_to_smt t)) =
    SmtType.Bool
  rw [typeof_str_lt_eq]
  simp [hsTy, htTy, native_ite, native_Teq]

/-- `eq s t` has Boolean type whenever its operands are `Seq Char`. -/
private theorem eo_has_bool_type_eq_of_seq_char (s t : Term)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq s) t) :=
  RuleProofs.eo_has_bool_type_eq_of_same_smt_type s t (by rw [hsTy, htTy])
    (by rw [hsTy]; simp)

/-- The rewritten right-hand side has Boolean type. -/
private theorem eo_has_bool_type_str_lt_elim_rhs (s t : Term)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char) :
    RuleProofs.eo_has_bool_type (str_lt_elim_rhs s t) := by
  unfold str_lt_elim_rhs
  have hEq := eo_has_bool_type_eq_of_seq_char s t hsTy htTy
  have hNotEq := RuleProofs.eo_has_bool_type_not_of_bool_arg _ hEq
  have hLeq := eo_has_bool_type_str_leq_of_seq_char s t hsTy htTy
  have hInner := RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hLeq
    RuleProofs.eo_has_bool_type_true
  exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hNotEq hInner

/-- The full conclusion of `str_lt_elim` has Boolean type. -/
private theorem typed___eo_prog_str_lt_elim_impl (s t : Term)
    (hsTrans : RuleProofs.eo_has_smt_translation s)
    (htTrans : RuleProofs.eo_has_smt_translation t)
    (hsTy : __eo_typeof s = Term.Apply Term.Seq Term.Char)
    (htTy : __eo_typeof t = Term.Apply Term.Seq Term.Char) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_lt_elim s t) := by
  have hsSmtTy := smtx_typeof_of_eo_seq_char s hsTrans hsTy
  have htSmtTy := smtx_typeof_of_eo_seq_char t htTrans htTy
  have hsNotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation s hsTrans
  have htNotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation t htTrans
  rw [prog_str_lt_elim_eq_of_ne_stuck s t hsNotStuck htNotStuck]
  have hLt := eo_has_bool_type_str_lt_of_seq_char s t hsSmtTy htSmtTy
  have hRhs := eo_has_bool_type_str_lt_elim_rhs s t hsSmtTy htSmtTy
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLt.trans hRhs.symm) (by rw [hLt]; decide)

/-- The model interprets the `str_lt_elim` conclusion as `true`. -/
private theorem facts___eo_prog_str_lt_elim_impl
    (M : SmtModel) (s t : Term)
    (hsTrans : RuleProofs.eo_has_smt_translation s)
    (htTrans : RuleProofs.eo_has_smt_translation t)
    (hsTy : __eo_typeof s = Term.Apply Term.Seq Term.Char)
    (htTy : __eo_typeof t = Term.Apply Term.Seq Term.Char) :
    eo_interprets M (__eo_prog_str_lt_elim s t) true := by
  have hsNotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation s hsTrans
  have htNotStuck := RuleProofs.term_ne_stuck_of_has_smt_translation t htTrans
  have hProgBool := typed___eo_prog_str_lt_elim_impl s t hsTrans htTrans hsTy htTy
  rw [prog_str_lt_elim_eq_of_ne_stuck s t hsNotStuck htNotStuck]
  have hProgBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_lt s) t))
          (str_lt_elim_rhs s t)) := by
    rwa [prog_str_lt_elim_eq_of_ne_stuck s t hsNotStuck htNotStuck] at hProgBool
  apply RuleProofs.eo_interprets_eq_of_rel M _ _ hProgBool'
  -- Reduce both sides of the relation to the value-level identity.
  unfold RuleProofs.smt_value_rel
  rw [show __eo_to_smt (Term.Apply (Term.Apply Term.str_lt s) t) =
      SmtTerm.str_lt (__eo_to_smt s) (__eo_to_smt t) from rfl]
  rw [show __eo_to_smt (str_lt_elim_rhs s t) =
      SmtTerm.and
        (SmtTerm.not (SmtTerm.eq (__eo_to_smt s) (__eo_to_smt t)))
        (SmtTerm.and (SmtTerm.str_leq (__eo_to_smt s) (__eo_to_smt t))
          (SmtTerm.Boolean true)) from rfl]
  rw [smtx_eval_str_lt_term_eq, smtx_eval_and_term_eq, smtx_eval_not_term_eq,
    smtx_eval_eq_term_eq, smtx_eval_and_term_eq, smtx_eval_str_leq_term_eq,
    smtx_eval_boolean_term_eq]
  rw [← str_lt_elim_value_identity]
  exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_str_lt_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_lt_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_lt_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_lt_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_lt_elim args premises ≠ Term.Stuck :=
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
              cases premises with
              | nil =>
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.1
                  have hA1NotStuck : a1 ≠ Term.Stuck := by
                    intro hStuck
                    subst a1
                    apply hProg
                    rfl
                  have hA2NotStuck : a2 ≠ Term.Stuck := by
                    intro hStuck
                    subst a2
                    apply hProg
                    cases a1 <;> rfl
                  have hProgEq :
                      __eo_cmd_step_proven s CRule.str_lt_elim
                        (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                        CIndexList.nil =
                        Term.Apply
                          (Term.Apply Term.eq
                            (Term.Apply (Term.Apply Term.str_lt a1) a2))
                          (str_lt_elim_rhs a1 a2) := by
                    change __eo_prog_str_lt_elim a1 a2 = _
                    exact prog_str_lt_elim_eq_of_ne_stuck a1 a2 hA1NotStuck hA2NotStuck
                  rw [hProgEq] at hResultTy
                  change __eo_typeof_eq
                    (__eo_typeof (Term.Apply (Term.Apply Term.str_lt a1) a2))
                    (__eo_typeof (str_lt_elim_rhs a1 a2)) = Term.Bool at hResultTy
                  have hLtNotStuck :
                      __eo_typeof (Term.Apply (Term.Apply Term.str_lt a1) a2) ≠
                        Term.Stuck :=
                    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).1
                  have hArgTypes :
                      __eo_typeof a1 = Term.Apply Term.Seq Term.Char ∧
                        __eo_typeof a2 = Term.Apply Term.Seq Term.Char := by
                    change __eo_typeof_str_lt (__eo_typeof a1) (__eo_typeof a2) ≠
                      Term.Stuck at hLtNotStuck
                    exact eo_typeof_str_lt_args_of_ne_stuck _ _ hLtNotStuck
                  rcases hArgTypes with ⟨hA1Ty, hA2Ty⟩
                  have hProps :
                      StepRuleProperties M (premiseTermList s CIndexList.nil)
                        (__eo_prog_str_lt_elim a1 a2) := by
                    refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_str_lt_elim_impl a1 a2 hA1Trans hA2Trans
                        hA1Ty hA2Ty)⟩
                    intro _hTrue
                    exact facts___eo_prog_str_lt_elim_impl M a1 a2
                      hA1Trans hA2Trans hA1Ty hA2Ty
                  change StepRuleProperties M [] (__eo_prog_str_lt_elim a1 a2)
                  simpa [premiseTermList] using hProps
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
