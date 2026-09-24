module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ArithIntEqConflict

private abbrev toRealTerm (t : Term) : Term :=
  Term.Apply (Term.UOp UserOp.to_real) t

private abbrev toIntTerm (t : Term) : Term :=
  Term.Apply (Term.UOp UserOp.to_int) t

private abbrev eqTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

private abbrev nonIntPremise (c0 c1 : Term) : Term :=
  eqTerm (eqTerm (toRealTerm (toIntTerm c0)) c1) (Term.Boolean false)

private abbrev conclusionTerm (t c : Term) : Term :=
  eqTerm (eqTerm (toRealTerm t) c) (Term.Boolean false)

private theorem eo_to_smt_to_real_eq (x : Term) :
    __eo_to_smt (toRealTerm x) = SmtTerm.to_real (__eo_to_smt x) := by
  rfl

private theorem eo_to_smt_to_int_eq (x : Term) :
    __eo_to_smt (toIntTerm x) = SmtTerm.to_int (__eo_to_smt x) := by
  rfl

private theorem native_to_int_to_real (n : native_Int) :
    native_to_int (native_to_real n) = n := by
  rw [native_to_int, native_to_real, native_mk_rational]
  change Rat.floor ((n : Rat) / (1 : Rat)) = n
  have hDiv : ((n : Rat) / (1 : Rat)) = (n : Rat) := by
    change (n : Rat) * ((1 : Rat)⁻¹) = (n : Rat)
    rw [Rat.inv_def]
    change (n : Rat) * Rat.divInt 1 1 = (n : Rat)
    rw [show Rat.divInt 1 1 = (1 : Rat) by rfl]
    exact Rat.mul_one _
  rw [hDiv]
  exact Rat.floor_intCast n

private theorem smtx_typeof_of_eo_type
    (a T : Term) (S : SmtType)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = T)
    (hSTy : __eo_to_smt_type T = S) :
    __smtx_typeof (__eo_to_smt a) = S := by
  exact (TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
    a T (__eo_to_smt a) rfl hTrans hTy).trans hSTy

private theorem prog_arith_int_eq_conflict_info
    (t c P : Term)
    (hProg : __eo_prog_arith_int_eq_conflict t c (Proof.pf P) ≠ Term.Stuck) :
    ∃ c0 c1,
      P = nonIntPremise c0 c1 ∧
      c0 = c ∧ c1 = c ∧
      __eo_prog_arith_int_eq_conflict t c (Proof.pf P) =
        conclusionTerm t c := by
  unfold __eo_prog_arith_int_eq_conflict at hProg
  split at hProg <;> try contradiction
  next h1 h2 heq =>
    rename_i tArg cArg _ _ _ c0 c1
    injection heq with hPEq
    have hBoth : c0 = cArg ∧ c1 = cArg := by
      exact RuleProofs.eqs_of_requires_and_eq_true_not_stuck
        cArg cArg c0 c1 _ hProg
    rcases hBoth with ⟨hc0, hc1⟩
    refine ⟨c0, c1, ?_, hc0, hc1, ?_⟩
    · simpa [nonIntPremise, eqTerm, toRealTerm, toIntTerm] using hPEq
    · rw [hPEq, hc0, hc1]
      simp [__eo_prog_arith_int_eq_conflict, __eo_requires, __eo_and,
        __eo_eq, SmtEval.native_ite, native_teq, SmtEval.native_not,
        native_and, conclusionTerm, toRealTerm, eqTerm]

/-- Since `to_real` accepts `Int` only, a well-typed conclusion forces `t : Int`. -/
private theorem eo_typeof_int_of_to_real_ne_stuck {A : Term}
    (h : __eo_typeof_to_real A ≠ Term.Stuck) :
    A = Term.Int := by
  cases A <;> simp [__eo_typeof_to_real] at h ⊢
  case UOp op =>
    cases op <;> simp [__eo_typeof_to_real] at h ⊢

/-- Recovers the `Int` type of the `to_real` argument from the conclusion's type. -/
private theorem t_int_of_result_bool
    (t c : Term)
    (hTy : __eo_typeof (conclusionTerm t c) = Term.Bool) :
    __eo_typeof t = Term.Int := by
  change __eo_typeof_eq (__eo_typeof (eqTerm (toRealTerm t) c))
      Term.Bool = Term.Bool at hTy
  change __eo_typeof_eq
      (__eo_typeof_eq (__eo_typeof (toRealTerm t)) (__eo_typeof c))
      Term.Bool = Term.Bool at hTy
  change __eo_typeof_eq
      (__eo_typeof_eq (__eo_typeof_to_real (__eo_typeof t)) (__eo_typeof c))
      Term.Bool = Term.Bool at hTy
  refine eo_typeof_int_of_to_real_ne_stuck ?_
  intro hSt
  rw [hSt] at hTy
  simp [__eo_typeof_eq] at hTy

private theorem c_real_of_result_bool
    (t c : Term)
    (hTInt : __eo_typeof t = Term.Int)
    (hTy : __eo_typeof (conclusionTerm t c) = Term.Bool) :
    __eo_typeof c = Term.Real := by
  change __eo_typeof_eq (__eo_typeof (eqTerm (toRealTerm t) c))
      Term.Bool = Term.Bool at hTy
  change __eo_typeof_eq
      (__eo_typeof_eq (__eo_typeof (toRealTerm t)) (__eo_typeof c))
      Term.Bool = Term.Bool at hTy
  change __eo_typeof_eq
      (__eo_typeof_eq (__eo_typeof_to_real (__eo_typeof t)) (__eo_typeof c))
      Term.Bool = Term.Bool at hTy
  rw [hTInt] at hTy
  cases hc : __eo_typeof c with
  | UOp op =>
      cases op <;> simp [__eo_typeof_eq, __eo_typeof_to_real,
        __eo_requires, __is_arith_type, __eo_eq, native_ite, native_teq,
        native_not, SmtEval.native_not, hc] at hTy ⊢
  | _ =>
      simp [__eo_typeof_eq, __eo_typeof_to_real, __eo_requires,
        __is_arith_type, __eo_eq, native_ite, native_teq, native_not,
        SmtEval.native_not, hc] at hTy

private theorem typed___eo_prog_arith_int_eq_conflict_impl
    (t c P : Term) :
    RuleProofs.eo_has_smt_translation t ->
    RuleProofs.eo_has_smt_translation c ->
    __eo_prog_arith_int_eq_conflict t c (Proof.pf P) =
      conclusionTerm t c ->
    __eo_typeof (__eo_prog_arith_int_eq_conflict t c (Proof.pf P)) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (__eo_prog_arith_int_eq_conflict t c (Proof.pf P)) := by
  intro hTTrans hCTrans hProgEq hResultTy
  have hResultTy' : __eo_typeof (conclusionTerm t c) = Term.Bool := by
    simpa [hProgEq] using hResultTy
  have hTInt : __eo_typeof t = Term.Int :=
    t_int_of_result_bool t c hResultTy'
  have hCReal : __eo_typeof c = Term.Real :=
    c_real_of_result_bool t c hTInt hResultTy'
  have hTSmtTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    smtx_typeof_of_eo_type t Term.Int SmtType.Int hTTrans hTInt rfl
  have hCSmtTy : __smtx_typeof (__eo_to_smt c) = SmtType.Real :=
    smtx_typeof_of_eo_type c Term.Real SmtType.Real hCTrans hCReal rfl
  have hToRealTy :
      __smtx_typeof (__eo_to_smt (toRealTerm t)) = SmtType.Real := by
    rw [eo_to_smt_to_real_eq, typeof_to_real_eq]
    simp [native_ite, native_Teq, hTSmtTy]
  have hInnerTy :
      __smtx_typeof (__eo_to_smt (eqTerm (toRealTerm t) c)) =
        SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.eq (__eo_to_smt (toRealTerm t)) (__eo_to_smt c)) =
        SmtType.Bool
    rw [typeof_eq_eq]
    simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq,
      hToRealTy, hCSmtTy]
  have hInnerTrans :
      RuleProofs.eo_has_smt_translation (eqTerm (toRealTerm t) c) := by
    simp [RuleProofs.eo_has_smt_translation, hInnerTy]
  rw [hProgEq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (eqTerm (toRealTerm t) c) (Term.Boolean false)
    (by
      rw [hInnerTy]
      change SmtType.Bool = __smtx_typeof (SmtTerm.Boolean false)
      rw [__smtx_typeof.eq_1]) hInnerTrans

private theorem facts___eo_prog_arith_int_eq_conflict_impl
    (M : SmtModel) (hM : model_wf M) (t c P : Term) :
    RuleProofs.eo_has_smt_translation t ->
    RuleProofs.eo_has_smt_translation c ->
    __eo_prog_arith_int_eq_conflict t c (Proof.pf P) =
      conclusionTerm t c ->
    __eo_typeof (__eo_prog_arith_int_eq_conflict t c (Proof.pf P)) =
      Term.Bool ->
    eo_interprets M (nonIntPremise c c) true ->
    eo_interprets M (__eo_prog_arith_int_eq_conflict t c (Proof.pf P)) true := by
  intro hTTrans hCTrans hProgEq hResultTy hPrem
  have hProgBool :
      RuleProofs.eo_has_bool_type
        (__eo_prog_arith_int_eq_conflict t c (Proof.pf P)) :=
    typed___eo_prog_arith_int_eq_conflict_impl t c P
      hTTrans hCTrans hProgEq hResultTy
  have hProgBool' : RuleProofs.eo_has_bool_type (conclusionTerm t c) := by
    simpa [hProgEq] using hProgBool
  have hResultTy' : __eo_typeof (conclusionTerm t c) = Term.Bool := by
    simpa [hProgEq] using hResultTy
  have hTInt : __eo_typeof t = Term.Int :=
    t_int_of_result_bool t c hResultTy'
  have hCReal : __eo_typeof c = Term.Real :=
    c_real_of_result_bool t c hTInt hResultTy'
  have hTSmtTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    smtx_typeof_of_eo_type t Term.Int SmtType.Int hTTrans hTInt rfl
  have hCSmtTy : __smtx_typeof (__eo_to_smt c) = SmtType.Real :=
    smtx_typeof_of_eo_type c Term.Real SmtType.Real hCTrans hCReal rfl
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Int :=
    smt_model_eval_preserves_type M hM (__eo_to_smt t) SmtType.Int hTSmtTy
      (by simp) type_inhabited_int
  have hCEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c)) =
        SmtType.Real :=
    smt_model_eval_preserves_type M hM (__eo_to_smt c) SmtType.Real hCSmtTy
      (by simp) type_inhabited_real
  rcases int_value_canonical hTEvalTy with ⟨ti, hTEval⟩
  rcases real_value_canonical hCEvalTy with ⟨cq, hCEval⟩
  have hPremFalse :
      __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt (toRealTerm (toIntTerm c))))
        (__smtx_model_eval M (__eo_to_smt c)) = SmtValue.Boolean false :=
    RuleProofs.model_eval_eq_false_of_eq_false_eq_true M
      (toRealTerm (toIntTerm c)) c hPrem
  have hPremFalseQ :
      __smtx_model_eval_eq
        (SmtValue.Rational (native_to_real (native_to_int cq)))
        (SmtValue.Rational cq) = SmtValue.Boolean false := by
    rw [eo_to_smt_to_real_eq, smtx_eval_to_real_term_eq,
      eo_to_smt_to_int_eq, smtx_eval_to_int_term_eq, hCEval] at hPremFalse
    simpa [__smtx_model_eval_to_int, __smtx_model_eval_to_real] using hPremFalse
  have hCNonInt : native_to_real (native_to_int cq) ≠ cq := by
    intro hEq
    rw [hEq] at hPremFalseQ
    simp [__smtx_model_eval_eq, native_veq, native_qeq] at hPremFalseQ
  have hTargetNe : native_to_real ti ≠ cq := by
    intro hEq
    have hFloor : native_to_int cq = ti := by
      rw [← hEq, native_to_int_to_real]
    exact hCNonInt (by rw [hFloor]; exact hEq)
  have hEvalInner :
      __smtx_model_eval M (__eo_to_smt (eqTerm (toRealTerm t) c)) =
        SmtValue.Boolean false := by
    change __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt (toRealTerm t)) (__eo_to_smt c)) =
        SmtValue.Boolean false
    rw [smtx_eval_eq_term_eq, eo_to_smt_to_real_eq,
      smtx_eval_to_real_term_eq, hTEval, hCEval]
    simp [__smtx_model_eval_to_real, __smtx_model_eval_eq, native_veq,
      native_qeq, hTargetNe]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M
    (eqTerm (toRealTerm t) c) (Term.Boolean false) hProgBool' <| by
      rw [hEvalInner]
      rw [RuleProofs.eo_to_smt_false_eq, __smtx_model_eval.eq_1]
      exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean false)

end ArithIntEqConflict

open ArithIntEqConflict

public theorem cmd_step_arith_int_eq_conflict_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_int_eq_conflict args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_int_eq_conflict args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_int_eq_conflict args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.arith_int_eq_conflict args premises ≠
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
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              cases premises with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons p premises =>
                  cases premises with
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | nil =>
                      let T1 := a1
                      let C1 := a2
                      let P := __eo_state_proven_nth s p
                      have hArgsTrans :
                          RuleProofs.eo_has_smt_translation T1 ∧
                            (RuleProofs.eo_has_smt_translation C1 ∧ True) := by
                        simpa [cmdTranslationOk, cArgListTranslationOk,
                          RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                          using hCmdTrans
                      have hTTrans :
                          RuleProofs.eo_has_smt_translation T1 := hArgsTrans.1
                      have hCTrans :
                          RuleProofs.eo_has_smt_translation C1 := hArgsTrans.2.1
                      change __eo_typeof
                        (__eo_prog_arith_int_eq_conflict T1 C1 (Proof.pf P)) =
                        Term.Bool at hResultTy
                      change __eo_prog_arith_int_eq_conflict T1 C1
                        (Proof.pf P) ≠ Term.Stuck at hProg
                      rcases prog_arith_int_eq_conflict_info T1 C1 P hProg with
                        ⟨C0, C2, hPEq, hC0Eq, hC2Eq, hProgEq⟩
                      refine ⟨?_, ?_⟩
                      · intro hPremTrue
                        change eo_interprets M
                          (__eo_prog_arith_int_eq_conflict T1 C1
                            (Proof.pf P)) true
                        have hPremC :
                            eo_interprets M (nonIntPremise C1 C1) true := by
                          have hPTrue : eo_interprets M P true :=
                            hPremTrue P (by simp [premiseTermList, P])
                          rw [hPEq, hC0Eq, hC2Eq] at hPTrue
                          exact hPTrue
                        exact facts___eo_prog_arith_int_eq_conflict_impl
                          M hM T1 C1 P hTTrans hCTrans hProgEq
                          hResultTy hPremC
                      · change RuleProofs.eo_has_smt_translation
                          (__eo_prog_arith_int_eq_conflict T1 C1
                            (Proof.pf P))
                        exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                          (__eo_prog_arith_int_eq_conflict T1 C1
                            (Proof.pf P))
                          (typed___eo_prog_arith_int_eq_conflict_impl
                            T1 C1 P hTTrans hCTrans hProgEq hResultTy)
