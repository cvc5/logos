module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
public import Cpc.Proofs.RuleSupport.TypeInversionSupport
import all Cpc.Proofs.RuleSupport.TypeInversionSupport
public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace ArithLeqIteLift

private abbrev relTerm (op : UserOp) (t s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp op) t) s

private abbrev iteTerm (c t s : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) s

private abbrev leqLiftLhs (C t s r : Term) : Term :=
  relTerm UserOp.leq (iteTerm C t s) r

private abbrev leqLiftRhs (C t s r : Term) : Term :=
  iteTerm C (relTerm UserOp.leq t r) (relTerm UserOp.leq s r)

/-- A `leq` application has `__eo_typeof` either `Bool` or `Stuck`; if not
stuck, it is `Bool`. -/
private theorem leq_typeof_bool_of_ne_stuck (A B : Term)
    (h : __eo_typeof (relTerm UserOp.leq A B) ≠ Term.Stuck) :
    __eo_typeof (relTerm UserOp.leq A B) = Term.Bool := by
  change __eo_typeof_lt (__eo_typeof A) (__eo_typeof B) ≠ Term.Stuck at h
  change __eo_typeof_lt (__eo_typeof A) (__eo_typeof B) = Term.Bool
  exact RuleProofs.eo_typeof_lt_eq_bool_of_ne_stuck
    (__eo_typeof A) (__eo_typeof B) h

/-- Program reduction for non-stuck arguments. -/
private theorem prog_eq_of_nonstuck
    (C t s r : Term)
    (hC : C ≠ Term.Stuck) (ht : t ≠ Term.Stuck)
    (hs : s ≠ Term.Stuck) (hr : r ≠ Term.Stuck) :
    __eo_prog_arith_leq_ite_lift C t s r =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (leqLiftLhs C t s r)) (leqLiftRhs C t s r) := by
  by_cases hCSt : C = Term.Stuck
  · exact False.elim (hC hCSt)
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  by_cases hsSt : s = Term.Stuck
  · exact False.elim (hs hsSt)
  by_cases hrSt : r = Term.Stuck
  · exact False.elim (hr hrSt)
  simp [__eo_prog_arith_leq_ite_lift, relTerm, iteTerm, leqLiftLhs, leqLiftRhs]

/-- From `__eo_typeof (ite C t s) = Int/Real` recover the operand types. -/
private theorem ite_typeof_arith_cases
    {C t s X : Term}
    (hX : X = Term.UOp UserOp.Int ∨ X = Term.UOp UserOp.Real)
    (hIte : __eo_typeof (iteTerm C t s) = X) :
    __eo_typeof C = Term.Bool ∧ __eo_typeof t = X ∧ __eo_typeof s = X := by
  change __eo_typeof_ite (__eo_typeof C) (__eo_typeof t) (__eo_typeof s) = X at hIte
  have hXNe : X ≠ Term.Stuck := by
    rcases hX with rfl | rfl <;> exact Term.noConfusion
  exact RuleProofs.eo_typeof_ite_eq_nonstuck_args
    (__eo_typeof C) (__eo_typeof t) (__eo_typeof s) X hIte hXNe

/-- Argument type case analysis from the result having Bool type. -/
private theorem arg_type_cases_of_result
    (C t s r : Term)
    (hCTrans : RuleProofs.eo_has_smt_translation C)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hResultTy : __eo_typeof (__eo_prog_arith_leq_ite_lift C t s r) = Term.Bool) :
    __eo_typeof C = Term.Bool ∧
      ((__eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int ∧
          __eo_typeof r = Term.Int) ∨
        (__eo_typeof t = Term.Real ∧ __eo_typeof s = Term.Real ∧
          __eo_typeof r = Term.Real)) := by
  have hC : C ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation C hCTrans
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hr : r ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation r hRTrans
  have hProgEq := prog_eq_of_nonstuck C t s r hC ht hs hr
  have hResultTy' :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (leqLiftLhs C t s r)) (leqLiftRhs C t s r)) = Term.Bool := by
    simpa [hProgEq] using hResultTy
  have hEqArgs :
      __eo_typeof (leqLiftLhs C t s r) = __eo_typeof (leqLiftRhs C t s r) ∧
        __eo_typeof (leqLiftLhs C t s r) ≠ Term.Stuck := by
    change __eo_typeof_eq (__eo_typeof (leqLiftLhs C t s r))
      (__eo_typeof (leqLiftRhs C t s r)) = Term.Bool at hResultTy'
    exact RuleProofs.eo_typeof_eq_bool_same _ _ hResultTy'
  have hLhsTy : __eo_typeof (leqLiftLhs C t s r) = Term.Bool :=
    leq_typeof_bool_of_ne_stuck (iteTerm C t s) r hEqArgs.2
  change __eo_typeof_lt (__eo_typeof (iteTerm C t s)) (__eo_typeof r) =
    Term.Bool at hLhsTy
  rcases RuleProofs.eo_typeof_lt_bool_cases _ _ hLhsTy with hInt | hReal
  · have hIte := ite_typeof_arith_cases (Or.inl rfl) hInt.1
    exact ⟨hIte.1, Or.inl ⟨hIte.2.1, hIte.2.2, hInt.2⟩⟩
  · have hIte := ite_typeof_arith_cases (Or.inr rfl) hReal.1
    exact ⟨hIte.1, Or.inr ⟨hIte.2.1, hIte.2.2, hReal.2⟩⟩

/-- `C` has Bool type given its `__eo_typeof` is Bool. -/
private theorem cond_has_bool_type (C : Term)
    (hCTrans : RuleProofs.eo_has_smt_translation C)
    (hCTy : __eo_typeof C = Term.Bool) :
    RuleProofs.eo_has_bool_type C := by
  unfold RuleProofs.eo_has_bool_type
  exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
    C Term.Bool (__eo_to_smt C) rfl hCTrans hCTy

/-- An `ite` of same-typed branches has the branch's smt type. -/
private theorem ite_smt_type_eq
    (C T E : Term)
    (hC : RuleProofs.eo_has_bool_type C)
    (hSame : __smtx_typeof (__eo_to_smt T) = __smtx_typeof (__eo_to_smt E)) :
    __smtx_typeof (__eo_to_smt (iteTerm C T E)) =
      __smtx_typeof (__eo_to_smt T) := by
  unfold RuleProofs.eo_has_bool_type at hC
  change __smtx_typeof (SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E)) =
    __smtx_typeof (__eo_to_smt T)
  rw [typeof_ite_eq]
  simp [__smtx_typeof_ite, hC, hSame, native_Teq, native_ite]

/-- `leq A B` has Bool type when both args have the same smt type that is
Int or Real. -/
private theorem leq_has_bool_type_of_smt_types
    (A B : Term) (ST : SmtType)
    (hSTArith : ST = SmtType.Int ∨ ST = SmtType.Real)
    (hA : __smtx_typeof (__eo_to_smt A) = ST)
    (hB : __smtx_typeof (__eo_to_smt B) = ST) :
    RuleProofs.eo_has_bool_type (relTerm UserOp.leq A B) := by
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.leq (__eo_to_smt A) (__eo_to_smt B)) = SmtType.Bool
  rw [typeof_leq_eq, hA, hB]
  rcases hSTArith with h | h <;> subst h <;>
    simp [__smtx_typeof_arith_overload_op_2_ret]

/-- The smt type of an arith eo term of type Int/Real. -/
private theorem smt_type_of_arith_eo_type
    (x : Term) (X : Term) (ST : SmtType)
    (hXmap : (X = Term.Int ∧ ST = SmtType.Int) ∨ (X = Term.Real ∧ ST = SmtType.Real))
    (hTrans : RuleProofs.eo_has_smt_translation x)
    (hTy : __eo_typeof x = X) :
    __smtx_typeof (__eo_to_smt x) = ST := by
  rcases hXmap with ⟨hX, hST⟩ | ⟨hX, hST⟩ <;> subst hX <;> subst hST <;>
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x _ (__eo_to_smt x) rfl hTrans hTy

private theorem typed_arith_leq_ite_lift
    (C t s r : Term)
    (hCTrans : RuleProofs.eo_has_smt_translation C)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hResultTy : __eo_typeof (__eo_prog_arith_leq_ite_lift C t s r) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_leq_ite_lift C t s r) := by
  have hCases :=
    arg_type_cases_of_result C t s r hCTrans hTTrans hSTrans hRTrans hResultTy
  have hCBool : RuleProofs.eo_has_bool_type C :=
    cond_has_bool_type C hCTrans hCases.1
  have hC : C ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation C hCTrans
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hr : r ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation r hRTrans
  have hProgEq := prog_eq_of_nonstuck C t s r hC ht hs hr
  rw [hProgEq]
  -- choose the common arith smt type
  obtain ⟨ST, hSTArith, hSt, hSs, hSr⟩ :
      ∃ ST : SmtType, (ST = SmtType.Int ∨ ST = SmtType.Real) ∧
        __smtx_typeof (__eo_to_smt t) = ST ∧
        __smtx_typeof (__eo_to_smt s) = ST ∧
        __smtx_typeof (__eo_to_smt r) = ST := by
    rcases hCases.2 with ⟨hT, hS, hR⟩ | ⟨hT, hS, hR⟩
    · exact ⟨SmtType.Int, Or.inl rfl,
        smt_type_of_arith_eo_type t Term.Int SmtType.Int (Or.inl ⟨rfl, rfl⟩) hTTrans hT,
        smt_type_of_arith_eo_type s Term.Int SmtType.Int (Or.inl ⟨rfl, rfl⟩) hSTrans hS,
        smt_type_of_arith_eo_type r Term.Int SmtType.Int (Or.inl ⟨rfl, rfl⟩) hRTrans hR⟩
    · exact ⟨SmtType.Real, Or.inr rfl,
        smt_type_of_arith_eo_type t Term.Real SmtType.Real (Or.inr ⟨rfl, rfl⟩) hTTrans hT,
        smt_type_of_arith_eo_type s Term.Real SmtType.Real (Or.inr ⟨rfl, rfl⟩) hSTrans hS,
        smt_type_of_arith_eo_type r Term.Real SmtType.Real (Or.inr ⟨rfl, rfl⟩) hRTrans hR⟩
  -- LHS bool type: leq (ite C t s) r
  have hIteType : __smtx_typeof (__eo_to_smt (iteTerm C t s)) = ST := by
    rw [ite_smt_type_eq C t s hCBool (by rw [hSt, hSs])]; exact hSt
  have hLhsBool : RuleProofs.eo_has_bool_type (leqLiftLhs C t s r) :=
    leq_has_bool_type_of_smt_types (iteTerm C t s) r ST hSTArith hIteType hSr
  -- RHS bool type: ite C (leq t r) (leq s r)
  have hLeqTR : RuleProofs.eo_has_bool_type (relTerm UserOp.leq t r) :=
    leq_has_bool_type_of_smt_types t r ST hSTArith hSt hSr
  have hLeqSR : RuleProofs.eo_has_bool_type (relTerm UserOp.leq s r) :=
    leq_has_bool_type_of_smt_types s r ST hSTArith hSs hSr
  have hRhsBool : RuleProofs.eo_has_bool_type (leqLiftRhs C t s r) :=
    CnfSupport.eo_has_bool_type_ite_of_bool_args C
      (relTerm UserOp.leq t r) (relTerm UserOp.leq s r)
      hCBool hLeqTR hLeqSR
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (leqLiftLhs C t s r) (leqLiftRhs C t s r) hLhsBool hRhsBool

/-- Stable rewrite for evaluating SMT `leq` terms. -/
private theorem smtx_eval_leq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.leq x y) =
      __smtx_model_eval_leq (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- `eo_to_smt` of the LHS of the lift. -/
private theorem eo_to_smt_lhs (C t s r : Term) :
    __eo_to_smt (leqLiftLhs C t s r) =
      SmtTerm.leq
        (SmtTerm.ite (__eo_to_smt C) (__eo_to_smt t) (__eo_to_smt s))
        (__eo_to_smt r) := rfl

/-- `eo_to_smt` of the RHS of the lift. -/
private theorem eo_to_smt_rhs (C t s r : Term) :
    __eo_to_smt (leqLiftRhs C t s r) =
      SmtTerm.ite (__eo_to_smt C)
        (SmtTerm.leq (__eo_to_smt t) (__eo_to_smt r))
        (SmtTerm.leq (__eo_to_smt s) (__eo_to_smt r)) := rfl

private theorem eval_leq_ite_lift_rel
    (M : SmtModel) (hM : model_wf M)
    (C t s r : Term)
    (hCTrans : RuleProofs.eo_has_smt_translation C)
    (hCTy : __eo_typeof C = Term.Bool) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (leqLiftLhs C t s r)))
      (__smtx_model_eval M (__eo_to_smt (leqLiftRhs C t s r))) := by
  -- C evaluates to a Boolean value
  have hCSmt : __smtx_typeof (__eo_to_smt C) = SmtType.Bool :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      C Term.Bool (__eo_to_smt C) rfl hCTrans hCTy
  have hCPres :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt C)) = SmtType.Bool := by
    simpa [hCSmt] using
      Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt C)
        (by simp [term_has_non_none_type, hCSmt])
  obtain ⟨b, hCEval⟩ := bool_value_canonical hCPres
  rw [eo_to_smt_lhs, eo_to_smt_rhs]
  rw [smtx_eval_leq_term_eq, smtx_eval_ite_term_eq, smtx_eval_ite_term_eq,
    smtx_eval_leq_term_eq, smtx_eval_leq_term_eq]
  rw [hCEval]
  cases b <;>
    simp [__smtx_model_eval_ite] <;>
    exact RuleProofs.smtx_model_eval_eq_refl _

private theorem facts_arith_leq_ite_lift
    (M : SmtModel) (hM : model_wf M)
    (C t s r : Term)
    (hCTrans : RuleProofs.eo_has_smt_translation C)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hResultTy : __eo_typeof (__eo_prog_arith_leq_ite_lift C t s r) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_leq_ite_lift C t s r) true := by
  have hCases :=
    arg_type_cases_of_result C t s r hCTrans hTTrans hSTrans hRTrans hResultTy
  have hC : C ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation C hCTrans
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hr : r ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation r hRTrans
  have hProgEq := prog_eq_of_nonstuck C t s r hC ht hs hr
  have hBool :=
    typed_arith_leq_ite_lift C t s r hCTrans hTTrans hSTrans hRTrans hResultTy
  rw [hProgEq]
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (leqLiftLhs C t s r)) (leqLiftRhs C t s r)) := by
    simpa [hProgEq] using hBool
  exact RuleProofs.eo_interprets_eq_of_rel M
    (leqLiftLhs C t s r) (leqLiftRhs C t s r)
    hBool'
    (eval_leq_ite_lift_rel M hM C t s r hCTrans hCases.1)

end ArithLeqIteLift

public theorem cmd_step_arith_leq_ite_lift_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_leq_ite_lift args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_leq_ite_lift args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_leq_ite_lift args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.arith_leq_ite_lift args premises ≠ Term.Stuck :=
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
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons a4 args =>
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
                          let C1 := a1
                          let T1 := a2
                          let S1 := a3
                          let R1 := a4
                          have hArgsTrans :
                              cArgListTranslationOk
                                (CArgList.cons C1 (CArgList.cons T1
                                  (CArgList.cons S1 (CArgList.cons R1 CArgList.nil)))) := by
                            simpa [cmdTranslationOk] using hCmdTrans
                          have hC1Trans : RuleProofs.eo_has_smt_translation C1 := by
                            simpa [cArgListTranslationOk] using hArgsTrans.1
                          have hT1Trans : RuleProofs.eo_has_smt_translation T1 := by
                            simpa [cArgListTranslationOk] using hArgsTrans.2.1
                          have hS1Trans : RuleProofs.eo_has_smt_translation S1 := by
                            simpa [cArgListTranslationOk] using hArgsTrans.2.2.1
                          have hR1Trans : RuleProofs.eo_has_smt_translation R1 := by
                            simpa [cArgListTranslationOk] using hArgsTrans.2.2.2
                          change __eo_typeof
                            (__eo_prog_arith_leq_ite_lift C1 T1 S1 R1) = Term.Bool at hResultTy
                          refine ⟨?_, ?_⟩
                          · intro _hTrue
                            change eo_interprets M
                              (__eo_prog_arith_leq_ite_lift C1 T1 S1 R1) true
                            exact ArithLeqIteLift.facts_arith_leq_ite_lift
                              M hM C1 T1 S1 R1
                              hC1Trans hT1Trans hS1Trans hR1Trans hResultTy
                          · change RuleProofs.eo_has_smt_translation
                              (__eo_prog_arith_leq_ite_lift C1 T1 S1 R1)
                            exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                              (__eo_prog_arith_leq_ite_lift C1 T1 S1 R1)
                              (ArithLeqIteLift.typed_arith_leq_ite_lift
                                C1 T1 S1 R1
                                hC1Trans hT1Trans hS1Trans hR1Trans hResultTy)
