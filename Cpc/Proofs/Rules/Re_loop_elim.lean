module

public import Cpc.Proofs.RuleSupport.ReLoopElimSupport
import all Cpc.Proofs.RuleSupport.ReLoopElimSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private abbrev mkReLoopEq (l u r rhs : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.UOp2 UserOp2.re_loop l u) r))
    rhs

private theorem eo_requires_eq_result_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    __eo_requires x y z = z := by
  intro h
  by_cases hxy : x = y
  · subst y
    by_cases hx : x = Term.Stuck
    · subst x
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at h
    · simp [__eo_requires, hx, native_ite, native_teq, native_not,
        SmtEval.native_not]
  · simp [__eo_requires, hxy, native_ite, native_teq] at h

private theorem eo_requires_result_ne_stuck_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    z ≠ Term.Stuck := by
  intro h hz
  have hReq : __eo_requires x y z = z :=
    eo_requires_eq_result_of_ne_stuck x y z h
  exact h (by rw [hReq, hz])

private theorem eo_requires_arg_eq_of_ne_stuck
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · have hStuck : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, native_ite, hxy]
    exact False.elim (hReq hStuck)

private theorem re_loop_translation_types
    (lo hi : native_Int) (r rhs : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (mkReLoopEq (Term.Numeral lo) (Term.Numeral hi) r rhs)) :
    native_zleq 0 lo = true ∧ native_zleq 0 hi = true ∧
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt rhs) = SmtType.RegLan := by
  unfold RuleProofs.eo_has_smt_translation mkReLoopEq at hTrans
  change
    __smtx_typeof
        (SmtTerm.eq
          (SmtTerm.re_loop (SmtTerm.Numeral lo) (SmtTerm.Numeral hi)
            (__eo_to_smt r))
          (__eo_to_smt rhs)) ≠ SmtType.None at hTrans
  rw [typeof_eq_eq, typeof_re_loop_eq] at hTrans
  unfold __smtx_typeof_eq __smtx_typeof_guard __smtx_typeof_re_loop at hTrans
  cases hR : __smtx_typeof (__eo_to_smt r) <;>
    simp [hR, native_ite, native_Teq] at hTrans
  by_cases hlo : native_zleq 0 lo
  · by_cases hhi : native_zleq 0 hi
    · simp [hlo, hhi] at hTrans
      cases hRhs : __smtx_typeof (__eo_to_smt rhs) <;>
        simp [hRhs] at hTrans
      exact ⟨hlo, hhi, by simpa using hR, by simpa using hRhs⟩
    · simp [hlo, hhi] at hTrans
  · simp [hlo] at hTrans

private theorem re_loop_elim_prog_eq_arg_of_ne_stuck
    (l u r rhs : Term)
    (hProg : __eo_prog_re_loop_elim (mkReLoopEq l u r rhs) ≠ Term.Stuck) :
    __eo_prog_re_loop_elim (mkReLoopEq l u r rhs) = mkReLoopEq l u r rhs := by
  simp only [mkReLoopEq, __eo_prog_re_loop_elim] at hProg ⊢
  let diff := __eo_add (__eo_neg l) u
  let expansion :=
    __eo_list_singleton_elim (Term.UOp UserOp.re_union)
      (__str_mk_re_loop_elim_rec
        (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons) (Term.Numeral 0) diff)
        r
        (__eo_list_repeat (Term.UOp UserOp.re_concat) r l))
  change
    __eo_requires (__eo_is_neg diff) (Term.Boolean false)
      (__eo_requires expansion rhs
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp2 UserOp2.re_loop l u) r))
          rhs)) =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp2 UserOp2.re_loop l u) r))
        rhs
  have hOuter :
      __eo_requires (__eo_is_neg diff) (Term.Boolean false)
        (__eo_requires expansion rhs
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp2 UserOp2.re_loop l u) r))
            rhs)) =
        __eo_requires expansion rhs
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp2 UserOp2.re_loop l u) r))
            rhs) :=
    eo_requires_eq_result_of_ne_stuck _ _ _ hProg
  have hInnerNe :
      __eo_requires expansion rhs
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp2 UserOp2.re_loop l u) r))
          rhs) ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hProg
  have hInner :
      __eo_requires expansion rhs
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp2 UserOp2.re_loop l u) r))
          rhs) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp2 UserOp2.re_loop l u) r))
          rhs :=
    eo_requires_eq_result_of_ne_stuck _ _ _ hInnerNe
  exact hOuter.trans hInner

private theorem re_loop_elim_canonical_true
    (M : SmtModel) (hM : model_wf M)
    (l u r rhs : Term) :
    RuleProofs.eo_has_smt_translation (mkReLoopEq l u r rhs) ->
    __eo_typeof
        (__eo_prog_re_loop_elim (mkReLoopEq l u r rhs)) = Term.Bool ->
    eo_interprets M (mkReLoopEq l u r rhs) true := by
  intro hTrans hTy
  have hProgNe :
      __eo_prog_re_loop_elim (mkReLoopEq l u r rhs) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  cases l <;> cases u <;> try
    (exfalso
     simpa [mkReLoopEq, __eo_prog_re_loop_elim, __eo_neg, __eo_add,
       __eo_is_neg, __eo_list_repeat, __eo_requires, native_ite,
       native_teq, native_not, SmtEval.native_not] using hProgNe)
  case Rational.Rational qlo qhi =>
    exfalso
    unfold RuleProofs.eo_has_smt_translation mkReLoopEq at hTrans
    change
      __smtx_typeof
          (SmtTerm.eq
            (SmtTerm.re_loop (SmtTerm.Rational qlo) (SmtTerm.Rational qhi)
              (__eo_to_smt r))
            (__eo_to_smt rhs)) ≠ SmtType.None at hTrans
    rw [typeof_eq_eq, typeof_re_loop_eq] at hTrans
    simp [__smtx_typeof_eq, __smtx_typeof_guard, __smtx_typeof_re_loop,
      native_ite, native_Teq] at hTrans
  case Binary.Binary wlo nlo whi nhi =>
    exfalso
    unfold RuleProofs.eo_has_smt_translation mkReLoopEq at hTrans
    change
      __smtx_typeof
          (SmtTerm.eq
            (SmtTerm.re_loop (SmtTerm.Binary wlo nlo) (SmtTerm.Binary whi nhi)
              (__eo_to_smt r))
            (__eo_to_smt rhs)) ≠ SmtType.None at hTrans
    rw [typeof_eq_eq, typeof_re_loop_eq] at hTrans
    simp [__smtx_typeof_eq, __smtx_typeof_guard, __smtx_typeof_re_loop,
      native_ite, native_Teq] at hTrans
  case Numeral.Numeral lo hi =>
      let loopTerm :=
        Term.Apply (Term.UOp2 UserOp2.re_loop (Term.Numeral lo)
          (Term.Numeral hi)) r
      let expansion :=
        __eo_list_singleton_elim (Term.UOp UserOp.re_union)
          (__str_mk_re_loop_elim_rec
            (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0)
              (Term.Numeral (native_zplus (native_zneg lo) hi)))
            r
            (__eo_list_repeat (Term.UOp UserOp.re_concat) r
              (Term.Numeral lo)))
      let orig := mkReLoopEq (Term.Numeral lo) (Term.Numeral hi) r rhs
      have hOuterNe :
          __eo_requires
              (__eo_is_neg
                (__eo_add (__eo_neg (Term.Numeral lo)) (Term.Numeral hi)))
              (Term.Boolean false)
              (__eo_requires expansion rhs orig) ≠ Term.Stuck := by
        simpa [mkReLoopEq, __eo_prog_re_loop_elim, expansion, orig,
          __eo_neg, __eo_add] using hProgNe
      have hCondEq :
          __eo_is_neg
              (__eo_add (__eo_neg (Term.Numeral lo)) (Term.Numeral hi)) =
            Term.Boolean false :=
        eo_requires_arg_eq_of_ne_stuck hOuterNe
      have hDiffNonneg : 0 ≤ hi - lo := by
        have hNotNeg : native_zlt (-lo + hi) 0 = false := by
          simpa [__eo_neg, __eo_add, __eo_is_neg, native_zplus,
            native_zneg] using hCondEq
        have hNotLt : ¬ (-lo + hi) < 0 := by
          simpa [native_zlt] using hNotNeg
        have hComm : -lo + hi = hi - lo := by
          change -lo + hi = hi + -lo
          rw [Int.add_comm]
        rw [hComm] at hNotLt
        exact (Int.not_lt.mp hNotLt)
      have hInnerNe :
          __eo_requires expansion rhs orig ≠ Term.Stuck :=
        eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hOuterNe
      have hExpandedEq : expansion = rhs :=
        eo_requires_arg_eq_of_ne_stuck hInnerNe
      have hProgEq :
          __eo_prog_re_loop_elim orig = orig := by
        simpa [orig] using
          re_loop_elim_prog_eq_arg_of_ne_stuck
            (Term.Numeral lo) (Term.Numeral hi) r rhs hProgNe
      have hOrigTy : __eo_typeof orig = Term.Bool := by
        simpa [orig, hProgEq] using hTy
      have hOrigBool : RuleProofs.eo_has_bool_type orig :=
        RuleProofs.eo_typeof_bool_implies_has_bool_type orig hTrans hOrigTy
      rcases re_loop_translation_types lo hi r rhs hTrans with
        ⟨hloZ, _hhiZ, hrTy, _hrhsTy⟩
      have hlo : 0 ≤ lo := by
        simpa [native_zleq] using hloZ
      have hRNN : term_has_non_none_type (__eo_to_smt r) := by
        unfold term_has_non_none_type
        rw [hrTy]
        intro h
        cases h
      have hEvalTy := type_preservation M hM (__eo_to_smt r) hRNN
      rw [hrTy] at hEvalTy
      rcases reglan_value_canonical hEvalTy with ⟨rv, hREval⟩
      have hRelExpandedLoop :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt expansion))
            (__smtx_model_eval M (__eo_to_smt loopTerm)) := by
        simpa [expansion, loopTerm] using
          re_loop_elim_eval_rel M lo hi r rv hrTy hREval hlo hDiffNonneg
      have hRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt loopTerm))
            (__smtx_model_eval M (__eo_to_smt rhs)) := by
        rw [← hExpandedEq]
        exact RuleProofs.smt_value_rel_symm _ _ hRelExpandedLoop
      have hFact : eo_interprets M orig true := by
        simpa [orig, mkReLoopEq, loopTerm] using
          RuleProofs.eo_interprets_eq_of_rel M loopTerm rhs hOrigBool hRel
      simpa [orig] using hFact

public theorem cmd_step_re_loop_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_loop_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_loop_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_loop_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_loop_elim args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hArgsTrans : cArgListTranslationOk (CArgList.cons a1 CArgList.nil) := by
                simpa [cmdTranslationOk] using hCmdTrans
              change StepRuleProperties M [] (__eo_prog_re_loop_elim a1)
              cases a1 with
              | Apply f rhs =>
                  cases f with
                  | Apply op lhs =>
                      cases op with
                      | UOp op =>
                          cases op <;> try
                            (change Term.Stuck ≠ Term.Stuck at hProg
                             exact False.elim (hProg rfl))
                          case eq =>
                            cases lhs with
                            | Apply reLoopArg r =>
                                cases reLoopArg with
                                | UOp2 op2 l u =>
                                    cases op2 <;> try
                                      (change Term.Stuck ≠ Term.Stuck at hProg
                                       exact False.elim (hProg rfl))
                                    case re_loop =>
                                      have hTermTrans :
                                          RuleProofs.eo_has_smt_translation
                                            (mkReLoopEq l u r rhs) := by
                                        simpa [mkReLoopEq, cArgListTranslationOk]
                                          using hArgsTrans.1
                                      have hProgEq :
                                          __eo_prog_re_loop_elim (mkReLoopEq l u r rhs) =
                                            mkReLoopEq l u r rhs :=
                                        re_loop_elim_prog_eq_arg_of_ne_stuck l u r rhs hProg
                                      refine ⟨?_, ?_⟩
                                      · intro _hPremisesTrue
                                        rw [hProgEq]
                                        exact re_loop_elim_canonical_true
                                          M hM l u r rhs hTermTrans hResultTy
                                      · rw [hProgEq]
                                        exact hTermTrans
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
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
