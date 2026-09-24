module

public import Cpc.Proofs.RuleSupport.BvExtractMultLeadingBitSupport
import all Cpc.Proofs.RuleSupport.BvExtractMultLeadingBitSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

private def bvExtractMultLeadingArgs
    (high low xi xin x yi yin y w : Term) : CArgList :=
  .cons high (.cons low (.cons xi (.cons xin (.cons x
    (.cons yi (.cons yin (.cons y (.cons w .nil))))))))

set_option maxHeartbeats 100000000 in
private theorem bvExtractMultLeading_premises0_stuck
    (s : CState) (high low xi xin x yi yin y w : Term) :
    __eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit
      (bvExtractMultLeadingArgs high low xi xin x yi yin y w) .nil =
      Term.Stuck := by
  rfl

set_option maxHeartbeats 100000000 in
private theorem bvExtractMultLeading_premises1_stuck
    (s : CState) (high low xi xin x yi yin y w : Term) (n1 : CIndex) :
    __eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit
      (bvExtractMultLeadingArgs high low xi xin x yi yin y w)
      (.cons n1 .nil) = Term.Stuck := by
  rfl

set_option maxHeartbeats 100000000 in
private theorem bvExtractMultLeading_premises2_stuck
    (s : CState) (high low xi xin x yi yin y w : Term)
    (n1 n2 : CIndex) :
    __eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit
      (bvExtractMultLeadingArgs high low xi xin x yi yin y w)
      (.cons n1 (.cons n2 .nil)) = Term.Stuck := by
  rfl

set_option maxHeartbeats 100000000 in
private theorem bvExtractMultLeading_premises3_stuck
    (s : CState) (high low xi xin x yi yin y w : Term)
    (n1 n2 n3 : CIndex) :
    __eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit
      (bvExtractMultLeadingArgs high low xi xin x yi yin y w)
      (.cons n1 (.cons n2 (.cons n3 .nil))) = Term.Stuck := by
  rfl

set_option maxHeartbeats 100000000 in
private theorem bvExtractMultLeading_premises4_stuck
    (s : CState) (high low xi xin x yi yin y w : Term)
    (n1 n2 n3 n4 : CIndex) :
    __eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit
      (bvExtractMultLeadingArgs high low xi xin x yi yin y w)
      (.cons n1 (.cons n2 (.cons n3 (.cons n4 .nil)))) = Term.Stuck := by
  rfl

set_option maxHeartbeats 100000000 in
private theorem bvExtractMultLeading_premises5_stuck
    (s : CState) (high low xi xin x yi yin y w : Term)
    (n1 n2 n3 n4 n5 : CIndex) :
    __eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit
      (bvExtractMultLeadingArgs high low xi xin x yi yin y w)
      (.cons n1 (.cons n2 (.cons n3 (.cons n4 (.cons n5 .nil))))) =
      Term.Stuck := by
  rfl

set_option maxHeartbeats 100000000 in
private theorem bvExtractMultLeading_premises6_stuck
    (s : CState) (high low xi xin x yi yin y w : Term)
    (n1 n2 n3 n4 n5 n6 : CIndex) :
    __eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit
      (bvExtractMultLeadingArgs high low xi xin x yi yin y w)
      (.cons n1 (.cons n2 (.cons n3 (.cons n4
        (.cons n5 (.cons n6 .nil)))))) = Term.Stuck := by
  rfl

set_option maxHeartbeats 100000000 in
private theorem bvExtractMultLeading_extra_premises_stuck
    (s : CState) (high low xi xin x yi yin y w : Term)
    (n1 n2 n3 n4 n5 n6 n7 n8 : CIndex) (tail : CIndexList) :
    __eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit
      (bvExtractMultLeadingArgs high low xi xin x yi yin y w)
      (.cons n1 (.cons n2 (.cons n3 (.cons n4 (.cons n5 (.cons n6
        (.cons n7 (.cons n8 tail)))))))) = Term.Stuck := by
  rfl

private theorem bvExtractMultLeading_args_shape
    (s : CState) (args : CArgList) (premises : CIndexList)
    (hProg :
      __eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit args premises ≠
        Term.Stuck) :
    ∃ high low xi xin x yi yin y w,
      args = bvExtractMultLeadingArgs high low xi xin x yi yin y w := by
  cases args with
  | nil => exact False.elim (hProg rfl)
  | cons high args =>
    cases args with
    | nil => exact False.elim (hProg rfl)
    | cons low args =>
      cases args with
      | nil => exact False.elim (hProg rfl)
      | cons xi args =>
        cases args with
        | nil => exact False.elim (hProg rfl)
        | cons xin args =>
          cases args with
          | nil => exact False.elim (hProg rfl)
          | cons x args =>
            cases args with
            | nil => exact False.elim (hProg rfl)
            | cons yi args =>
              cases args with
              | nil => exact False.elim (hProg rfl)
              | cons yin args =>
                cases args with
                | nil => exact False.elim (hProg rfl)
                | cons y args =>
                  cases args with
                  | nil => exact False.elim (hProg rfl)
                  | cons w args =>
                    cases args with
                    | nil =>
                      exact ⟨high, low, xi, xin, x, yi, yin, y, w, rfl⟩
                    | cons _ _ => exact False.elim (hProg rfl)

private theorem bvExtractMultLeading_premises_suffix_shape
    (s : CState) (high low xi xin x yi yin y w : Term)
    (n1 n2 n3 n4 : CIndex) (premises : CIndexList)
    (hProg :
      __eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit
        (bvExtractMultLeadingArgs high low xi xin x yi yin y w)
        (.cons n1 (.cons n2 (.cons n3 (.cons n4 premises)))) ≠
        Term.Stuck) :
    ∃ n5 n6 n7,
      premises = .cons n5 (.cons n6 (.cons n7 .nil)) := by
  cases premises with
  | nil =>
    exact False.elim (hProg
      (bvExtractMultLeading_premises4_stuck s high low xi xin x yi yin y w
        n1 n2 n3 n4))
  | cons n5 premises =>
    cases premises with
    | nil =>
      exact False.elim (hProg
        (bvExtractMultLeading_premises5_stuck s high low xi xin x yi yin y w
          n1 n2 n3 n4 n5))
    | cons n6 premises =>
      cases premises with
      | nil =>
        exact False.elim (hProg
          (bvExtractMultLeading_premises6_stuck s high low xi xin x yi yin y w
            n1 n2 n3 n4 n5 n6))
      | cons n7 premises =>
        by_cases hTailEq : premises = .nil
        · exact ⟨n5, n6, n7, by rw [hTailEq]⟩
        · have hCons : ∃ n tail, premises = .cons n tail := by
            clear hProg
            cases premises with
            | nil => exact False.elim (hTailEq rfl)
            | cons n tail => exact ⟨n, tail, rfl⟩
          rcases hCons with ⟨n, tail, hConsEq⟩
          apply False.elim
          apply hProg
          rw [hConsEq]
          exact bvExtractMultLeading_extra_premises_stuck s high low xi xin x
            yi yin y w n1 n2 n3 n4 n5 n6 n7 n tail

private theorem bvExtractMultLeading_premises_shape
    (s : CState) (high low xi xin x yi yin y w : Term)
    (premises : CIndexList)
    (hProg :
      __eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit
        (bvExtractMultLeadingArgs high low xi xin x yi yin y w) premises ≠
        Term.Stuck) :
    ∃ n1 n2 n3 n4 n5 n6 n7,
      premises = .cons n1 (.cons n2 (.cons n3 (.cons n4
        (.cons n5 (.cons n6 (.cons n7 .nil)))))) := by
  cases premises with
  | nil =>
    exact False.elim (hProg
      (bvExtractMultLeading_premises0_stuck s high low xi xin x yi yin y w))
  | cons n1 premises =>
    cases premises with
    | nil =>
      exact False.elim (hProg
        (bvExtractMultLeading_premises1_stuck s high low xi xin x yi yin y w
          n1))
    | cons n2 premises =>
      cases premises with
      | nil =>
        exact False.elim (hProg
          (bvExtractMultLeading_premises2_stuck s high low xi xin x yi yin y w
            n1 n2))
      | cons n3 premises =>
        cases premises with
        | nil =>
          exact False.elim (hProg
            (bvExtractMultLeading_premises3_stuck s high low xi xin x yi yin y
              w n1 n2 n3))
        | cons n4 premises =>
          rcases bvExtractMultLeading_premises_suffix_shape s high low xi xin
              x yi yin y w n1 n2 n3 n4 premises hProg with
            ⟨n5, n6, n7, hPremises⟩
          exact ⟨n1, n2, n3, n4, n5, n6, n7, by rw [hPremises]⟩

set_option maxHeartbeats 100000000 in
private theorem bvExtractMultLeading_command_shape
    (s : CState) (args : CArgList) (premises : CIndexList)
    (hProg :
      __eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit args premises ≠
        Term.Stuck) :
    ∃ high low xi xin x yi yin y w n1 n2 n3 n4 n5 n6 n7,
      args = bvExtractMultLeadingArgs high low xi xin x yi yin y w ∧
      premises = .cons n1 (.cons n2 (.cons n3 (.cons n4
        (.cons n5 (.cons n6 (.cons n7 .nil)))))) := by
  rcases bvExtractMultLeading_args_shape s args premises hProg with
    ⟨high, low, xi, xin, x, yi, yin, y, w, hArgsEq⟩
  have hProgArgs :
      __eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit
        (bvExtractMultLeadingArgs high low xi xin x yi yin y w) premises ≠
        Term.Stuck := by
    intro hStuck
    apply hProg
    rw [hArgsEq]
    exact hStuck
  rcases bvExtractMultLeading_premises_shape s high low xi xin x yi yin y w
      premises hProgArgs with
    ⟨n1, n2, n3, n4, n5, n6, n7, hPremisesEq⟩
  exact ⟨high, low, xi, xin, x, yi, yin, y, w, n1, n2, n3, n4, n5, n6,
    n7, hArgsEq, hPremisesEq⟩

set_option maxHeartbeats 100000000 in
private theorem bvExtractMultLeading_command_valid
    (s : CState) (high low xi xin x yi yin y w : Term)
    (n1 n2 n3 n4 n5 n6 n7 : CIndex) :
    __eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit
      (bvExtractMultLeadingArgs high low xi xin x yi yin y w)
      (.cons n1 (.cons n2 (.cons n3 (.cons n4
        (.cons n5 (.cons n6 (.cons n7 .nil))))))) =
      bvExtractMultLeadingProgram high low xi xin x yi yin y w
        (__eo_state_proven_nth s n1) (__eo_state_proven_nth s n2)
        (__eo_state_proven_nth s n3) (__eo_state_proven_nth s n4)
        (__eo_state_proven_nth s n5) (__eo_state_proven_nth s n6)
        (__eo_state_proven_nth s n7) := by
  rfl

set_option maxHeartbeats 100000000 in
private theorem bvExtractMultLeading_argument_translations
    (args : CArgList) (premises : CIndexList)
    (high low xi xin x yi yin y w : Term)
    (hArgsEq : args = bvExtractMultLeadingArgs high low xi xin x yi yin y w)
    (hCmdTrans :
      cmdTranslationOk
        (CCmd.step CRule.bv_extract_mult_leading_bit args premises)) :
    RuleProofs.eo_has_smt_translation high ∧
    RuleProofs.eo_has_smt_translation low ∧
    RuleProofs.eo_has_smt_translation xi ∧
    RuleProofs.eo_has_smt_translation xin ∧
    RuleProofs.eo_has_smt_translation x ∧
    RuleProofs.eo_has_smt_translation yi ∧
    RuleProofs.eo_has_smt_translation yin ∧
    RuleProofs.eo_has_smt_translation y ∧
    RuleProofs.eo_has_smt_translation w ∧ True := by
  rw [hArgsEq] at hCmdTrans
  simpa [bvExtractMultLeadingArgs, cmdTranslationOk, cArgListTranslationOk]
    using hCmdTrans

set_option maxHeartbeats 100000000 in
private theorem bvExtractMultLeading_program_type
    (s : CState) (args : CArgList) (premises : CIndexList)
    (high low xi xin x yi yin y w : Term)
    (n1 n2 n3 n4 n5 n6 n7 : CIndex)
    (hArgsEq : args = bvExtractMultLeadingArgs high low xi xin x yi yin y w)
    (hPremisesEq : premises = .cons n1 (.cons n2 (.cons n3 (.cons n4
      (.cons n5 (.cons n6 (.cons n7 .nil)))))))
    (hResultTy :
      __eo_typeof
          (__eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit args
            premises) =
        Term.Bool) :
    __eo_typeof
        (bvExtractMultLeadingProgram high low xi xin x yi yin y w
          (__eo_state_proven_nth s n1) (__eo_state_proven_nth s n2)
          (__eo_state_proven_nth s n3) (__eo_state_proven_nth s n4)
          (__eo_state_proven_nth s n5) (__eo_state_proven_nth s n6)
          (__eo_state_proven_nth s n7)) =
      Term.Bool := by
  rw [hArgsEq, hPremisesEq] at hResultTy
  rw [bvExtractMultLeading_command_valid] at hResultTy
  exact hResultTy

set_option maxHeartbeats 100000000 in
private theorem bvExtractMultLeading_result_eq_program
    (s : CState) (args : CArgList) (premises : CIndexList) (result : Term)
    (high low xi xin x yi yin y w : Term)
    (n1 n2 n3 n4 n5 n6 n7 : CIndex)
    (hArgsEq : args = bvExtractMultLeadingArgs high low xi xin x yi yin y w)
    (hPremisesEq : premises = .cons n1 (.cons n2 (.cons n3 (.cons n4
      (.cons n5 (.cons n6 (.cons n7 .nil)))))))
    (hResultEq :
      __eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit args premises =
        result) :
    result =
      bvExtractMultLeadingProgram high low xi xin x yi yin y w
        (__eo_state_proven_nth s n1) (__eo_state_proven_nth s n2)
        (__eo_state_proven_nth s n3) (__eo_state_proven_nth s n4)
        (__eo_state_proven_nth s n5) (__eo_state_proven_nth s n6)
        (__eo_state_proven_nth s n7) := by
  rw [hArgsEq, hPremisesEq] at hResultEq
  rw [bvExtractMultLeading_command_valid] at hResultEq
  exact hResultEq.symm

private def bvExtractMultLeadingMatchGuard
    (high low xi xin x yi yin y w r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
      r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 : Term) : Term :=
  [__eo_eq x r2, __eo_eq xi r3, __eo_eq xi r4, __eo_eq xin r5,
    __eo_eq yi r6, __eo_eq yi r7, __eo_eq yin r8, __eo_eq xin r9,
    __eo_eq x r10, __eo_eq xi r11, __eo_eq xin r12, __eo_eq xin r13,
    __eo_eq xi r14, __eo_eq yi r15, __eo_eq yin r16, __eo_eq yin r17,
    __eo_eq yi r18, __eo_eq low r19, __eo_eq w r20, __eo_eq high r21,
    __eo_eq low r22].foldl __eo_and (__eo_eq xin r1)

private theorem bvExtractMultLeadingMatchGuard_eqs
    (high low xi xin x yi yin y w r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
      r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 : Term)
    (hGuard : bvExtractMultLeadingMatchGuard high low xi xin x yi yin y w
      r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18
      r19 r20 r21 r22 = Term.Boolean true) :
    r1 = xin ∧ r2 = x ∧ r3 = xi ∧ r4 = xi ∧ r5 = xin ∧ r6 = yi ∧
    r7 = yi ∧ r8 = yin ∧ r9 = xin ∧ r10 = x ∧ r11 = xi ∧ r12 = xin ∧
    r13 = xin ∧ r14 = xi ∧ r15 = yi ∧ r16 = yin ∧ r17 = yin ∧
    r18 = yi ∧ r19 = low ∧ r20 = w ∧ r21 = high ∧ r22 = low := by
  unfold bvExtractMultLeadingMatchGuard at hGuard
  dsimp only [List.foldl] at hGuard
  rcases eo_and_eq_true_cases hGuard with ⟨g21, e22⟩
  rcases eo_and_eq_true_cases g21 with ⟨g20, e21⟩
  rcases eo_and_eq_true_cases g20 with ⟨g19, e20⟩
  rcases eo_and_eq_true_cases g19 with ⟨g18, e19⟩
  rcases eo_and_eq_true_cases g18 with ⟨g17, e18⟩
  rcases eo_and_eq_true_cases g17 with ⟨g16, e17⟩
  rcases eo_and_eq_true_cases g16 with ⟨g15, e16⟩
  rcases eo_and_eq_true_cases g15 with ⟨g14, e15⟩
  rcases eo_and_eq_true_cases g14 with ⟨g13, e14⟩
  rcases eo_and_eq_true_cases g13 with ⟨g12, e13⟩
  rcases eo_and_eq_true_cases g12 with ⟨g11, e12⟩
  rcases eo_and_eq_true_cases g11 with ⟨g10, e11⟩
  rcases eo_and_eq_true_cases g10 with ⟨g9, e10⟩
  rcases eo_and_eq_true_cases g9 with ⟨g8, e9⟩
  rcases eo_and_eq_true_cases g8 with ⟨g7, e8⟩
  rcases eo_and_eq_true_cases g7 with ⟨g6, e7⟩
  rcases eo_and_eq_true_cases g6 with ⟨g5, e6⟩
  rcases eo_and_eq_true_cases g5 with ⟨g4, e5⟩
  rcases eo_and_eq_true_cases g4 with ⟨g3, e4⟩
  rcases eo_and_eq_true_cases g3 with ⟨g2, e3⟩
  rcases eo_and_eq_true_cases g2 with ⟨e1, e2⟩
  exact ⟨support_eq_of_eo_eq_true xin r1 e1,
    support_eq_of_eo_eq_true x r2 e2,
    support_eq_of_eo_eq_true xi r3 e3,
    support_eq_of_eo_eq_true xi r4 e4,
    support_eq_of_eo_eq_true xin r5 e5,
    support_eq_of_eo_eq_true yi r6 e6,
    support_eq_of_eo_eq_true yi r7 e7,
    support_eq_of_eo_eq_true yin r8 e8,
    support_eq_of_eo_eq_true xin r9 e9,
    support_eq_of_eo_eq_true x r10 e10,
    support_eq_of_eo_eq_true xi r11 e11,
    support_eq_of_eo_eq_true xin r12 e12,
    support_eq_of_eo_eq_true xin r13 e13,
    support_eq_of_eo_eq_true xi r14 e14,
    support_eq_of_eo_eq_true yi r15 e15,
    support_eq_of_eo_eq_true yin r16 e16,
    support_eq_of_eo_eq_true yin r17 e17,
    support_eq_of_eo_eq_true yi r18 e18,
    support_eq_of_eo_eq_true low r19 e19,
    support_eq_of_eo_eq_true w r20 e20,
    support_eq_of_eo_eq_true high r21 e21,
    support_eq_of_eo_eq_true low r22 e22⟩

set_option maxHeartbeats 100000000 in
private theorem facts_bvExtractMultLeadingProgram
    (M : SmtModel) (hM : model_wf M)
    (result high low xi xin x yi yin y w P1 P2 P3 P4 P5 P6 P7 : Term) :
    RuleProofs.eo_has_smt_translation high ->
    RuleProofs.eo_has_smt_translation low ->
    RuleProofs.eo_has_smt_translation xi ->
    RuleProofs.eo_has_smt_translation xin ->
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation yi ->
    RuleProofs.eo_has_smt_translation yin ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation w ->
    result = bvExtractMultLeadingProgram high low xi xin x yi yin y w
      P1 P2 P3 P4 P5 P6 P7 ->
    __eo_typeof result = Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M P3 true -> eo_interprets M P4 true ->
    eo_interprets M P5 true -> eo_interprets M P6 true ->
    eo_interprets M P7 true ->
    eo_interprets M result true := by
  intro hHighTrans hLowTrans hXiTrans hXinTrans hXTrans hYiTrans hYinTrans
    hYTrans hWTrans hResult hProgramTy hP1True hP2True hP3True hP4True
    hP5True hP6True hP7True
  rw [hResult] at hProgramTy ⊢
  have hProg' := term_ne_stuck_of_typeof_bool hProgramTy
  have hHigh :=
    RuleProofs.term_ne_stuck_of_has_smt_translation high hHighTrans
  have hLow :=
    RuleProofs.term_ne_stuck_of_has_smt_translation low hLowTrans
  have hXi := RuleProofs.term_ne_stuck_of_has_smt_translation xi hXiTrans
  have hXin :=
    RuleProofs.term_ne_stuck_of_has_smt_translation xin hXinTrans
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYi := RuleProofs.term_ne_stuck_of_has_smt_translation yi hYiTrans
  have hYin :=
    RuleProofs.term_ne_stuck_of_has_smt_translation yin hYinTrans
  have hY := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hW := RuleProofs.term_ne_stuck_of_has_smt_translation w hWTrans
  have hFactsRaw := facts_bv_extract_mult_leading_raw M hM
    high low xi xin x yi yin y w hHighTrans hLowTrans hXiTrans hXinTrans
    hXTrans hYiTrans hYinTrans hYTrans hWTrans
  unfold bvExtractMultLeadingProgram at hProgramTy hProg' ⊢
  generalize hQ1 : Proof.pf P1 = q1 at hProgramTy hProg' ⊢
  generalize hQ2 : Proof.pf P2 = q2 at hProgramTy hProg' ⊢
  generalize hQ3 : Proof.pf P3 = q3 at hProgramTy hProg' ⊢
  generalize hQ4 : Proof.pf P4 = q4 at hProgramTy hProg' ⊢
  generalize hQ5 : Proof.pf P5 = q5 at hProgramTy hProg' ⊢
  generalize hQ6 : Proof.pf P6 = q6 at hProgramTy hProg' ⊢
  generalize hQ7 : Proof.pf P7 = q7 at hProgramTy hProg' ⊢
  revert hProgramTy hProg'
  -- `fun_cases` cannot build the cases principle for this 16-argument function
  -- under v4.33 (it diverges); unfolding to the raw matcher and using `split`
  -- gives the same eleven cases without generating a principle.
  unfold __eo_prog_bv_extract_mult_leading_bit
  split <;>
    simp_all [bvExtractMultLeadingNonnegPrem,
      bvExtractMultLeadingRangePrem, bvExtractMultLeadingLowPrem,
      bvExtractMultLeadingZerosTerm, bvExtractMultLeadingRaw,
      bvExtractMultLeadingOperand, extractLeadApp1, extractLeadApp2,
      extractLeadApp3]
  case h_10 =>
    -- `split` re-binds the nine `Term` arguments and the seven `Proof`s ahead of
    -- the pattern variables, so name only the trailing 22 (`xFull` was unused)
    rename_i r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
      r17 r18 r19 r20 r21 r22
    intro hMatchedTy hMatched
    have hGuardRaw := support_eo_requires_cond_eq_of_non_stuck hMatched
    have hGuard :
        bvExtractMultLeadingMatchGuard high low xi xin x yi yin y w r1 r2 r3
            r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
            r21 r22 = Term.Boolean true := by
      simpa [bvExtractMultLeadingMatchGuard] using hGuardRaw
    rcases bvExtractMultLeadingMatchGuard_eqs high low xi xin x yi yin y w r1
        r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
        r20 r21 r22 hGuard with
      ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12,
        hr13, hr14, hr15, hr16, hr17, hr18, hr19, hr20, hr21, hr22⟩
    subst r1; subst r2; subst r3; subst r4; subst r5; subst r6
    subst r7; subst r8; subst r9; subst r10; subst r11; subst r12
    subst r13; subst r14; subst r15; subst r16; subst r17; subst r18
    subst r19; subst r20; subst r21; subst r22
    rw [hGuardRaw] at hMatchedTy ⊢
    simp only [__eo_requires, native_ite, native_teq, native_not] at hMatchedTy ⊢
    exact hFactsRaw hMatchedTy hP2True hP3True hP4True hP5True hP6True

set_option maxHeartbeats 100000000 in
private theorem typed_bvExtractMultLeadingProgram
    (result high low xi xin x yi yin y w P1 P2 P3 P4 P5 P6 P7 : Term) :
    RuleProofs.eo_has_smt_translation high ->
    RuleProofs.eo_has_smt_translation low ->
    RuleProofs.eo_has_smt_translation xi ->
    RuleProofs.eo_has_smt_translation xin ->
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation yi ->
    RuleProofs.eo_has_smt_translation yin ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation w ->
    result = bvExtractMultLeadingProgram high low xi xin x yi yin y w
      P1 P2 P3 P4 P5 P6 P7 ->
    __eo_typeof result = Term.Bool ->
    RuleProofs.eo_has_bool_type result := by
  intro hHighTrans hLowTrans hXiTrans hXinTrans hXTrans hYiTrans hYinTrans
    hYTrans hWTrans hResult hProgramTy
  rw [hResult] at hProgramTy ⊢
  have hProg' := term_ne_stuck_of_typeof_bool hProgramTy
  have hHigh :=
    RuleProofs.term_ne_stuck_of_has_smt_translation high hHighTrans
  have hLow :=
    RuleProofs.term_ne_stuck_of_has_smt_translation low hLowTrans
  have hXi := RuleProofs.term_ne_stuck_of_has_smt_translation xi hXiTrans
  have hXin :=
    RuleProofs.term_ne_stuck_of_has_smt_translation xin hXinTrans
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYi := RuleProofs.term_ne_stuck_of_has_smt_translation yi hYiTrans
  have hYin :=
    RuleProofs.term_ne_stuck_of_has_smt_translation yin hYinTrans
  have hY := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hW := RuleProofs.term_ne_stuck_of_has_smt_translation w hWTrans
  have hTypedRaw := typed_bvExtractMultLeadingRaw high low xi xin x yi yin y w
    hHighTrans hLowTrans hXiTrans hXinTrans hXTrans hYiTrans hYinTrans
    hYTrans hWTrans
  unfold bvExtractMultLeadingProgram at hProgramTy hProg' ⊢
  generalize hQ1 : Proof.pf P1 = q1 at hProgramTy hProg' ⊢
  generalize hQ2 : Proof.pf P2 = q2 at hProgramTy hProg' ⊢
  generalize hQ3 : Proof.pf P3 = q3 at hProgramTy hProg' ⊢
  generalize hQ4 : Proof.pf P4 = q4 at hProgramTy hProg' ⊢
  generalize hQ5 : Proof.pf P5 = q5 at hProgramTy hProg' ⊢
  generalize hQ6 : Proof.pf P6 = q6 at hProgramTy hProg' ⊢
  generalize hQ7 : Proof.pf P7 = q7 at hProgramTy hProg' ⊢
  revert hProgramTy hProg'
  -- as above: `fun_cases` diverges on this 16-argument function under v4.33
  unfold __eo_prog_bv_extract_mult_leading_bit
  split <;>
    simp_all [bvExtractMultLeadingRaw, bvExtractMultLeadingOperand,
      extractLeadApp1, extractLeadApp2]
  case h_10 =>
    -- `split` re-binds the nine `Term` arguments and the seven `Proof`s ahead of
    -- the pattern variables, so name only the trailing 22 (`xFull` was unused)
    rename_i r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
      r17 r18 r19 r20 r21 r22
    intro hMatchedTy hMatched
    have hGuardRaw := support_eo_requires_cond_eq_of_non_stuck hMatched
    have hGuard :
        bvExtractMultLeadingMatchGuard high low xi xin x yi yin y w r1 r2 r3
            r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20
            r21 r22 = Term.Boolean true := by
      simpa [bvExtractMultLeadingMatchGuard] using hGuardRaw
    rcases bvExtractMultLeadingMatchGuard_eqs high low xi xin x yi yin y w r1
        r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19
        r20 r21 r22 hGuard with
      ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12,
        hr13, hr14, hr15, hr16, hr17, hr18, hr19, hr20, hr21, hr22⟩
    subst r1; subst r2; subst r3; subst r4; subst r5; subst r6
    subst r7; subst r8; subst r9; subst r10; subst r11; subst r12
    subst r13; subst r14; subst r15; subst r16; subst r17; subst r18
    subst r19; subst r20; subst r21; subst r22
    rw [hGuardRaw] at hMatchedTy ⊢
    simp only [__eo_requires, native_ite, native_teq, native_not] at hMatchedTy ⊢
    exact hTypedRaw hMatchedTy

public section

set_option maxHeartbeats 100000000 in
private theorem cmd_step_bv_extract_mult_leading_bit_properties_aux
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_mult_leading_bit args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit args premises) := by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  generalize hResultEq :
    __eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit args premises =
      result
  rcases bvExtractMultLeading_command_shape s args premises hProg with
    ⟨high, low, xi, xin, x, yi, yin, y, w, n1, n2, n3, n4, n5, n6, n7,
      hArgsEq, hPremisesEq⟩
  set_option maxHeartbeats 100000000 in
    rw [hPremisesEq]
    let P1 := __eo_state_proven_nth s n1
    let P2 := __eo_state_proven_nth s n2
    let P3 := __eo_state_proven_nth s n3
    let P4 := __eo_state_proven_nth s n4
    let P5 := __eo_state_proven_nth s n5
    let P6 := __eo_state_proven_nth s n6
    let P7 := __eo_state_proven_nth s n7
    change StepRuleProperties M
      [P1, P2, P3, P4, P5, P6, P7]
      result
    have hArgsTrans :
        RuleProofs.eo_has_smt_translation high ∧
        RuleProofs.eo_has_smt_translation low ∧
        RuleProofs.eo_has_smt_translation xi ∧
        RuleProofs.eo_has_smt_translation xin ∧
        RuleProofs.eo_has_smt_translation x ∧
        RuleProofs.eo_has_smt_translation yi ∧
        RuleProofs.eo_has_smt_translation yin ∧
        RuleProofs.eo_has_smt_translation y ∧
        RuleProofs.eo_has_smt_translation w ∧
        True := by
      exact bvExtractMultLeading_argument_translations args premises high low
        xi xin x yi yin y w hArgsEq hCmdTrans
    have hHighTrans := hArgsTrans.1
    have hLowTrans := hArgsTrans.2.1
    have hXiTrans := hArgsTrans.2.2.1
    have hXinTrans := hArgsTrans.2.2.2.1
    have hXTrans := hArgsTrans.2.2.2.2.1
    have hYiTrans := hArgsTrans.2.2.2.2.2.1
    have hYinTrans :=
      hArgsTrans.2.2.2.2.2.2.1
    have hYTrans :=
      hArgsTrans.2.2.2.2.2.2.2.1
    have hWTrans :=
      hArgsTrans.2.2.2.2.2.2.2.2.1
    have hProgramTy :
        __eo_typeof
          (bvExtractMultLeadingProgram high
            low xi xin x yi yin y w P1 P2
            P3 P4 P5 P6 P7) = Term.Bool := by
      simpa [P1, P2, P3, P4, P5, P6, P7] using
        (bvExtractMultLeading_program_type s args premises high low xi xin x
          yi yin y w n1 n2 n3 n4 n5 n6 n7 hArgsEq hPremisesEq hResultTy)
    have hResultProgram :
        result = bvExtractMultLeadingProgram high low xi xin x yi yin y w
          P1 P2 P3 P4 P5 P6 P7 := by
      simpa [P1, P2, P3, P4, P5, P6, P7] using
        (bvExtractMultLeading_result_eq_program s args premises result high low
          xi xin x yi yin y w n1 n2 n3 n4 n5 n6 n7 hArgsEq hPremisesEq
          hResultEq)
    have hResultProgramTy : __eo_typeof result = Term.Bool := by
      rw [hResultProgram]
      exact hProgramTy
    clear hCmdTrans _hPremisesBool hResultTy hProg hResultEq hArgsEq
      hPremisesEq
    refine ⟨?_, ?_⟩
    · intro hPremisesTrue
      exact facts_bvExtractMultLeadingProgram M hM result high low xi xin x yi
        yin y w P1 P2 P3 P4 P5 P6 P7 hHighTrans hLowTrans hXiTrans hXinTrans
        hXTrans hYiTrans hYinTrans hYTrans hWTrans hResultProgram
        hResultProgramTy
        (hPremisesTrue P1 (by simp)) (hPremisesTrue P2 (by simp))
        (hPremisesTrue P3 (by simp)) (hPremisesTrue P4 (by simp))
        (hPremisesTrue P5 (by simp)) (hPremisesTrue P6 (by simp))
        (hPremisesTrue P7 (by simp))
    · apply RuleProofs.eo_has_smt_translation_of_has_bool_type
      exact typed_bvExtractMultLeadingProgram result high low xi xin x yi yin y
        w P1 P2 P3 P4 P5 P6 P7 hHighTrans hLowTrans hXiTrans hXinTrans
        hXTrans hYiTrans hYinTrans hYTrans hWTrans hResultProgram
        hResultProgramTy

theorem cmd_step_bv_extract_mult_leading_bit_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_mult_leading_bit args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit args premises) :=
  cmd_step_bv_extract_mult_leading_bit_properties_aux M hM s args premises
