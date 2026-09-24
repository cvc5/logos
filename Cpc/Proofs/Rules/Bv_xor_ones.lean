module

public import Cpc.Proofs.RuleSupport.BvXorOnesSupport
import all Cpc.Proofs.RuleSupport.BvXorOnesSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private def bvXorOnesSkeleton (xs zs n w : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (BvXorOnesSupport.lhs xs zs n w))
    (__eo_mk_apply (Term.UOp UserOp.bvnot)
      (BvXorOnesSupport.base xs zs))

private theorem bv_xor_ones_skeleton_eq_term_of_ne_stuck
    (xs zs n w : Term) :
    bvXorOnesSkeleton xs zs n w ≠ Term.Stuck ->
    bvXorOnesSkeleton xs zs n w =
      BvXorOnesSupport.term xs zs n w := by
  intro hTop
  have hEqFun := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hTop
  have hRhs := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hTop
  unfold bvXorOnesSkeleton
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hTop]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFun]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hRhs]
  rfl

private theorem prog_bv_xor_ones_eq_term_of_ne_stuck
    (xs zs n w : Term) :
    xs ≠ Term.Stuck -> zs ≠ Term.Stuck ->
    n ≠ Term.Stuck -> w ≠ Term.Stuck ->
    __eo_prog_bv_xor_ones xs zs n w
        (Proof.pf (bvAllOnesValuePrem n w)) ≠ Term.Stuck ->
    __eo_prog_bv_xor_ones xs zs n w
        (Proof.pf (bvAllOnesValuePrem n w)) =
      BvXorOnesSupport.term xs zs n w := by
  intro hXs hZs hN hW hProg
  have hSkeleton :
      __eo_prog_bv_xor_ones xs zs n w
          (Proof.pf (bvAllOnesValuePrem n w)) =
        bvXorOnesSkeleton xs zs n w := by
    unfold bvAllOnesValuePrem
    rw [__eo_prog_bv_xor_ones.eq_5 xs zs n w n w hXs hZs hN hW]
    simp [bvXorOnesSkeleton, BvXorOnesSupport.lhs,
      BvXorOnesSupport.insertedTail, BvXorOnesSupport.base,
      BvXorOnesSupport.baseList, bvAllOnesConst,
      __eo_requires, __eo_and, __eo_eq,
      native_ite, native_teq, native_not, SmtEval.native_not,
      SmtEval.native_and, hN, hW]
  have hSkeletonNe : bvXorOnesSkeleton xs zs n w ≠ Term.Stuck := by
    rwa [hSkeleton] at hProg
  rw [hSkeleton]
  exact bv_xor_ones_skeleton_eq_term_of_ne_stuck xs zs n w hSkeletonNe

private theorem bv_xor_ones_shape_of_ne_stuck
    (xs zs n w P : Term) :
    __eo_prog_bv_xor_ones xs zs n w (Proof.pf P) ≠ Term.Stuck ->
    xs ≠ Term.Stuck ∧ zs ≠ Term.Stuck ∧
      n ≠ Term.Stuck ∧ w ≠ Term.Stuck ∧
      ∃ pn pw, P = bvAllOnesValuePrem pn pw := by
  intro hProg
  have hXs : xs ≠ Term.Stuck := by
    intro h
    subst xs
    exact hProg (__eo_prog_bv_xor_ones.eq_1 zs n w (Proof.pf P))
  have hZs : zs ≠ Term.Stuck := by
    intro h
    subst zs
    exact hProg (__eo_prog_bv_xor_ones.eq_2 xs n w (Proof.pf P) hXs)
  have hN : n ≠ Term.Stuck := by
    intro h
    subst n
    exact hProg (__eo_prog_bv_xor_ones.eq_3 xs zs w (Proof.pf P) hXs hZs)
  have hW : w ≠ Term.Stuck := by
    intro h
    subst w
    exact hProg
      (__eo_prog_bv_xor_ones.eq_4 xs zs n (Proof.pf P) hXs hZs hN)
  by_cases hShape : ∃ pn pw, P = bvAllOnesValuePrem pn pw
  · rcases hShape with ⟨pn, pw, hP⟩
    exact ⟨hXs, hZs, hN, hW, pn, pw, hP⟩
  · have hStuck :
        __eo_prog_bv_xor_ones xs zs n w (Proof.pf P) = Term.Stuck := by
      exact __eo_prog_bv_xor_ones.eq_6 xs zs n w (Proof.pf P)
        hXs hZs hN hW (by
          intro pn pw hp
          cases hp
          exact hShape ⟨pn, pw, rfl⟩)
    exact False.elim (hProg hStuck)

public theorem cmd_step_bv_xor_ones_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_xor_ones args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_xor_ones args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_xor_ones args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_xor_ones args premises ≠
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
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons i1 premises =>
                          cases premises with
                          | cons _ _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | nil =>
                              let P1 := __eo_state_proven_nth s i1
                              change StepRuleProperties M [P1]
                                (__eo_prog_bv_xor_ones a1 a2 a3 a4
                                  (Proof.pf P1))
                              have hProgLocal :
                                  __eo_prog_bv_xor_ones a1 a2 a3 a4
                                      (Proof.pf P1) ≠ Term.Stuck := by
                                have hsimpa := hProg
                                try simp [P1] at hsimpa ⊢
                                exact hsimpa
                              rcases bv_xor_ones_shape_of_ne_stuck
                                  a1 a2 a3 a4 P1 hProgLocal with
                                ⟨hA1Ne, hA2Ne, hA3Ne, hA4Ne,
                                  pn, pw, hP1⟩
                              have hReqNe := hProgLocal
                              rw [hP1] at hReqNe
                              unfold bvAllOnesValuePrem at hReqNe
                              rw [__eo_prog_bv_xor_ones.eq_5
                                a1 a2 a3 a4 pn pw
                                hA1Ne hA2Ne hA3Ne hA4Ne] at hReqNe
                              rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                                  a3 a4 pn pw _ hReqNe with
                                ⟨hPn, hPw⟩
                              subst pn
                              subst pw
                              have hProgEq :=
                                prog_bv_xor_ones_eq_term_of_ne_stuck
                                  a1 a2 a3 a4 hA1Ne hA2Ne hA3Ne hA4Ne
                                  (by simpa [hP1] using hProgLocal)
                              have hResultTyCanonical :
                                  __eo_typeof
                                      (BvXorOnesSupport.term a1 a2 a3 a4) =
                                    Term.Bool := by
                                have h := hResultTy
                                change __eo_typeof
                                    (__eo_prog_bv_xor_ones a1 a2 a3 a4
                                      (Proof.pf
                                        (__eo_state_proven_nth s i1))) =
                                      Term.Bool at h
                                simpa [P1, hP1, hProgEq] using h
                              have hArgTranslations :
                                  RuleProofs.eo_has_smt_translation a1 ∧
                                    RuleProofs.eo_has_smt_translation a2 ∧
                                    RuleProofs.eo_has_smt_translation a3 ∧
                                    RuleProofs.eo_has_smt_translation a4 := by
                                simpa [cmdTranslationOk, cArgListTranslationOk,
                                  eoHasSmtTranslation,
                                  RuleProofs.eo_has_smt_translation] using hCmdTrans
                              rcases BvXorOnesSupport.inferred_argument_types
                                  a1 a2 a3 a4 hArgTranslations.1
                                  hArgTranslations.2.1 hArgTranslations.2.2.1
                                  hArgTranslations.2.2.2 hResultTyCanonical with
                                ⟨W, hA4, hW0, hA2Ty, hA3Ty,
                                  hA1TypeOrNil⟩
                              simpa [hP1, hProgEq] using
                                (show StepRuleProperties M
                                    [bvAllOnesValuePrem a3 a4]
                                    (BvXorOnesSupport.term a1 a2 a3 a4) from
                                  ⟨(by
                                      intro hPremisesTrue
                                      have hPrem :
                                          eo_interprets M
                                            (bvAllOnesValuePrem a3 a4) true :=
                                        hPremisesTrue.true_here _ (by simp)
                                      exact
                                        BvXorOnesSupport.facts_term_of_type_or_nil
                                        M hM a1 a2 a3 a4 W hA1TypeOrNil hA2Ty
                                        hA3Ty hA4 hW0 hPrem
                                        hResultTyCanonical),
                                    RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                      (BvXorOnesSupport.typed_term_of_type_or_nil
                                        a1 a2 a3 a4 W hA1TypeOrNil hA2Ty
                                        hA3Ty hA4 hW0
                                        hResultTyCanonical)⟩)
