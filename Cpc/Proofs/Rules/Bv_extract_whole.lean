module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.TypePreservation.BitVec
import all Cpc.Proofs.TypePreservation.BitVec

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private def bvExtractWholePrem (x n : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.geq) n)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp._at_bvsize) x))
          (Term.Numeral 1))))
    (Term.Boolean true)

private def bvExtractWholeLhs (x n : Term) : Term :=
  Term.Apply (Term.UOp2 UserOp2.extract n (Term.Numeral 0)) x

private def bvExtractWholeTerm (x n : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq) (bvExtractWholeLhs x n))
    x

private theorem prog_bv_extract_whole_eq_of_ne_stuck
    (x n : Term) :
    x ≠ Term.Stuck ->
    n ≠ Term.Stuck ->
    __eo_prog_bv_extract_whole x n (Proof.pf (bvExtractWholePrem x n)) =
      bvExtractWholeTerm x n := by
  intro hX hN
  unfold bvExtractWholePrem
  rw [__eo_prog_bv_extract_whole.eq_3 x n n x hX hN]
  unfold bvExtractWholeTerm bvExtractWholeLhs
  cases n <;> cases x <;>
    simp [__eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
      native_not, SmtEval.native_not, SmtEval.native_and] at hN hX ⊢

private theorem bv_extract_whole_shape_of_ne_stuck (x n P : Term) :
    __eo_prog_bv_extract_whole x n (Proof.pf P) ≠ Term.Stuck ->
    x ≠ Term.Stuck ∧ n ≠ Term.Stuck ∧
      ∃ px pn, P = bvExtractWholePrem px pn := by
  intro hProg
  have hXNe : x ≠ Term.Stuck := by
    intro hX
    subst x
    exact hProg (__eo_prog_bv_extract_whole.eq_1 n (Proof.pf P))
  have hNNe : n ≠ Term.Stuck := by
    intro hN
    subst n
    exact hProg (__eo_prog_bv_extract_whole.eq_2 x (Proof.pf P) hXNe)
  refine ⟨hXNe, hNNe, ?_⟩
  by_cases hShape : ∃ px pn, P = bvExtractWholePrem px pn
  · exact hShape
  · exact False.elim (hProg
      (__eo_prog_bv_extract_whole.eq_4 x n (Proof.pf P) hXNe hNNe (by
        intro pn px hP
        cases hP
        exact hShape ⟨px, pn, rfl⟩)))

private theorem smt_bitvec_type_of_eo_bitvec_type_with_width
    (x w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof x =
      Term.Apply (Term.UOp UserOp.BitVec) w ->
    ∃ n, w = Term.Numeral n ∧ native_zleq 0 n = true ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) := by
  intro hXTrans hXType
  have hSmtType :
      __smtx_typeof (__eo_to_smt x) =
        __eo_to_smt_type
          (Term.Apply (Term.UOp UserOp.BitVec) w) := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x (Term.Apply (Term.UOp UserOp.BitVec) w)
      (__eo_to_smt x) rfl hXTrans hXType
  cases w <;> simp [__eo_to_smt_type] at hSmtType
  case Numeral n =>
    cases hNonneg : native_zleq 0 n <;>
      simp [__eo_to_smt_type, hNonneg] at hSmtType
    · exact False.elim (hXTrans hSmtType)
    · exact ⟨n, rfl, hNonneg, hSmtType⟩
  all_goals
    exact False.elim (hXTrans hSmtType)

private theorem eo_mk_apply_bitvec_stuck_or_bitvec (w : Term) :
    __eo_mk_apply (Term.UOp UserOp.BitVec) w = Term.Stuck ∨
      ∃ u, __eo_mk_apply (Term.UOp UserOp.BitVec) w =
        Term.Apply (Term.UOp UserOp.BitVec) u := by
  cases w <;> simp [__eo_mk_apply]

private theorem eo_mk_apply_bitvec_eq_apply_inv (u v : Term) :
    __eo_mk_apply (Term.UOp UserOp.BitVec) u =
      Term.Apply (Term.UOp UserOp.BitVec) v ->
    u = v := by
  intro h
  cases u <;> simp [__eo_mk_apply] at h ⊢ <;> simpa using h

private theorem eo_typeof_extract_stuck_or_bitvec
    (A h B l C : Term) :
    __eo_typeof_extract A h B l C = Term.Stuck ∨
      ∃ w, __eo_typeof_extract A h B l C =
        Term.Apply (Term.UOp UserOp.BitVec) w := by
  unfold __eo_typeof_extract
  split
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact eo_mk_apply_bitvec_stuck_or_bitvec _
  · exact Or.inl rfl

private theorem extract_whole_args_of_type_bool
    (x n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractWholeTerm x n) = Term.Bool ->
    ∃ w hi,
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ∧
      n = Term.Numeral hi ∧
      native_zleq 0 w = true ∧
      native_zlt hi w = true ∧
      native_zlt 0 (native_zplus hi 1) = true ∧
      native_zplus hi 1 = w ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w) := by
  intro hXTrans hTy
  have hTypes :
      __eo_typeof (bvExtractWholeLhs x n) = __eo_typeof x := by
    change __eo_typeof_eq (__eo_typeof (bvExtractWholeLhs x n))
        (__eo_typeof x) = Term.Bool at hTy
    exact support_eo_typeof_eq_bool_operands_eq
      (__eo_typeof (bvExtractWholeLhs x n)) (__eo_typeof x) hTy
  change
      __eo_typeof_extract (__eo_typeof n) n (Term.UOp UserOp.Int)
        (Term.Numeral 0) (__eo_typeof x) = __eo_typeof x at hTypes
  rcases eo_typeof_extract_stuck_or_bitvec (__eo_typeof n) n
      (Term.UOp UserOp.Int) (Term.Numeral 0) (__eo_typeof x) with
    hExtractStuck | ⟨wTerm, hExtractTy⟩
  · have hXStuck : __eo_typeof x = Term.Stuck := by
      rw [← hTypes, hExtractStuck]
    have hSmtType :
        __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type Term.Stuck :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        x Term.Stuck (__eo_to_smt x) rfl hXTrans hXStuck
    exact False.elim (hXTrans (by simpa [__eo_to_smt_type] using hSmtType))
  · have hXBitVec :
        __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) wTerm := by
      rw [← hTypes, hExtractTy]
    rcases smt_bitvec_type_of_eo_bitvec_type_with_width
        x wTerm hXTrans hXBitVec with
      ⟨w, hWTerm, hWNonneg, hXSmtTy⟩
    subst wTerm
    have hExtractTyX :
        __eo_typeof_extract (__eo_typeof n) n (Term.UOp UserOp.Int)
            (Term.Numeral 0)
            (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w)) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
      simpa [hXBitVec] using hExtractTy
    cases hNTy : __eo_typeof n with
    | UOp op =>
      by_cases hOp : op = UserOp.Int
      · subst op
        have hExtractTyInt :
            __eo_typeof_extract (Term.UOp UserOp.Int) n
                (Term.UOp UserOp.Int) (Term.Numeral 0)
                (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w)) =
              Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
          simpa [hNTy] using hExtractTyX
        cases n <;>
          try
            (exfalso
             simpa [__eo_typeof_extract, __eo_mk_apply,
               __eo_requires, __eo_gt, __eo_add, __eo_neg, native_ite,
               native_teq, native_not, SmtEval.native_not,
               SmtEval.native_zplus, SmtEval.native_zneg] using hExtractTyInt)
        case pos.Numeral hi =>
          let lowReq :=
            __eo_requires
              (__eo_gt (Term.Numeral 0) (Term.Numeral (-1 : native_Int)))
              (Term.Boolean true)
              (__eo_requires (__eo_gt (Term.Numeral w) (Term.Numeral hi))
                (Term.Boolean true)
                (__eo_requires
                  (__eo_gt (Term.Numeral (native_zplus hi 1))
                    (Term.Numeral 0))
                  (Term.Boolean true) (Term.Numeral (native_zplus hi 1))))
          have hApplyEq :
              __eo_mk_apply (Term.UOp UserOp.BitVec) lowReq =
                Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
            simpa [lowReq, __eo_typeof_extract, __eo_add, __eo_neg,
              SmtEval.native_zplus, SmtEval.native_zneg] using hExtractTyInt
          have hReqEqLow :
              lowReq = Term.Numeral w :=
            eo_mk_apply_bitvec_eq_apply_inv lowReq (Term.Numeral w) hApplyEq
          have hLowTrue :
              __eo_gt (Term.Numeral 0) (Term.Numeral (-1 : native_Int)) =
                Term.Boolean true := by
            simp [__eo_gt, SmtEval.native_zlt]
          have hReqEq :
              __eo_requires (__eo_gt (Term.Numeral w) (Term.Numeral hi))
                  (Term.Boolean true)
                  (__eo_requires
                    (__eo_gt (Term.Numeral (native_zplus hi 1))
                      (Term.Numeral 0))
                    (Term.Boolean true) (Term.Numeral (native_zplus hi 1))) =
                Term.Numeral w := by
            have hLowReqReduce :
                lowReq =
                  __eo_requires (__eo_gt (Term.Numeral w) (Term.Numeral hi))
                    (Term.Boolean true)
                    (__eo_requires
                      (__eo_gt (Term.Numeral (native_zplus hi 1))
                        (Term.Numeral 0))
                      (Term.Boolean true) (Term.Numeral (native_zplus hi 1))) := by
              simp [lowReq, __eo_requires, hLowTrue, native_ite, native_teq,
                native_not, SmtEval.native_not]
            rw [hLowReqReduce] at hReqEqLow
            exact hReqEqLow
          have hReqNe :
              __eo_requires (__eo_gt (Term.Numeral w) (Term.Numeral hi))
                  (Term.Boolean true)
                  (__eo_requires
                    (__eo_gt (Term.Numeral (native_zplus hi 1))
                      (Term.Numeral 0))
                    (Term.Boolean true) (Term.Numeral (native_zplus hi 1))) ≠
                Term.Stuck := by
            rw [hReqEq]
            intro h
            cases h
          have hHiLtTerm :
              __eo_gt (Term.Numeral w) (Term.Numeral hi) =
                Term.Boolean true :=
            support_eo_requires_cond_eq_of_non_stuck hReqNe
          have hHiLt : native_zlt hi w = true := by
            simpa [__eo_gt] using hHiLtTerm
          have hInnerEq :
              __eo_requires
                  (__eo_gt (Term.Numeral (native_zplus hi 1))
                    (Term.Numeral 0))
                  (Term.Boolean true) (Term.Numeral (native_zplus hi 1)) =
                Term.Numeral w := by
            simpa [__eo_requires, hHiLtTerm, native_ite, native_teq,
              native_not, SmtEval.native_not] using hReqEq
          have hInnerNe :
              __eo_requires
                  (__eo_gt (Term.Numeral (native_zplus hi 1))
                    (Term.Numeral 0))
                  (Term.Boolean true) (Term.Numeral (native_zplus hi 1)) ≠
                Term.Stuck := by
            rw [hInnerEq]
            intro h
            cases h
          have hWidthNonnegTerm :
              __eo_gt (Term.Numeral (native_zplus hi 1))
                  (Term.Numeral 0) =
                Term.Boolean true :=
            support_eo_requires_cond_eq_of_non_stuck hInnerNe
          have hWidthPos :
              native_zlt 0 (native_zplus hi 1) = true := by
            simpa [__eo_gt] using hWidthNonnegTerm
          have hHiWidth : native_zplus hi 1 = w := by
            simpa [__eo_requires, hWidthNonnegTerm, native_ite, native_teq,
              native_not, SmtEval.native_not] using hInnerEq
          exact ⟨w, hi, hXBitVec, rfl, hWNonneg, hHiLt,
            hWidthPos, hHiWidth, hXSmtTy⟩
      · exfalso
        have hBad := hExtractTyX
        rw [hNTy] at hBad
        unfold __eo_typeof_extract at hBad
        split at hBad <;> simp_all
    | _ =>
      exfalso
      have hBad := hExtractTyX
      rw [hNTy] at hBad
      unfold __eo_typeof_extract at hBad
      split at hBad <;> simp_all

private theorem native_nat_to_int_int_to_nat_eq
    (n : native_Int) :
    native_zleq 0 n = true ->
    native_nat_to_int (native_int_to_nat n) = n := by
  intro hNonneg
  have hn : (0 : native_Int) <= n := by
    simpa [SmtEval.native_zleq] using hNonneg
  have hInt : (Int.ofNat (Int.toNat n) : Int) = n :=
    Int.toNat_of_nonneg hn
  simpa [Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
    native_nat_to_int, native_int_to_nat] using hInt

private theorem typed_bv_extract_whole_term
    (x n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractWholeTerm x n) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvExtractWholeTerm x n) := by
  intro hXTrans hResultTy
  rcases extract_whole_args_of_type_bool x n hXTrans hResultTy with
    ⟨w, hi, hXTy, hN, hWNonneg, hHiLt, hWidthNonneg, hHiWidth, hXSmtTy⟩
  subst n
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt (bvExtractWholeLhs x (Term.Numeral hi))) =
        SmtType.BitVec (native_int_to_nat w) := by
    have hLow : native_zleq 0 (0 : native_Int) = true := by decide
    have hRound := native_nat_to_int_int_to_nat_eq w hWNonneg
    have hWidthExpr :
        native_zplus (native_zplus hi 1) (native_zneg (0 : native_Int)) = w := by
      simpa [SmtEval.native_zplus, SmtEval.native_zneg] using hHiWidth
    have hWidthNonneg' : native_zlt 0 (hi + 1) = true := by
      simpa [SmtEval.native_zplus] using hWidthNonneg
    have hWPos : native_zlt 0 w = true := by
      rw [← hHiWidth]
      exact hWidthNonneg
    have hHiWidth' : hi + 1 = w := by
      simpa [SmtEval.native_zplus] using hHiWidth
    unfold bvExtractWholeLhs
    change __smtx_typeof
        (SmtTerm.extract (SmtTerm.Numeral hi) (SmtTerm.Numeral 0)
          (__eo_to_smt x)) =
      SmtType.BitVec (native_int_to_nat w)
    rw [typeof_extract_eq, hXSmtTy]
    simp [__smtx_typeof_extract, native_ite, hLow, hHiLt,
      hWNonneg, hWPos, hWidthNonneg, hWidthNonneg', hHiWidth, hHiWidth', hRound, hWidthExpr,
      SmtEval.native_zplus, SmtEval.native_zneg]
  unfold bvExtractWholeTerm
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (bvExtractWholeLhs x (Term.Numeral hi)) x
    (hLhsTy.trans hXSmtTy.symm)
    (by
      rw [hLhsTy]
      intro hNone
      cases hNone)

private theorem smtx_eval_numeral_term_eq
    (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def]

private theorem eval_extract_whole_matches
    (M : SmtModel) (hM : model_wf M) (x n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractWholeTerm x n) = Term.Bool ->
    __smtx_model_eval M (__eo_to_smt (bvExtractWholeLhs x n)) =
      __smtx_model_eval M (__eo_to_smt x) := by
  intro hXTrans hResultTy
  rcases extract_whole_args_of_type_bool x n hXTrans hResultTy with
    ⟨w, hi, hXTy, hN, hWNonneg, _hHiLt, _hWidthNonneg, hHiWidth,
      hXSmtTy⟩
  subst n
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.BitVec (native_int_to_nat w) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type]
          using hXTrans)
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalX⟩
  have hRound := native_nat_to_int_int_to_nat_eq w hWNonneg
  rw [hRound] at hEvalX
  have hEvalTyW :
      __smtx_typeof_value (SmtValue.Binary w payload) =
        SmtType.BitVec (native_int_to_nat w) := by
    simpa [hEvalX] using hEvalTy
  have hPayloadCanon :
      native_zeq payload (native_mod_total payload (native_int_pow2 w)) = true :=
    bitvec_payload_canonical hEvalTyW
  have hPayloadMod :
      native_mod_total payload (native_int_pow2 w) = payload := by
    have hEq : payload = native_mod_total payload (native_int_pow2 w) := by
      simpa [SmtEval.native_zeq] using hPayloadCanon
    exact hEq.symm
  have hWidthExpr :
      native_zplus (native_zplus hi 1) (native_zneg (0 : native_Int)) = w := by
    simpa [SmtEval.native_zplus, SmtEval.native_zneg] using hHiWidth
  have hPow0 : native_int_pow2 (0 : native_Int) = 1 := by decide
  unfold bvExtractWholeLhs
  change __smtx_model_eval M
      (SmtTerm.extract (SmtTerm.Numeral hi) (SmtTerm.Numeral 0)
        (__eo_to_smt x)) =
    __smtx_model_eval M (__eo_to_smt x)
  rw [smtx_eval_extract_term_eq, smtx_eval_numeral_term_eq,
    smtx_eval_numeral_term_eq, hEvalX]
  simp [__smtx_model_eval_extract, native_binary_extract,
    SmtEval.native_div_total, hPow0, hWidthExpr, hPayloadMod]

private theorem facts_bv_extract_whole_term
    (M : SmtModel) (hM : model_wf M) (x n : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractWholeTerm x n) = Term.Bool ->
    eo_interprets M (bvExtractWholeTerm x n) true := by
  intro hXTrans hResultTy
  have hTermBool := typed_bv_extract_whole_term x n hXTrans hResultTy
  unfold bvExtractWholeTerm
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvExtractWholeTerm] using hTermBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvExtractWholeLhs x n)))
      (__smtx_model_eval M (__eo_to_smt x))
    rw [eval_extract_whole_matches M hM x n hXTrans hResultTy]
    exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_bv_extract_whole_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_whole args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_extract_whole args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_whole args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_extract_whole args premises ≠ Term.Stuck :=
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
              | cons n1 premises =>
                  cases premises with
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | nil =>
                      let P1 := __eo_state_proven_nth s n1
                      change
                        StepRuleProperties M [P1]
                          (__eo_prog_bv_extract_whole a1 a2 (Proof.pf P1))
                      have hProgLocal :
                          __eo_prog_bv_extract_whole a1 a2 (Proof.pf P1) ≠ Term.Stuck := by
                        exact hProg
                      rcases bv_extract_whole_shape_of_ne_stuck a1 a2 P1 hProgLocal with
                        ⟨hA1Ne, hA2Ne, px, pn, hP1⟩
                      have hReqNe :
                          __eo_requires (__eo_and (__eo_eq a2 pn) (__eo_eq a1 px))
                              (Term.Boolean true)
                              (bvExtractWholeTerm a1 a2) ≠ Term.Stuck := by
                        have h := hProgLocal
                        rw [hP1] at h
                        unfold bvExtractWholePrem at h
                        rw [__eo_prog_bv_extract_whole.eq_3 a1 a2 pn px hA1Ne hA2Ne]
                          at h
                        simpa [bvExtractWholePrem, bvExtractWholeTerm,
                          bvExtractWholeLhs] using h
                      rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                          a2 a1 pn px (bvExtractWholeTerm a1 a2) hReqNe with
                        ⟨hPn, hPx⟩
                      subst pn
                      subst px
                      have hATransPair :
                          RuleProofs.eo_has_smt_translation a1 ∧
                            RuleProofs.eo_has_smt_translation a2 ∧ True := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                      have hA1Trans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
                      have hResultTyCanonical :
                          __eo_typeof (bvExtractWholeTerm a1 a2) = Term.Bool := by
                        have hResultTyLocal := hResultTy
                        change __eo_typeof
                            (__eo_prog_bv_extract_whole a1 a2
                              (Proof.pf (__eo_state_proven_nth s n1))) =
                          Term.Bool at hResultTyLocal
                        simpa [P1, hP1, prog_bv_extract_whole_eq_of_ne_stuck
                          a1 a2 hA1Ne hA2Ne] using hResultTyLocal
                      refine ⟨?_, ?_⟩
                      · intro _hTrue
                        change eo_interprets M
                          (__eo_prog_bv_extract_whole a1 a2 (Proof.pf P1)) true
                        rw [hP1, prog_bv_extract_whole_eq_of_ne_stuck
                          a1 a2 hA1Ne hA2Ne]
                        exact facts_bv_extract_whole_term M hM a1 a2 hA1Trans
                          hResultTyCanonical
                      · rw [hP1, prog_bv_extract_whole_eq_of_ne_stuck
                          a1 a2 hA1Ne hA2Ne]
                        exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed_bv_extract_whole_term a1 a2 hA1Trans
                            hResultTyCanonical)
