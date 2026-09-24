module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private abbrev intToBvTerm (w t : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv w) t

private abbrev ubvToIntTerm (t : Term) : Term :=
  Term.Apply (Term.UOp UserOp.ubv_to_int) t

private abbrev intPow2Term (w : Term) : Term :=
  Term.Apply (Term.UOp UserOp.int_pow2) w

private abbrev modTotalTerm (t w : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) t) (intPow2Term w)

private abbrev ufInt2bvBv2natConclusion (w t : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (ubvToIntTerm (intToBvTerm w t)))
    (modTotalTerm t w)

private abbrev ufInt2bvBv2natType (w t : Term) : Term :=
  __eo_typeof_eq
    (__eo_typeof__at_bvsize
      (__eo_typeof_int_to_bv (__eo_typeof w) w (__eo_typeof t)))
    (__eo_typeof_div (__eo_typeof t)
      (__eo_typeof_int_pow2 (__eo_typeof w)))

private theorem typeof_ufInt2bvBv2natConclusion_eq (w t : Term) :
    __eo_typeof (ufInt2bvBv2natConclusion w t) =
      ufInt2bvBv2natType w t := by
  rfl

private theorem smtx_eval_int_pow2_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.int_pow2 x) =
      __smtx_model_eval_int_pow2 (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_mod_total_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.mod_total x y) =
      __smtx_model_eval_mod_total
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem prog_uf_int2bv_bv2nat_eq_of_ne_stuck (w t : Term) :
    w ≠ Term.Stuck ->
    t ≠ Term.Stuck ->
    __eo_prog_uf_int2bv_bv2nat w t =
      ufInt2bvBv2natConclusion w t := by
  intro hW hT
  cases w <;> cases t <;>
    simp [__eo_prog_uf_int2bv_bv2nat, ufInt2bvBv2natConclusion,
      ubvToIntTerm, intToBvTerm, modTotalTerm, intPow2Term] at hW hT ⊢

private theorem typeof_prog_uf_int2bv_bv2nat_eq_of_ne_stuck (w t : Term) :
    w ≠ Term.Stuck ->
    t ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_uf_int2bv_bv2nat w t) =
      ufInt2bvBv2natType w t := by
  intro hW hT
  cases w <;> cases t <;>
    simp [__eo_prog_uf_int2bv_bv2nat, ufInt2bvBv2natConclusion,
      ubvToIntTerm, intToBvTerm, modTotalTerm, intPow2Term,
      typeof_ufInt2bvBv2natConclusion_eq] at hW hT ⊢

private theorem nonneg_of_width_guard (n : native_Int) :
    native_zlt (-1 : native_Int) n = true ->
    native_zleq 0 n = true := by
  intro hLt
  have hLt' : (-1 : native_Int) < n := by
    simpa [native_zlt, SmtEval.native_zlt] using hLt
  have hNonneg : (0 : native_Int) <= n := by
    have hStep : (-1 : native_Int) + 1 <= n :=
      (Int.add_one_le_iff).2 hLt'
    simpa using hStep
  simpa [native_zleq, SmtEval.native_zleq] using hNonneg

private theorem typeof_args_of_prog_uf_int2bv_bv2nat_bool (w t : Term) :
    __eo_typeof (__eo_prog_uf_int2bv_bv2nat w t) = Term.Bool ->
    ∃ n, w = Term.Numeral n ∧ native_zleq 0 n = true ∧
      __eo_typeof t = Term.UOp UserOp.Int := by
  intro hTy
  by_cases hW : w = Term.Stuck
  · subst w
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hStuckTy hTy)
  · by_cases hT : t = Term.Stuck
    · subst t
      cases w <;> simp [__eo_prog_uf_int2bv_bv2nat] at hW hTy
      all_goals
        have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
          native_decide
        exact False.elim (hStuckTy hTy)
    · have hTySmall : ufInt2bvBv2natType w t = Term.Bool :=
        (typeof_prog_uf_int2bv_bv2nat_eq_of_ne_stuck w t hW hT).symm.trans hTy
      clear hTy
      cases hWTy : __eo_typeof w with
      | UOp op =>
          by_cases hOp : op = UserOp.Int
          · subst op
            cases w
            case pos.Numeral n =>
              cases hTTy : __eo_typeof t with
              | UOp op =>
                  by_cases hTOp : op = UserOp.Int
                  · subst op
                    cases hPos : native_zlt (-1 : native_Int) n <;>
                      simp [ufInt2bvBv2natType, hWTy, __eo_lit_type_Numeral,
                        __eo_typeof_eq, __eo_typeof__at_bvsize,
                        __eo_typeof_int_to_bv, __eo_typeof_int_pow2,
                        __eo_typeof_div, __eo_requires, __eo_gt, __eo_eq,
                        native_ite, native_teq, native_not, __is_arith_type,
                        hTTy, hPos] at hTySmall
                    exact ⟨n, rfl, nonneg_of_width_guard n hPos, by simpa [hTTy]⟩
                  · exfalso
                    cases op <;>
                      simp [ufInt2bvBv2natType, hWTy, __eo_lit_type_Numeral,
                        __eo_typeof_eq, __eo_typeof__at_bvsize,
                        __eo_typeof_int_to_bv, __eo_typeof_int_pow2,
                        __eo_typeof_div, __eo_requires, __eo_gt, __eo_eq,
                        native_ite, native_teq, native_not, __is_arith_type,
                        hTTy] at hTOp hTySmall
              | _ =>
                  simp [ufInt2bvBv2natType, hWTy, __eo_lit_type_Numeral,
                    __eo_typeof_eq, __eo_typeof__at_bvsize,
                    __eo_typeof_int_to_bv, __eo_typeof_int_pow2,
                    __eo_typeof_div, __eo_requires, __eo_gt, __eo_eq,
                    native_ite, native_teq, native_not, __is_arith_type,
                    hTTy] at hTySmall
            all_goals
              exfalso
              cases hTTy : __eo_typeof t with
              | UOp tOp =>
                  cases tOp <;>
                    simpa [ufInt2bvBv2natType, hWTy, hTTy, __eo_typeof_eq,
                      __eo_typeof__at_bvsize, __eo_typeof_int_to_bv,
                      __eo_typeof_int_pow2, __eo_typeof_div, __eo_requires,
                      __eo_gt, __eo_eq, native_ite, native_teq, native_not,
                      __is_arith_type] using hTySmall
              | _ =>
                  simpa [ufInt2bvBv2natType, hWTy, hTTy, __eo_typeof_eq,
                    __eo_typeof__at_bvsize, __eo_typeof_int_to_bv,
                    __eo_typeof_int_pow2, __eo_typeof_div, __eo_requires,
                    __eo_gt, __eo_eq, native_ite, native_teq, native_not,
                    __is_arith_type] using hTySmall
          · exfalso
            cases op <;>
              simp [ufInt2bvBv2natType, hWTy, __eo_typeof_eq,
                __eo_typeof__at_bvsize, __eo_typeof_int_to_bv,
                __eo_typeof_int_pow2, __eo_typeof_div] at hOp hTySmall
      | _ =>
          exfalso
          simpa [ufInt2bvBv2natType, hWTy, __eo_typeof_eq,
            __eo_typeof__at_bvsize, __eo_typeof_int_to_bv,
            __eo_typeof_int_pow2, __eo_typeof_div] using hTySmall

private theorem smtx_typeof_of_eo_int
    (t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    __eo_typeof t = Term.UOp UserOp.Int ->
    __smtx_typeof (__eo_to_smt t) = SmtType.Int := by
  intro hTrans hTy
  have hSmtType :
      __smtx_typeof (__eo_to_smt t) =
        __eo_to_smt_type (Term.UOp UserOp.Int) := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t (Term.UOp UserOp.Int) (__eo_to_smt t) rfl hTrans hTy
  simpa [__eo_to_smt_type] using hSmtType

private theorem smt_typeof_ubv_int_to_bv_term_eq
    (n : native_Int) (t : Term) :
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt t) = SmtType.Int ->
    __smtx_typeof (__eo_to_smt (ubvToIntTerm (intToBvTerm (Term.Numeral n) t))) =
      SmtType.Int := by
  intro hNonneg hTSmtTy
  change __smtx_typeof
      (SmtTerm.ubv_to_int (SmtTerm.int_to_bv (SmtTerm.Numeral n) (__eo_to_smt t))) =
    SmtType.Int
  rw [smtx_typeof_ubv_to_int_term_eq, smtx_typeof_int_to_bv_term_eq]
  simp [__smtx_typeof_int_to_bv, __smtx_typeof_bv_op_1_ret, native_ite,
    hTSmtTy,
    hNonneg]

private theorem smt_typeof_mod_pow2_term_eq
    (n : native_Int) (t : Term) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Int ->
    __smtx_typeof (__eo_to_smt (modTotalTerm t (Term.Numeral n))) =
      SmtType.Int := by
  intro hTSmtTy
  change __smtx_typeof
      (SmtTerm.mod_total (__eo_to_smt t) (SmtTerm.int_pow2 (SmtTerm.Numeral n))) =
    SmtType.Int
  rw [typeof_mod_total_eq, typeof_int_pow2_eq]
  rw [__smtx_typeof.eq_2]
  simp [native_ite, native_Teq, hTSmtTy]

private theorem typed___eo_prog_uf_int2bv_bv2nat_impl
    (w t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    __eo_typeof (__eo_prog_uf_int2bv_bv2nat w t) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_uf_int2bv_bv2nat w t) := by
  intro hTTrans hResultTy
  rcases typeof_args_of_prog_uf_int2bv_bv2nat_bool w t hResultTy with
    ⟨n, hW, hNonneg, hTType⟩
  subst w
  have hTNotStuck : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hTSmtTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    smtx_typeof_of_eo_int t hTTrans hTType
  have hLhsTy :
      __smtx_typeof (__eo_to_smt
        (ubvToIntTerm (intToBvTerm (Term.Numeral n) t))) = SmtType.Int :=
    smt_typeof_ubv_int_to_bv_term_eq n t hNonneg hTSmtTy
  have hRhsTy :
      __smtx_typeof (__eo_to_smt (modTotalTerm t (Term.Numeral n))) =
        SmtType.Int :=
    smt_typeof_mod_pow2_term_eq n t hTSmtTy
  rw [prog_uf_int2bv_bv2nat_eq_of_ne_stuck (Term.Numeral n) t (by intro h; cases h)
    hTNotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (ubvToIntTerm (intToBvTerm (Term.Numeral n) t))
    (modTotalTerm t (Term.Numeral n))
    (by rw [hLhsTy, hRhsTy])
    (by rw [hLhsTy]; decide)

private theorem eval_ubv_int_to_bv_matches_mod_pow2
    (M : SmtModel) (hM : model_wf M) (n : native_Int) (t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    __eo_typeof t = Term.UOp UserOp.Int ->
    __smtx_model_eval M
        (__eo_to_smt (ubvToIntTerm (intToBvTerm (Term.Numeral n) t))) =
      __smtx_model_eval M (__eo_to_smt (modTotalTerm t (Term.Numeral n))) := by
  intro hTTrans hTType
  have hTSmtTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    smtx_typeof_of_eo_int t hTTrans hTType
  have hEvalTTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Int :=
    smt_model_eval_preserves_type M hM (__eo_to_smt t) SmtType.Int hTSmtTy
      (by simp) type_inhabited_int
  rcases int_value_canonical hEvalTTy with ⟨ti, hEvalT⟩
  have hEvalN :
      __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
    rw [__smtx_model_eval.eq_2]
  change __smtx_model_eval M
      (SmtTerm.ubv_to_int (SmtTerm.int_to_bv (SmtTerm.Numeral n) (__eo_to_smt t))) =
    __smtx_model_eval M
      (SmtTerm.mod_total (__eo_to_smt t) (SmtTerm.int_pow2 (SmtTerm.Numeral n)))
  rw [smtx_eval_ubv_to_int_term_eq, smtx_eval_int_to_bv_term_eq,
    smtx_eval_mod_total_term_eq, smtx_eval_int_pow2_term_eq, hEvalT, hEvalN]
  simp [__smtx_model_eval_int_to_bv, __smtx_model_eval_ubv_to_int,
    __smtx_model_eval_mod_total, __smtx_model_eval_int_pow2]

private theorem facts___eo_prog_uf_int2bv_bv2nat_impl
    (M : SmtModel) (hM : model_wf M) (w t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    __eo_typeof (__eo_prog_uf_int2bv_bv2nat w t) = Term.Bool ->
    eo_interprets M (__eo_prog_uf_int2bv_bv2nat w t) true := by
  intro hTTrans hResultTy
  rcases typeof_args_of_prog_uf_int2bv_bv2nat_bool w t hResultTy with
    ⟨n, hW, _hNonneg, hTType⟩
  subst w
  have hTNotStuck : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hProgBool :
      RuleProofs.eo_has_bool_type (__eo_prog_uf_int2bv_bv2nat (Term.Numeral n) t) :=
    typed___eo_prog_uf_int2bv_bv2nat_impl (Term.Numeral n) t hTTrans hResultTy
  rw [prog_uf_int2bv_bv2nat_eq_of_ne_stuck (Term.Numeral n) t (by intro h; cases h)
    hTNotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_uf_int2bv_bv2nat_eq_of_ne_stuck (Term.Numeral n) t
      (by intro h; cases h) hTNotStuck] using hProgBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (ubvToIntTerm (intToBvTerm (Term.Numeral n) t))))
      (__smtx_model_eval M (__eo_to_smt (modTotalTerm t (Term.Numeral n))))
    rw [eval_ubv_int_to_bv_matches_mod_pow2 M hM n t hTTrans hTType]
    exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_uf_int2bv_bv2nat_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.uf_int2bv_bv2nat args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.uf_int2bv_bv2nat args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.uf_int2bv_bv2nat args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.uf_int2bv_bv2nat args premises ≠ Term.Stuck :=
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
                  have hATransPair :
                      RuleProofs.eo_has_smt_translation a1 ∧
                        RuleProofs.eo_has_smt_translation a2 ∧ True := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := hATransPair.2.1
                  change __eo_typeof (__eo_prog_uf_int2bv_bv2nat a1 a2) =
                    Term.Bool at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_uf_int2bv_bv2nat a1 a2) true
                    exact facts___eo_prog_uf_int2bv_bv2nat_impl M hM a1 a2
                      hA2Trans hResultTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_uf_int2bv_bv2nat_impl a1 a2 hA2Trans
                        hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
