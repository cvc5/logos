module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.TypeInversionSupport
import all Cpc.Proofs.RuleSupport.TypeInversionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private def bvRedorElimBody (x w : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (Term.Apply (Term.UOp UserOp.bvredor) x))
    (Term.Apply (Term.UOp UserOp.bvnot)
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x)
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))))

private theorem bv_redor_eliminate_shape_of_ne_stuck (x w P : Term) :
    __eo_prog_bv_redor_eliminate x w (Proof.pf P) ≠ Term.Stuck ->
    x ≠ Term.Stuck ∧ w ≠ Term.Stuck ∧
    ∃ pw px,
      P = Term.Apply (Term.Apply (Term.UOp UserOp.eq) pw)
            (Term.Apply (Term.UOp UserOp._at_bvsize) px) := by
  intro hProg
  have hx : x ≠ Term.Stuck := by
    intro hx
    subst x
    exact hProg (__eo_prog_bv_redor_eliminate.eq_1 w (Proof.pf P))
  have hw : w ≠ Term.Stuck := by
    intro hw
    subst w
    exact hProg (__eo_prog_bv_redor_eliminate.eq_2 x (Proof.pf P) hx)
  refine ⟨hx, hw, ?_⟩
  by_cases hShape : ∃ pw px,
      P = Term.Apply (Term.Apply (Term.UOp UserOp.eq) pw)
            (Term.Apply (Term.UOp UserOp._at_bvsize) px)
  · exact hShape
  · exact False.elim (hProg
      (__eo_prog_bv_redor_eliminate.eq_4 x w (Proof.pf P) hx hw (by
        intro pw px hP
        cases hP
        exact hShape ⟨pw, px, rfl⟩)))

private theorem bv_redor_eliminate_guard_eqs_of_ne_stuck
    {x w pw px body : Term} :
    __eo_requires (__eo_and (__eo_eq w pw) (__eo_eq x px))
        (Term.Boolean true) body ≠ Term.Stuck ->
    pw = w ∧ px = x := by
  exact RuleProofs.eqs_of_requires_and_eq_true_not_stuck w x pw px body

private theorem prog_bv_redor_eliminate_canonical_eq_of_ne_stuck (x w : Term) :
    x ≠ Term.Stuck ->
    w ≠ Term.Stuck ->
    __eo_prog_bv_redor_eliminate x w
        (Proof.pf (Term.Apply (Term.Apply (Term.UOp UserOp.eq) w)
          (Term.Apply (Term.UOp UserOp._at_bvsize) x))) =
      bvRedorElimBody x w := by
  intro hx hw
  rw [__eo_prog_bv_redor_eliminate.eq_3 x w w x hx hw]
  rw [RuleProofs.eo_eq_self_of_ne_stuck w hw,
    RuleProofs.eo_eq_self_of_ne_stuck x hx]
  simp [bvRedorElimBody, __eo_and, __eo_requires, native_ite, native_teq,
    native_and, native_not, SmtEval.native_not]

private theorem width_eq_of_typeof_at_bv_eq_bitvec
    (w u : Term) :
    w ≠ Term.Stuck ->
    __eo_typeof_int_to_bv (__eo_typeof w) w (Term.UOp UserOp.Int) =
      Term.Apply (Term.UOp UserOp.BitVec) u ->
    w = u := by
  intro hW hTy
  cases hWTy : __eo_typeof w with
  | UOp op =>
      cases op
      case Int =>
        simp [__eo_typeof_int_to_bv, hW, hWTy] at hTy
        have hReqNN :
            __eo_requires (__eo_gt w (Term.Numeral (-1 : native_Int)))
                (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) w) ≠
              Term.Stuck := by
          rw [hTy]
          intro h
          cases h
        have hGuard :=
          support_eo_requires_cond_eq_of_non_stuck hReqNN
        have hReqEq :
            __eo_requires (__eo_gt w (Term.Numeral (-1 : native_Int)))
                (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) w) =
              Term.Apply (Term.UOp UserOp.BitVec) w := by
          simp [__eo_requires, hGuard, native_ite, native_teq, native_not]
        rw [hReqEq] at hTy
        cases hTy
        rfl
      all_goals
        simp [__eo_typeof_int_to_bv, hW, hWTy] at hTy
  | _ =>
      simp [__eo_typeof_int_to_bv, hWTy] at hTy

private theorem typeof_args_of_redor_body_bool (x w : Term) :
    w ≠ Term.Stuck ->
    __eo_typeof (bvRedorElimBody x w) = Term.Bool ->
    ∃ u, __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) u ∧
      w = u := by
  intro hW hTy
  change __eo_typeof_eq
      (__eo_typeof_bvredand (__eo_typeof x))
      (__eo_typeof_bvnot
        (__eo_typeof_bvcomp (__eo_typeof x)
          (__eo_typeof_int_to_bv (__eo_typeof w) w (Term.UOp UserOp.Int)))) =
    Term.Bool at hTy
  have hOperandsNN :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof_bvredand (__eo_typeof x))
      (__eo_typeof_bvnot
        (__eo_typeof_bvcomp (__eo_typeof x)
          (__eo_typeof_int_to_bv (__eo_typeof w) w (Term.UOp UserOp.Int))))
      hTy
  rcases RuleProofs.eo_typeof_bvredand_arg_bitvec_of_ne_stuck _ hOperandsNN.1 with
    ⟨u, hXTy⟩
  rcases RuleProofs.eo_typeof_bvnot_arg_bitvec_of_ne_stuck _ hOperandsNN.2 with
    ⟨_one, hCompTy⟩
  have hCompNN :
      __eo_typeof_bvcomp (__eo_typeof x)
          (__eo_typeof_int_to_bv (__eo_typeof w) w (Term.UOp UserOp.Int)) ≠
        Term.Stuck := by
    rw [hCompTy]
    intro h
    cases h
  rcases RuleProofs.eo_typeof_bvcomp_args_of_ne_stuck _ _ hCompNN with
    ⟨v, hXTy', hAtTy⟩
  rw [hXTy] at hXTy'
  injection hXTy' with _ hVU
  subst v
  have hWU : w = u :=
    width_eq_of_typeof_at_bv_eq_bitvec w u hW hAtTy
  exact ⟨u, hXTy, hWU⟩

private theorem smt_bitvec_type_of_eo_bitvec_type_with_width
    (x w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w ->
    ∃ n, w = Term.Numeral n ∧ native_zleq 0 n = true ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) := by
  intro hXTrans hXType
  have hSmtType :
      __smtx_typeof (__eo_to_smt x) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x (Term.Apply (Term.UOp UserOp.BitVec) w) (__eo_to_smt x) rfl
      hXTrans hXType
  cases w <;> simp [__eo_to_smt_type] at hSmtType
  case Numeral n =>
    cases hNonneg : native_zleq 0 n <;> simp [__eo_to_smt_type, hNonneg] at hSmtType
    · exact False.elim (hXTrans hSmtType)
    · exact ⟨n, rfl, hNonneg, hSmtType⟩
  all_goals
    exact False.elim (hXTrans hSmtType)

private theorem native_nat_to_int_of_int_to_nat_of_nonneg (n : native_Int) :
    native_zleq 0 n = true ->
    native_nat_to_int (native_int_to_nat n) = n := by
  intro hNonneg
  have hn : 0 <= n := by
    simpa [SmtEval.native_zleq] using hNonneg
  have hInt : (Int.ofNat (Int.toNat n) : Int) = n :=
    Int.toNat_of_nonneg hn
  simpa [Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
    native_nat_to_int, native_int_to_nat] using hInt

private theorem native_mod_total_zero_pow2_of_nonneg (n : native_Int) :
    native_zleq 0 n = true ->
    native_mod_total 0 (native_int_pow2 n) = 0 := by
  intro hNonneg
  have hn : 0 <= n := by
    simpa [SmtEval.native_zleq] using hNonneg
  have hPowPos : 0 < native_int_pow2 n := by
    have hnot : ¬ n < 0 := Int.not_lt_of_ge hn
    rw [native_int_pow2, native_zexp_total]
    simp [hnot]
    exact Int.pow_pos (by decide : (0 : Int) < 2)
  simpa [SmtEval.native_mod_total] using
    Int.emod_eq_of_lt (by decide : (0 : Int) <= 0) hPowPos

private theorem smt_typeof_binary_nat_to_int_zero_local (w : native_Nat) :
    __smtx_typeof (SmtTerm.Binary (native_nat_to_int w) 0) =
      SmtType.BitVec w := by
  have hWidth : native_zleq 0 (native_nat_to_int w) = true := by
    simp [SmtEval.native_zleq, Smtm.native_nat_to_int]
  have hPowPos : 0 < native_int_pow2 (native_nat_to_int w) := by
    have hNonneg : 0 <= native_nat_to_int w := by
      simp [Smtm.native_nat_to_int]
    have hnot : ¬ native_nat_to_int w < 0 := Int.not_lt_of_ge hNonneg
    simp [SmtEval.native_int_pow2, SmtEval.native_zexp_total, hnot]
    exact Int.pow_pos (by decide : (0 : Int) < 2)
  have hMod0 :
      native_mod_total 0 (native_int_pow2 (native_nat_to_int w)) = 0 := by
    simp [SmtEval.native_mod_total]
  have hMod :
      native_zeq 0
          (native_mod_total 0 (native_int_pow2 (native_nat_to_int w))) =
        true := by
    simp [SmtEval.native_zeq, hMod0]
  have hNN :
      __smtx_typeof (SmtTerm.Binary (native_nat_to_int w) 0) ≠
        SmtType.None := by
    unfold __smtx_typeof
    simp [SmtEval.native_and, hWidth, hMod, native_ite]
  simpa [SmtEval.native_int_to_nat, Smtm.native_nat_to_int] using
    TranslationProofs.smtx_typeof_binary_of_non_none
      (native_nat_to_int w) 0 hNN

private theorem smt_typeof_redor_rhs
    (x : Term) (n : native_Int) :
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.bvnot)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n))
                (Term.Numeral 0))))) =
      SmtType.BitVec 1 := by
  intro hNonneg hXSmtTy
  change __smtx_typeof
      (SmtTerm.bvnot
        (SmtTerm.bvcomp (__eo_to_smt x)
          (SmtTerm.int_to_bv (SmtTerm.Numeral n) (SmtTerm.Numeral 0)))) =
    SmtType.BitVec 1
  rw [smtx_typeof_bvnot_term_eq]
  rw [smtx_typeof_bvcomp_term_eq, hXSmtTy]
  rw [smtx_typeof_int_to_bv_numerals n 0 hNonneg]
  simp [__smtx_typeof_bv_op_1, __smtx_typeof_bv_op_2_ret,
    Smtm.native_nateq, native_ite]

private theorem smt_eval_redor_rhs_eq_lhs
    (M : SmtModel) (x : Term) (n : native_Int) :
    native_zleq 0 n = true ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.bvnot)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n))
                (Term.Numeral 0))))) =
      __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvredor) x)) := by
  intro hNonneg hXSmtTy
  change __smtx_model_eval M
      (SmtTerm.bvnot
        (SmtTerm.bvcomp (__eo_to_smt x)
          (SmtTerm.int_to_bv (SmtTerm.Numeral n) (SmtTerm.Numeral 0)))) =
    __smtx_model_eval M
      (SmtTerm.bvnot
        (SmtTerm.bvcomp (__eo_to_smt x)
          (SmtTerm.Binary
            (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))) 0)))
  have hSize :
      __eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)) = n := by
    rw [hXSmtTy]
    exact native_nat_to_int_of_int_to_nat_of_nonneg n hNonneg
  have hMod0 :
      native_mod_total 0 (native_int_pow2 n) = 0 :=
    native_mod_total_zero_pow2_of_nonneg n hNonneg
  rw [smtx_eval_bvnot_term_eq, smtx_eval_bvnot_term_eq]
  rw [smtx_eval_bvcomp_term_eq, smtx_eval_bvcomp_term_eq]
  rw [smtx_eval_int_to_bv_numerals]
  rw [hSize, hMod0]
  rw [smtx_eval_binary_term_eq]

private theorem smt_typeof_redor_lhs
    (x : Term) (n : native_Int) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvredor) x)) =
      SmtType.BitVec 1 := by
  intro hXSmtTy
  change __smtx_typeof
      (SmtTerm.bvnot
        (SmtTerm.bvcomp (__eo_to_smt x)
          (SmtTerm.Binary
            (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))) 0))) =
    SmtType.BitVec 1
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hXSmtTy]
  change __smtx_typeof_bv_op_1
      (__smtx_typeof_bv_op_2_ret (SmtType.BitVec (native_int_to_nat n))
        (__smtx_typeof (SmtTerm.Binary (native_nat_to_int (native_int_to_nat n)) 0))
        (SmtType.BitVec 1)) =
    SmtType.BitVec 1
  rw [smt_typeof_binary_nat_to_int_zero_local]
  simp [__eo_to_smt_bv_size, __smtx_typeof_bv_op_1,
    __smtx_typeof_bv_op_2_ret, native_nateq, Smtm.native_nateq,
    native_ite]

private theorem typed_redor_body (x w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    w ≠ Term.Stuck ->
    __eo_typeof (bvRedorElimBody x w) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvRedorElimBody x w) := by
  intro hXTrans hW hTy
  rcases typeof_args_of_redor_body_bool x w hW hTy with ⟨u, hXTy, hWU⟩
  subst w
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x u hXTrans hXTy with
    ⟨n, hU, hNonneg, hXSmtTy⟩
  subst u
  unfold RuleProofs.eo_has_bool_type
  unfold bvRedorElimBody
  change __smtx_typeof
      (SmtTerm.eq (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvredor) x))
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.bvnot)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0)))))) =
    SmtType.Bool
  have hLhsTy := smt_typeof_redor_lhs x n hXSmtTy
  have hRhsTy := smt_typeof_redor_rhs x n hNonneg hXSmtTy
  rw [typeof_eq_eq]
  simp [__smtx_typeof_eq, hLhsTy, hRhsTy, __smtx_typeof_guard,
    native_Teq, native_ite]

private theorem facts_redor_body
    (M : SmtModel) (x w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    w ≠ Term.Stuck ->
    __eo_typeof (bvRedorElimBody x w) = Term.Bool ->
    eo_interprets M (bvRedorElimBody x w) true := by
  intro hXTrans hW hTy
  rcases typeof_args_of_redor_body_bool x w hW hTy with ⟨u, hXTy, hWU⟩
  subst w
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x u hXTrans hXTy with
    ⟨n, hU, hNonneg, hXSmtTy⟩
  subst u
  have hBodyBool : RuleProofs.eo_has_bool_type
      (bvRedorElimBody x (Term.Numeral n)) :=
    typed_redor_body x (Term.Numeral n) hXTrans (by intro h; cases h)
      (by simpa using hTy)
  unfold bvRedorElimBody
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvRedorElimBody] using hBodyBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvredor) x)))
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.bvnot)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) x)
              (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral n)) (Term.Numeral 0))))))
    rw [smt_eval_redor_rhs_eq_lhs M x n hNonneg hXSmtTy]
    exact RuleProofs.smt_value_rel_refl _

private theorem trusted_bv_redor_eliminate_canonical_properties
    (M : SmtModel) (x w : Term) :
    cArgListTranslationOk (CArgList.cons x (CArgList.cons w CArgList.nil)) ->
    __eo_typeof
        (__eo_prog_bv_redor_eliminate x w
          (Proof.pf (Term.Apply (Term.Apply (Term.UOp UserOp.eq) w)
            (Term.Apply (Term.UOp UserOp._at_bvsize) x)))) = Term.Bool ->
    StepRuleProperties M
      [Term.Apply (Term.Apply (Term.UOp UserOp.eq) w)
        (Term.Apply (Term.UOp UserOp._at_bvsize) x)]
      (__eo_prog_bv_redor_eliminate x w
        (Proof.pf (Term.Apply (Term.Apply (Term.UOp UserOp.eq) w)
          (Term.Apply (Term.UOp UserOp._at_bvsize) x)))) := by
  intro hArgsTrans hResultTy
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    simpa [cArgListTranslationOk, eoHasSmtTranslation,
      RuleProofs.eo_has_smt_translation] using hArgsTrans.1
  have hWTrans : RuleProofs.eo_has_smt_translation w := by
    simpa [cArgListTranslationOk, eoHasSmtTranslation,
      RuleProofs.eo_has_smt_translation] using hArgsTrans.2.1
  have hxNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hwNe : w ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation w hWTrans
  have hProgEq := prog_bv_redor_eliminate_canonical_eq_of_ne_stuck x w hxNe hwNe
  have hBodyTy : __eo_typeof (bvRedorElimBody x w) = Term.Bool := by
    simpa [hProgEq] using hResultTy
  rw [hProgEq]
  refine ⟨?_, ?_⟩
  · intro _hPrem
    exact facts_redor_body M x w hXTrans hwNe hBodyTy
  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
      (typed_redor_body x w hXTrans hwNe hBodyTy)

public theorem cmd_step_bv_redor_eliminate_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_redor_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_redor_eliminate args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_redor_eliminate args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_redor_eliminate args premises ≠
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
              | cons n1 premises =>
                  cases premises with
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | nil =>
                      let P1 := __eo_state_proven_nth s n1
                      change StepRuleProperties M [P1]
                        (__eo_prog_bv_redor_eliminate a1 a2 (Proof.pf P1))
                      have hProgLocal :
                          __eo_prog_bv_redor_eliminate a1 a2 (Proof.pf P1) ≠
                            Term.Stuck := by
                        exact hProg
                      rcases bv_redor_eliminate_shape_of_ne_stuck a1 a2 P1 hProgLocal with
                        ⟨ha1, ha2, pw, px, hP1⟩
                      subst P1
                      have hReqNe := by
                        have h := hProgLocal
                        rw [hP1] at h
                        rw [__eo_prog_bv_redor_eliminate.eq_3 a1 a2 pw px ha1 ha2] at h
                        exact h
                      rcases bv_redor_eliminate_guard_eqs_of_ne_stuck hReqNe with
                        ⟨hpw, hpx⟩
                      subst pw
                      subst px
                      have hArgsTrans :
                          cArgListTranslationOk
                            (CArgList.cons a1 (CArgList.cons a2 CArgList.nil)) := by
                        simpa [cmdTranslationOk] using hCmdTrans
                      have hResultTyCanonical :
                          __eo_typeof
                              (__eo_prog_bv_redor_eliminate a1 a2
                                (Proof.pf
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a2)
                                    (Term.Apply (Term.UOp UserOp._at_bvsize) a1)))) =
                            Term.Bool := by
                        have h := hResultTy
                        change __eo_typeof
                            (__eo_prog_bv_redor_eliminate a1 a2
                              (Proof.pf (__eo_state_proven_nth s n1))) =
                          Term.Bool at h
                        simpa [hP1] using h
                      simpa [hP1] using
                        trusted_bv_redor_eliminate_canonical_properties M a1 a2
                          hArgsTrans hResultTyCanonical
