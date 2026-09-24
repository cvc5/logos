module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ArithIntGeqTighten

private abbrev toRealTerm (t : Term) : Term :=
  Term.Apply (Term.UOp UserOp.to_real) t

private abbrev toIntTerm (t : Term) : Term :=
  Term.Apply (Term.UOp UserOp.to_int) t

private abbrev eqTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

private abbrev plusTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.plus) x) y

private abbrev geqTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) y

private abbrev nonIntPremise (c0 c1 : Term) : Term :=
  eqTerm (eqTerm (toRealTerm (toIntTerm c0)) c1) (Term.Boolean false)

private abbrev ccRhs (c : Term) : Term :=
  plusTerm (toIntTerm c) (plusTerm (Term.Numeral 1) (Term.Numeral 0))

private abbrev ccPremise (cc c : Term) : Term :=
  eqTerm cc (ccRhs c)

private abbrev conclusionTerm (t c cc : Term) : Term :=
  eqTerm (geqTerm (toRealTerm t) c) (geqTerm t cc)

private theorem eo_to_smt_to_real_eq (x : Term) :
    __eo_to_smt (toRealTerm x) = SmtTerm.to_real (__eo_to_smt x) := by
  rfl

private theorem eo_to_smt_to_int_eq (x : Term) :
    __eo_to_smt (toIntTerm x) = SmtTerm.to_int (__eo_to_smt x) := by
  rfl

private theorem smtx_eval_plus_term_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.plus x y) =
      __smtx_model_eval_plus
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_geq_term_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.geq x y) =
      __smtx_model_eval_geq
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_typeof_of_eo_type
    (a T : Term) (S : SmtType)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = T)
    (hSTy : __eo_to_smt_type T = S) :
    __smtx_typeof (__eo_to_smt a) = S := by
  exact (TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
    a T (__eo_to_smt a) rfl hTrans hTy).trans hSTy

private theorem native_to_real_eq_intCast (n : native_Int) :
    native_to_real n = (n : Rat) := by
  rw [native_to_real, native_mk_rational]
  change (n : Rat) / (1 : Rat) = (n : Rat)
  change (n : Rat) * ((1 : Rat)⁻¹) = (n : Rat)
  rw [Rat.inv_def]
  change (n : Rat) * Rat.divInt 1 1 = (n : Rat)
  rw [show Rat.divInt 1 1 = (1 : Rat) by rfl]
  exact Rat.mul_one _

private theorem rat_le_int_iff_floor_add_one_le_of_nonint
    (q : Rat) (n : Int)
    (hNonInt : native_to_real (native_to_int q) ≠ q) :
    q ≤ native_to_real n ↔ native_to_int q + 1 ≤ n := by
  have hNonInt' : (q.floor : Rat) ≠ q := by
    simpa [native_to_int, native_to_real_eq_intCast] using hNonInt
  rw [native_to_real_eq_intCast n]
  change q ≤ (n : Rat) ↔ native_to_int q + 1 ≤ n
  rw [native_to_int]
  constructor
  · intro hqle
    have hqNe : q ≠ (n : Rat) := by
      intro hqEq
      have hFloorEq : (q.floor : Rat) = q := by
        rw [hqEq, Rat.floor_intCast]
      exact hNonInt' hFloorEq
    have hqLt : q < (n : Rat) := Rat.lt_of_le_of_ne hqle hqNe
    exact (Int.add_one_le_iff).mpr ((Rat.floor_lt_iff).mpr hqLt)
  · intro hle
    exact Rat.le_trans (Rat.le_of_lt (Rat.lt_floor_add_one q))
      ((Rat.intCast_le_intCast).mpr hle)

private theorem native_qleq_to_real_eq_floor_add_one
    (q : Rat) (n : Int)
    (hNonInt : native_to_real (native_to_int q) ≠ q) :
    native_qleq q (native_to_real n) =
      native_zleq (native_to_int q + 1) n := by
  unfold native_qleq native_zleq
  change decide (q ≤ native_to_real n) =
    decide (native_to_int q + 1 ≤ n)
  have hIff := rat_le_int_iff_floor_add_one_le_of_nonint q n hNonInt
  by_cases hL : q ≤ native_to_real n
  · have hR : native_to_int q + 1 ≤ n := hIff.mp hL
    simp [hL, hR]
  · have hR : ¬ native_to_int q + 1 ≤ n := by
      intro h
      exact hL (hIff.mpr h)
    simp [hL, hR]

private theorem requires_guard_true_of_not_stuck (A B : Term) :
    __eo_requires A (Term.Boolean true) B ≠ Term.Stuck ->
    A = Term.Boolean true := by
  intro h
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at h
  exact h.1

private theorem eo_and_eq_true (A B : Term) :
    __eo_and A B = Term.Boolean true ->
    A = Term.Boolean true ∧ B = Term.Boolean true := by
  intro h
  cases A <;> cases B <;>
    simp [__eo_and, __eo_requires, __eo_eq, native_and, native_ite,
      native_teq, native_not, SmtEval.native_not] at h ⊢
  · exact h
  · split at h <;> cases h

private theorem eqs_of_eo_and4_eq_true
    (x1 y1 x2 y2 x3 y3 x4 y4 : Term)
    (h : __eo_and
        (__eo_and (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
          (__eo_eq x3 y3))
        (__eo_eq x4 y4) = Term.Boolean true) :
    y1 = x1 ∧ y2 = x2 ∧ y3 = x3 ∧ y4 = x4 := by
  rcases eo_and_eq_true _ _ h with ⟨h123, h4⟩
  rcases eo_and_eq_true _ _ h123 with ⟨h12, h3⟩
  rcases eo_and_eq_true _ _ h12 with ⟨h1, h2⟩
  exact ⟨RuleProofs.eq_of_eo_eq_true x1 y1 h1,
    RuleProofs.eq_of_eo_eq_true x2 y2 h2,
    RuleProofs.eq_of_eo_eq_true x3 y3 h3,
    RuleProofs.eq_of_eo_eq_true x4 y4 h4⟩

private theorem prog_arith_int_geq_tighten_info
    (t c cc P1 P2 : Term)
    (hProg :
      __eo_prog_arith_int_geq_tighten t c cc
        (Proof.pf P1) (Proof.pf P2) ≠ Term.Stuck) :
    ∃ c0 c1 cc0 c2,
      P1 = nonIntPremise c0 c1 ∧ P2 = ccPremise cc0 c2 ∧
      c0 = c ∧ c1 = c ∧ cc0 = cc ∧ c2 = c ∧
      __eo_prog_arith_int_geq_tighten t c cc
        (Proof.pf P1) (Proof.pf P2) = conclusionTerm t c cc := by
  unfold __eo_prog_arith_int_geq_tighten at hProg
  split at hProg <;> try contradiction
  next h1 h2 h3 heq1 heq2 =>
    rename_i tArg cArg ccArg _ _ _ _ _ c0 c1 cc0 c2
    injection heq1 with hP1Eq
    injection heq2 with hP2Eq
    have hGuard := requires_guard_true_of_not_stuck _ _ hProg
    rcases eqs_of_eo_and4_eq_true cArg c0 cArg c1 ccArg cc0 cArg c2 hGuard with
      ⟨hc0, hc1, hcc0, hc2⟩
    refine ⟨c0, c1, cc0, c2, ?_, ?_, hc0, hc1, hcc0, hc2,
      ?_⟩
    · simpa [nonIntPremise, eqTerm, toRealTerm, toIntTerm] using hP1Eq
    · simpa [ccPremise, ccRhs, eqTerm, plusTerm, toIntTerm] using hP2Eq
    · rw [hP1Eq, hP2Eq, hc0, hc1, hcc0, hc2]
      simp [__eo_prog_arith_int_geq_tighten, __eo_requires, __eo_and,
        __eo_eq, native_ite, native_teq, native_not, SmtEval.native_not,
        native_and, conclusionTerm, geqTerm, toRealTerm, eqTerm]

/-- Since `to_real` accepts `Int` only, a well-typed conclusion forces `t : Int`. -/
private theorem eo_typeof_int_of_to_real_ne_stuck {A : Term}
    (h : __eo_typeof_to_real A ≠ Term.Stuck) :
    A = Term.Int := by
  cases A <;> simp [__eo_typeof_to_real] at h ⊢
  case UOp op =>
    cases op <;> simp [__eo_typeof_to_real] at h ⊢

/-- Recovers the argument types of the conclusion from its `Bool` type.

    `to_real t` forces `t : Int`; the `geq` against `c` then forces `c : Real`,
    and the `geq` of `t` against `cc` forces `cc : Int`. -/
private theorem arg_types_of_result_bool
    (t c cc : Term)
    (hTy : __eo_typeof (conclusionTerm t c cc) = Term.Bool) :
    __eo_typeof t = Term.Int ∧ __eo_typeof c = Term.Real ∧
      __eo_typeof cc = Term.Int := by
  change __eo_typeof_eq
      (__eo_typeof_lt (__eo_typeof_to_real (__eo_typeof t)) (__eo_typeof c))
      (__eo_typeof_lt (__eo_typeof t) (__eo_typeof cc)) = Term.Bool at hTy
  have hTInt : __eo_typeof t = Term.Int := by
    refine eo_typeof_int_of_to_real_ne_stuck ?_
    intro hSt
    rw [hSt] at hTy
    simp [__eo_typeof_lt, __eo_typeof_eq] at hTy
  rw [hTInt] at hTy
  have hCReal : __eo_typeof c = Term.Real := by
    cases hc : __eo_typeof c with
    | UOp op =>
        cases op <;> simp [__eo_typeof_eq, __eo_typeof_lt, __eo_typeof_to_real,
          __eo_requires, __is_arith_type, __eo_eq, native_ite, native_teq,
          native_not, SmtEval.native_not, hc] at hTy ⊢
    | _ =>
        simp [__eo_typeof_eq, __eo_typeof_lt, __eo_typeof_to_real,
          __eo_requires, __is_arith_type, __eo_eq, native_ite, native_teq,
          native_not, SmtEval.native_not, hc] at hTy
  rw [hCReal] at hTy
  refine ⟨hTInt, hCReal, ?_⟩
  cases hcc : __eo_typeof cc with
  | UOp op =>
      cases op <;> simp [__eo_typeof_eq, __eo_typeof_lt, __eo_typeof_to_real,
        __eo_requires, __is_arith_type, __eo_eq, native_ite, native_teq,
        native_not, SmtEval.native_not, hcc] at hTy ⊢
  | _ =>
      simp [__eo_typeof_eq, __eo_typeof_lt, __eo_typeof_to_real,
        __eo_requires, __is_arith_type, __eo_eq, native_ite, native_teq,
        native_not, SmtEval.native_not, hcc] at hTy

private theorem geq_to_real_ty
    (t c : Term)
    (hTSmtTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int)
    (hCSmtTy : __smtx_typeof (__eo_to_smt c) = SmtType.Real) :
    __smtx_typeof (__eo_to_smt (geqTerm (toRealTerm t) c)) = SmtType.Bool := by
  change __smtx_typeof
      (SmtTerm.geq (SmtTerm.to_real (__eo_to_smt t)) (__eo_to_smt c)) =
    SmtType.Bool
  rw [typeof_geq_eq, typeof_to_real_eq]
  simp [__smtx_typeof_arith_overload_op_2_ret, native_ite, native_Teq,
    hTSmtTy, hCSmtTy]

private theorem geq_int_ty
    (t cc : Term)
    (hTSmtTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int)
    (hCCSmtTy : __smtx_typeof (__eo_to_smt cc) = SmtType.Int) :
    __smtx_typeof (__eo_to_smt (geqTerm t cc)) = SmtType.Bool := by
  change __smtx_typeof (SmtTerm.geq (__eo_to_smt t) (__eo_to_smt cc)) =
    SmtType.Bool
  rw [typeof_geq_eq]
  simp [__smtx_typeof_arith_overload_op_2_ret, native_ite, native_Teq,
    hTSmtTy, hCCSmtTy]

private theorem typed___eo_prog_arith_int_geq_tighten_impl
    (t c cc P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation t ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation cc ->
    __eo_typeof t = Term.Int ->
    __eo_typeof c = Term.Real ->
    __eo_typeof cc = Term.Int ->
    __eo_prog_arith_int_geq_tighten t c cc (Proof.pf P1) (Proof.pf P2) =
      conclusionTerm t c cc ->
    RuleProofs.eo_has_bool_type
      (__eo_prog_arith_int_geq_tighten t c cc (Proof.pf P1) (Proof.pf P2)) := by
  intro hTTrans hCTrans hCCTrans hTInt hCReal hCCInt hProgEq
  have hTSmtTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    smtx_typeof_of_eo_type t Term.Int SmtType.Int hTTrans hTInt rfl
  have hCSmtTy : __smtx_typeof (__eo_to_smt c) = SmtType.Real :=
    smtx_typeof_of_eo_type c Term.Real SmtType.Real hCTrans hCReal rfl
  have hCCSmtTy : __smtx_typeof (__eo_to_smt cc) = SmtType.Int :=
    smtx_typeof_of_eo_type cc Term.Int SmtType.Int hCCTrans hCCInt rfl
  have hLhsTy :
      __smtx_typeof (__eo_to_smt (geqTerm (toRealTerm t) c)) =
        SmtType.Bool :=
    geq_to_real_ty t c hTSmtTy hCSmtTy
  have hRhsTy :
      __smtx_typeof (__eo_to_smt (geqTerm t cc)) = SmtType.Bool :=
    geq_int_ty t cc hTSmtTy hCCSmtTy
  have hLhsTrans :
      RuleProofs.eo_has_smt_translation (geqTerm (toRealTerm t) c) := by
    simp [RuleProofs.eo_has_smt_translation, hLhsTy]
  rw [hProgEq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (geqTerm (toRealTerm t) c) (geqTerm t cc)
    (by rw [hLhsTy, hRhsTy]) hLhsTrans

private theorem facts___eo_prog_arith_int_geq_tighten_impl
    (M : SmtModel) (hM : model_wf M) (t c cc P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation t ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation cc ->
    __eo_typeof t = Term.Int ->
    __eo_typeof c = Term.Real ->
    __eo_typeof cc = Term.Int ->
    __eo_prog_arith_int_geq_tighten t c cc (Proof.pf P1) (Proof.pf P2) =
      conclusionTerm t c cc ->
    eo_interprets M (nonIntPremise c c) true ->
    eo_interprets M (ccPremise cc c) true ->
    eo_interprets M
      (__eo_prog_arith_int_geq_tighten t c cc (Proof.pf P1) (Proof.pf P2))
      true := by
  intro hTTrans hCTrans hCCTrans hTInt hCReal hCCInt hProgEq hPremNonInt hPremCc
  have hProgBool :
      RuleProofs.eo_has_bool_type
        (__eo_prog_arith_int_geq_tighten t c cc (Proof.pf P1) (Proof.pf P2)) :=
    typed___eo_prog_arith_int_geq_tighten_impl t c cc P1 P2
      hTTrans hCTrans hCCTrans hTInt hCReal hCCInt hProgEq
  have hProgBool' : RuleProofs.eo_has_bool_type (conclusionTerm t c cc) := by
    simpa [hProgEq] using hProgBool
  have hTSmtTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    smtx_typeof_of_eo_type t Term.Int SmtType.Int hTTrans hTInt rfl
  have hCSmtTy : __smtx_typeof (__eo_to_smt c) = SmtType.Real :=
    smtx_typeof_of_eo_type c Term.Real SmtType.Real hCTrans hCReal rfl
  have hCCSmtTy : __smtx_typeof (__eo_to_smt cc) = SmtType.Int :=
    smtx_typeof_of_eo_type cc Term.Int SmtType.Int hCCTrans hCCInt rfl
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
  have hCCEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt cc)) =
        SmtType.Int :=
    smt_model_eval_preserves_type M hM (__eo_to_smt cc) SmtType.Int hCCSmtTy
      (by simp) type_inhabited_int
  rcases int_value_canonical hTEvalTy with ⟨ti, hTEval⟩
  rcases real_value_canonical hCEvalTy with ⟨cq, hCEval⟩
  rcases int_value_canonical hCCEvalTy with ⟨cci, hCCEval⟩
  have hPremFalse :
      __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt (toRealTerm (toIntTerm c))))
        (__smtx_model_eval M (__eo_to_smt c)) = SmtValue.Boolean false :=
    RuleProofs.model_eval_eq_false_of_eq_false_eq_true M
      (toRealTerm (toIntTerm c)) c hPremNonInt
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
  have hEvalCcRhs :
      __smtx_model_eval M (__eo_to_smt (ccRhs c)) =
        SmtValue.Numeral (native_to_int cq + 1) := by
    change __smtx_model_eval M
        (SmtTerm.plus (SmtTerm.to_int (__eo_to_smt c))
          (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0))) =
      SmtValue.Numeral (native_to_int cq + 1)
    rw [smtx_eval_plus_term_eq, smtx_eval_to_int_term_eq,
      smtx_eval_plus_term_eq, hCEval]
    simp [__smtx_model_eval_to_int, __smtx_model_eval_plus,
      __smtx_model_eval.eq_2, native_zplus]
  have hRelCc := RuleProofs.eo_interprets_eq_rel M cc (ccRhs c) hPremCc
  have hCcEq : cci = native_to_int cq + 1 := by
    unfold RuleProofs.smt_value_rel at hRelCc
    rw [hCCEval, hEvalCcRhs] at hRelCc
    simpa [__smtx_model_eval_eq, native_veq, native_zeq] using hRelCc
  have hEvalLhs :
      __smtx_model_eval M (__eo_to_smt (geqTerm (toRealTerm t) c)) =
        SmtValue.Boolean (native_qleq cq (native_to_real ti)) := by
    change __smtx_model_eval M
        (SmtTerm.geq (SmtTerm.to_real (__eo_to_smt t)) (__eo_to_smt c)) =
      SmtValue.Boolean (native_qleq cq (native_to_real ti))
    rw [smtx_eval_geq_term_eq, smtx_eval_to_real_term_eq, hTEval, hCEval]
    simp [__smtx_model_eval_to_real, __smtx_model_eval_geq,
      __smtx_model_eval_leq]
  have hEvalRhs :
      __smtx_model_eval M (__eo_to_smt (geqTerm t cc)) =
        SmtValue.Boolean (native_zleq cci ti) := by
    change __smtx_model_eval M
        (SmtTerm.geq (__eo_to_smt t) (__eo_to_smt cc)) =
      SmtValue.Boolean (native_zleq cci ti)
    rw [smtx_eval_geq_term_eq, hTEval, hCCEval]
    simp [__smtx_model_eval_geq, __smtx_model_eval_leq]
  have hBoolEq :
      native_qleq cq (native_to_real ti) = native_zleq cci ti := by
    rw [hCcEq]
    exact native_qleq_to_real_eq_floor_add_one cq ti hCNonInt
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M
    (geqTerm (toRealTerm t) c) (geqTerm t cc) hProgBool' <| by
      rw [hEvalLhs, hEvalRhs, hBoolEq]
      exact RuleProofs.smt_value_rel_refl
        (SmtValue.Boolean (native_zleq cci ti))

end ArithIntGeqTighten

open ArithIntGeqTighten

public theorem cmd_step_arith_int_geq_tighten_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_int_geq_tighten args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_int_geq_tighten args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_int_geq_tighten args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.arith_int_geq_tighten args premises ≠
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
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | nil =>
                  cases premises with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons p1 premises =>
                      cases premises with
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons p2 premises =>
                          cases premises with
                          | cons _ _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | nil =>
                              let T1 := a1
                              let C1 := a2
                              let CC1 := a3
                              let P1 := __eo_state_proven_nth s p1
                              let P2 := __eo_state_proven_nth s p2
                              have hArgsTrans :
                                  RuleProofs.eo_has_smt_translation T1 ∧
                                    (RuleProofs.eo_has_smt_translation C1 ∧
                                      (RuleProofs.eo_has_smt_translation CC1 ∧
                                        True)) := by
                                simpa [cmdTranslationOk, cArgListTranslationOk,
                                  RuleProofs.eo_has_smt_translation,
                                  eoHasSmtTranslation] using hCmdTrans
                              have hTTrans :
                                  RuleProofs.eo_has_smt_translation T1 :=
                                hArgsTrans.1
                              have hCTrans :
                                  RuleProofs.eo_has_smt_translation C1 :=
                                hArgsTrans.2.1
                              have hCCTrans :
                                  RuleProofs.eo_has_smt_translation CC1 :=
                                hArgsTrans.2.2.1
                              change __eo_typeof
                                (__eo_prog_arith_int_geq_tighten T1 C1 CC1
                                  (Proof.pf P1) (Proof.pf P2)) = Term.Bool at hResultTy
                              change __eo_prog_arith_int_geq_tighten T1 C1 CC1
                                (Proof.pf P1) (Proof.pf P2) ≠ Term.Stuck at hProg
                              rcases prog_arith_int_geq_tighten_info
                                  T1 C1 CC1 P1 P2 hProg with
                                ⟨C0, C2, CC0, C3, hP1Eq, hP2Eq, hC0Eq,
                                  hC2Eq, hCC0Eq, hC3Eq, hProgEq⟩
                              have hResultTy' :
                                  __eo_typeof (conclusionTerm T1 C1 CC1) =
                                    Term.Bool := by
                                simpa [hProgEq] using hResultTy
                              obtain ⟨hTInt, hCReal, hCCInt⟩ :=
                                arg_types_of_result_bool T1 C1 CC1 hResultTy'
                              refine ⟨?_, ?_⟩
                              · intro hPremTrue
                                change eo_interprets M
                                  (__eo_prog_arith_int_geq_tighten T1 C1 CC1
                                    (Proof.pf P1) (Proof.pf P2)) true
                                have hPremNonInt :
                                    eo_interprets M (nonIntPremise C1 C1) true := by
                                  have hP1True : eo_interprets M P1 true :=
                                    hPremTrue P1 (by simp [premiseTermList, P1, P2])
                                  rw [hP1Eq, hC0Eq, hC2Eq] at hP1True
                                  exact hP1True
                                have hPremCc :
                                    eo_interprets M (ccPremise CC1 C1) true := by
                                  have hP2True : eo_interprets M P2 true :=
                                    hPremTrue P2 (by simp [premiseTermList, P1, P2])
                                  rw [hP2Eq, hCC0Eq, hC3Eq] at hP2True
                                  exact hP2True
                                exact facts___eo_prog_arith_int_geq_tighten_impl
                                  M hM T1 C1 CC1 P1 P2
                                  hTTrans hCTrans hCCTrans hTInt hCReal
                                  hCCInt hProgEq hPremNonInt hPremCc
                              · change RuleProofs.eo_has_smt_translation
                                  (__eo_prog_arith_int_geq_tighten T1 C1 CC1
                                    (Proof.pf P1) (Proof.pf P2))
                                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                                  (__eo_prog_arith_int_geq_tighten T1 C1 CC1
                                    (Proof.pf P1) (Proof.pf P2))
                                  (typed___eo_prog_arith_int_geq_tighten_impl
                                    T1 C1 CC1 P1 P2
                                    hTTrans hCTrans hCCTrans hTInt hCReal
                                    hCCInt hProgEq)
