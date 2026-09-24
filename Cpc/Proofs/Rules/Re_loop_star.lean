module

public import Cpc.Proofs.RuleSupport.ReConcatStarSupport
import all Cpc.Proofs.RuleSupport.ReConcatStarSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace ReLoopStarProof

/-- The equality conclusion produced by `re_loop_star`. -/
abbrev mkConcl (a1 a2 a3 : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.UOp2 UserOp2.re_loop a1 a2)
        (Term.Apply (Term.UOp UserOp.re_mult) a3)))
    (Term.Apply (Term.UOp UserOp.re_mult) a3)

/-- `geq x y = true`, the shape of the first premise. -/
abbrev mkGeqEq (x y : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) y))
    (Term.Boolean true)

/-- `geq x 1 = true`, the shape of the second premise. -/
abbrev mkGeq1Eq (x : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) (Term.Numeral 1)))
    (Term.Boolean true)

/-! ## `__eo_requires` helpers (mirrors `Re_loop_elim`) -/

theorem eo_requires_eq_result_of_ne_stuck (x y z : Term) :
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

theorem eo_requires_arg_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · have hStuck : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, native_ite, hxy]
    exact False.elim (hReq hStuck)

/-! ## Decoding `__eo_eq` / `__eo_and` equality checks -/

theorem eo_eq_eq_true {t s : Term} (h : __eo_eq t s = Term.Boolean true) :
    s = t := by
  unfold __eo_eq at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · simp only [Term.Boolean.injEq, native_teq] at h
    exact of_decide_eq_true h

theorem eo_and_eq_true {x y : Term}
    (h : __eo_and x y = Term.Boolean true) :
    x = Term.Boolean true ∧ y = Term.Boolean true := by
  unfold __eo_and at h
  split at h
  · rename_i b1 b2
    simp only [Term.Boolean.injEq, SmtEval.native_and, Bool.and_eq_true] at h
    exact ⟨by rw [h.1], by rw [h.2]⟩
  · -- Binary case: the result is a `requires` of a `Binary`, never `Boolean true`
    rename_i w1 n1 w2 n2
    simp only [__eo_requires, native_ite] at h
    split at h
    · split at h <;> exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ## Numeral evaluation -/

theorem eval_numeral (M : SmtModel) (n : Int) :
    __smtx_model_eval M (__eo_to_smt (Term.Numeral n)) = SmtValue.Numeral n := by
  change __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n
  rw [__smtx_model_eval.eq_2]

/-! ## Structural extraction of the program result -/

theorem prog_form (a1 a2 a3 P1 P2 : Term)
    (hNe : __eo_prog_re_loop_star a1 a2 a3 (Proof.pf P1) (Proof.pf P2) ≠ Term.Stuck) :
    P1 = mkGeqEq a2 a1 ∧ P2 = mkGeq1Eq a2 ∧
      __eo_prog_re_loop_star a1 a2 a3 (Proof.pf P1) (Proof.pf P2) = mkConcl a1 a2 a3 := by
  unfold __eo_prog_re_loop_star at hNe ⊢
  split at hNe
  · exact absurd rfl hNe
  · exact absurd rfl hNe
  · exact absurd rfl hNe
  · rename_i heqP1 heqP2
    injection heqP1 with hP1
    injection heqP2 with hP2
    -- `hNe` is the `__eo_requires` of the matched branch.
    have hCond := eo_requires_arg_eq_of_ne_stuck hNe
    have hReqEq := eo_requires_eq_result_of_ne_stuck _ _ _ hNe
    -- Decompose the conjunction of syntactic equality checks.
    obtain ⟨hC12, hC3⟩ := eo_and_eq_true hCond
    obtain ⟨hC1, hC2⟩ := eo_and_eq_true hC12
    have hm2 := eo_eq_eq_true hC1
    have hn2 := eo_eq_eq_true hC2
    have hm3 := eo_eq_eq_true hC3
    rw [hm2, hn2] at hP1
    rw [hm3] at hP2
    exact ⟨hP1, hP2, hReqEq⟩
  · exact absurd rfl hNe

end ReLoopStarProof

open ReLoopStarProof

/-! ## Arithmetic helpers over `Int` (so `omega` sees the atoms) -/

theorem le_of_zleq {a b : Int} (h : native_zleq a b = true) : a ≤ b := by
  simpa [native_zleq] using h

theorem zlt_false_of_le {a b : Int} (h : a ≤ b) : native_zlt b a = false := by
  simp only [native_zlt, decide_eq_false_iff_not, Int.not_lt]
  exact h

theorem one_le_of_zleq_one {b : Int} (h : native_zleq 1 b = true) : 1 ≤ b :=
  le_of_zleq h

/-! ## Evaluation helpers -/

theorem eval_smt_numeral (M : SmtModel) (n : Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_2]

/-- Typing constraints imposed by the `re.loop` head in the conclusion. -/
theorem loop_star_types (a1 a2 a3 : Term)
    (hTrans : RuleProofs.eo_has_smt_translation (mkConcl a1 a2 a3)) :
    ∃ lo hi : Int,
      __eo_to_smt a1 = SmtTerm.Numeral lo ∧
      __eo_to_smt a2 = SmtTerm.Numeral hi ∧
      native_zleq 0 lo = true ∧ native_zleq 0 hi = true ∧
      __smtx_typeof (__eo_to_smt a3) = SmtType.RegLan := by
  have hTy : __smtx_typeof (__eo_to_smt (mkConcl a1 a2 a3)) ≠ SmtType.None := hTrans
  rw [show __eo_to_smt (mkConcl a1 a2 a3) =
        SmtTerm.eq
          (SmtTerm.re_loop (__eo_to_smt a1) (__eo_to_smt a2)
            (SmtTerm.re_mult (__eo_to_smt a3)))
          (SmtTerm.re_mult (__eo_to_smt a3)) from rfl, typeof_eq_eq] at hTy
  have hLoopNN :
      term_has_non_none_type
        (SmtTerm.re_loop (__eo_to_smt a1) (__eo_to_smt a2)
          (SmtTerm.re_mult (__eo_to_smt a3))) := by
    unfold term_has_non_none_type
    intro hNone
    rw [hNone, __smtx_typeof_eq, __smtx_typeof_guard] at hTy
    simp [native_ite, native_Teq] at hTy
  cases h1 : __eo_to_smt a1 with
  | Numeral lo =>
      cases h2 : __eo_to_smt a2 with
      | Numeral hi =>
          rw [h1, h2] at hLoopNN
          rcases re_loop_arg_of_non_none hLoopNN with ⟨hlo, hhi, hRm⟩
          have hA3 : __smtx_typeof (__eo_to_smt a3) = SmtType.RegLan := by
            rw [typeof_re_mult_eq] at hRm
            by_cases hh : __smtx_typeof (__eo_to_smt a3) = SmtType.RegLan
            · exact hh
            · simp [native_ite, native_Teq, hh] at hRm
          exact ⟨lo, hi, rfl, rfl, hlo, hhi, hA3⟩
      | _ =>
          exfalso
          rw [h1, h2] at hLoopNN
          unfold term_has_non_none_type at hLoopNN
          rw [typeof_re_loop_eq] at hLoopNN
          simp [__smtx_typeof_re_loop] at hLoopNN
  | _ =>
      exfalso
      cases h2 : __eo_to_smt a2 <;>
        (rw [h1] at hLoopNN
         unfold term_has_non_none_type at hLoopNN
         rw [typeof_re_loop_eq] at hLoopNN
         simp [__smtx_typeof_re_loop] at hLoopNN)

/-- The premise `geq x y = true` forces the numeral values to satisfy `b ≤ a`. -/
theorem zleq_of_geq_premise (M : SmtModel) (x y : Term) (a b : Int)
    (hx : __eo_to_smt x = SmtTerm.Numeral a)
    (hy : __eo_to_smt y = SmtTerm.Numeral b)
    (hP : eo_interprets M (mkGeqEq x y) true) :
    native_zleq b a = true := by
  have hRel :=
    RuleProofs.eo_interprets_eq_rel M
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) y) (Term.Boolean true) hP
  have hEvalGeq :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) y)) =
        SmtValue.Boolean (native_zleq b a) := by
    change __smtx_model_eval M (SmtTerm.geq (__eo_to_smt x) (__eo_to_smt y)) = _
    rw [hx, hy]
    simp only [__smtx_model_eval, __smtx_model_eval_geq,
      __smtx_model_eval_leq]
  have hEvalTrue :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) = SmtValue.Boolean true := by
    change __smtx_model_eval M (SmtTerm.Boolean true) = _
    rw [__smtx_model_eval.eq_1]
  rw [hEvalGeq, hEvalTrue] at hRel
  have hEq :
      SmtValue.Boolean (native_zleq b a) = SmtValue.Boolean true :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by rintro ⟨r1, r2, hbad, _⟩; cases hbad)).1 hRel
  simpa using hEq

/-- Extensional soundness of the rule conclusion. -/
theorem re_loop_star_canonical_true
    (M : SmtModel) (hM : model_wf M)
    (a1 a2 a3 : Term)
    (hBool : RuleProofs.eo_has_bool_type (mkConcl a1 a2 a3))
    (hP1 : eo_interprets M (mkGeqEq a2 a1) true)
    (hP2 : eo_interprets M (mkGeq1Eq a2) true) :
    eo_interprets M (mkConcl a1 a2 a3) true := by
  have hTrans : RuleProofs.eo_has_smt_translation (mkConcl a1 a2 a3) :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type _ hBool
  -- Read off the numeral bounds and the `RegLan` argument from typing.
  obtain ⟨lo, hi, h1, h2, _hlo0, _hhi0, hA3Ty⟩ := loop_star_types a1 a2 a3 hTrans
  -- The regex argument evaluates to a concrete language value.
  have hA3NN : term_has_non_none_type (__eo_to_smt a3) := by
    unfold term_has_non_none_type; rw [hA3Ty]; intro h; cases h
  have hA3Eval := type_preservation M hM (__eo_to_smt a3) hA3NN
  rw [hA3Ty] at hA3Eval
  rcases reglan_value_canonical hA3Eval with ⟨rv, hRv⟩
  -- The two inequalities from the premises.
  have hle : lo ≤ hi :=
    le_of_zleq (zleq_of_geq_premise M a2 a1 hi lo h2 h1 hP1)
  have hge1 : 1 ≤ hi :=
    one_le_of_zleq_one (zleq_of_geq_premise M a2 (Term.Numeral 1) hi 1 h2 rfl hP2)
  -- Evaluate the left-hand `re.loop (r*)` term.
  have hLoopEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.UOp2 UserOp2.re_loop a1 a2)
              (Term.Apply (Term.UOp UserOp.re_mult) a3))) =
        SmtValue.RegLan
          (nativeReLoopRec (native_int_to_nat (native_zplus hi (native_zneg lo)))
            lo hi (native_re_mult rv)) := by
    change __smtx_model_eval M
        (SmtTerm.re_loop (__eo_to_smt a1) (__eo_to_smt a2)
          (SmtTerm.re_mult (__eo_to_smt a3))) = _
    rw [h1, h2]
    simp only [__smtx_model_eval]
    rw [hRv]
    simp only [__smtx_model_eval_re_mult, __smtx_model_eval_re_loop,
      __smtx_model_eval_gt, __smtx_model_eval_lt, zlt_false_of_le hle,
      __smtx_model_eval_ite]
    rw [model_eval_re_loop_rec_reglan_eq]
  -- Evaluate the right-hand `r*` term.
  have hMultEval :
      __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) a3)) =
        SmtValue.RegLan (native_re_mult rv) := by
    change __smtx_model_eval M (SmtTerm.re_mult (__eo_to_smt a3)) = _
    simp only [__smtx_model_eval]
    rw [hRv]
    rfl
  -- The two values are semantically equal.
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.UOp2 UserOp2.re_loop a1 a2)
              (Term.Apply (Term.UOp UserOp.re_mult) a3))))
        (__smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) a3))) := by
    rw [hLoopEval, hMultEval]
    exact RuleProofs.re_loop_star_smt_value_rel lo hi rv hge1 hle
  -- Conclude the equality holds in the model.
  exact RuleProofs.eo_interprets_eq_of_rel M _ _ hBool hRel

/-- `__eo_gt t (-1) = true` forces `t` to be a non-negative integer literal. -/
theorem gt_neg_one_nonneg (t : Term)
    (h : __eo_gt t (Term.Numeral (-1 : native_Int)) = Term.Boolean true) :
    ∃ n : Int, t = Term.Numeral n ∧ native_zleq 0 n = true := by
  cases t
  case Numeral n =>
    refine ⟨n, rfl, ?_⟩
    have he : __eo_gt (Term.Numeral n) (Term.Numeral (-1 : native_Int))
        = Term.Boolean (native_zlt (-1 : native_Int) n) := rfl
    rw [he] at h
    have hb : native_zlt (-1 : native_Int) n = true := (Term.Boolean.injEq _ _).mp h
    have h1 : (-1 : Int) < n := by
      simp only [native_zlt] at hb; exact of_decide_eq_true hb
    have h0 : (0 : Int) ≤ n := by omega
    show native_zleq 0 n = true
    simpa [native_zleq] using h0
  all_goals simp [__eo_gt] at h

/-- `__eo_typeof_re_mult X = RegLan` forces `X = RegLan`. -/
theorem typeof_re_mult_arg_reglan (X : Term)
    (h : __eo_typeof_re_mult X = Term.UOp UserOp.RegLan) :
    X = Term.UOp UserOp.RegLan := by
  cases X with
  | UOp op => cases op <;> first | rfl | simp [__eo_typeof_re_mult] at h
  | _ => simp [__eo_typeof_re_mult] at h

/-- Inversion of the `re.loop` type rule: a non-stuck result forces the two
bounds to satisfy `> -1` and the body type to be `RegLan`. -/
theorem typeof_re_loop_inv (T1 l T2 h T3 : Term)
    (hNe : __eo_typeof_re_loop T1 l T2 h T3 ≠ Term.Stuck) :
    __eo_gt l (Term.Numeral (-1 : native_Int)) = Term.Boolean true ∧
    __eo_gt h (Term.Numeral (-1 : native_Int)) = Term.Boolean true ∧
    T3 = Term.UOp UserOp.RegLan := by
  unfold __eo_typeof_re_loop at hNe
  split at hNe
  · exact absurd rfl hNe
  · exact absurd rfl hNe
  · refine ⟨eo_requires_arg_eq_of_ne_stuck hNe, ?_, rfl⟩
    have hReqInner := eo_requires_eq_result_of_ne_stuck _ _ _ hNe
    rw [hReqInner] at hNe
    exact eo_requires_arg_eq_of_ne_stuck hNe
  · exact absurd rfl hNe

/-- Well-typedness of the conclusion, given non-negative literal bounds and a
`RegLan`-typed regex argument.  This is the rule-independent SMT computation: the
EO→SMT bridge sends the `RegLan` argument across, and `re.loop`/`re.*` over
non-negative numeral bounds is `RegLan`-typed, so the `eq` is `Bool`-typed. -/
theorem loop_has_bool_type_of_bounds (a1 a2 a3 : Term) (lo hi : Int)
    (h1 : a1 = Term.Numeral lo) (h2 : a2 = Term.Numeral hi)
    (hlo : native_zleq 0 lo = true) (hhi : native_zleq 0 hi = true)
    (hA3Ty : __eo_typeof a3 = Term.UOp UserOp.RegLan)
    (hA3Trans : eoHasSmtTranslation a3) :
    RuleProofs.eo_has_bool_type (mkConcl a1 a2 a3) := by
  have hA3SmtTy : __smtx_typeof (__eo_to_smt a3) = SmtType.RegLan := by
    have h := TranslationProofs.eo_to_smt_typeof_matches_translation a3 hA3Trans
    rw [hA3Ty] at h; exact h
  subst h1 h2
  have hMultTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) a3)) =
        SmtType.RegLan := by
    change __smtx_typeof (SmtTerm.re_mult (__eo_to_smt a3)) = SmtType.RegLan
    rw [typeof_re_mult_eq]; simp [hA3SmtTy, native_ite, native_Teq]
  have hLoopTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.UOp2 UserOp2.re_loop (Term.Numeral lo) (Term.Numeral hi))
              (Term.Apply (Term.UOp UserOp.re_mult) a3))) =
        SmtType.RegLan := by
    change __smtx_typeof
        (SmtTerm.re_loop (SmtTerm.Numeral lo) (SmtTerm.Numeral hi)
          (SmtTerm.re_mult (__eo_to_smt a3))) = SmtType.RegLan
    rw [typeof_re_loop_eq]
    have hM : __smtx_typeof (SmtTerm.re_mult (__eo_to_smt a3)) = SmtType.RegLan := hMultTy
    rw [hM]
    simp [__smtx_typeof_re_loop, hlo, hhi, native_ite]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UOp2 UserOp2.re_loop (Term.Numeral lo) (Term.Numeral hi))
      (Term.Apply (Term.UOp UserOp.re_mult) a3))
    (Term.Apply (Term.UOp UserOp.re_mult) a3)
    (by rw [hLoopTy, hMultTy]) (by rw [hLoopTy]; decide)

/--
Soundness wrapper for `re_loop_star`.

Fully proved.  The conclusion `re.loop[m,n](r*) = r*` is well typed (`hbt`,
via `loop_has_bool_type_of_bounds`) and semantically valid
(`re_loop_star_canonical_true`).

Well-typedness relies on the `re.loop` type rule requiring both bounds to be
*non-negative* integer literals: SMT `__smtx_typeof_re_loop` needs `native_zleq 0`
on each bound, so `__eo_typeof_re_loop` enforces `__eo_gt · (-1)` on both `l` and
`h`.  From `__eo_typeof (mkConcl …) = Bool`, `hBounds` inverts that rule to recover
`a1 = Numeral lo`, `a2 = Numeral hi` with `lo, hi ≥ 0` and a `RegLan` body.
-/
public theorem cmd_step_re_loop_star_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_loop_star args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_loop_star args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_loop_star args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_loop_star args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl)
  | cons a1 args =>
    cases args with
    | nil => change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl)
    | cons a2 args =>
      cases args with
      | nil => change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl)
      | cons a3 args =>
        cases args with
        | cons _ _ => change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl)
        | nil =>
          cases premises with
          | nil => change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl)
          | cons n1 premises =>
            cases premises with
            | nil => change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl)
            | cons n2 premises =>
              cases premises with
              | cons _ _ => change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl)
              | nil =>
                -- Argument SMT-translation of the regex body, from the command side condition.
                have hCArgs :
                    cArgListTranslationOk
                      (CArgList.cons a1 (CArgList.cons a2 (CArgList.cons a3 CArgList.nil))) :=
                  hCmdTrans
                have hA3Trans : eoHasSmtTranslation a3 := hCArgs.2.2.1
                -- The conclusion is `Bool`-typed.
                have hConclTy : __eo_typeof (mkConcl a1 a2 a3) = Term.Bool := by
                  have hPNe :
                      __eo_prog_re_loop_star a1 a2 a3
                          (Proof.pf (__eo_state_proven_nth s n1))
                          (Proof.pf (__eo_state_proven_nth s n2)) ≠ Term.Stuck := hProg
                  rw [← (prog_form a1 a2 a3 (__eo_state_proven_nth s n1)
                        (__eo_state_proven_nth s n2) hPNe).2.2]
                  exact hResultTy
                -- Well-typedness of the conclusion.  The bounds are non-negative integer
                -- literals and the body is `RegLan`; see the header note on `hBounds`.
                have hbt : RuleProofs.eo_has_bool_type (mkConcl a1 a2 a3) := by
                  have hBounds :
                      ∃ lo hi : Int,
                        a1 = Term.Numeral lo ∧ a2 = Term.Numeral hi ∧
                        native_zleq 0 lo = true ∧ native_zleq 0 hi = true ∧
                        __eo_typeof a3 = Term.UOp UserOp.RegLan := by
                    -- Invert `__eo_typeof_re_loop` from `__eo_typeof (mkConcl …) = Bool`.
                    have hLhsNe :
                        __eo_typeof_re_loop (__eo_typeof a1) a1 (__eo_typeof a2) a2
                            (__eo_typeof (Term.Apply (Term.UOp UserOp.re_mult) a3)) ≠
                          Term.Stuck := by
                      intro hS
                      have h := hConclTy
                      change __eo_typeof_eq
                          (__eo_typeof_re_loop (__eo_typeof a1) a1 (__eo_typeof a2) a2
                            (__eo_typeof (Term.Apply (Term.UOp UserOp.re_mult) a3)))
                          (__eo_typeof (Term.Apply (Term.UOp UserOp.re_mult) a3)) =
                        Term.Bool at h
                      rw [hS] at h
                      simp [__eo_typeof_eq] at h
                    obtain ⟨hg1, hg2, hT3eq⟩ :=
                      typeof_re_loop_inv (__eo_typeof a1) a1 (__eo_typeof a2) a2
                        (__eo_typeof (Term.Apply (Term.UOp UserOp.re_mult) a3)) hLhsNe
                    obtain ⟨lo, h1, hlo⟩ := gt_neg_one_nonneg a1 hg1
                    obtain ⟨hi, h2, hhi⟩ := gt_neg_one_nonneg a2 hg2
                    refine ⟨lo, hi, h1, h2, hlo, hhi, ?_⟩
                    -- `__eo_typeof (re_mult a3) = RegLan` ⟹ `__eo_typeof a3 = RegLan`.
                    have hMultArg :
                        __eo_typeof_re_mult (__eo_typeof a3) = Term.UOp UserOp.RegLan := hT3eq
                    exact typeof_re_mult_arg_reglan (__eo_typeof a3) hMultArg
                  obtain ⟨lo, hi, h1, h2, hlo, hhi, hA3Ty⟩ := hBounds
                  exact loop_has_bool_type_of_bounds a1 a2 a3 lo hi h1 h2 hlo hhi hA3Ty hA3Trans
                show StepRuleProperties M
                    [__eo_state_proven_nth s n1, __eo_state_proven_nth s n2]
                    (__eo_prog_re_loop_star a1 a2 a3
                      (Proof.pf (__eo_state_proven_nth s n1))
                      (Proof.pf (__eo_state_proven_nth s n2)))
                generalize hP1 : __eo_state_proven_nth s n1 = P1
                generalize hP2 : __eo_state_proven_nth s n2 = P2
                have hProgNe :
                    __eo_prog_re_loop_star a1 a2 a3 (Proof.pf P1) (Proof.pf P2) ≠
                      Term.Stuck := by
                  rw [← hP1, ← hP2]
                  exact hProg
                obtain ⟨hf1, hf2, hProgEq⟩ := prog_form a1 a2 a3 P1 P2 hProgNe
                rw [hProgEq]
                refine ⟨?_, ?_⟩
                · intro hEv
                  have h1t : eo_interprets M (mkGeqEq a2 a1) true := by
                    have h := hEv.true_here P1 (by simp)
                    rwa [hf1] at h
                  have h2t : eo_interprets M (mkGeq1Eq a2) true := by
                    have h := hEv.true_here P2 (by simp)
                    rwa [hf2] at h
                  exact re_loop_star_canonical_true M hM a1 a2 a3 hbt h1t h2t
                · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hbt
