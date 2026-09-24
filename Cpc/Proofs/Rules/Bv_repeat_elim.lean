module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

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

private theorem eo_requires_left_ne_stuck_of_ne_stuck
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
    x ≠ Term.Stuck := by
  intro hReq hx
  have hStuck : __eo_requires x y z = Term.Stuck := by
    subst x
    simp [__eo_requires, native_teq, native_ite, native_not, SmtEval.native_not]
  exact hReq hStuck

private theorem smt_eval_bv_concat_right_empty
    (M : SmtModel) (hM : model_wf M) (a : Term) (w : native_Nat)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w) :
    __smtx_model_eval_concat
        (__smtx_model_eval M (__eo_to_smt a)) (SmtValue.Binary 0 0) =
      __smtx_model_eval M (__eo_to_smt a) := by
  have hNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    intro h
    cases h
  have hEvalTy :=
    type_preservation M hM (__eo_to_smt a) hNN
  rw [haTy] at hEvalTy
  rcases bitvec_value_canonical hEvalTy with ⟨na, hEval⟩
  have hPayload :
      native_zeq na
        (native_mod_total na (native_int_pow2 (native_nat_to_int w))) = true := by
    have hTy :
        __smtx_typeof_value (SmtValue.Binary (native_nat_to_int w) na) =
          SmtType.BitVec w := by
      simpa [hEval] using hEvalTy
    exact bitvec_payload_canonical hTy
  have hPayloadEq :
      na = native_mod_total na (native_int_pow2 (native_nat_to_int w)) := by
    simpa [native_zeq] using hPayload
  rw [hEval]
  change
    SmtValue.Binary
        (native_zplus (native_nat_to_int w) 0)
        (native_mod_total
          (native_binary_concat (native_nat_to_int w) na 0 0)
          (native_int_pow2 (native_zplus (native_nat_to_int w) 0))) =
      SmtValue.Binary (native_nat_to_int w) na
  have hWidth :
      native_zplus (native_nat_to_int w) 0 = native_nat_to_int w := by
    simp [native_zplus]
  have hConcat :
      native_binary_concat (native_nat_to_int w) na 0 0 = na := by
    simp [native_binary_concat, native_zplus, native_zmult, native_int_pow2,
      native_zexp_total]
  rw [hWidth, hConcat, ← hPayloadEq]

private theorem eo_typeof_ne_stuck_of_smt_bitvec
    (a : Term) (w : native_Nat)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w) :
    __eo_typeof a ≠ Term.Stuck := by
  have hNN : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [haTy]
    intro h
    cases h
  have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation a hNN
  intro hStuck
  rw [hStuck] at hMatch
  rw [haTy] at hMatch
  cases hMatch

private theorem term_ne_stuck_of_smt_bitvec
    (a : Term) (w : native_Nat)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w) :
    a ≠ Term.Stuck := by
  intro h
  subst a
  exact (eo_typeof_ne_stuck_of_smt_bitvec Term.Stuck w haTy) rfl

private theorem eo_mk_apply_of_ne_stuck
    {f x : Term}
    (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem concat_apply_head_ne_stuck (a : Term) :
    Term.Apply (Term.UOp UserOp.concat) a ≠ Term.Stuck := by
  intro h
  cases h

private theorem eo_is_list_true_of_get_nil_eq
    {f x nil : Term}
    (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck)
    (hNil : __eo_get_nil_rec f x = nil)
    (hNilNe : nil ≠ Term.Stuck) :
    __eo_is_list f x = Term.Boolean true := by
  have hGetNe : __eo_get_nil_rec f x ≠ Term.Stuck := by
    intro hGet
    rw [hGet] at hNil
    exact hNilNe hNil.symm
  cases f <;> cases x <;>
    simp [__eo_is_list, __eo_is_ok, native_teq, native_not,
      SmtEval.native_not, hGetNe] at hf hx hNil hNilNe ⊢

private theorem bv_list_repeat_rec_zero_eq
    (a : Term) (hANe : a ≠ Term.Stuck) :
    __eo_list_repeat_rec (Term.UOp UserOp.concat) a (0 : native_Nat) =
      __eo_nil (Term.UOp UserOp.concat) (__eo_typeof a) := by
  cases a <;> simp [__eo_list_repeat_rec] at hANe ⊢

private theorem bv_list_repeat_rec_succ_eq
    (a : Term) (hANe : a ≠ Term.Stuck) (n : native_Nat) :
    __eo_list_repeat_rec (Term.UOp UserOp.concat) a (Nat.succ n) =
      __eo_mk_apply
        (Term.Apply (Term.UOp UserOp.concat) a)
        (__eo_list_repeat_rec (Term.UOp UserOp.concat) a n) := by
  cases a <;> simp [__eo_list_repeat_rec] at hANe ⊢

private theorem bv_list_repeat_rec_ne_stuck
    (a : Term) (w : native_Nat)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w) :
    ∀ n : native_Nat,
      __eo_list_repeat_rec (Term.UOp UserOp.concat) a n ≠ Term.Stuck := by
  intro n
  have hANe := term_ne_stuck_of_smt_bitvec a w haTy
  induction n with
  | zero =>
      have hTyNe := eo_typeof_ne_stuck_of_smt_bitvec a w haTy
      rw [bv_list_repeat_rec_zero_eq a hANe]
      cases hTy : __eo_typeof a
      case Stuck => exact False.elim (hTyNe hTy)
      all_goals simp [__eo_nil]
  | succ n ih =>
      rw [bv_list_repeat_rec_succ_eq a hANe n]
      rw [eo_mk_apply_of_ne_stuck (concat_apply_head_ne_stuck a) ih]
      intro h
      cases h

private theorem bv_list_repeat_rec_get_nil
    (a : Term) (w : native_Nat)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w) :
    ∀ n : native_Nat,
      __eo_get_nil_rec (Term.UOp UserOp.concat)
        (__eo_list_repeat_rec (Term.UOp UserOp.concat) a n) =
        Term.Binary 0 0 := by
  intro n
  have hANe := term_ne_stuck_of_smt_bitvec a w haTy
  induction n with
  | zero =>
      have hTyNe := eo_typeof_ne_stuck_of_smt_bitvec a w haTy
      rw [bv_list_repeat_rec_zero_eq a hANe]
      cases hTy : __eo_typeof a
      case Stuck => exact False.elim (hTyNe hTy)
      all_goals
        simp [__eo_nil, __eo_get_nil_rec, __eo_is_list_nil, __eo_requires,
          native_ite, native_teq, native_not, SmtEval.native_not]
  | succ n ih =>
      have hTailNe := bv_list_repeat_rec_ne_stuck a w haTy n
      rw [bv_list_repeat_rec_succ_eq a hANe n]
      rw [eo_mk_apply_of_ne_stuck (concat_apply_head_ne_stuck a) hTailNe]
      simp [__eo_get_nil_rec, __eo_requires, native_ite, native_teq,
        native_not, SmtEval.native_not, ih]

private theorem bv_list_repeat_rec_is_list
    (a : Term) (w : native_Nat)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w)
    (n : native_Nat) :
    __eo_is_list (Term.UOp UserOp.concat)
      (__eo_list_repeat_rec (Term.UOp UserOp.concat) a n) =
      Term.Boolean true := by
  have hNil := bv_list_repeat_rec_get_nil a w haTy n
  have hXNe := bv_list_repeat_rec_ne_stuck a w haTy n
  exact eo_is_list_true_of_get_nil_eq
    (by intro h; cases h) hXNe hNil (by intro h; cases h)

private theorem bv_list_repeat_rec_succ_not_nil
    (a : Term) (w : native_Nat)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w)
    (n : native_Nat) :
    __eo_is_list_nil (Term.UOp UserOp.concat)
      (__eo_list_repeat_rec (Term.UOp UserOp.concat) a (Nat.succ n)) =
      Term.Boolean false := by
  have hANe := term_ne_stuck_of_smt_bitvec a w haTy
  have hTailNe := bv_list_repeat_rec_ne_stuck a w haTy n
  rw [bv_list_repeat_rec_succ_eq a hANe n]
  rw [eo_mk_apply_of_ne_stuck (concat_apply_head_ne_stuck a) hTailNe]
  simp [__eo_is_list_nil]

private theorem bv_list_repeat_rec_eval_eq_repeat_rec
    (M : SmtModel) (a : Term) (w : native_Nat)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w) :
    ∀ n : native_Nat,
      __smtx_model_eval M
          (__eo_to_smt (__eo_list_repeat_rec (Term.UOp UserOp.concat) a n)) =
        __smtx_repeat_rec n
          (__smtx_model_eval M (__eo_to_smt a)) := by
  intro n
  have hANe := term_ne_stuck_of_smt_bitvec a w haTy
  induction n with
  | zero =>
      have hTyNe := eo_typeof_ne_stuck_of_smt_bitvec a w haTy
      rw [bv_list_repeat_rec_zero_eq a hANe]
      cases hTy : __eo_typeof a
      case Stuck => exact False.elim (hTyNe hTy)
      all_goals
        simp [__eo_nil]
        change __smtx_model_eval M (SmtTerm.Binary 0 0) =
          SmtValue.Binary 0 0
        rw [__smtx_model_eval.eq_5]
  | succ n ih =>
      have hTailNe := bv_list_repeat_rec_ne_stuck a w haTy n
      rw [bv_list_repeat_rec_succ_eq a hANe n]
      rw [eo_mk_apply_of_ne_stuck (concat_apply_head_ne_stuck a) hTailNe]
      rw [show
        __eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.concat) a)
            (__eo_list_repeat_rec (Term.UOp UserOp.concat) a n)) =
          SmtTerm.concat (__eo_to_smt a)
            (__eo_to_smt
              (__eo_list_repeat_rec (Term.UOp UserOp.concat) a n)) by rfl]
      rw [__smtx_model_eval.eq_36, __smtx_repeat_rec]
      rw [ih]

private theorem bv_list_repeat_singleton_eval_eq_repeat_rec
    (M : SmtModel) (hM : model_wf M) (a : Term) (w : native_Nat)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w) :
    ∀ n : native_Nat,
      __smtx_model_eval M
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.concat)
              (__eo_list_repeat_rec (Term.UOp UserOp.concat) a n))) =
        __smtx_repeat_rec n
          (__smtx_model_eval M (__eo_to_smt a)) := by
  intro n
  have hANe := term_ne_stuck_of_smt_bitvec a w haTy
  cases n with
  | zero =>
      have hTyNe := eo_typeof_ne_stuck_of_smt_bitvec a w haTy
      rw [bv_list_repeat_rec_zero_eq a hANe]
      cases hTy : __eo_typeof a
      case Stuck => exact False.elim (hTyNe hTy)
      all_goals
        simp [__eo_nil, __eo_list_singleton_elim,
          __eo_list_singleton_elim_2, __eo_is_list, __eo_get_nil_rec,
          __eo_is_list_nil, __eo_is_ok, __eo_requires, native_ite,
          native_teq, native_not, SmtEval.native_not]
        change __smtx_model_eval M (SmtTerm.Binary 0 0) =
          SmtValue.Binary 0 0
        rw [__smtx_model_eval.eq_5]
  | succ n =>
      cases n with
      | zero =>
          have hTailNe :=
            bv_list_repeat_rec_ne_stuck a w haTy (0 : native_Nat)
          have hRight :=
            smt_eval_bv_concat_right_empty M hM a w haTy
          rw [bv_list_repeat_rec_succ_eq a hANe (0 : native_Nat)]
          rw [eo_mk_apply_of_ne_stuck (concat_apply_head_ne_stuck a) hTailNe]
          rw [bv_list_repeat_rec_zero_eq a hANe]
          have hTyNe := eo_typeof_ne_stuck_of_smt_bitvec a w haTy
          cases hTy : __eo_typeof a
          case Stuck => exact False.elim (hTyNe hTy)
          all_goals
            simp [__eo_nil, __eo_list_singleton_elim,
              __eo_list_singleton_elim_2, __eo_is_list, __eo_get_nil_rec,
              __eo_is_list_nil, __eo_is_ok, __eo_requires, native_ite,
              native_teq, native_not, SmtEval.native_not,
              __smtx_repeat_rec]
            exact hRight.symm
      | succ n =>
          have hTailNe :=
            bv_list_repeat_rec_ne_stuck a w haTy (Nat.succ n)
          have hTailEval :=
            bv_list_repeat_rec_eval_eq_repeat_rec M a w haTy (Nat.succ n)
          have hIsList :=
            bv_list_repeat_rec_is_list a w haTy (Nat.succ (Nat.succ n))
          have hTailNotNil :=
            bv_list_repeat_rec_succ_not_nil a w haTy n
          change
            __smtx_model_eval M
              (__eo_to_smt
                (__eo_requires
                  (__eo_is_list (Term.UOp UserOp.concat)
                    (__eo_list_repeat_rec (Term.UOp UserOp.concat) a
                      (Nat.succ (Nat.succ n))))
                  (Term.Boolean true)
                  (__eo_list_singleton_elim_2
                    (__eo_list_repeat_rec (Term.UOp UserOp.concat) a
                      (Nat.succ (Nat.succ n)))))) =
            __smtx_repeat_rec (Nat.succ (Nat.succ n))
              (__smtx_model_eval M (__eo_to_smt a))
          rw [hIsList]
          simp [__eo_requires, native_ite, native_teq, native_not,
            SmtEval.native_not]
          rw [bv_list_repeat_rec_succ_eq a hANe (Nat.succ n)]
          rw [eo_mk_apply_of_ne_stuck (concat_apply_head_ne_stuck a) hTailNe]
          simp [__eo_list_singleton_elim_2, hTailNotNil, __eo_ite,
            native_ite, native_teq]
          -- v4.33 `simp` already leaves the concat translated, so the explicit
          -- `rw` is redundant; only the `succ`/`+ 1` spelling has to be aligned.
          simp only [Nat.succ_eq_add_one] at hTailEval
          rw [__smtx_model_eval.eq_36, __smtx_repeat_rec]
          rw [hTailEval]

private theorem bv_repeat_elim_eval_rel
    (M : SmtModel) (hM : model_wf M)
    (n a : Term) (i : native_Int) (w : native_Nat)
    (hn : __eo_to_smt n = SmtTerm.Numeral i)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w)
    (hi : native_zleq 1 i = true) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.concat)
            (__eo_ite
              (__eo_and (__eo_is_z n) (__eo_not (__eo_is_neg n)))
              (__eo_list_repeat (Term.UOp UserOp.concat) a n)
              (Term.Apply (Term.UOp1 UserOp1.repeat n) a)))))
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.repeat n) a))) := by
  have hnTerm : n = Term.Numeral i := by
    exact TranslationProofs.eo_to_smt_eq_numeral n i hn
  subst n
  have hiGe : (1 : Int) ≤ i := by
    simpa [native_zleq] using hi
  have h0le : (0 : Int) ≤ i := by
    omega
  have hiNonneg : native_zlt i 0 = false := by
    simp [native_zlt]
    omega
  have hANe := term_ne_stuck_of_smt_bitvec a w haTy
  have hCond :
      __eo_and (__eo_is_z (Term.Numeral i))
          (__eo_not (__eo_is_neg (Term.Numeral i))) =
        Term.Boolean true := by
    simp [__eo_and, __eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_not,
      native_teq, native_and, native_not, SmtEval.native_not, native_zlt,
      h0le]
  have hList :
      __eo_list_repeat (Term.UOp UserOp.concat) a (Term.Numeral i) =
        __eo_list_repeat_rec (Term.UOp UserOp.concat) a (native_int_to_nat i) := by
    cases a <;> simp [__eo_list_repeat, native_ite, hiNonneg] at hANe ⊢
  have hEval :=
    bv_list_repeat_singleton_eval_eq_repeat_rec M hM a w haTy
      (native_int_to_nat i)
  rw [hCond, hList]
  simp [__eo_ite, native_teq, native_ite]
  rw [hEval]
  rw [show
    __eo_to_smt
      (Term.Apply (Term.UOp1 UserOp1.repeat (Term.Numeral i)) a) =
      SmtTerm.repeat (SmtTerm.Numeral i) (__eo_to_smt a) by rfl]
  have hANN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    intro h
    cases h
  have hEvalTy :=
    type_preservation M hM (__eo_to_smt a) hANN
  rw [haTy] at hEvalTy
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalA⟩
  rw [__smtx_model_eval.eq_38, __smtx_model_eval.eq_2, hEvalA]
  simp [__smtx_model_eval_repeat]
  exact RuleProofs.smt_value_rel_refl _

private theorem bv_repeat_elim_shape_of_ne_stuck (A : Term) :
    __eo_prog_bv_repeat_elim A ≠ Term.Stuck ->
    ∃ n a b,
      A =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp1 UserOp1.repeat n) a)) b := by
  intro h
  by_cases hShape :
      ∃ n a b,
        A =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp1 UserOp1.repeat n) a)) b
  · exact hShape
  · have hStuck : __eo_prog_bv_repeat_elim A = Term.Stuck := by
      rw [__eo_prog_bv_repeat_elim.eq_2]
      intro n a b hEq
      exact hShape ⟨n, a, b, hEq⟩
    exact False.elim (h hStuck)

public theorem cmd_step_bv_repeat_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_repeat_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_repeat_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_repeat_elim args premises) :=
by
  intro hCmdTrans _hPremBool hResultTy
  have hProgNe :
      __eo_cmd_step_proven s CRule.bv_repeat_elim args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProgNe
      exact False.elim (hProgNe rfl)
  | cons A argsTail =>
      cases argsTail with
      | cons A2 argsRest =>
          change Term.Stuck ≠ Term.Stuck at hProgNe
          exact False.elim (hProgNe rfl)
      | nil =>
          cases premises with
          | cons n rest =>
              change Term.Stuck ≠ Term.Stuck at hProgNe
              exact False.elim (hProgNe rfl)
          | nil =>
              have hATrans : RuleProofs.eo_has_smt_translation A := by
                simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation,
                  cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
              change StepRuleProperties M [] (__eo_prog_bv_repeat_elim A)
              change __eo_typeof (__eo_prog_bv_repeat_elim A) = Term.Bool
                at hResultTy
              have hProgNe' : __eo_prog_bv_repeat_elim A ≠ Term.Stuck := by
                exact hProgNe
              rcases bv_repeat_elim_shape_of_ne_stuck A hProgNe' with
                ⟨n, a, rhs, hShape⟩
              subst A
              let rep := Term.Apply (Term.UOp1 UserOp1.repeat n) a
              let expanded :=
                __eo_list_singleton_elim (Term.UOp UserOp.concat)
                  (__eo_ite
                    (__eo_and (__eo_is_z n) (__eo_not (__eo_is_neg n)))
                    (__eo_list_repeat (Term.UOp UserOp.concat) a n) rep)
              let orig :=
                Term.Apply (Term.Apply (Term.UOp UserOp.eq) rep) rhs
              have hReqNe :
                  __eo_requires expanded rhs orig ≠ Term.Stuck := by
                simpa [__eo_prog_bv_repeat_elim, rep, expanded, orig] using
                  hProgNe'
              have hExpandedEq : expanded = rhs :=
                eo_requires_arg_eq_of_ne_stuck hReqNe
              have hExpandedNe : expanded ≠ Term.Stuck :=
                eo_requires_left_ne_stuck_of_ne_stuck hReqNe
              have hRhsNe : rhs ≠ Term.Stuck := by
                rw [← hExpandedEq]
                exact hExpandedNe
              have hProgEq :
                  __eo_prog_bv_repeat_elim
                      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) rep) rhs) =
                    orig := by
                rw [__eo_prog_bv_repeat_elim.eq_1]
                change __eo_requires expanded rhs orig = orig
                simp [__eo_requires, hExpandedEq, hRhsNe, native_ite,
                  native_teq, native_not, SmtEval.native_not]
              have hOrigTy : __eo_typeof orig = Term.Bool := by
                simpa [hProgEq, orig, rep] using hResultTy
              have hOrigBool : RuleProofs.eo_has_bool_type orig :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  orig hATrans hOrigTy
              rcases
                  RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                    rep rhs hOrigBool with
                ⟨_hSameTy, hRepNN⟩
              have hRepeatNN :
                  term_has_non_none_type
                    (SmtTerm.repeat (__eo_to_smt n) (__eo_to_smt a)) := by
                unfold term_has_non_none_type
                exact hRepNN
              rcases repeat_args_of_non_none hRepeatNN with
                ⟨i, w, hn, haTy, hi⟩
              have hRelExpanded :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt expanded))
                    (__smtx_model_eval M (__eo_to_smt rep)) := by
                simpa [expanded, rep] using
                  bv_repeat_elim_eval_rel M hM n a i w hn haTy hi
              have hRel :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt rep))
                    (__smtx_model_eval M (__eo_to_smt rhs)) := by
                rw [← hExpandedEq]
                exact RuleProofs.smt_value_rel_symm _ _ hRelExpanded
              have hFact :
                  eo_interprets M (__eo_prog_bv_repeat_elim orig) true := by
                rw [hProgEq]
                exact RuleProofs.eo_interprets_eq_of_rel
                  M rep rhs hOrigBool hRel
              exact
                { facts_of_true := by
                    intro _premisesTrue
                    simpa [orig] using hFact
                  has_smt_translation := by
                    rw [hProgEq]
                    exact
                      RuleProofs.eo_has_smt_translation_of_has_bool_type
                        orig hOrigBool }
