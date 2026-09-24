module

public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport
public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.RegexSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_typeof_stuck_ne_bool :
    __eo_typeof Term.Stuck ≠ Term.Bool := by
  native_decide

private theorem eo_requires_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · have hNe : native_teq x y = false := by
      simp [native_teq, hxy]
    simp [__eo_requires, hNe, native_ite] at hReq

private theorem eo_requires_result_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    __eo_requires x y z = z := by
  intro hReq
  have hxy : x = y := eo_requires_eq_of_ne_stuck x y z hReq
  subst y
  by_cases hxStuck : x = Term.Stuck
  · subst x
    simp [__eo_requires, native_teq, native_ite, native_not, SmtEval.native_not] at hReq
  · simp [__eo_requires, hxStuck, native_teq, native_ite, native_not,
      SmtEval.native_not]

private theorem eo_requires_body_ne_stuck_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    z ≠ Term.Stuck := by
  intro hReq hz
  have hxy : x = y := eo_requires_eq_of_ne_stuck x y z hReq
  subst y
  by_cases hxStuck : x = Term.Stuck
  · subst x
    simp [__eo_requires, native_teq, native_ite, native_not, SmtEval.native_not] at hReq
  · subst z
    simp [__eo_requires, hxStuck, native_teq, native_ite, native_not,
      SmtEval.native_not] at hReq

private inductive AbsorbTree (f zero : Term) : Term -> Prop where
  | here : AbsorbTree f zero zero
  | left (a b : Term) :
      AbsorbTree f zero a ->
      AbsorbTree f zero (Term.Apply (Term.Apply f a) b)
  | right (a b : Term) :
      AbsorbTree f zero b ->
      AbsorbTree f zero (Term.Apply (Term.Apply f a) b)

private abbrev mkBvAnd (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvand) x) y

private abbrev mkBvOr (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvor) x) y

private abbrev mkReConcat (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x) y

private abbrev mkReInter (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x) y

private abbrev mkReUnion (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x) y

private theorem absorbTree_of_is_absorb_rec_eq_true
    (f zero t : Term) :
    f ≠ Term.Stuck ->
    zero ≠ Term.Stuck ->
    __is_absorb_rec f t zero = Term.Boolean true ->
    AbsorbTree f zero t := by
  intro hfStuck hZeroStuck hAbs
  cases t with
  | UOp op =>
      by_cases hZero : zero = Term.UOp op
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | UOp1 op a =>
      by_cases hZero : zero = Term.UOp1 op a
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | UOp2 op a b =>
      by_cases hZero : zero = Term.UOp2 op a b
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | UOp3 op a b c =>
      by_cases hZero : zero = Term.UOp3 op a b c
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | __eo_List =>
      by_cases hZero : zero = Term.__eo_List
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | __eo_List_nil =>
      by_cases hZero : zero = Term.__eo_List_nil
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | __eo_List_cons =>
      by_cases hZero : zero = Term.__eo_List_cons
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | Bool =>
      by_cases hZero : zero = Term.Bool
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | Boolean b =>
      by_cases hZero : zero = Term.Boolean b
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;> cases b <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | Numeral n =>
      by_cases hZero : zero = Term.Numeral n
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | Rational q =>
      by_cases hZero : zero = Term.Rational q
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | String s =>
      by_cases hZero : zero = Term.String s
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | Binary w n =>
      by_cases hZero : zero = Term.Binary w n
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | «Type» =>
      by_cases hZero : zero = Term.Type
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | Stuck =>
      simp [__is_absorb_rec] at hAbs
  | Apply g b =>
      by_cases hZero : zero = Term.Apply g b
      · subst zero
        exact AbsorbTree.here
      · simp [__is_absorb_rec, __eo_ite, __eo_eq, native_ite, native_teq,
          hZero] at hAbs
        cases g with
        | Apply g' a =>
            by_cases hF : g' = f
            · subst g'
              simp [__eo_l_1___is_absorb_rec,
                __eo_ite, __eo_eq, native_ite, native_teq] at hAbs
              by_cases hLeft :
                  __is_absorb_rec f a zero = Term.Boolean true
              · exact AbsorbTree.left a b
                  (absorbTree_of_is_absorb_rec_eq_true f zero a
                    hfStuck hZeroStuck hLeft)
              · have hTail := hAbs hLeft
                by_cases hLeftFalse :
                    __is_absorb_rec f a zero = Term.Boolean false
                · have hRight :
                      __is_absorb_rec f b zero = Term.Boolean true := by
                    simpa [hLeftFalse] using hTail
                  exact AbsorbTree.right a b
                    (absorbTree_of_is_absorb_rec_eq_true f zero b
                      hfStuck hZeroStuck hRight)
                · simp [hLeftFalse] at hTail
            · exfalso
              by_cases hgStuck : g' = Term.Stuck
              · subst g'
                simp [__eo_l_1___is_absorb_rec,
                  __eo_ite, __eo_eq, native_ite, native_teq] at hAbs
              · have hEqFalse : __eo_eq f g' = Term.Boolean false := by
                  simp [__eo_eq, native_teq, hF]
                simp [__eo_l_1___is_absorb_rec, __eo_l_2___is_absorb_rec,
                  __eo_ite, native_ite, native_teq, hEqFalse] at hAbs
        | _ =>
            exfalso
            simp [__eo_l_1___is_absorb_rec, __eo_l_2___is_absorb_rec] at hAbs
  | FunType =>
      by_cases hZero : zero = Term.FunType
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | Var name ty =>
      by_cases hZero : zero = Term.Var name ty
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | DatatypeType s d =>
      by_cases hZero : zero = Term.DatatypeType s d
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | DatatypeTypeRef s =>
      by_cases hZero : zero = Term.DatatypeTypeRef s
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | DtcAppType a b =>
      by_cases hZero : zero = Term.DtcAppType a b
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | DtCons s d i =>
      by_cases hZero : zero = Term.DtCons s d i
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | DtSel s d i j =>
      by_cases hZero : zero = Term.DtSel s d i j
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | USort u =>
      by_cases hZero : zero = Term.USort u
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  | UConst u ty =>
      by_cases hZero : zero = Term.UConst u ty
      · subst zero
        exact AbsorbTree.here
      · exfalso
        cases zero <;>
          simp [__is_absorb_rec, __eo_l_1___is_absorb_rec,
            __eo_l_2___is_absorb_rec, __eo_ite, __eo_eq, native_ite,
            native_teq] at hAbs hZero
        all_goals
          have hBad := hAbs hZero
          split at hBad <;> simp at hBad
  all_goals
    have hBad := hAbs hZero
    split at hBad <;> simp at hBad
termination_by t
decreasing_by
  all_goals
    subst_vars
    change Term._sizeOf_1 _ < Term._sizeOf_1 _
    simp [Term._sizeOf_1]
    omega

private theorem eo_interprets_and_left_false_intro
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    eo_interprets M A false ->
    RuleProofs.eo_has_bool_type B ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) false := by
  intro hAFalse hBBool
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hAFalse ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) =
      SmtTerm.and (__eo_to_smt A) (__eo_to_smt B) by rfl]
  rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM B hBBool with
    ⟨b, hBEval⟩
  cases hAFalse with
  | intro_false hATy hAEval =>
      refine smt_interprets.intro_false M
        (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) ?_ ?_
      · rw [typeof_and_eq]
        have hBTy : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
          simpa [RuleProofs.eo_has_bool_type] using hBBool
        simp [hATy, hBTy, native_Teq, native_ite]
      · rw [__smtx_model_eval.eq_9, hAEval, hBEval]
        cases b <;> simp [__smtx_model_eval_and, SmtEval.native_and]

private theorem eo_interprets_and_right_false_intro
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    eo_interprets M B false ->
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) false := by
  intro hABool hBFalse
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hBFalse ⊢
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) =
      SmtTerm.and (__eo_to_smt A) (__eo_to_smt B) by rfl]
  rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM A hABool with
    ⟨a, hAEval⟩
  cases hBFalse with
  | intro_false hBTy hBEval =>
      refine smt_interprets.intro_false M
        (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) ?_ ?_
      · rw [typeof_and_eq]
        have hATy : __smtx_typeof (__eo_to_smt A) = SmtType.Bool := by
          simpa [RuleProofs.eo_has_bool_type] using hABool
        simp [hATy, hBTy, native_Teq, native_ite]
      · rw [__smtx_model_eval.eq_9, hAEval, hBEval]
        cases a <;> simp [__smtx_model_eval_and, SmtEval.native_and]

private theorem absorbTree_or_true
    (M : SmtModel) (hM : model_wf M) :
    ∀ {t : Term},
      AbsorbTree (Term.UOp UserOp.or) (Term.Boolean true) t ->
      RuleProofs.eo_has_bool_type t ->
      eo_interprets M t true := by
  intro t hTree
  induction hTree with
  | here =>
      intro _hBool
      exact RuleProofs.eo_interprets_true M
  | left a b _ ih =>
      intro hBool
      have hABool : RuleProofs.eo_has_bool_type a :=
        RuleProofs.eo_has_bool_type_or_left a b hBool
      have hBBool : RuleProofs.eo_has_bool_type b :=
        RuleProofs.eo_has_bool_type_or_right a b hBool
      exact RuleProofs.eo_interprets_or_left_intro M hM a b (ih hABool) hBBool
  | right a b _ ih =>
      intro hBool
      have hABool : RuleProofs.eo_has_bool_type a :=
        RuleProofs.eo_has_bool_type_or_left a b hBool
      have hBBool : RuleProofs.eo_has_bool_type b :=
        RuleProofs.eo_has_bool_type_or_right a b hBool
      exact RuleProofs.eo_interprets_or_right_intro M hM a b hABool (ih hBBool)

private theorem absorbTree_and_false
    (M : SmtModel) (hM : model_wf M) :
    ∀ {t : Term},
      AbsorbTree (Term.UOp UserOp.and) (Term.Boolean false) t ->
      RuleProofs.eo_has_bool_type t ->
      eo_interprets M t false := by
  intro t hTree
  induction hTree with
  | here =>
      intro _hBool
      exact CnfSupport.eo_interprets_false M
  | left a b _ ih =>
      intro hBool
      have hABool : RuleProofs.eo_has_bool_type a :=
        RuleProofs.eo_has_bool_type_and_left a b hBool
      have hBBool : RuleProofs.eo_has_bool_type b :=
        RuleProofs.eo_has_bool_type_and_right a b hBool
      exact eo_interprets_and_left_false_intro M hM a b (ih hABool) hBBool
  | right a b _ ih =>
      intro hBool
      have hABool : RuleProofs.eo_has_bool_type a :=
        RuleProofs.eo_has_bool_type_and_left a b hBool
      have hBBool : RuleProofs.eo_has_bool_type b :=
        RuleProofs.eo_has_bool_type_and_right a b hBool
      exact eo_interprets_and_right_false_intro M hM a b hABool (ih hBBool)

private theorem smt_value_rel_of_eo_interprets_bool_const
    (M : SmtModel) (t : Term) (b : Bool) :
    eo_interprets M t b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt t))
      (__smtx_model_eval M (__eo_to_smt (Term.Boolean b))) := by
  intro hInterp
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hInterp
  cases b with
  | false =>
      cases hInterp with
      | intro_false _ hEval =>
          rw [show __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false by rfl]
          rw [__smtx_model_eval.eq_1]
          simp [hEval, __smtx_model_eval_eq, native_veq]
  | true =>
      cases hInterp with
      | intro_true _ hEval =>
          rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true by rfl]
          rw [__smtx_model_eval.eq_1]
          simp [hEval, __smtx_model_eval_eq, native_veq]

private theorem smt_eval_reglan_of_smt_type_reglan
    (M : SmtModel) (hM : model_wf M) (t : SmtTerm) :
    __smtx_typeof t = SmtType.RegLan ->
    ∃ r, __smtx_model_eval M t = SmtValue.RegLan r := by
  intro hTy
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    intro h
    cases h
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.RegLan := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t hNN
  exact reglan_value_canonical hValTy

private theorem smt_eval_binary_of_smt_type_bitvec
    (M : SmtModel) (hM : model_wf M) (t : SmtTerm)
    (w : native_Nat) :
    __smtx_typeof t = SmtType.BitVec w ->
    ∃ n, __smtx_model_eval M t =
      SmtValue.Binary (native_nat_to_int w) n := by
  intro hTy
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    intro h
    cases h
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.BitVec w := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t hNN
  exact bitvec_value_canonical hValTy

private theorem smt_bitvec_ne_none (w : native_Nat) :
    SmtType.BitVec w ≠ SmtType.None := by
  intro h
  cases h

private theorem smt_reglan_ne_none : SmtType.RegLan ≠ SmtType.None := by
  intro h
  cases h

private theorem reConcat_args_of_reglan_type (y x : Term) :
    __smtx_typeof (__eo_to_smt (mkReConcat y x)) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt y) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.RegLan := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.re_concat (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.RegLan := by
    simpa [mkReConcat] using hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.re_concat (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hTy']
    exact smt_reglan_ne_none
  exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
    (typeof_re_concat_eq (__eo_to_smt y) (__eo_to_smt x)) hNN

private theorem reInter_args_of_reglan_type (y x : Term) :
    __smtx_typeof (__eo_to_smt (mkReInter y x)) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt y) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.RegLan := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.re_inter (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.RegLan := by
    simpa [mkReInter] using hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.re_inter (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hTy']
    exact smt_reglan_ne_none
  exact reglan_binop_args_of_non_none (op := SmtTerm.re_inter)
    (typeof_re_inter_eq (__eo_to_smt y) (__eo_to_smt x)) hNN

private theorem reUnion_args_of_reglan_type (y x : Term) :
    __smtx_typeof (__eo_to_smt (mkReUnion y x)) = SmtType.RegLan ->
    __smtx_typeof (__eo_to_smt y) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.RegLan := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.re_union (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.RegLan := by
    simpa [mkReUnion] using hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.re_union (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hTy']
    exact smt_reglan_ne_none
  exact reglan_binop_args_of_non_none (op := SmtTerm.re_union)
    (typeof_re_union_eq (__eo_to_smt y) (__eo_to_smt x)) hNN

private theorem bvand_args_of_bitvec_type (y x : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt (mkBvAnd y x)) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.bvand (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.BitVec w := by
    simpa [mkBvAnd] using hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.bvand (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hTy']
    exact smt_bitvec_ne_none w
  rcases bv_binop_args_of_non_none (op := SmtTerm.bvand)
      (show
        __smtx_typeof (SmtTerm.bvand (__eo_to_smt y) (__eo_to_smt x)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt y))
            (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_40]) hNN with
    ⟨w', hyTy, hxTy⟩
  have hWidth : w' = w := by
    have hResult :
        SmtType.BitVec w' = SmtType.BitVec w := by
      rw [show
          __smtx_typeof (SmtTerm.bvand (__eo_to_smt y) (__eo_to_smt x)) =
            __smtx_typeof_bv_op_2
              (__smtx_typeof (__eo_to_smt y))
              (__smtx_typeof (__eo_to_smt x)) by
          rw [__smtx_typeof.eq_40]] at hTy'
      simpa [__smtx_typeof_bv_op_2, hyTy, hxTy, native_ite,
        native_nateq, Smtm.native_nateq] using hTy'
    cases hResult
    rfl
  subst w'
  exact ⟨hyTy, hxTy⟩

private theorem bvor_args_of_bitvec_type (y x : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt (mkBvOr y x)) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.bvor (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.BitVec w := by
    simpa [mkBvOr] using hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.bvor (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hTy']
    exact smt_bitvec_ne_none w
  rcases bv_binop_args_of_non_none (op := SmtTerm.bvor)
      (show
        __smtx_typeof (SmtTerm.bvor (__eo_to_smt y) (__eo_to_smt x)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt y))
            (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_41]) hNN with
    ⟨w', hyTy, hxTy⟩
  have hWidth : w' = w := by
    have hResult :
        SmtType.BitVec w' = SmtType.BitVec w := by
      rw [show
          __smtx_typeof (SmtTerm.bvor (__eo_to_smt y) (__eo_to_smt x)) =
            __smtx_typeof_bv_op_2
              (__smtx_typeof (__eo_to_smt y))
              (__smtx_typeof (__eo_to_smt x)) by
          rw [__smtx_typeof.eq_41]] at hTy'
      simpa [__smtx_typeof_bv_op_2, hyTy, hxTy, native_ite,
        native_nateq, Smtm.native_nateq] using hTy'
    cases hResult
    rfl
  subst w'
  exact ⟨hyTy, hxTy⟩

private theorem bvand_result_type_of_non_none (y x : Term) :
    __smtx_typeof (__eo_to_smt (mkBvAnd y x)) ≠ SmtType.None ->
    ∃ w : native_Nat,
      __smtx_typeof (__eo_to_smt (mkBvAnd y x)) = SmtType.BitVec w ∧
        __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
  intro hNNResult
  have hNN :
      term_has_non_none_type
        (SmtTerm.bvand (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    simpa [mkBvAnd] using hNNResult
  rcases bv_binop_args_of_non_none (op := SmtTerm.bvand)
      (show
        __smtx_typeof (SmtTerm.bvand (__eo_to_smt y) (__eo_to_smt x)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt y))
            (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_40]) hNN with
    ⟨w, hyTy, hxTy⟩
  refine ⟨w, ?_, hyTy, hxTy⟩
  change __smtx_typeof (SmtTerm.bvand (__eo_to_smt y) (__eo_to_smt x)) =
    SmtType.BitVec w
  rw [__smtx_typeof.eq_40]
  simp [__smtx_typeof_bv_op_2, hyTy, hxTy, native_ite, native_nateq,
    Smtm.native_nateq]

private theorem bvor_result_type_of_non_none (y x : Term) :
    __smtx_typeof (__eo_to_smt (mkBvOr y x)) ≠ SmtType.None ->
    ∃ w : native_Nat,
      __smtx_typeof (__eo_to_smt (mkBvOr y x)) = SmtType.BitVec w ∧
        __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
  intro hNNResult
  have hNN :
      term_has_non_none_type
        (SmtTerm.bvor (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    simpa [mkBvOr] using hNNResult
  rcases bv_binop_args_of_non_none (op := SmtTerm.bvor)
      (show
        __smtx_typeof (SmtTerm.bvor (__eo_to_smt y) (__eo_to_smt x)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt y))
            (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_41]) hNN with
    ⟨w, hyTy, hxTy⟩
  refine ⟨w, ?_, hyTy, hxTy⟩
  change __smtx_typeof (SmtTerm.bvor (__eo_to_smt y) (__eo_to_smt x)) =
    SmtType.BitVec w
  rw [__smtx_typeof.eq_41]
  simp [__smtx_typeof_bv_op_2, hyTy, hxTy, native_ite, native_nateq,
    Smtm.native_nateq]

private theorem native_str_in_re_mk_union
    (str : native_String) (r s : SmtRegLan) :
    native_str_in_re str (native_re_mk_union r s) =
      (native_str_in_re str r || native_str_in_re str s) := by
  simp only [← RuleProofs.native_str_in_re_eq_model]
  by_cases hValid : native_string_valid str = true
  · simpa [RuleProofs.native_str_in_re, hValid, RuleProofs.nativeListInRe] using
      RuleProofs.nativeListInRe_mk_union str r s
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [RuleProofs.native_str_in_re, hInvalid]

private theorem native_str_in_re_all (str : native_String)
    (hValid : native_string_valid str = true) :
    native_str_in_re str native_re_all = true := by
  simp only [← RuleProofs.native_str_in_re_eq_model]
  exact RuleProofs.native_str_in_re_re_all str hValid

private theorem bitvec_toInt_emod_pow (w : Nat) (x : BitVec w) :
    x.toInt % (2 ^ w : Int) = x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond]
  by_cases h : 2 * x.toNat < 2 ^ w
  · simp [h]
    exact Int.emod_eq_of_lt (by exact Int.natCast_nonneg _)
      (by exact_mod_cast x.isLt)
  · simp [h]
    exact Int.emod_eq_of_lt (by exact Int.natCast_nonneg _)
      (by exact_mod_cast x.isLt)

private theorem native_int_pow2_nat (w : Nat) :
    native_int_pow2 (native_nat_to_int w) = (2 ^ w : Int) := by
  have h : ¬ (↑w : Int) < 0 := by simp
  simp [native_int_pow2, native_zexp_total, native_nat_to_int, h]

private theorem native_binary_and_mod_eq_toNat
    (w : Nat) (n1 n2 : Int) :
    native_mod_total (native_binary_and (native_nat_to_int w) n1 n2)
        (native_int_pow2 (native_nat_to_int w)) =
      ((BitVec.ofInt w n1 &&& BitVec.ofInt w n2).toNat : Int) := by
  cases w with
  | zero =>
      simp [native_binary_and, native_piand, native_mod_total,
        native_int_pow2_nat]
  | succ w =>
      simp [native_binary_and, native_piand, native_mod_total,
        native_nat_to_int, native_ite, native_zeq]
      exact bitvec_toInt_emod_pow (Nat.succ w)
        (BitVec.ofInt (Nat.succ w) n1 &&& BitVec.ofInt (Nat.succ w) n2)

private theorem native_binary_or_mod_eq_toNat
    (w : Nat) (n1 n2 : Int) :
    native_mod_total (native_binary_or (native_nat_to_int w) n1 n2)
        (native_int_pow2 (native_nat_to_int w)) =
      ((BitVec.ofInt w n1 ||| BitVec.ofInt w n2).toNat : Int) := by
  cases w with
  | zero =>
      simp [native_binary_or, impl_native_pior, native_mod_total,
        native_int_pow2_nat]
  | succ w =>
      simp [native_binary_or, impl_native_pior, native_mod_total,
        native_nat_to_int, native_ite, native_zeq]
      exact bitvec_toInt_emod_pow (Nat.succ w)
        (BitVec.ofInt (Nat.succ w) n1 ||| BitVec.ofInt (Nat.succ w) n2)

private theorem native_pow2_minus_one_mod_self_nat (w : Nat) :
    native_mod_total
        (native_int_pow2 (native_nat_to_int w) - 1)
        (native_int_pow2 (native_nat_to_int w)) =
      native_int_pow2 (native_nat_to_int w) - 1 := by
  rw [native_int_pow2_nat]
  have hPowPos : 0 < (2 ^ w : Int) := by
    exact_mod_cast Nat.two_pow_pos w
  have hLower : 0 <= (2 ^ w : Int) - 1 := by
    omega
  have hUpper : (2 ^ w : Int) - 1 < (2 ^ w : Int) := by
    omega
  simpa [native_mod_total] using Int.emod_eq_of_lt hLower hUpper

private theorem bitvec_ofInt_allOnes (w : Nat) :
    BitVec.ofInt w (native_int_pow2 (native_nat_to_int w) - 1) =
      BitVec.allOnes w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_allOnes, native_int_pow2_nat]
  have hPowPos : 0 < (2 ^ w : Int) := by
    exact_mod_cast Nat.two_pow_pos w
  have hLower : 0 <= (2 ^ w : Int) - 1 := by
    omega
  have hUpper : (2 ^ w : Int) - 1 < (2 ^ w : Int) := by
    omega
  change (((2 ^ w : Int) - 1) % (2 ^ w : Int)).toNat = 2 ^ w - 1
  rw [Int.emod_eq_of_lt hLower hUpper]
  have hToNat :
      (((2 ^ w : Int) - 1).toNat : Int) = (2 ^ w : Int) - 1 :=
    Int.toNat_of_nonneg hLower
  have hRhs :
      ((2 ^ w - 1 : Nat) : Int) = (2 ^ w : Int) - 1 :=
    Int.ofNat_sub Nat.one_le_two_pow
  exact Int.ofNat.inj (hToNat.trans hRhs.symm)

private theorem native_binary_and_left_zero_mod_nat (w : Nat) (n : Int) :
    native_mod_total (native_binary_and (native_nat_to_int w) 0 n)
        (native_int_pow2 (native_nat_to_int w)) = 0 := by
  rw [native_binary_and_mod_eq_toNat]
  simp

private theorem native_binary_and_right_zero_mod_nat (w : Nat) (n : Int) :
    native_mod_total (native_binary_and (native_nat_to_int w) n 0)
        (native_int_pow2 (native_nat_to_int w)) = 0 := by
  rw [native_binary_and_mod_eq_toNat]
  simp

private theorem native_binary_or_left_allOnes_mod_nat (w : Nat) (n : Int) :
    native_mod_total
        (native_binary_or (native_nat_to_int w)
          (native_int_pow2 (native_nat_to_int w) - 1) n)
        (native_int_pow2 (native_nat_to_int w)) =
      native_int_pow2 (native_nat_to_int w) - 1 := by
  rw [native_binary_or_mod_eq_toNat]
  rw [bitvec_ofInt_allOnes, BitVec.allOnes_or, BitVec.toNat_allOnes,
    native_int_pow2_nat]
  exact Int.ofNat_sub Nat.one_le_two_pow

private theorem native_binary_or_right_allOnes_mod_nat (w : Nat) (n : Int) :
    native_mod_total
        (native_binary_or (native_nat_to_int w) n
          (native_int_pow2 (native_nat_to_int w) - 1))
        (native_int_pow2 (native_nat_to_int w)) =
      native_int_pow2 (native_nat_to_int w) - 1 := by
  rw [native_binary_or_mod_eq_toNat]
  rw [bitvec_ofInt_allOnes, BitVec.or_allOnes, BitVec.toNat_allOnes,
    native_int_pow2_nat]
  exact Int.ofNat_sub Nat.one_le_two_pow

private theorem bvZero_to_bin_eq_of_bound (w : Nat) :
    native_zleq (native_nat_to_int w) 4294967296 = true ->
    __eo_to_bin (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0) =
      Term.Binary (native_nat_to_int w) 0 := by
  intro hBound
  have hBoundProp : native_nat_to_int w <= 4294967296 := by
    simpa [native_zleq] using hBound
  have hWidthNonneg : 0 <= native_nat_to_int w := by
    simp [native_nat_to_int]
  simp [__eo_to_bin, __eo_mk_binary, native_ite, native_zleq,
    hBoundProp, hWidthNonneg, native_mod_total]

private theorem bvZero_to_bin_eq_of_ne_stuck (w : Nat) :
    __eo_to_bin (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0) ≠
      Term.Stuck ->
    __eo_to_bin (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0) =
      Term.Binary (native_nat_to_int w) 0 := by
  intro hNe
  by_cases hBound : native_zleq (native_nat_to_int w) 4294967296 = true
  · exact bvZero_to_bin_eq_of_bound w hBound
  · have hStuck :
        __eo_to_bin (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0) =
          Term.Stuck := by
      have hBoundFalse : ¬ native_nat_to_int w <= 4294967296 := by
        simpa [native_zleq] using hBound
      simp [__eo_to_bin, hBoundFalse, native_ite, native_zleq]
    exact False.elim (hNe hStuck)

private theorem bvAllOnes_to_bin_eq_of_ne_stuck (w : Nat) :
    __eo_to_bin (Term.Numeral (native_nat_to_int w))
        (__eo_add
          (__eo_ite (__eo_is_z (Term.Numeral (native_nat_to_int w)))
            (__eo_ite (__eo_is_neg (Term.Numeral (native_nat_to_int w)))
              (Term.Numeral 0)
              (__eo_pow (Term.Numeral 2)
                (Term.Numeral (native_nat_to_int w))))
            (__eo_mk_apply (Term.UOp UserOp.int_pow2)
              (Term.Numeral (native_nat_to_int w))))
          (Term.Numeral (-1 : native_Int))) ≠ Term.Stuck ->
    __eo_to_bin (Term.Numeral (native_nat_to_int w))
        (__eo_add
          (__eo_ite (__eo_is_z (Term.Numeral (native_nat_to_int w)))
            (__eo_ite (__eo_is_neg (Term.Numeral (native_nat_to_int w)))
              (Term.Numeral 0)
              (__eo_pow (Term.Numeral 2)
                (Term.Numeral (native_nat_to_int w))))
            (__eo_mk_apply (Term.UOp UserOp.int_pow2)
              (Term.Numeral (native_nat_to_int w))))
          (Term.Numeral (-1 : native_Int))) =
      Term.Binary (native_nat_to_int w)
        (native_int_pow2 (native_nat_to_int w) - 1) := by
  intro hNe
  have hPayload :
      __eo_add
          (__eo_ite (__eo_is_z (Term.Numeral (native_nat_to_int w)))
            (__eo_ite (__eo_is_neg (Term.Numeral (native_nat_to_int w)))
              (Term.Numeral 0)
              (__eo_pow (Term.Numeral 2)
                (Term.Numeral (native_nat_to_int w))))
            (__eo_mk_apply (Term.UOp UserOp.int_pow2)
              (Term.Numeral (native_nat_to_int w))))
          (Term.Numeral (-1 : native_Int)) =
        Term.Numeral (native_int_pow2 (native_nat_to_int w) - 1) := by
    have hNotNeg : native_zlt (native_nat_to_int w) 0 = false := by
      have hNonneg : ¬native_nat_to_int w < 0 :=
        Int.not_lt.mpr (by simp [native_nat_to_int])
      simp [native_zlt, hNonneg]
    simp [__eo_ite, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
      __eo_pow, __eo_add, native_teq, native_ite,
      native_not, SmtEval.native_not, native_and, hNotNeg, native_int_pow2,
      native_zplus]
    change native_zexp_total 2 (native_nat_to_int w) + (-1 : native_Int) =
      native_zexp_total 2 (native_nat_to_int w) + (-1 : native_Int)
    rfl
  rw [hPayload] at hNe ⊢
  by_cases hBound : native_zleq (native_nat_to_int w) 4294967296 = true
  · have hBoundProp : native_nat_to_int w <= 4294967296 := by
      simpa [native_zleq] using hBound
    have hWidthNonneg : 0 <= native_nat_to_int w := by
      simp [native_nat_to_int]
    simp [__eo_to_bin, __eo_mk_binary, native_ite, native_zleq,
      hBoundProp, hWidthNonneg, native_pow2_minus_one_mod_self_nat]
  · have hStuck :
        __eo_to_bin (Term.Numeral (native_nat_to_int w))
            (Term.Numeral (native_int_pow2 (native_nat_to_int w) - 1)) =
          Term.Stuck := by
      have hBoundFalse : ¬ native_nat_to_int w <= 4294967296 := by
        simpa [native_zleq] using hBound
      simp [__eo_to_bin, hBoundFalse, native_ite, native_zleq]
    exact False.elim (hNe hStuck)

private theorem reUnion_smt_value_rel_left_all_eval
    (M : SmtModel) (x y : Term) (rx ry : SmtRegLan) :
    __smtx_model_eval M (__eo_to_smt x) = SmtValue.RegLan rx ->
    __smtx_model_eval M (__eo_to_smt y) = SmtValue.RegLan ry ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt (Term.UOp UserOp.re_all))) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkReUnion x y)))
      (__smtx_model_eval M (__eo_to_smt (Term.UOp UserOp.re_all))) := by
  intro hxEval hyEval hxRel
  have hAllEval :
      __smtx_model_eval M (__eo_to_smt (Term.UOp UserOp.re_all)) =
        SmtValue.RegLan native_re_all := by
    simp [__smtx_model_eval]
  have hxExt : ∀ str, native_string_valid str = true ->
      native_str_in_re str rx = native_str_in_re str native_re_all := by
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hxRel
    rw [hxEval, hAllEval] at hxRel
    simpa [__smtx_model_eval_eq] using hxRel
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt x) (__eo_to_smt y)))
      (__smtx_model_eval M SmtTerm.re_all) =
    SmtValue.Boolean true
  simp only [__smtx_model_eval, __smtx_model_eval_re_union, hxEval,
    hyEval]
  simp [__smtx_model_eval_eq, native_str_in_re_mk_union]
  intro str hValid
  rw [hxExt str hValid, native_str_in_re_all str hValid]
  simp

private theorem reUnion_smt_value_rel_right_all_eval
    (M : SmtModel) (x y : Term) (rx ry : SmtRegLan) :
    __smtx_model_eval M (__eo_to_smt x) = SmtValue.RegLan rx ->
    __smtx_model_eval M (__eo_to_smt y) = SmtValue.RegLan ry ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt (Term.UOp UserOp.re_all))) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkReUnion x y)))
      (__smtx_model_eval M (__eo_to_smt (Term.UOp UserOp.re_all))) := by
  intro hxEval hyEval hyRel
  have hAllEval :
      __smtx_model_eval M (__eo_to_smt (Term.UOp UserOp.re_all)) =
        SmtValue.RegLan native_re_all := by
    simp [__smtx_model_eval]
  have hyExt : ∀ str, native_string_valid str = true ->
      native_str_in_re str ry = native_str_in_re str native_re_all := by
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hyRel
    rw [hyEval, hAllEval] at hyRel
    simpa [__smtx_model_eval_eq] using hyRel
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt x) (__eo_to_smt y)))
      (__smtx_model_eval M SmtTerm.re_all) =
    SmtValue.Boolean true
  simp only [__smtx_model_eval, __smtx_model_eval_re_union, hxEval,
    hyEval]
  simp [__smtx_model_eval_eq, native_str_in_re_mk_union]
  intro str hValid
  rw [hyExt str hValid, native_str_in_re_all str hValid]
  simp

private theorem absorbTree_re_union_all
    (M : SmtModel) (hM : model_wf M) :
    ∀ {t : Term},
      AbsorbTree (Term.UOp UserOp.re_union) (Term.UOp UserOp.re_all) t ->
      __smtx_typeof (__eo_to_smt t) = SmtType.RegLan ->
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt t))
        (__smtx_model_eval M (__eo_to_smt (Term.UOp UserOp.re_all))) := by
  intro t hTree
  induction hTree with
  | here =>
      intro _hTy
      exact RuleProofs.smt_value_rel_refl _
  | left a b _ ih =>
      intro hTy
      rcases reUnion_args_of_reglan_type a b hTy with ⟨haTy, hbTy⟩
      rcases smt_eval_reglan_of_smt_type_reglan M hM (__eo_to_smt a)
          haTy with ⟨ra, haEval⟩
      rcases smt_eval_reglan_of_smt_type_reglan M hM (__eo_to_smt b)
          hbTy with ⟨rb, hbEval⟩
      exact reUnion_smt_value_rel_left_all_eval M a b ra rb
        haEval hbEval (ih haTy)
  | right a b _ ih =>
      intro hTy
      rcases reUnion_args_of_reglan_type a b hTy with ⟨haTy, hbTy⟩
      rcases smt_eval_reglan_of_smt_type_reglan M hM (__eo_to_smt a)
          haTy with ⟨ra, haEval⟩
      rcases smt_eval_reglan_of_smt_type_reglan M hM (__eo_to_smt b)
          hbTy with ⟨rb, hbEval⟩
      exact reUnion_smt_value_rel_right_all_eval M a b ra rb
        haEval hbEval (ih hbTy)

private theorem absorbTree_re_inter_none_eval
    (M : SmtModel) (hM : model_wf M) :
    ∀ {t : Term},
      AbsorbTree (Term.UOp UserOp.re_inter) (Term.UOp UserOp.re_none) t ->
      __smtx_typeof (__eo_to_smt t) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt t) =
        SmtValue.RegLan native_re_none := by
  intro t hTree
  induction hTree with
  | here =>
      intro _hTy
      simp [__smtx_model_eval]
  | left a b _ ih =>
      intro hTy
      rcases reInter_args_of_reglan_type a b hTy with ⟨haTy, hbTy⟩
      rcases smt_eval_reglan_of_smt_type_reglan M hM (__eo_to_smt b)
          hbTy with ⟨rb, hbEval⟩
      have haEval := ih haTy
      change __smtx_model_eval M
          (SmtTerm.re_inter (__eo_to_smt a) (__eo_to_smt b)) =
        SmtValue.RegLan native_re_none
      simp only [__smtx_model_eval, __smtx_model_eval_re_inter, haEval,
        hbEval]
      cases rb <;> rfl
  | right a b _ ih =>
      intro hTy
      rcases reInter_args_of_reglan_type a b hTy with ⟨haTy, hbTy⟩
      rcases smt_eval_reglan_of_smt_type_reglan M hM (__eo_to_smt a)
          haTy with ⟨ra, haEval⟩
      have hbEval := ih hbTy
      change __smtx_model_eval M
          (SmtTerm.re_inter (__eo_to_smt a) (__eo_to_smt b)) =
        SmtValue.RegLan native_re_none
      simp only [__smtx_model_eval, __smtx_model_eval_re_inter, haEval,
        hbEval]
      cases ra <;> rfl

private theorem absorbTree_re_concat_none_eval
    (M : SmtModel) (hM : model_wf M) :
    ∀ {t : Term},
      AbsorbTree (Term.UOp UserOp.re_concat) (Term.UOp UserOp.re_none) t ->
      __smtx_typeof (__eo_to_smt t) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt t) =
        SmtValue.RegLan native_re_none := by
  intro t hTree
  induction hTree with
  | here =>
      intro _hTy
      simp [__smtx_model_eval]
  | left a b _ ih =>
      intro hTy
      rcases reConcat_args_of_reglan_type a b hTy with ⟨haTy, hbTy⟩
      rcases smt_eval_reglan_of_smt_type_reglan M hM (__eo_to_smt b)
          hbTy with ⟨rb, hbEval⟩
      have haEval := ih haTy
      change __smtx_model_eval M
          (SmtTerm.re_concat (__eo_to_smt a) (__eo_to_smt b)) =
        SmtValue.RegLan native_re_none
      simp only [__smtx_model_eval, __smtx_model_eval_re_concat, haEval,
        hbEval]
      cases rb <;> rfl
  | right a b _ ih =>
      intro hTy
      rcases reConcat_args_of_reglan_type a b hTy with ⟨haTy, hbTy⟩
      rcases smt_eval_reglan_of_smt_type_reglan M hM (__eo_to_smt a)
          haTy with ⟨ra, haEval⟩
      have hbEval := ih hbTy
      change __smtx_model_eval M
          (SmtTerm.re_concat (__eo_to_smt a) (__eo_to_smt b)) =
        SmtValue.RegLan native_re_none
      simp only [__smtx_model_eval, __smtx_model_eval_re_concat, haEval,
        hbEval]
      cases ra <;> rfl

private theorem absorbTree_bvand_zero_eval
    (M : SmtModel) (hM : model_wf M) :
    ∀ {t : Term} {w : native_Nat},
      AbsorbTree (Term.UOp UserOp.bvand)
        (Term.Binary (native_nat_to_int w) 0) t ->
      __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
      __smtx_model_eval M (__eo_to_smt t) =
        SmtValue.Binary (native_nat_to_int w) 0 := by
  intro t w hTree
  induction hTree with
  | here =>
      intro _hTy
      rw [show
        __eo_to_smt (Term.Binary (native_nat_to_int w) 0) =
          SmtTerm.Binary (native_nat_to_int w) 0 by rfl]
      rw [__smtx_model_eval]
  | left a b _ ih =>
      intro hTy
      rcases bvand_args_of_bitvec_type a b w hTy with ⟨haTy, hbTy⟩
      rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt b) w
          hbTy with ⟨nb, hbEval⟩
      have haEval := ih haTy
      change __smtx_model_eval M
          (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)) =
        SmtValue.Binary (native_nat_to_int w) 0
      simp only [__smtx_model_eval, __smtx_model_eval_bvand, haEval,
        hbEval]
      rw [native_binary_and_left_zero_mod_nat w nb]
  | right a b _ ih =>
      intro hTy
      rcases bvand_args_of_bitvec_type a b w hTy with ⟨haTy, hbTy⟩
      rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt a) w
          haTy with ⟨na, haEval⟩
      have hbEval := ih hbTy
      change __smtx_model_eval M
          (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)) =
        SmtValue.Binary (native_nat_to_int w) 0
      simp only [__smtx_model_eval, __smtx_model_eval_bvand, haEval,
        hbEval]
      rw [native_binary_and_right_zero_mod_nat w na]

private theorem absorbTree_bvor_allOnes_eval
    (M : SmtModel) (hM : model_wf M) :
    ∀ {t : Term} {w : native_Nat},
      AbsorbTree (Term.UOp UserOp.bvor)
        (Term.Binary (native_nat_to_int w)
          (native_int_pow2 (native_nat_to_int w) - 1)) t ->
      __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
      __smtx_model_eval M (__eo_to_smt t) =
        SmtValue.Binary (native_nat_to_int w)
          (native_int_pow2 (native_nat_to_int w) - 1) := by
  intro t w hTree
  induction hTree with
  | here =>
      intro _hTy
      rw [show
        __eo_to_smt
            (Term.Binary (native_nat_to_int w)
              (native_int_pow2 (native_nat_to_int w) - 1)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_int_pow2 (native_nat_to_int w) - 1) by rfl]
      rw [__smtx_model_eval]
  | left a b _ ih =>
      intro hTy
      rcases bvor_args_of_bitvec_type a b w hTy with ⟨haTy, hbTy⟩
      rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt b) w
          hbTy with ⟨nb, hbEval⟩
      have haEval := ih haTy
      change __smtx_model_eval M
          (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)) =
        SmtValue.Binary (native_nat_to_int w)
          (native_int_pow2 (native_nat_to_int w) - 1)
      simp only [__smtx_model_eval, __smtx_model_eval_bvor, haEval,
        hbEval]
      rw [native_binary_or_left_allOnes_mod_nat w nb]
  | right a b _ ih =>
      intro hTy
      rcases bvor_args_of_bitvec_type a b w hTy with ⟨haTy, hbTy⟩
      rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt a) w
          haTy with ⟨na, haEval⟩
      have hbEval := ih hbTy
      change __smtx_model_eval M
          (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)) =
        SmtValue.Binary (native_nat_to_int w)
          (native_int_pow2 (native_nat_to_int w) - 1)
      simp only [__smtx_model_eval, __smtx_model_eval_bvor, haEval,
        hbEval]
      rw [native_binary_or_right_allOnes_mod_nat w na]

private theorem eo_prog_absorb_guards_of_type_bool (t zero : Term) :
    __eo_typeof
      (__eo_prog_absorb
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) zero)) = Term.Bool ->
    __get_zero t = zero ∧ __is_absorb t zero = Term.Boolean true := by
  intro hTy
  have hReq :
      __eo_requires (__get_zero t) zero
        (__eo_requires (__is_absorb t zero) (Term.Boolean true)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) zero)) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  have hReqBody :
      __eo_requires (__is_absorb t zero) (Term.Boolean true)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) zero) ≠ Term.Stuck :=
    eo_requires_body_ne_stuck_of_ne_stuck _ _ _ hReq
  exact ⟨eo_requires_eq_of_ne_stuck _ _ _ hReq,
    eo_requires_eq_of_ne_stuck _ _ _ hReqBody⟩

private theorem eo_has_type_of_eq_left_const
    (x y : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
    __smtx_typeof (__eo_to_smt y) = SmtType.Bool ->
    RuleProofs.eo_has_bool_type x := by
  intro hEq hY
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type x y hEq with
    ⟨hSame, _⟩
  unfold RuleProofs.eo_has_bool_type
  rw [hSame, hY]

private theorem eo_prog_absorb_eq_input_of_type_bool (a1 : Term) :
    __eo_typeof (__eo_prog_absorb a1) = Term.Bool ->
    __eo_prog_absorb a1 = a1 := by
  intro hTy
  cases a1
  all_goals try
    have hStuck : __eo_typeof Term.Stuck = Term.Bool := by
      simpa [__eo_prog_absorb] using hTy
    exact False.elim (eo_typeof_stuck_ne_bool hStuck)
  case Apply f zero =>
    cases f
    all_goals try
      have hStuck : __eo_typeof Term.Stuck = Term.Bool := by
        simpa [__eo_prog_absorb] using hTy
      exact False.elim (eo_typeof_stuck_ne_bool hStuck)
    case Apply g t =>
      cases g
      all_goals try
        have hStuck : __eo_typeof Term.Stuck = Term.Bool := by
          simpa [__eo_prog_absorb] using hTy
        exact False.elim (eo_typeof_stuck_ne_bool hStuck)
      case UOp op =>
        cases op <;> simp [__eo_prog_absorb] at hTy ⊢
        case eq =>
          have hReq :
              __eo_requires (__get_zero t) zero
                (__eo_requires (__is_absorb t zero) (Term.Boolean true)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) zero)) ≠ Term.Stuck :=
            term_ne_stuck_of_typeof_bool hTy
          have hReqBody :
              __eo_requires (__is_absorb t zero) (Term.Boolean true)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) zero) ≠ Term.Stuck :=
            eo_requires_body_ne_stuck_of_ne_stuck _ _ _ hReq
          rw [eo_requires_result_eq_of_ne_stuck _ _ _ hReq]
          exact eo_requires_result_eq_of_ne_stuck _ _ _ hReqBody
        all_goals
          exact False.elim (eo_typeof_stuck_ne_bool hTy)

private theorem eo_absorb_eq_interprets_true_of_guards
    (M : SmtModel) (hM : model_wf M) (t zero : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) zero) ->
    __get_zero t = zero ->
    __is_absorb t zero = Term.Boolean true ->
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) zero) true := by
  intro hEqBool hGet hAbs
  cases t
  case Apply tf b =>
    cases tf
    case Apply head a =>
      cases head
      case UOp topOp =>
        have hGet' :
            __get_zero
              (Term.Apply (Term.Apply (Term.UOp topOp) a) b) = zero :=
          hGet
        have hAbs' :
            __is_absorb
              (Term.Apply (Term.Apply (Term.UOp topOp) a) b) zero =
                Term.Boolean true :=
          hAbs
        clear hGet hAbs
        cases topOp <;> simp [__get_zero] at hGet'
        case or =>
          subst zero
          have hTree :
              AbsorbTree (Term.UOp UserOp.or) (Term.Boolean true)
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) :=
            absorbTree_of_is_absorb_rec_eq_true
              (Term.UOp UserOp.or) (Term.Boolean true)
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b)
              (by decide) (by decide) (by
                simpa [__is_absorb] using hAbs')
          have hTBool :
              RuleProofs.eo_has_bool_type
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) :=
            eo_has_type_of_eq_left_const
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b)
              (Term.Boolean true) hEqBool (by native_decide)
          exact RuleProofs.eo_interprets_eq_of_rel M
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b)
            (Term.Boolean true) hEqBool
            (smt_value_rel_of_eo_interprets_bool_const M
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) true
              (absorbTree_or_true M hM hTree hTBool))
        case and =>
          subst zero
          have hTree :
              AbsorbTree (Term.UOp UserOp.and) (Term.Boolean false)
                (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) :=
            absorbTree_of_is_absorb_rec_eq_true
              (Term.UOp UserOp.and) (Term.Boolean false)
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b)
              (by decide) (by decide) (by
                simpa [__is_absorb] using hAbs')
          have hTBool :
              RuleProofs.eo_has_bool_type
                (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) :=
            eo_has_type_of_eq_left_const
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b)
              (Term.Boolean false) hEqBool (by native_decide)
          exact RuleProofs.eo_interprets_eq_of_rel M
            (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b)
            (Term.Boolean false) hEqBool
            (smt_value_rel_of_eo_interprets_bool_const M
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) false
              (absorbTree_and_false M hM hTree hTBool))
        case re_concat =>
          subst zero
          have hTree :
              AbsorbTree (Term.UOp UserOp.re_concat)
                (Term.UOp UserOp.re_none) (mkReConcat a b) :=
            absorbTree_of_is_absorb_rec_eq_true
              (Term.UOp UserOp.re_concat) (Term.UOp UserOp.re_none)
              (mkReConcat a b) (by decide) (by decide) (by
                simpa [mkReConcat, __is_absorb] using hAbs')
          have hTTy :
              __smtx_typeof (__eo_to_smt (mkReConcat a b)) =
                SmtType.RegLan := by
            rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                (mkReConcat a b) (Term.UOp UserOp.re_none) hEqBool with
              ⟨hSameTy, _⟩
            have hConstTy :
                __smtx_typeof (__eo_to_smt (Term.UOp UserOp.re_none)) =
                  SmtType.RegLan := by
              native_decide
            rw [hSameTy, hConstTy]
          have hEval := absorbTree_re_concat_none_eval M hM hTree hTTy
          have hRel :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M (__eo_to_smt (mkReConcat a b)))
                (__smtx_model_eval M
                  (__eo_to_smt (Term.UOp UserOp.re_none))) := by
            rw [hEval]
            change RuleProofs.smt_value_rel
              (SmtValue.RegLan native_re_none)
              (__smtx_model_eval M SmtTerm.re_none)
            rw [__smtx_model_eval]
            exact RuleProofs.smt_value_rel_refl _
          exact RuleProofs.eo_interprets_eq_of_rel M
            (mkReConcat a b) (Term.UOp UserOp.re_none) hEqBool hRel
        case re_inter =>
          subst zero
          have hTree :
              AbsorbTree (Term.UOp UserOp.re_inter)
                (Term.UOp UserOp.re_none) (mkReInter a b) :=
            absorbTree_of_is_absorb_rec_eq_true
              (Term.UOp UserOp.re_inter) (Term.UOp UserOp.re_none)
              (mkReInter a b) (by decide) (by decide) (by
                simpa [mkReInter, __is_absorb] using hAbs')
          have hTTy :
              __smtx_typeof (__eo_to_smt (mkReInter a b)) =
                SmtType.RegLan := by
            rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                (mkReInter a b) (Term.UOp UserOp.re_none) hEqBool with
              ⟨hSameTy, _⟩
            have hConstTy :
                __smtx_typeof (__eo_to_smt (Term.UOp UserOp.re_none)) =
                  SmtType.RegLan := by
              native_decide
            rw [hSameTy, hConstTy]
          have hEval := absorbTree_re_inter_none_eval M hM hTree hTTy
          have hRel :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M (__eo_to_smt (mkReInter a b)))
                (__smtx_model_eval M
                  (__eo_to_smt (Term.UOp UserOp.re_none))) := by
            rw [hEval]
            change RuleProofs.smt_value_rel
              (SmtValue.RegLan native_re_none)
              (__smtx_model_eval M SmtTerm.re_none)
            rw [__smtx_model_eval]
            exact RuleProofs.smt_value_rel_refl _
          exact RuleProofs.eo_interprets_eq_of_rel M
            (mkReInter a b) (Term.UOp UserOp.re_none) hEqBool hRel
        case re_union =>
          subst zero
          have hTree :
              AbsorbTree (Term.UOp UserOp.re_union)
                (Term.UOp UserOp.re_all) (mkReUnion a b) :=
            absorbTree_of_is_absorb_rec_eq_true
              (Term.UOp UserOp.re_union) (Term.UOp UserOp.re_all)
              (mkReUnion a b) (by decide) (by decide) (by
                simpa [mkReUnion, __is_absorb] using hAbs')
          have hTTy :
              __smtx_typeof (__eo_to_smt (mkReUnion a b)) =
                SmtType.RegLan := by
            rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                (mkReUnion a b) (Term.UOp UserOp.re_all) hEqBool with
              ⟨hSameTy, _⟩
            have hConstTy :
                __smtx_typeof (__eo_to_smt (Term.UOp UserOp.re_all)) =
                  SmtType.RegLan := by
              native_decide
            rw [hSameTy, hConstTy]
          exact RuleProofs.eo_interprets_eq_of_rel M
            (mkReUnion a b) (Term.UOp UserOp.re_all) hEqBool
            (absorbTree_re_union_all M hM hTree hTTy)
        case bvand =>
          rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
              (mkBvAnd a b) zero hEqBool with
            ⟨hSameTy, hTNonNone⟩
          rcases bvand_result_type_of_non_none a b hTNonNone with
            ⟨w, hTTy, haTy, _hbTy⟩
          have hATypeMatch :
              __smtx_typeof (__eo_to_smt a) =
                __eo_to_smt_type (__eo_typeof a) :=
            TranslationProofs.eo_to_smt_typeof_matches_translation a (by
              rw [haTy]
              exact smt_bitvec_ne_none w)
          have hATypeBitVec :
              __eo_to_smt_type (__eo_typeof a) = SmtType.BitVec w := by
            rw [← hATypeMatch, haTy]
          have hEoTy :
              __eo_typeof a =
                Term.Apply (Term.UOp UserOp.BitVec)
                  (Term.Numeral (native_nat_to_int w)) :=
            TranslationProofs.eo_to_smt_type_eq_bitvec hATypeBitVec
          have hZeroTrans :
              RuleProofs.eo_has_smt_translation zero := by
            unfold RuleProofs.eo_has_smt_translation
            intro hNone
            exact hTNonNone (by
              rw [hSameTy, hNone])
          have hZeroNe : zero ≠ Term.Stuck :=
            RuleProofs.term_ne_stuck_of_has_smt_translation zero hZeroTrans
          have hZeroEq :
              zero = Term.Binary (native_nat_to_int w) 0 := by
            have hExpr :
                __eo_to_bin (Term.Numeral (native_nat_to_int w))
                    (Term.Numeral 0) =
                  zero := by
              simpa [mkBvAnd, __get_zero, hEoTy, __bv_bitwidth]
                using hGet'
            rw [← hExpr]
            exact bvZero_to_bin_eq_of_ne_stuck w (by
              rw [hExpr]
              exact hZeroNe)
          clear hGet'
          subst zero
          have hTree :
              AbsorbTree (Term.UOp UserOp.bvand)
                (Term.Binary (native_nat_to_int w) 0) (mkBvAnd a b) :=
            absorbTree_of_is_absorb_rec_eq_true
              (Term.UOp UserOp.bvand)
              (Term.Binary (native_nat_to_int w) 0)
              (mkBvAnd a b) (by decide) (by
                intro h
                cases h) (by
                simpa [mkBvAnd, __is_absorb] using hAbs')
          have hEval := absorbTree_bvand_zero_eval M hM hTree hTTy
          have hRel :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M (__eo_to_smt (mkBvAnd a b)))
                (__smtx_model_eval M
                  (__eo_to_smt (Term.Binary (native_nat_to_int w) 0))) := by
            rw [hEval]
            change RuleProofs.smt_value_rel
              (SmtValue.Binary (native_nat_to_int w) 0)
              (__smtx_model_eval M
                (SmtTerm.Binary (native_nat_to_int w) 0))
            rw [__smtx_model_eval]
            exact RuleProofs.smt_value_rel_refl _
          exact RuleProofs.eo_interprets_eq_of_rel M
            (mkBvAnd a b) (Term.Binary (native_nat_to_int w) 0)
            hEqBool hRel
        case bvor =>
          rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
              (mkBvOr a b) zero hEqBool with
            ⟨hSameTy, hTNonNone⟩
          rcases bvor_result_type_of_non_none a b hTNonNone with
            ⟨w, hTTy, haTy, _hbTy⟩
          have hATypeMatch :
              __smtx_typeof (__eo_to_smt a) =
                __eo_to_smt_type (__eo_typeof a) :=
            TranslationProofs.eo_to_smt_typeof_matches_translation a (by
              rw [haTy]
              exact smt_bitvec_ne_none w)
          have hATypeBitVec :
              __eo_to_smt_type (__eo_typeof a) = SmtType.BitVec w := by
            rw [← hATypeMatch, haTy]
          have hEoTy :
              __eo_typeof a =
                Term.Apply (Term.UOp UserOp.BitVec)
                  (Term.Numeral (native_nat_to_int w)) :=
            TranslationProofs.eo_to_smt_type_eq_bitvec hATypeBitVec
          have hZeroTrans :
              RuleProofs.eo_has_smt_translation zero := by
            unfold RuleProofs.eo_has_smt_translation
            intro hNone
            exact hTNonNone (by
              rw [hSameTy, hNone])
          have hZeroNe : zero ≠ Term.Stuck :=
            RuleProofs.term_ne_stuck_of_has_smt_translation zero hZeroTrans
          have hZeroEq :
              zero = Term.Binary (native_nat_to_int w)
                (native_int_pow2 (native_nat_to_int w) - 1) := by
            have hExpr :
                __eo_to_bin (Term.Numeral (native_nat_to_int w))
                    (__eo_add
                      (__eo_ite
                        (__eo_is_z
                          (Term.Numeral (native_nat_to_int w)))
                        (__eo_ite
                          (__eo_is_neg
                            (Term.Numeral (native_nat_to_int w)))
                          (Term.Numeral 0)
                          (__eo_pow (Term.Numeral 2)
                            (Term.Numeral (native_nat_to_int w))))
                        (__eo_mk_apply (Term.UOp UserOp.int_pow2)
                          (Term.Numeral (native_nat_to_int w))))
                      (Term.Numeral (-1 : native_Int))) =
                  zero := by
              simpa [mkBvOr, __get_zero, hEoTy, __bv_bitwidth]
                using hGet'
            rw [← hExpr]
            exact bvAllOnes_to_bin_eq_of_ne_stuck w (by
              rw [hExpr]
              exact hZeroNe)
          clear hGet'
          subst zero
          have hTree :
              AbsorbTree (Term.UOp UserOp.bvor)
                (Term.Binary (native_nat_to_int w)
                  (native_int_pow2 (native_nat_to_int w) - 1))
                (mkBvOr a b) :=
            absorbTree_of_is_absorb_rec_eq_true
              (Term.UOp UserOp.bvor)
              (Term.Binary (native_nat_to_int w)
                (native_int_pow2 (native_nat_to_int w) - 1))
              (mkBvOr a b) (by decide) (by
                intro h
                cases h) (by
                simpa [mkBvOr, __is_absorb] using hAbs')
          have hEval := absorbTree_bvor_allOnes_eval M hM hTree hTTy
          have hRel :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M (__eo_to_smt (mkBvOr a b)))
                (__smtx_model_eval M
                  (__eo_to_smt
                    (Term.Binary (native_nat_to_int w)
                      (native_int_pow2 (native_nat_to_int w) - 1)))) := by
            rw [hEval]
            change RuleProofs.smt_value_rel
              (SmtValue.Binary (native_nat_to_int w)
                (native_int_pow2 (native_nat_to_int w) - 1))
              (__smtx_model_eval M
                (SmtTerm.Binary (native_nat_to_int w)
                  (native_int_pow2 (native_nat_to_int w) - 1)))
            rw [__smtx_model_eval]
            exact RuleProofs.smt_value_rel_refl _
          exact RuleProofs.eo_interprets_eq_of_rel M
            (mkBvOr a b)
            (Term.Binary (native_nat_to_int w)
              (native_int_pow2 (native_nat_to_int w) - 1))
            hEqBool hRel
        all_goals
          subst zero
          simp [__is_absorb] at hAbs'
      all_goals
        simp [__get_zero] at hGet
        subst zero
        simp [__is_absorb] at hAbs
    all_goals
      simp [__get_zero] at hGet
      subst zero
      simp [__is_absorb] at hAbs
  all_goals
    simp [__get_zero] at hGet
    subst zero
    simp [__is_absorb] at hAbs

private theorem eo_prog_absorb_interprets_true
    (M : SmtModel) (hM : model_wf M) (a1 : Term) :
    RuleProofs.eo_has_smt_translation a1 ->
    __eo_typeof (__eo_prog_absorb a1) = Term.Bool ->
    eo_interprets M (__eo_prog_absorb a1) true := by
  intro hA1Trans hResultTy
  have hProgEq : __eo_prog_absorb a1 = a1 :=
    eo_prog_absorb_eq_input_of_type_bool a1 hResultTy
  have hA1Type : __eo_typeof a1 = Term.Bool := by
    simpa [hProgEq] using hResultTy
  have hA1Bool : RuleProofs.eo_has_bool_type a1 :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hA1Trans hA1Type
  rw [hProgEq]
  cases a1
  all_goals try
    have hStuck : __eo_typeof Term.Stuck = Term.Bool := by
      simpa [__eo_prog_absorb] using hResultTy
    exact False.elim (eo_typeof_stuck_ne_bool hStuck)
  case Apply f zero =>
    cases f
    all_goals try
      have hStuck : __eo_typeof Term.Stuck = Term.Bool := by
        simpa [__eo_prog_absorb] using hResultTy
      exact False.elim (eo_typeof_stuck_ne_bool hStuck)
    case Apply g t =>
      cases g
      all_goals try
        have hStuck : __eo_typeof Term.Stuck = Term.Bool := by
          simpa [__eo_prog_absorb] using hResultTy
        exact False.elim (eo_typeof_stuck_ne_bool hStuck)
      case UOp op =>
        cases op <;> simp [__eo_prog_absorb] at hResultTy
        case eq =>
          have hGuards := eo_prog_absorb_guards_of_type_bool t zero hResultTy
          exact eo_absorb_eq_interprets_true_of_guards M hM t zero
            hA1Bool hGuards.1 hGuards.2
        all_goals
          exact False.elim (eo_typeof_stuck_ne_bool hResultTy)

public theorem cmd_step_absorb_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.absorb args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.absorb args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.absorb args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.absorb args premises ≠ Term.Stuck :=
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
              have hArgsTrans :
                  cArgListTranslationOk (CArgList.cons a1 CArgList.nil) := by
                simpa [cmdTranslationOk] using hCmdTrans
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cArgListTranslationOk] using hArgsTrans
              change __eo_typeof (__eo_prog_absorb a1) = Term.Bool at hResultTy
              have hProgEq : __eo_prog_absorb a1 = a1 :=
                eo_prog_absorb_eq_input_of_type_bool a1 hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                exact eo_prog_absorb_interprets_true M hM a1 hA1Trans
                  hResultTy
              · change RuleProofs.eo_has_smt_translation (__eo_prog_absorb a1)
                rw [hProgEq]
                exact hA1Trans
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
