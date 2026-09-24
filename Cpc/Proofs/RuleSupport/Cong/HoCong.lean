module

public import Cpc.Proofs.RuleSupport.Cong.ValueRel
import all Cpc.Proofs.RuleSupport.Cong.ValueRel

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace CongSupport

attribute [local simp] native_streq native_and native_ite

private inductive HoAppSpine (base : Term) : Term -> Prop where
  | base : HoAppSpine base base
  | app {f x : Term} :
      HoAppSpine base f ->
      HoAppSpine base (Term.Apply f x)

private theorem eo_typeof_apply_head_ne_stuck {F X : Term} :
    __eo_typeof_apply F X ≠ Term.Stuck ->
    F ≠ Term.Stuck := by
  intro h hF
  subst F
  cases X <;> simp [__eo_typeof_apply] at h

private theorem hoAppSpine_raw_uop_none_false
    (base : Term) (op : UserOp) :
    (__smtx_typeof (__eo_to_smt (Term.UOp op)) = SmtType.None) ->
    RuleProofs.eo_has_smt_translation base ->
    HoAppSpine base (Term.UOp op) ->
    False := by
  intro hNone hBase hSpine
  cases hSpine with
  | base =>
      exact hBase hNone

private theorem hoAppSpine_raw_funtype_false
    (base : Term) :
    RuleProofs.eo_has_smt_translation base ->
    HoAppSpine base Term.FunType ->
    False := by
  intro hBase hSpine
  cases hSpine with
  | base =>
      exact hBase (by
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none)

private theorem hoAppSpine_partial_uop_false
    (base : Term) (op : UserOp) (x : Term) :
    (__smtx_typeof (__eo_to_smt (Term.UOp op)) = SmtType.None) ->
    (__smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) x)) =
      SmtType.None) ->
    RuleProofs.eo_has_smt_translation base ->
    HoAppSpine base (Term.Apply (Term.UOp op) x) ->
    False := by
  intro hRawNone hNone hBase hSpine
  cases hSpine with
  | base =>
      exact hBase hNone
  | app hPrev =>
      exact hoAppSpine_raw_uop_none_false base op hRawNone hBase hPrev

private theorem hoAppSpine_binary_uop_false
    (base : Term) (op : UserOp) (x y : Term) :
    (__smtx_typeof (__eo_to_smt (Term.UOp op)) = SmtType.None) ->
    (__smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) x)) =
      SmtType.None) ->
    (__smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)) =
      SmtType.None) ->
    RuleProofs.eo_has_smt_translation base ->
    HoAppSpine base (Term.Apply (Term.Apply (Term.UOp op) x) y) ->
    False := by
  intro hRawNone hUnaryNone hNone hBase hSpine
  cases hSpine with
  | base =>
      exact hBase hNone
  | app hPrev =>
      exact hoAppSpine_partial_uop_false
        base op x hRawNone hUnaryNone hBase hPrev

private theorem hoAppSpine_typeof_apply_eq
    (base f x : Term)
    (hBase : RuleProofs.eo_has_smt_translation base)
    (hSpine : HoAppSpine base f) :
    __eo_typeof (Term.Apply f x) =
      __eo_typeof_apply (__eo_typeof f) (__eo_typeof x) := by
  induction hSpine generalizing x with
  | base =>
      exact eo_typeof_apply_eq_of_has_smt_translation base x hBase
  | app hPrev ih =>
      rename_i p y
      cases p <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        all_goals
          exact False.elim (hoAppSpine_raw_uop_none_false base _ (by
            change __smtx_typeof SmtTerm.None = SmtType.None
            exact TranslationProofs.smtx_typeof_none) hBase hPrev)
      case UOp1 op idx =>
        cases op <;> try rfl
        all_goals
          exact False.elim (by
            cases hPrev with
            | base =>
                exact hBase (by
                  change __smtx_typeof SmtTerm.None = SmtType.None
                  exact TranslationProofs.smtx_typeof_none))
      case FunType =>
        exact False.elim (hoAppSpine_raw_funtype_false base hBase hPrev)
      case Apply p₁ p₂ =>
        cases p₁ <;> try rfl
        case UOp op =>
          cases op <;> try rfl
          all_goals
            exact False.elim (hoAppSpine_partial_uop_false base _ p₂ (by
              change __smtx_typeof SmtTerm.None = SmtType.None
              exact TranslationProofs.smtx_typeof_none) (by
              change
                __smtx_typeof
                    (SmtTerm.Apply SmtTerm.None (__eo_to_smt p₂)) =
                  SmtType.None
              simp [__smtx_typeof, __smtx_typeof_apply]) hBase hPrev)
        case Apply p₀ p₃ =>
          cases p₀ <;> try rfl
          case UOp op =>
            cases op <;> try rfl
            all_goals
              exact False.elim (hoAppSpine_binary_uop_false
                base _ p₃ p₂
                (by
                  change __smtx_typeof SmtTerm.None = SmtType.None
                  exact TranslationProofs.smtx_typeof_none)
                (by
                  change
                    __smtx_typeof
                        (SmtTerm.Apply SmtTerm.None (__eo_to_smt p₃)) =
                      SmtType.None
                  simp [__smtx_typeof, __smtx_typeof_apply])
                (by
                  change
                    __smtx_typeof
                        (SmtTerm.Apply
                          (SmtTerm.Apply SmtTerm.None (__eo_to_smt p₃))
                          (__eo_to_smt p₂)) =
                      SmtType.None
                  simp [__smtx_typeof, __smtx_typeof_apply])
                hBase hPrev)

theorem eo_apply_apply_head_has_translation_of_generic_apply_translation
    (f z x : Term)
    (hToSmt :
      __eo_to_smt ((Term.Apply f z).Apply x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply f z)) (__eo_to_smt x)) :
    RuleProofs.eo_has_smt_translation ((Term.Apply f z).Apply x) ->
    RuleProofs.eo_has_smt_translation (Term.Apply f z) := by
  intro hTrans
  unfold RuleProofs.eo_has_smt_translation at hTrans ⊢
  have hGen :
      generic_apply_type (__eo_to_smt (Term.Apply f z)) (__eo_to_smt x) :=
    generic_apply_type_of_non_datatype_head
      (TranslationProofs.eo_to_smt_apply_ne_dt_sel f z)
      (TranslationProofs.eo_to_smt_apply_ne_dt_tester f z)
  have hAppNN :
      __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply f z)))
          (__smtx_typeof (__eo_to_smt x)) ≠ SmtType.None := by
    rw [hToSmt, hGen] at hTrans
    exact hTrans
  exact smt_apply_head_non_none_of_apply_non_none hAppNN

theorem congTypeSpine_generic_apply_eq_has_bool_type
    (f g x y : Term)
    (hTrans : RuleProofs.eo_has_smt_translation (Term.Apply f x))
    (hToSmtF :
      __eo_to_smt (Term.Apply f x) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))
    (hToSmtG :
      __eo_to_smt (Term.Apply g y) =
        SmtTerm.Apply (__eo_to_smt g) (__eo_to_smt y))
    (hGenF : generic_apply_type (__eo_to_smt f) (__eo_to_smt x))
    (hGenG : generic_apply_type (__eo_to_smt g) (__eo_to_smt y))
    (hFn : RuleProofs.eo_has_bool_type (mkEq f g))
    (hArg : RuleProofs.eo_has_bool_type (mkEq x y)) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply f x) (Term.Apply g y)) := by
  have hFnTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type f g hFn
  have hArgTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type x y hArg
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply f x) (Term.Apply g y)
    (by
      rw [hToSmtF, hToSmtG]
      unfold generic_apply_type at hGenF hGenG
      rw [hGenF, hGenG, hFnTypes.1, hArgTypes.1])
    hTrans

private inductive HoCongTypeSpine (f g : Term) : Term -> Term -> Prop where
  | base :
      RuleProofs.eo_has_bool_type (mkEq f g) ->
      HoCongTypeSpine f g f g
  | app {l r x y : Term} :
      HoCongTypeSpine f g l r ->
      RuleProofs.eo_has_bool_type (mkEq x y) ->
      HoCongTypeSpine f g (Term.Apply l x) (Term.Apply r y)

private theorem hoCongTypeSpine_base_bool
    {f g l r : Term} :
    HoCongTypeSpine f g l r ->
    RuleProofs.eo_has_bool_type (mkEq f g)
  | HoCongTypeSpine.base h => h
  | HoCongTypeSpine.app h _ => hoCongTypeSpine_base_bool h

private theorem hoCongTypeSpine_left_appSpine
    {f g l r : Term} :
    HoCongTypeSpine f g l r ->
    HoAppSpine f l
  | HoCongTypeSpine.base _ => HoAppSpine.base
  | HoCongTypeSpine.app h _ =>
      HoAppSpine.app (hoCongTypeSpine_left_appSpine h)

private theorem hoCongTypeSpine_left_translation_of_type
    {f g l r : Term}
    (hSpine : HoCongTypeSpine f g l r) :
    __eo_typeof l ≠ Term.Stuck ->
    RuleProofs.eo_has_smt_translation l := by
  intro hTy
  induction hSpine with
  | base hBase =>
      exact
        (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
          f g hBase).2
  | app hRec hArg ih =>
      rename_i l r x y
      have hBaseBool : RuleProofs.eo_has_bool_type (mkEq f g) :=
        hoCongTypeSpine_base_bool hRec
      have hBaseTrans : RuleProofs.eo_has_smt_translation f :=
        (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
          f g hBaseBool).2
      have hApplyEq :=
        hoAppSpine_typeof_apply_eq f l x hBaseTrans
          (hoCongTypeSpine_left_appSpine hRec)
      have hApplyTy :
          __eo_typeof_apply (__eo_typeof l) (__eo_typeof x) ≠
            Term.Stuck := by
        rwa [← hApplyEq]
      have hHeadTy : __eo_typeof l ≠ Term.Stuck :=
        eo_typeof_apply_head_ne_stuck hApplyTy
      have hLTrans : RuleProofs.eo_has_smt_translation l := ih hHeadTy
      have hXTrans : RuleProofs.eo_has_smt_translation x :=
        (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
          x y hArg).2
      exact eo_has_smt_translation_apply_of_head_arg_translation_and_type
        l x hLTrans hXTrans hTy

private theorem hoCongTypeSpine_smt_type_eq_of_left_translation
    {f g l r : Term}
    (hSpine : HoCongTypeSpine f g l r) :
    RuleProofs.eo_has_smt_translation l ->
    __smtx_typeof (__eo_to_smt l) = __smtx_typeof (__eo_to_smt r) := by
  intro hLTrans
  induction hSpine with
  | base hBase =>
      exact
        (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
          f g hBase).1
  | app hRec hArg ih =>
      rename_i l r x y
      have hTyL : __eo_typeof (Term.Apply l x) ≠ Term.Stuck :=
        TranslationProofs.eo_type_valid_not_stuck
          (TranslationProofs.eo_type_valid_typeof_of_smt_translation
            (Term.Apply l x) hLTrans)
      have hBaseBool : RuleProofs.eo_has_bool_type (mkEq f g) :=
        hoCongTypeSpine_base_bool hRec
      have hBaseTrans : RuleProofs.eo_has_smt_translation f :=
        (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
          f g hBaseBool).2
      have hApplyEq :=
        hoAppSpine_typeof_apply_eq f l x hBaseTrans
          (hoCongTypeSpine_left_appSpine hRec)
      have hApplyTy :
          __eo_typeof_apply (__eo_typeof l) (__eo_typeof x) ≠
            Term.Stuck := by
        rwa [← hApplyEq]
      have hHeadTy : __eo_typeof l ≠ Term.Stuck :=
        eo_typeof_apply_head_ne_stuck hApplyTy
      have hPrevLTrans :
          RuleProofs.eo_has_smt_translation l :=
        hoCongTypeSpine_left_translation_of_type hRec hHeadTy
      have hPrevTyEq := ih hPrevLTrans
      have hPrevRTrans :
          RuleProofs.eo_has_smt_translation r := by
        intro hNone
        exact hPrevLTrans (hPrevTyEq.trans hNone)
      have hArgTypes :=
        RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type x y hArg
      rw [eo_to_smt_apply_generic_of_has_smt_translation l x hPrevLTrans,
        eo_to_smt_apply_generic_of_has_smt_translation r y hPrevRTrans]
      have hGenL : generic_apply_type (__eo_to_smt l) (__eo_to_smt x) :=
        generic_apply_type_of_has_smt_translation l x hPrevLTrans
      have hGenR : generic_apply_type (__eo_to_smt r) (__eo_to_smt y) :=
        generic_apply_type_of_has_smt_translation r y hPrevRTrans
      unfold generic_apply_type at hGenL hGenR
      rw [hGenL, hGenR, hPrevTyEq, hArgTypes.1]

private theorem hoCongTypeSpine_eq_has_bool_type
    {f g l r : Term}
    (hSpine : HoCongTypeSpine f g l r) :
    __eo_typeof (mkEq l r) = Term.Bool ->
    RuleProofs.eo_has_bool_type (mkEq l r) := by
  intro hTy
  have hLeftTy : __eo_typeof l ≠ Term.Stuck :=
    eq_typeof_bool_left_ne_stuck l r hTy
  have hLeftTrans :
      RuleProofs.eo_has_smt_translation l :=
    hoCongTypeSpine_left_translation_of_type hSpine hLeftTy
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type l r
    (hoCongTypeSpine_smt_type_eq_of_left_translation hSpine hLeftTrans)
    hLeftTrans

private theorem mk_ho_cong_step_eq_of_ne_stuck
    (l r x y tail : Term) :
    __mk_ho_cong l r
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (mkEq x y)) tail) ≠
      Term.Stuck ->
    __mk_ho_cong l r
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (mkEq x y)) tail) =
      __mk_ho_cong (Term.Apply l x) (Term.Apply r y) tail := by
  intro hProg
  cases l <;> cases r <;>
    simp [__mk_ho_cong] at hProg ⊢

private theorem mk_ho_cong_step_ne_stuck_of_ne_stuck
    (l r x y tail : Term) :
    __mk_ho_cong l r
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (mkEq x y)) tail) ≠
      Term.Stuck ->
    __mk_ho_cong (Term.Apply l x) (Term.Apply r y) tail ≠ Term.Stuck := by
  intro hProg
  rw [← mk_ho_cong_step_eq_of_ne_stuck l r x y tail hProg]
  exact hProg

private theorem mk_ho_cong_bad_head_stuck
    (l r a tail : Term)
    (hBad : ∀ x y, a ≠ mkEq x y) :
    __mk_ho_cong l r
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) tail) =
      Term.Stuck := by
  by_cases hl : l = Term.Stuck
  · subst l
    rfl
  by_cases hr : r = Term.Stuck
  · subst r
    simp [__mk_ho_cong]
  cases a with
  | Apply pf y =>
      cases pf with
      | Apply pg x =>
          cases pg with
          | UOp op =>
              cases op <;>
                first
                | exact (hBad x y rfl).elim
                | simp [__mk_ho_cong]
          | _ => simp [__mk_ho_cong]
      | _ => simp [__mk_ho_cong]
  | _ => simp [__mk_ho_cong]

private theorem mk_ho_cong_type_spine_of_list
    (f g : Term) :
    ∀ (ps : List Term) (l r : Term),
      HoCongTypeSpine f g l r ->
      AllHaveBoolType ps ->
      __mk_ho_cong l r (premiseAndFormulaList ps) ≠ Term.Stuck ->
      ∃ L R,
        __mk_ho_cong l r (premiseAndFormulaList ps) = mkEq L R ∧
          HoCongTypeSpine f g L R := by
  intro ps
  induction ps with
  | nil =>
      intro l r hSpine _hBool hProg
      refine ⟨l, r, ?_, hSpine⟩
      cases l <;> cases r <;>
        simp [premiseAndFormulaList, __mk_ho_cong] at hProg ⊢
  | cons p ps ih =>
      intro l r hSpine hBool hProg
      cases p with
      | Apply pf tail =>
          cases pf with
          | Apply pg lhs =>
              cases pg with
              | UOp op =>
                  cases op
                  case eq =>
                    have hArgBool :
                        RuleProofs.eo_has_bool_type (mkEq lhs tail) := by
                      simpa [premiseAndFormulaList, mkEq] using
                        hBool (mkEq lhs tail) (by simp [mkEq])
                    have hRestBool : AllHaveBoolType ps := by
                      intro q hq
                      exact hBool q (by simp [hq])
                    have hRecNN :
                        __mk_ho_cong (Term.Apply l lhs)
                            (Term.Apply r tail) (premiseAndFormulaList ps) ≠
                          Term.Stuck :=
                      mk_ho_cong_step_ne_stuck_of_ne_stuck l r lhs tail
                        (premiseAndFormulaList ps) (by
                          simpa [premiseAndFormulaList, mkEq] using hProg)
                    rcases ih (Term.Apply l lhs) (Term.Apply r tail)
                        (HoCongTypeSpine.app hSpine hArgBool)
                        hRestBool hRecNN with
                      ⟨L, R, hEq, hOutSpine⟩
                    refine ⟨L, R, ?_, hOutSpine⟩
                    have hStep :=
                      mk_ho_cong_step_eq_of_ne_stuck l r lhs tail
                        (premiseAndFormulaList ps) (by
                          simpa [premiseAndFormulaList, mkEq] using hProg)
                    simpa [premiseAndFormulaList, mkEq, hStep] using hEq
                  all_goals
                    exact False.elim (hProg (by
                      simp [premiseAndFormulaList,
                        mk_ho_cong_bad_head_stuck, mkEq]))
              | _ =>
                  exact False.elim (hProg (by
                    simp [premiseAndFormulaList,
                      mk_ho_cong_bad_head_stuck, mkEq]))
          | _ =>
              exact False.elim (hProg (by
                simp [premiseAndFormulaList,
                  mk_ho_cong_bad_head_stuck, mkEq]))
      | _ =>
          exact False.elim (hProg (by
            simp [premiseAndFormulaList,
              mk_ho_cong_bad_head_stuck, mkEq]))

/-- Typing for the generated EO implementation of `ho_cong`. -/
theorem typed___eo_prog_ho_cong_impl (premises : List Term) :
  AllHaveBoolType premises ->
  __eo_prog_ho_cong (Proof.pf (premiseAndFormulaList premises)) ≠
    Term.Stuck ->
  __eo_typeof (__eo_prog_ho_cong
    (Proof.pf (premiseAndFormulaList premises))) = Term.Bool ->
  RuleProofs.eo_has_bool_type
    (__eo_prog_ho_cong (Proof.pf (premiseAndFormulaList premises))) := by
  intro hPremisesBool hProg hProgType
  cases premises with
  | nil =>
      exact False.elim (hProg (by simp [premiseAndFormulaList, __eo_prog_ho_cong]))
  | cons p ps =>
      cases p with
      | Apply pf g =>
          cases pf with
          | Apply pg f =>
              cases pg with
              | UOp op =>
                  cases op
                  case eq =>
                    have hBaseBool :
                        RuleProofs.eo_has_bool_type (mkEq f g) := by
                      simpa [premiseAndFormulaList, mkEq] using
                        hPremisesBool (mkEq f g) (by simp [mkEq])
                    have hRestBool : AllHaveBoolType ps := by
                      intro q hq
                      exact hPremisesBool q (by simp [hq])
                    have hMkNN :
                        __mk_ho_cong f g (premiseAndFormulaList ps) ≠
                          Term.Stuck := by
                      simpa [premiseAndFormulaList, __eo_prog_ho_cong, mkEq]
                        using hProg
                    rcases mk_ho_cong_type_spine_of_list f g ps f g
                        (HoCongTypeSpine.base hBaseBool) hRestBool hMkNN with
                      ⟨L, R, hEq, hSpine⟩
                    have hEqTy : __eo_typeof (mkEq L R) = Term.Bool := by
                      have hProgType' := hProgType
                      simp [premiseAndFormulaList, __eo_prog_ho_cong, mkEq,
                        hEq] at hProgType'
                      exact hProgType'
                    have hBool : RuleProofs.eo_has_bool_type (mkEq L R) :=
                      hoCongTypeSpine_eq_has_bool_type hSpine hEqTy
                    have hProgEq :
                        __eo_prog_ho_cong
                            (Proof.pf
                              (premiseAndFormulaList (mkEq f g :: ps))) =
                          mkEq L R := by
                      simp [premiseAndFormulaList, __eo_prog_ho_cong, mkEq,
                        hEq]
                    rwa [hProgEq]
                  all_goals
                    exact False.elim (hProg (by
                      simp [premiseAndFormulaList, __eo_prog_ho_cong]))
              | _ =>
                  exact False.elim (hProg (by
                    simp [premiseAndFormulaList, __eo_prog_ho_cong]))
          | _ =>
              exact False.elim (hProg (by
                simp [premiseAndFormulaList, __eo_prog_ho_cong]))
      | _ =>
          exact False.elim (hProg (by
            simp [premiseAndFormulaList, __eo_prog_ho_cong]))

theorem congTrueSpine_generic_apply_eq_true
    (M : SmtModel) (hM : model_wf M)
    (f g x y : Term)
    (hEqBool :
      RuleProofs.eo_has_bool_type
        (mkEq (Term.Apply f x) (Term.Apply g y)))
    (hToSmtF :
      __eo_to_smt (Term.Apply f x) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))
    (hToSmtG :
      __eo_to_smt (Term.Apply g y) =
        SmtTerm.Apply (__eo_to_smt g) (__eo_to_smt y))
    (hGenTyF : generic_apply_type (__eo_to_smt f) (__eo_to_smt x))
    (hGenEvalF : generic_apply_eval (__eo_to_smt f) (__eo_to_smt x))
    (hGenEvalG : generic_apply_eval (__eo_to_smt g) (__eo_to_smt y))
    (hFn : eo_interprets M (mkEq f g) true)
    (hArg : eo_interprets M (mkEq x y) true) :
    eo_interprets M
      (mkEq (Term.Apply f x) (Term.Apply g y)) true := by
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hOuterTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply f x) (Term.Apply g y) hEqBool
    have hLeftNN :
        __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) ≠
            SmtType.None := by
      simpa [hToSmtF] using hOuterTypes.2
    unfold generic_apply_type at hGenTyF
    have hAppNN :
        __smtx_typeof_apply
            (__smtx_typeof (__eo_to_smt f))
            (__smtx_typeof (__eo_to_smt x)) ≠ SmtType.None := by
      rw [← hGenTyF]
      exact hLeftNN
    have hFnTypes :=
      RuleProofs.eo_eq_operands_same_smt_type M f g hFn
    have hArgTypes :=
      RuleProofs.eo_eq_operands_same_smt_type M x y hArg
    have hFnRel :=
      RuleProofs.eo_interprets_eq_rel M f g hFn
    have hArgRel :=
      RuleProofs.eo_interprets_eq_rel M x y hArg
    rw [hToSmtF, hToSmtG]
    unfold generic_apply_eval at hGenEvalF hGenEvalG
    rw [hGenEvalF M, hGenEvalG M]
    exact smt_value_rel_model_eval_apply_of_rel_core M hM
      (__eo_to_smt f) (__eo_to_smt g) (__eo_to_smt x) (__eo_to_smt y)
      hAppNN hFnTypes.1 hArgTypes.1 hFnRel hArgRel

private inductive HoCongTrueSpine
    (M : SmtModel) (f g : Term) : Term -> Term -> Prop where
  | base :
      eo_interprets M (mkEq f g) true ->
      HoCongTrueSpine M f g f g
  | app {l r x y : Term} :
      HoCongTrueSpine M f g l r ->
      eo_interprets M (mkEq x y) true ->
      HoCongTrueSpine M f g (Term.Apply l x) (Term.Apply r y)

private theorem hoCongTypeSpine_of_hoCongTrueSpine
    {M : SmtModel} {f g l r : Term} :
    HoCongTrueSpine M f g l r ->
      HoCongTypeSpine f g l r
  | HoCongTrueSpine.base hBase =>
      HoCongTypeSpine.base
        (RuleProofs.eo_has_bool_type_of_interprets_true M _ hBase)
  | HoCongTrueSpine.app hRec hArg =>
      HoCongTypeSpine.app
        (hoCongTypeSpine_of_hoCongTrueSpine hRec)
        (RuleProofs.eo_has_bool_type_of_interprets_true M _ hArg)

private theorem hoCongTrueSpine_eq_true
    (M : SmtModel) (hM : model_wf M)
    {f g l r : Term}
    (hSpine : HoCongTrueSpine M f g l r) :
    RuleProofs.eo_has_bool_type (mkEq l r) ->
    eo_interprets M (mkEq l r) true := by
  intro hEqBool
  revert hEqBool
  induction hSpine with
  | base hBase =>
      intro _hEqBool
      exact hBase
  | app hPrev hArg ih =>
      rename_i l r x y
      intro hEqBool
      have hPrevTypeSpine :
          HoCongTypeSpine f g l r :=
        hoCongTypeSpine_of_hoCongTrueSpine hPrev
      have hFinalLeftTrans :
          RuleProofs.eo_has_smt_translation (Term.Apply l x) :=
        (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
          (Term.Apply l x) (Term.Apply r y) hEqBool).2
      have hFinalLeftTy : __eo_typeof (Term.Apply l x) ≠ Term.Stuck :=
        TranslationProofs.eo_type_valid_not_stuck
          (TranslationProofs.eo_type_valid_typeof_of_smt_translation
            (Term.Apply l x) hFinalLeftTrans)
      have hBaseBool : RuleProofs.eo_has_bool_type (mkEq f g) :=
        hoCongTypeSpine_base_bool hPrevTypeSpine
      have hBaseTrans : RuleProofs.eo_has_smt_translation f :=
        (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
          f g hBaseBool).2
      have hApplyEq :=
        hoAppSpine_typeof_apply_eq f l x hBaseTrans
          (hoCongTypeSpine_left_appSpine hPrevTypeSpine)
      have hApplyTy :
          __eo_typeof_apply (__eo_typeof l) (__eo_typeof x) ≠
            Term.Stuck := by
        rwa [← hApplyEq]
      have hHeadTy : __eo_typeof l ≠ Term.Stuck :=
        eo_typeof_apply_head_ne_stuck hApplyTy
      have hPrevLTrans :
          RuleProofs.eo_has_smt_translation l :=
        hoCongTypeSpine_left_translation_of_type hPrevTypeSpine hHeadTy
      have hPrevTyEq :
          __smtx_typeof (__eo_to_smt l) = __smtx_typeof (__eo_to_smt r) :=
        hoCongTypeSpine_smt_type_eq_of_left_translation
          hPrevTypeSpine hPrevLTrans
      have hPrevBool : RuleProofs.eo_has_bool_type (mkEq l r) :=
        RuleProofs.eo_has_bool_type_eq_of_same_smt_type l r
          hPrevTyEq hPrevLTrans
      have hPrevTrue : eo_interprets M (mkEq l r) true :=
        ih hPrevBool
      have hPrevRTrans : RuleProofs.eo_has_smt_translation r := by
        intro hNone
        exact hPrevLTrans (hPrevTyEq.trans hNone)
      exact congTrueSpine_generic_apply_eq_true M hM l r x y hEqBool
        (eo_to_smt_apply_generic_of_has_smt_translation l x hPrevLTrans)
        (eo_to_smt_apply_generic_of_has_smt_translation r y hPrevRTrans)
        (generic_apply_type_of_has_smt_translation l x hPrevLTrans)
        (generic_apply_eval_of_has_smt_translation l x hPrevLTrans)
        (generic_apply_eval_of_has_smt_translation r y hPrevRTrans)
        hPrevTrue hArg

private theorem mk_ho_cong_true_spine_of_list
    (M : SmtModel) (f g : Term) :
    ∀ (ps : List Term) (l r : Term),
      HoCongTrueSpine M f g l r ->
      AllInterpretedTrue M ps ->
      __mk_ho_cong l r (premiseAndFormulaList ps) ≠ Term.Stuck ->
      ∃ L R,
        __mk_ho_cong l r (premiseAndFormulaList ps) = mkEq L R ∧
          HoCongTrueSpine M f g L R := by
  intro ps
  induction ps with
  | nil =>
      intro l r hSpine _hTrue hProg
      refine ⟨l, r, ?_, hSpine⟩
      cases l <;> cases r <;>
        simp [premiseAndFormulaList, __mk_ho_cong] at hProg ⊢
  | cons p ps ih =>
      intro l r hSpine hTrue hProg
      cases p with
      | Apply pf tail =>
          cases pf with
          | Apply pg lhs =>
              cases pg with
              | UOp op =>
                  cases op
                  case eq =>
                    have hArgTrue :
                        eo_interprets M (mkEq lhs tail) true := by
                      simpa [premiseAndFormulaList, mkEq] using
                        hTrue (mkEq lhs tail) (by simp [mkEq])
                    have hRestTrue : AllInterpretedTrue M ps := by
                      intro q hq
                      exact hTrue q (by simp [hq])
                    have hRecNN :
                        __mk_ho_cong (Term.Apply l lhs)
                            (Term.Apply r tail) (premiseAndFormulaList ps) ≠
                          Term.Stuck :=
                      mk_ho_cong_step_ne_stuck_of_ne_stuck l r lhs tail
                        (premiseAndFormulaList ps) (by
                          simpa [premiseAndFormulaList, mkEq] using hProg)
                    rcases ih (Term.Apply l lhs) (Term.Apply r tail)
                        (HoCongTrueSpine.app hSpine hArgTrue)
                        hRestTrue hRecNN with
                      ⟨L, R, hEq, hOutSpine⟩
                    refine ⟨L, R, ?_, hOutSpine⟩
                    have hStep :=
                      mk_ho_cong_step_eq_of_ne_stuck l r lhs tail
                        (premiseAndFormulaList ps) (by
                          simpa [premiseAndFormulaList, mkEq] using hProg)
                    simpa [premiseAndFormulaList, mkEq, hStep] using hEq
                  all_goals
                    exact False.elim (hProg (by
                      simp [premiseAndFormulaList,
                        mk_ho_cong_bad_head_stuck, mkEq]))
              | _ =>
                  exact False.elim (hProg (by
                    simp [premiseAndFormulaList,
                      mk_ho_cong_bad_head_stuck, mkEq]))
          | _ =>
              exact False.elim (hProg (by
                simp [premiseAndFormulaList,
                  mk_ho_cong_bad_head_stuck, mkEq]))
      | _ =>
          exact False.elim (hProg (by
            simp [premiseAndFormulaList,
              mk_ho_cong_bad_head_stuck, mkEq]))

/-- Correctness for the generated EO implementation of `ho_cong`. -/
theorem facts___eo_prog_ho_cong_impl
    (M : SmtModel) (hM : model_wf M)
    (premises : List Term) :
  RulePremiseEvidence M premises ->
  RuleProofs.eo_has_bool_type
    (__eo_prog_ho_cong (Proof.pf (premiseAndFormulaList premises))) ->
  __eo_prog_ho_cong (Proof.pf (premiseAndFormulaList premises)) ≠
    Term.Stuck ->
  __eo_typeof (__eo_prog_ho_cong
    (Proof.pf (premiseAndFormulaList premises))) = Term.Bool ->
  eo_interprets M
    (__eo_prog_ho_cong (Proof.pf (premiseAndFormulaList premises))) true := by
  intro hEvidence hProgBool hProg _hProgType
  cases premises with
  | nil =>
      exact False.elim (hProg (by simp [premiseAndFormulaList, __eo_prog_ho_cong]))
  | cons p ps =>
      cases p with
      | Apply pf g =>
          cases pf with
          | Apply pg f =>
              cases pg with
              | UOp op =>
                  cases op
                  case eq =>
                    have hBaseTrue :
                        eo_interprets M (mkEq f g) true := by
                      simpa [premiseAndFormulaList, mkEq] using
                        hEvidence.true_here (mkEq f g) (by simp [mkEq])
                    have hRestTrue : AllInterpretedTrue M ps := by
                      intro q hq
                      exact hEvidence.true_here q (by simp [hq])
                    have hMkNN :
                        __mk_ho_cong f g (premiseAndFormulaList ps) ≠
                          Term.Stuck := by
                      simpa [premiseAndFormulaList, __eo_prog_ho_cong, mkEq]
                        using hProg
                    rcases mk_ho_cong_true_spine_of_list M f g ps f g
                        (HoCongTrueSpine.base hBaseTrue) hRestTrue hMkNN with
                      ⟨L, R, hEq, hSpine⟩
                    have hEqBool : RuleProofs.eo_has_bool_type (mkEq L R) := by
                      have hProgBool' := hProgBool
                      simpa [premiseAndFormulaList, __eo_prog_ho_cong, mkEq,
                        hEq] using hProgBool'
                    have hEqTrue : eo_interprets M (mkEq L R) true :=
                      hoCongTrueSpine_eq_true M hM hSpine hEqBool
                    have hProgEq :
                        __eo_prog_ho_cong
                            (Proof.pf
                              (premiseAndFormulaList (mkEq f g :: ps))) =
                          mkEq L R := by
                      simp [premiseAndFormulaList, __eo_prog_ho_cong, mkEq,
                        hEq]
                    rwa [hProgEq]
                  all_goals
                    exact False.elim (hProg (by
                      simp [premiseAndFormulaList, __eo_prog_ho_cong]))
              | _ =>
                  exact False.elim (hProg (by
                    simp [premiseAndFormulaList, __eo_prog_ho_cong]))
          | _ =>
              exact False.elim (hProg (by
                simp [premiseAndFormulaList, __eo_prog_ho_cong]))
      | _ =>
          exact False.elim (hProg (by
            simp [premiseAndFormulaList, __eo_prog_ho_cong]))

theorem congTypeSpine_same_generic_head_apply_eq_has_bool_type
    (f x y : Term)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply f a) =
          SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a))
    (hGenX : generic_apply_type (__eo_to_smt f) (__eo_to_smt x))
    (hGenY : generic_apply_type (__eo_to_smt f) (__eo_to_smt y)) :
    RuleProofs.eo_has_smt_translation (Term.Apply f x) ->
    RuleProofs.eo_has_bool_type (mkEq x y) ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply f x) (Term.Apply f y)) := by
  intro hTrans hArg
  have hArgTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type x y hArg
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply f x) (Term.Apply f y)
    (by
      rw [hToSmt x, hToSmt y]
      unfold generic_apply_type at hGenX hGenY
      rw [hGenX, hGenY, hArgTypes.1])
    hTrans

theorem congTrueSpine_same_generic_head_apply_eq_true
    (M : SmtModel) (hM : model_wf M)
    (f x y : Term)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply f a) =
          SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a))
    (hGenTyX : generic_apply_type (__eo_to_smt f) (__eo_to_smt x))
    (hGenEvalX : generic_apply_eval (__eo_to_smt f) (__eo_to_smt x))
    (hGenEvalY : generic_apply_eval (__eo_to_smt f) (__eo_to_smt y)) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply f x) (Term.Apply f y)) ->
    eo_interprets M (mkEq x y) true ->
    eo_interprets M
      (mkEq (Term.Apply f x) (Term.Apply f y)) true := by
  intro hEqBool hArg
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm := __eo_to_smt f
    let X : SmtTerm := __eo_to_smt x
    let Y : SmtTerm := __eo_to_smt y
    have hOuterTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply f x) (Term.Apply f y) hEqBool
    have hLeftNN : __smtx_typeof (SmtTerm.Apply F X) ≠ SmtType.None := by
      simpa [F, X, hToSmt x] using hOuterTypes.2
    unfold generic_apply_type at hGenTyX
    have hAppNN :
        __smtx_typeof_apply (__smtx_typeof F) (__smtx_typeof X) ≠
          SmtType.None := by
      rw [← hGenTyX]
      exact hLeftNN
    have hArgTypes := RuleProofs.eo_eq_operands_same_smt_type M x y hArg
    have hArgRel := RuleProofs.eo_interprets_eq_rel M x y hArg
    rw [hToSmt x, hToSmt y]
    unfold generic_apply_eval at hGenEvalX hGenEvalY
    rw [hGenEvalX M, hGenEvalY M]
    exact smt_value_rel_model_eval_apply_of_rel_core M hM F F X Y
      hAppNN rfl hArgTypes.1 (RuleProofs.smt_value_rel_refl _) hArgRel

private theorem smt_value_rel_cases_local {a b : SmtValue}
    (h : RuleProofs.smt_value_rel a b) :
    a = b ∨ ∃ r r', a = SmtValue.RegLan r ∧ b = SmtValue.RegLan r' := by
  unfold RuleProofs.smt_value_rel at h
  unfold __smtx_model_eval_eq at h
  split at h
  · rename_i r1 r2
    exact Or.inr ⟨r1, r2, rfl, rfl⟩
  · left
    have hveq : native_veq a b = true := by
      simpa using h
    simpa [native_veq] using hveq

private theorem smt_value_rel_eval_int_to_bv_right
    (a : SmtValue) {b b' : SmtValue}
    (h : RuleProofs.smt_value_rel b b') :
    RuleProofs.smt_value_rel (__smtx_model_eval_int_to_bv a b)
      (__smtx_model_eval_int_to_bv a b') := by
  rcases smt_value_rel_cases_local h with rfl | ⟨r, r', rfl, rfl⟩
  · exact RuleProofs.smt_value_rel_refl _
  · cases a <;> exact RuleProofs.smt_value_rel_refl _

/-- Congruent-head variant for `int_to_bv` applications: the spine may
decompose the (applied-form) `int_to_bv` head one level further, giving
congruent width arguments. -/
theorem congTypeSpine_int_to_bv_head_congr_eq_has_bool_type
    (w n n' x y : Term)
    (hTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) n) x))
    (hHeadArg : RuleProofs.eo_has_bool_type (mkEq n n'))
    (hArg : RuleProofs.eo_has_bool_type (mkEq x y)) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) n) x)
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) n') y)) := by
  have hHeadTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type n n' hHeadArg
  have hArgTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type x y hArg
  refine RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _ ?_ hTrans
  show __smtx_typeof
      (SmtTerm.Apply (SmtTerm.int_to_bv (__eo_to_smt w) (__eo_to_smt n))
        (__eo_to_smt x)) =
    __smtx_typeof
      (SmtTerm.Apply (SmtTerm.int_to_bv (__eo_to_smt w) (__eo_to_smt n'))
        (__eo_to_smt y))
  rw [show __smtx_typeof
      (SmtTerm.Apply (SmtTerm.int_to_bv (__eo_to_smt w) (__eo_to_smt n))
        (__eo_to_smt x)) =
      __smtx_typeof_apply
        (__smtx_typeof_int_to_bv (__eo_to_smt w)
          (__smtx_typeof (__eo_to_smt n)))
        (__smtx_typeof (__eo_to_smt x)) from rfl,
    show __smtx_typeof
      (SmtTerm.Apply (SmtTerm.int_to_bv (__eo_to_smt w) (__eo_to_smt n'))
        (__eo_to_smt y)) =
      __smtx_typeof_apply
        (__smtx_typeof_int_to_bv (__eo_to_smt w)
          (__smtx_typeof (__eo_to_smt n')))
        (__smtx_typeof (__eo_to_smt y)) from rfl,
    hHeadTypes.1, hArgTypes.1]

theorem congTrueSpine_int_to_bv_head_congr_eq_true
    (M : SmtModel) (hM : model_wf M)
    (w n n' x y : Term)
    (hEqBool : RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) n) x)
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) n') y)))
    (hHeadArg : eo_interprets M (mkEq n n') true)
    (hArg : eo_interprets M (mkEq x y) true) :
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) n) x)
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) n') y))
      true := by
  apply RuleProofs.eo_interprets_eq_of_rel M _ _ hEqBool
  have hHeadTypes := RuleProofs.eo_eq_operands_same_smt_type M n n' hHeadArg
  have hHeadRel := RuleProofs.eo_interprets_eq_rel M n n' hHeadArg
  have hArgTypes := RuleProofs.eo_eq_operands_same_smt_type M x y hArg
  have hArgRel := RuleProofs.eo_interprets_eq_rel M x y hArg
  have hOuterTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type _ _ hEqBool
  have hAppNN :
      __smtx_typeof_apply
          (__smtx_typeof
            (SmtTerm.int_to_bv (__eo_to_smt w) (__eo_to_smt n)))
          (__smtx_typeof (__eo_to_smt x)) ≠ SmtType.None := hOuterTypes.2
  show RuleProofs.smt_value_rel
    (__smtx_model_eval_apply M
      (__smtx_model_eval M
        (SmtTerm.int_to_bv (__eo_to_smt w) (__eo_to_smt n)))
      (__smtx_model_eval M (__eo_to_smt x)))
    (__smtx_model_eval_apply M
      (__smtx_model_eval M
        (SmtTerm.int_to_bv (__eo_to_smt w) (__eo_to_smt n')))
      (__smtx_model_eval M (__eo_to_smt y)))
  refine smt_value_rel_model_eval_apply_of_rel_core M hM
    (SmtTerm.int_to_bv (__eo_to_smt w) (__eo_to_smt n))
    (SmtTerm.int_to_bv (__eo_to_smt w) (__eo_to_smt n'))
    (__eo_to_smt x) (__eo_to_smt y) hAppNN ?_ hArgTypes.1 ?_ hArgRel
  · show __smtx_typeof_int_to_bv (__eo_to_smt w)
        (__smtx_typeof (__eo_to_smt n)) =
      __smtx_typeof_int_to_bv (__eo_to_smt w)
        (__smtx_typeof (__eo_to_smt n'))
    rw [hHeadTypes.1]
  · show RuleProofs.smt_value_rel
      (__smtx_model_eval_int_to_bv
        (__smtx_model_eval M (__eo_to_smt w))
        (__smtx_model_eval M (__eo_to_smt n)))
      (__smtx_model_eval_int_to_bv
        (__smtx_model_eval M (__eo_to_smt w))
        (__smtx_model_eval M (__eo_to_smt n')))
    exact smt_value_rel_eval_int_to_bv_right _ hHeadRel

theorem mkSmtAppSpineRev_ne_dt_sel
    {F : SmtTerm}
    (hF : ∀ s d i j, F ≠ SmtTerm.DtSel s d i j) :
    ∀ xs s d i j,
      mkSmtAppSpineRev F xs ≠ SmtTerm.DtSel s d i j
  | [], s, d, i, j => hF s d i j
  | _ :: _, _s, _d, _i, _j => by
      intro h
      cases h

theorem mkSmtAppSpineRev_ne_dt_tester
    {F : SmtTerm}
    (hF : ∀ s d i, F ≠ SmtTerm.DtTester s d i) :
    ∀ xs s d i,
      mkSmtAppSpineRev F xs ≠ SmtTerm.DtTester s d i
  | [], s, d, i => hF s d i
  | _ :: _, _s, _d, _i => by
      intro h
      cases h

theorem mkSmtAppSpineRev_cons_ne_dt_sel
    (F x : SmtTerm) :
    ∀ xs s d i j,
      mkSmtAppSpineRev F (x :: xs) ≠ SmtTerm.DtSel s d i j
  | _, _s, _d, _i, _j => by
      intro h
      cases h

theorem mkSmtAppSpineRev_cons_ne_dt_tester
    (F x : SmtTerm) :
    ∀ xs s d i,
      mkSmtAppSpineRev F (x :: xs) ≠ SmtTerm.DtTester s d i
  | _, _s, _d, _i => by
      intro h
      cases h

theorem smt_app_spine_type_eq_of_listRel_bool
    {F G : SmtTerm}
    (hFType : __smtx_typeof F = __smtx_typeof G)
    (hFNoSel : ∀ s d i j, F ≠ SmtTerm.DtSel s d i j)
    (hFNoTester : ∀ s d i, F ≠ SmtTerm.DtTester s d i)
    (hGNoSel : ∀ s d i j, G ≠ SmtTerm.DtSel s d i j)
    (hGNoTester : ∀ s d i, G ≠ SmtTerm.DtTester s d i) :
    ∀ {xs ys : List Term},
      ListRel EqBoolOrSame xs ys ->
        __smtx_typeof (mkSmtAppSpineRev F (xs.map __eo_to_smt)) =
          __smtx_typeof (mkSmtAppSpineRev G (ys.map __eo_to_smt))
  | [], [], ListRel.nil => by
      simpa [mkSmtAppSpineRev] using hFType
  | x :: xs, y :: ys, ListRel.cons hArg hTail => by
      have hTailTy :=
        smt_app_spine_type_eq_of_listRel_bool hFType hFNoSel hFNoTester
          hGNoSel hGNoTester hTail
      have hArgTy : __smtx_typeof (__eo_to_smt x) =
          __smtx_typeof (__eo_to_smt y) :=
        smt_type_eq_of_eq_bool_or_same x y hArg
      let LF := mkSmtAppSpineRev F (xs.map __eo_to_smt)
      let RG := mkSmtAppSpineRev G (ys.map __eo_to_smt)
      have hGenL : generic_apply_type LF (__eo_to_smt x) :=
        generic_apply_type_of_non_datatype_head
          (mkSmtAppSpineRev_ne_dt_sel hFNoSel (xs.map __eo_to_smt))
          (mkSmtAppSpineRev_ne_dt_tester hFNoTester (xs.map __eo_to_smt))
      have hGenR : generic_apply_type RG (__eo_to_smt y) :=
        generic_apply_type_of_non_datatype_head
          (mkSmtAppSpineRev_ne_dt_sel hGNoSel (ys.map __eo_to_smt))
          (mkSmtAppSpineRev_ne_dt_tester hGNoTester (ys.map __eo_to_smt))
      unfold generic_apply_type at hGenL hGenR
      change
        __smtx_typeof (SmtTerm.Apply LF (__eo_to_smt x)) =
          __smtx_typeof (SmtTerm.Apply RG (__eo_to_smt y))
      rw [hGenL, hGenR]
      simp [LF, RG, hTailTy, hArgTy]

private theorem smt_app_spine_type_eq_of_listRel_bool_special_head
    (F : SmtTerm) :
    ∀ {xs ys : List Term},
      ListRel EqBoolOrSame xs ys ->
        __smtx_typeof (mkSmtAppSpineRev F (xs.map __eo_to_smt)) =
          __smtx_typeof (mkSmtAppSpineRev F (ys.map __eo_to_smt))
  | [], [], ListRel.nil => by
      rfl
  | x :: xs, y :: ys, ListRel.cons hArg hTail => by
      cases hTail with
      | nil =>
          have hArgTy : __smtx_typeof (__eo_to_smt x) =
              __smtx_typeof (__eo_to_smt y) :=
            smt_type_eq_of_eq_bool_or_same x y hArg
          cases F <;> simp [mkSmtAppSpineRev, __smtx_typeof, hArgTy]
      | @cons x₂ y₂ xs₂ ys₂ hArg₂ hTail₂ =>
          have hTailTy :=
            smt_app_spine_type_eq_of_listRel_bool_special_head F
              (ListRel.cons hArg₂ hTail₂)
          have hArgTy : __smtx_typeof (__eo_to_smt x) =
              __smtx_typeof (__eo_to_smt y) :=
            smt_type_eq_of_eq_bool_or_same x y hArg
          let LF :=
            mkSmtAppSpineRev F ((x₂ :: xs₂).map __eo_to_smt)
          let RG :=
            mkSmtAppSpineRev F ((y₂ :: ys₂).map __eo_to_smt)
          have hGenL : generic_apply_type LF (__eo_to_smt x) :=
            generic_apply_type_of_non_datatype_head
              (mkSmtAppSpineRev_cons_ne_dt_sel F (__eo_to_smt x₂)
                (xs₂.map __eo_to_smt))
              (mkSmtAppSpineRev_cons_ne_dt_tester F (__eo_to_smt x₂)
                (xs₂.map __eo_to_smt))
          have hGenR : generic_apply_type RG (__eo_to_smt y) :=
            generic_apply_type_of_non_datatype_head
              (mkSmtAppSpineRev_cons_ne_dt_sel F (__eo_to_smt y₂)
                (ys₂.map __eo_to_smt))
              (mkSmtAppSpineRev_cons_ne_dt_tester F (__eo_to_smt y₂)
                (ys₂.map __eo_to_smt))
          unfold generic_apply_type at hGenL hGenR
          change
            __smtx_typeof (SmtTerm.Apply LF (__eo_to_smt x)) =
              __smtx_typeof (SmtTerm.Apply RG (__eo_to_smt y))
          rw [hGenL, hGenR]
          simp [LF, RG]
          have hTailTy' :
              __smtx_typeof
                  (mkSmtAppSpineRev F
                    (__eo_to_smt x₂ :: xs₂.map __eo_to_smt)) =
                __smtx_typeof
                  (mkSmtAppSpineRev F
                    (__eo_to_smt y₂ :: ys₂.map __eo_to_smt)) := by
            simpa using hTailTy
          rw [hTailTy', hArgTy]

theorem dt_sel_arg_non_reg_of_non_none_core
    (s : native_String) (d : DatatypeDecl) (i j : native_Nat) (a : SmtTerm) :
    __smtx_typeof
        (SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j)) a) ≠
      SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hSel :
      (∃ (ss : native_String) (dd : SmtDatatypeDecl) (ii jj : native_Nat),
          __eo_to_smt (Term.DtSel s d i j) =
            SmtTerm.DtSel ss dd ii jj) ∨
        __eo_to_smt (Term.DtSel s d i j) = SmtTerm.None := by
    rw [TranslationProofs.eo_to_smt_term_dt_sel]
    cases TranslationProofs.__eo_reserved_datatype_name s <;>
      simp [native_ite]
  rcases hSel with ⟨ss, dd, ii, jj, hSel⟩ | hSel
  · have hTerm :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.DtSel ss dd ii jj) a) := by
      unfold term_has_non_none_type
      simpa [hSel] using hNN
    exact ⟨SmtType.Datatype ss dd,
      dt_sel_arg_datatype_of_non_none hTerm, by simp, by simp⟩
  · exfalso
    apply hNN
    simp [hSel, __smtx_typeof, __smtx_typeof_apply]

theorem congTypeSpine_appSpineRev_var_eq_has_bool_type
    (s : native_String) (T t rhs : Term)
    (hHead : (appSpineRev t).1 = Term.Var (Term.String s) T)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hSpine : CongTypeSpine t rhs) :
    RuleProofs.eo_has_bool_type (mkEq t rhs) := by
  rcases congTypeSpine_appSpineRev hSpine with ⟨hHeadEq, hArgs⟩
  have hRightHead :
      (appSpineRev rhs).1 = Term.Var (Term.String s) T := by
    rw [← hHeadEq]
    exact hHead
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type t rhs
    (by
      rw [eo_to_smt_appSpineRev_var s T t hHead,
        eo_to_smt_appSpineRev_var s T rhs hRightHead]
      exact smt_app_spine_type_eq_of_listRel_bool rfl
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        hArgs)
    hTrans

theorem congTypeSpine_appSpineRev_uconst_eq_has_bool_type
    (i : native_Nat) (T t rhs : Term)
    (hHead : (appSpineRev t).1 = Term.UConst i T)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hSpine : CongTypeSpine t rhs) :
    RuleProofs.eo_has_bool_type (mkEq t rhs) := by
  rcases congTypeSpine_appSpineRev hSpine with ⟨hHeadEq, hArgs⟩
  have hRightHead :
      (appSpineRev rhs).1 = Term.UConst i T := by
    rw [← hHeadEq]
    exact hHead
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type t rhs
    (by
      rw [eo_to_smt_appSpineRev_uconst i T t hHead,
        eo_to_smt_appSpineRev_uconst i T rhs hRightHead]
      exact smt_app_spine_type_eq_of_listRel_bool rfl
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        hArgs)
    hTrans

theorem congTypeSpine_appSpineRev_dtcons_eq_has_bool_type
    (s : native_String) (d : DatatypeDecl) (i : native_Nat) (t rhs : Term)
    (hHead : (appSpineRev t).1 = Term.DtCons s d i)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hSpine : CongTypeSpine t rhs) :
    RuleProofs.eo_has_bool_type (mkEq t rhs) := by
  rcases congTypeSpine_appSpineRev hSpine with ⟨hHeadEq, hArgs⟩
  have hRightHead :
      (appSpineRev rhs).1 = Term.DtCons s d i := by
    rw [← hHeadEq]
    exact hHead
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type t rhs
    (by
      rw [eo_to_smt_appSpineRev_dtcons s d i t hHead,
        eo_to_smt_appSpineRev_dtcons s d i rhs hRightHead]
      exact smt_app_spine_type_eq_of_listRel_bool rfl
        (eo_to_smt_dtcons_ne_dt_sel s d i)
        (eo_to_smt_dtcons_ne_dt_tester s d i)
        (eo_to_smt_dtcons_ne_dt_sel s d i)
        (eo_to_smt_dtcons_ne_dt_tester s d i)
        hArgs)
    hTrans

theorem congTypeSpine_appSpineRev_dt_sel_eq_has_bool_type
    (s : native_String) (d : DatatypeDecl) (i j : native_Nat) (t rhs : Term)
    (hHead : (appSpineRev t).1 = Term.DtSel s d i j)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hSpine : CongTypeSpine t rhs) :
    RuleProofs.eo_has_bool_type (mkEq t rhs) := by
  rcases congTypeSpine_appSpineRev hSpine with ⟨hHeadEq, hArgs⟩
  have hRightHead :
      (appSpineRev rhs).1 = Term.DtSel s d i j := by
    rw [← hHeadEq]
    exact hHead
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type t rhs
    (by
      rw [eo_to_smt_appSpineRev_dt_sel s d i j t hHead,
        eo_to_smt_appSpineRev_dt_sel s d i j rhs hRightHead]
      exact smt_app_spine_type_eq_of_listRel_bool_special_head
        (__eo_to_smt (Term.DtSel s d i j)) hArgs)
    hTrans


end CongSupport
