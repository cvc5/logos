module

public import Cpc.Proofs.RuleSupport.Cong.HoCong
import all Cpc.Proofs.RuleSupport.Cong.HoCong

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace CongSupport

attribute [local simp] native_streq native_and native_ite

theorem smt_app_spine_type_eq_and_rel_of_listRel_true
    (M : SmtModel) (hM : model_wf M)
    {F G : SmtTerm}
    (hFType : __smtx_typeof F = __smtx_typeof G)
    (hFRel :
      RuleProofs.smt_value_rel (__smtx_model_eval M F)
        (__smtx_model_eval M G))
    (hFNoSel : ∀ s d i j, F ≠ SmtTerm.DtSel s d i j)
    (hFNoTester : ∀ s d i, F ≠ SmtTerm.DtTester s d i)
    (hGNoSel : ∀ s d i j, G ≠ SmtTerm.DtSel s d i j)
    (hGNoTester : ∀ s d i, G ≠ SmtTerm.DtTester s d i) :
    ∀ {xs ys : List Term},
      ListRel (EqTrueOrSame M) xs ys ->
      __smtx_typeof (mkSmtAppSpineRev F (xs.map __eo_to_smt)) ≠
        SmtType.None ->
        __smtx_typeof (mkSmtAppSpineRev F (xs.map __eo_to_smt)) =
            __smtx_typeof (mkSmtAppSpineRev G (ys.map __eo_to_smt)) ∧
          RuleProofs.smt_value_rel
            (__smtx_model_eval M
              (mkSmtAppSpineRev F (xs.map __eo_to_smt)))
            (__smtx_model_eval M
              (mkSmtAppSpineRev G (ys.map __eo_to_smt)))
  | [], [], ListRel.nil => by
      intro _hNN
      exact ⟨by simpa [mkSmtAppSpineRev] using hFType,
        by simpa [mkSmtAppSpineRev] using hFRel⟩
  | x :: xs, y :: ys, ListRel.cons hArg hTail => by
      intro hNN
      let LF := mkSmtAppSpineRev F (xs.map __eo_to_smt)
      let RG := mkSmtAppSpineRev G (ys.map __eo_to_smt)
      let X := __eo_to_smt x
      let Y := __eo_to_smt y
      have hGenTyL : generic_apply_type LF X :=
        generic_apply_type_of_non_datatype_head
          (mkSmtAppSpineRev_ne_dt_sel hFNoSel (xs.map __eo_to_smt))
          (mkSmtAppSpineRev_ne_dt_tester hFNoTester (xs.map __eo_to_smt))
      have hGenTyR : generic_apply_type RG Y :=
        generic_apply_type_of_non_datatype_head
          (mkSmtAppSpineRev_ne_dt_sel hGNoSel (ys.map __eo_to_smt))
          (mkSmtAppSpineRev_ne_dt_tester hGNoTester (ys.map __eo_to_smt))
      have hGenEvalL : generic_apply_eval LF X :=
        generic_apply_eval_of_non_datatype_head
          (mkSmtAppSpineRev_ne_dt_sel hFNoSel (xs.map __eo_to_smt))
          (mkSmtAppSpineRev_ne_dt_tester hFNoTester (xs.map __eo_to_smt))
      have hGenEvalR : generic_apply_eval RG Y :=
        generic_apply_eval_of_non_datatype_head
          (mkSmtAppSpineRev_ne_dt_sel hGNoSel (ys.map __eo_to_smt))
          (mkSmtAppSpineRev_ne_dt_tester hGNoTester (ys.map __eo_to_smt))
      unfold generic_apply_type at hGenTyL hGenTyR
      have hAppNN : __smtx_typeof_apply (__smtx_typeof LF) (__smtx_typeof X) ≠
          SmtType.None := by
        rw [← hGenTyL]
        simpa [LF, X, mkSmtAppSpineRev] using hNN
      have hTailNN : __smtx_typeof LF ≠ SmtType.None :=
        smt_apply_head_non_none_of_apply_non_none hAppNN
      have hTail :=
        smt_app_spine_type_eq_and_rel_of_listRel_true M hM hFType hFRel
          hFNoSel hFNoTester hGNoSel hGNoTester hTail hTailNN
      have hTailTy : __smtx_typeof LF = __smtx_typeof RG := by
        simpa [LF, RG] using hTail.1
      have hTailRel :
          RuleProofs.smt_value_rel (__smtx_model_eval M LF)
            (__smtx_model_eval M RG) := by
        simpa [LF, RG] using hTail.2
      have hArgTy : __smtx_typeof X = __smtx_typeof Y := by
        exact smt_type_eq_of_eq_true_or_same M x y hArg
      have hArgRel :
          RuleProofs.smt_value_rel (__smtx_model_eval M X)
            (__smtx_model_eval M Y) := by
        exact smt_value_rel_of_eq_true_or_same M x y hArg
      have hTypeEq :
          __smtx_typeof (SmtTerm.Apply LF X) =
            __smtx_typeof (SmtTerm.Apply RG Y) := by
        rw [hGenTyL, hGenTyR]
        rw [hTailTy, hArgTy]
      have hRel :
          RuleProofs.smt_value_rel
            (__smtx_model_eval M (SmtTerm.Apply LF X))
            (__smtx_model_eval M (SmtTerm.Apply RG Y)) := by
        unfold generic_apply_eval at hGenEvalL hGenEvalR
        rw [hGenEvalL M, hGenEvalR M]
        exact smt_value_rel_model_eval_apply_of_rel_core M hM LF RG X Y
          hAppNN hTailTy hArgTy hTailRel hArgRel
      exact ⟨by simpa [LF, RG, X, Y, mkSmtAppSpineRev] using hTypeEq,
        by simpa [LF, RG, X, Y, mkSmtAppSpineRev] using hRel⟩

private theorem smt_app_spine_type_eq_and_rel_of_listRel_true_dt_sel
    (M : SmtModel) (hM : model_wf M)
    (s : native_String) (d : DatatypeDecl) (i j : native_Nat) :
    let F := __eo_to_smt (Term.DtSel s d i j)
    ∀ {xs ys : List Term},
      ListRel (EqTrueOrSame M) xs ys ->
      __smtx_typeof (mkSmtAppSpineRev F (xs.map __eo_to_smt)) ≠
        SmtType.None ->
        __smtx_typeof (mkSmtAppSpineRev F (xs.map __eo_to_smt)) =
            __smtx_typeof (mkSmtAppSpineRev F (ys.map __eo_to_smt)) ∧
          RuleProofs.smt_value_rel
            (__smtx_model_eval M
              (mkSmtAppSpineRev F (xs.map __eo_to_smt)))
            (__smtx_model_eval M
              (mkSmtAppSpineRev F (ys.map __eo_to_smt))) := by
  intro F xs ys hArgs
  induction hArgs with
  | nil =>
      intro _hNN
      exact ⟨rfl, RuleProofs.smt_value_rel_refl _⟩
  | @cons x y xs ys hArg hTail ih =>
      intro hNN
      cases hTail with
      | nil =>
          let X := __eo_to_smt x
          let Y := __eo_to_smt y
          have hArgTy : __smtx_typeof X = __smtx_typeof Y :=
            smt_type_eq_of_eq_true_or_same M x y hArg
          have hTypeEq :
              __smtx_typeof (SmtTerm.Apply F X) =
                __smtx_typeof (SmtTerm.Apply F Y) := by
            cases F <;> simp [__smtx_typeof, hArgTy]
          have hXNN :
              __smtx_typeof (SmtTerm.Apply F X) ≠ SmtType.None := by
            simpa [F, X, mkSmtAppSpineRev] using hNN
          have hEvalArg : __smtx_model_eval M X = __smtx_model_eval M Y := by
            subst F
            rcases dt_sel_arg_non_reg_of_non_none_core s d i j X hXNN with
              ⟨A, hXA, hANN, hAReg⟩
            have hYA : __smtx_typeof Y = A := by
              rw [← hArgTy]
              exact hXA
            exact eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type
              M hM x y A hXA hYA hANN hAReg hArg
          have hRel :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M (SmtTerm.Apply F X))
                (__smtx_model_eval M (SmtTerm.Apply F Y)) := by
            subst F
            rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
            change
              __smtx_model_eval_eq
                (__smtx_model_eval M
                  (SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j)) X))
                (__smtx_model_eval M
                  (SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j)) Y)) =
                  SmtValue.Boolean true
            rw [TranslationProofs.eo_to_smt_term_dt_sel]
            cases hRes : TranslationProofs.__eo_reserved_datatype_name s
            · simp [native_ite]
              rw [__smtx_model_eval, __smtx_model_eval, hEvalArg]
              exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
                (RuleProofs.smt_value_rel_refl _)
            · simp [native_ite, __smtx_model_eval]
              rw [hEvalArg]
              exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
                (RuleProofs.smt_value_rel_refl _)
          exact ⟨by simpa [F, X, Y, mkSmtAppSpineRev] using hTypeEq,
            by simpa [F, X, Y, mkSmtAppSpineRev] using hRel⟩
      | @cons x₂ y₂ xs₂ ys₂ hArg₂ hTail₂ =>
          let LF :=
            mkSmtAppSpineRev F ((x₂ :: xs₂).map __eo_to_smt)
          let RG :=
            mkSmtAppSpineRev F ((y₂ :: ys₂).map __eo_to_smt)
          let X := __eo_to_smt x
          let Y := __eo_to_smt y
          have hGenTyL : generic_apply_type LF X :=
            generic_apply_type_of_non_datatype_head
              (mkSmtAppSpineRev_cons_ne_dt_sel F (__eo_to_smt x₂)
                (xs₂.map __eo_to_smt))
              (mkSmtAppSpineRev_cons_ne_dt_tester F (__eo_to_smt x₂)
                (xs₂.map __eo_to_smt))
          have hGenTyR : generic_apply_type RG Y :=
            generic_apply_type_of_non_datatype_head
              (mkSmtAppSpineRev_cons_ne_dt_sel F (__eo_to_smt y₂)
                (ys₂.map __eo_to_smt))
              (mkSmtAppSpineRev_cons_ne_dt_tester F (__eo_to_smt y₂)
                (ys₂.map __eo_to_smt))
          have hGenEvalL : generic_apply_eval LF X :=
            generic_apply_eval_of_non_datatype_head
              (mkSmtAppSpineRev_cons_ne_dt_sel F (__eo_to_smt x₂)
                (xs₂.map __eo_to_smt))
              (mkSmtAppSpineRev_cons_ne_dt_tester F (__eo_to_smt x₂)
                (xs₂.map __eo_to_smt))
          have hGenEvalR : generic_apply_eval RG Y :=
            generic_apply_eval_of_non_datatype_head
              (mkSmtAppSpineRev_cons_ne_dt_sel F (__eo_to_smt y₂)
                (ys₂.map __eo_to_smt))
              (mkSmtAppSpineRev_cons_ne_dt_tester F (__eo_to_smt y₂)
                (ys₂.map __eo_to_smt))
          unfold generic_apply_type at hGenTyL hGenTyR
          have hAppNN :
              __smtx_typeof_apply (__smtx_typeof LF) (__smtx_typeof X) ≠
                SmtType.None := by
            rw [← hGenTyL]
            simpa [LF, X, mkSmtAppSpineRev] using hNN
          have hTailNN : __smtx_typeof LF ≠ SmtType.None :=
            smt_apply_head_non_none_of_apply_non_none hAppNN
          have hTailResult :=
            ih (by
              simpa [LF] using hTailNN)
          have hTailTy : __smtx_typeof LF = __smtx_typeof RG := by
            simpa [LF, RG] using hTailResult.1
          have hTailRel :
              RuleProofs.smt_value_rel (__smtx_model_eval M LF)
                (__smtx_model_eval M RG) := by
            simpa [LF, RG] using hTailResult.2
          have hArgTy : __smtx_typeof X = __smtx_typeof Y :=
            smt_type_eq_of_eq_true_or_same M x y hArg
          have hArgRel :
              RuleProofs.smt_value_rel (__smtx_model_eval M X)
                (__smtx_model_eval M Y) :=
            smt_value_rel_of_eq_true_or_same M x y hArg
          have hTypeEq :
              __smtx_typeof (SmtTerm.Apply LF X) =
                __smtx_typeof (SmtTerm.Apply RG Y) := by
            rw [hGenTyL, hGenTyR]
            rw [hTailTy, hArgTy]
          have hRel :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M (SmtTerm.Apply LF X))
                (__smtx_model_eval M (SmtTerm.Apply RG Y)) := by
            unfold generic_apply_eval at hGenEvalL hGenEvalR
            rw [hGenEvalL M, hGenEvalR M]
            exact smt_value_rel_model_eval_apply_of_rel_core M hM LF RG X Y
              hAppNN hTailTy hArgTy hTailRel hArgRel
          exact ⟨by simpa [LF, RG, X, Y, mkSmtAppSpineRev] using hTypeEq,
            by simpa [LF, RG, X, Y, mkSmtAppSpineRev] using hRel⟩

theorem congTrueSpine_appSpineRev_var_eq_true
    (M : SmtModel) (hM : model_wf M)
    (s : native_String) (T t rhs : Term)
    (hHead : (appSpineRev t).1 = Term.Var (Term.String s) T)
    (hEqBool : RuleProofs.eo_has_bool_type (mkEq t rhs))
    (hSpine : CongTrueSpine M t rhs) :
    eo_interprets M (mkEq t rhs) true := by
  rcases congTrueSpine_appSpineRev M hSpine with ⟨hHeadEq, hArgs⟩
  have hRightHead :
      (appSpineRev rhs).1 = Term.Var (Term.String s) T := by
    rw [← hHeadEq]
    exact hHead
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · rw [eo_to_smt_appSpineRev_var s T t hHead,
      eo_to_smt_appSpineRev_var s T rhs hRightHead]
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type t rhs hEqBool
    have hLeftNN :
        __smtx_typeof
            (mkSmtAppSpineRev (SmtTerm.Var s (__eo_to_smt_type T))
              ((appSpineRev t).2.map __eo_to_smt)) ≠ SmtType.None := by
      simpa [eo_to_smt_appSpineRev_var s T t hHead] using hTypes.2
    exact (smt_app_spine_type_eq_and_rel_of_listRel_true M hM rfl
      (RuleProofs.smt_value_rel_refl _)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hArgs hLeftNN).2

theorem congTrueSpine_appSpineRev_uconst_eq_true
    (M : SmtModel) (hM : model_wf M)
    (i : native_Nat) (T t rhs : Term)
    (hHead : (appSpineRev t).1 = Term.UConst i T)
    (hEqBool : RuleProofs.eo_has_bool_type (mkEq t rhs))
    (hSpine : CongTrueSpine M t rhs) :
    eo_interprets M (mkEq t rhs) true := by
  rcases congTrueSpine_appSpineRev M hSpine with ⟨hHeadEq, hArgs⟩
  have hRightHead :
      (appSpineRev rhs).1 = Term.UConst i T := by
    rw [← hHeadEq]
    exact hHead
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · rw [eo_to_smt_appSpineRev_uconst i T t hHead,
      eo_to_smt_appSpineRev_uconst i T rhs hRightHead]
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type t rhs hEqBool
    have hLeftNN :
        __smtx_typeof
            (mkSmtAppSpineRev
              (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
              ((appSpineRev t).2.map __eo_to_smt)) ≠ SmtType.None := by
      simpa [eo_to_smt_appSpineRev_uconst i T t hHead] using hTypes.2
    exact (smt_app_spine_type_eq_and_rel_of_listRel_true M hM rfl
      (RuleProofs.smt_value_rel_refl _)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hArgs hLeftNN).2

theorem congTrueSpine_appSpineRev_dtcons_eq_true
    (M : SmtModel) (hM : model_wf M)
    (s : native_String) (d : DatatypeDecl) (i : native_Nat) (t rhs : Term)
    (hHead : (appSpineRev t).1 = Term.DtCons s d i)
    (hEqBool : RuleProofs.eo_has_bool_type (mkEq t rhs))
    (hSpine : CongTrueSpine M t rhs) :
    eo_interprets M (mkEq t rhs) true := by
  rcases congTrueSpine_appSpineRev M hSpine with ⟨hHeadEq, hArgs⟩
  have hRightHead :
      (appSpineRev rhs).1 = Term.DtCons s d i := by
    rw [← hHeadEq]
    exact hHead
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · rw [eo_to_smt_appSpineRev_dtcons s d i t hHead,
      eo_to_smt_appSpineRev_dtcons s d i rhs hRightHead]
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type t rhs hEqBool
    have hLeftNN :
        __smtx_typeof
            (mkSmtAppSpineRev (__eo_to_smt (Term.DtCons s d i))
              ((appSpineRev t).2.map __eo_to_smt)) ≠ SmtType.None := by
      simpa [eo_to_smt_appSpineRev_dtcons s d i t hHead] using hTypes.2
    exact (smt_app_spine_type_eq_and_rel_of_listRel_true M hM rfl
      (RuleProofs.smt_value_rel_refl _)
      (eo_to_smt_dtcons_ne_dt_sel s d i)
      (eo_to_smt_dtcons_ne_dt_tester s d i)
      (eo_to_smt_dtcons_ne_dt_sel s d i)
      (eo_to_smt_dtcons_ne_dt_tester s d i)
      hArgs hLeftNN).2

theorem congTrueSpine_appSpineRev_dt_sel_eq_true
    (M : SmtModel) (hM : model_wf M)
    (s : native_String) (d : DatatypeDecl) (i j : native_Nat) (t rhs : Term)
    (hHead : (appSpineRev t).1 = Term.DtSel s d i j)
    (hEqBool : RuleProofs.eo_has_bool_type (mkEq t rhs))
    (hSpine : CongTrueSpine M t rhs) :
    eo_interprets M (mkEq t rhs) true := by
  rcases congTrueSpine_appSpineRev M hSpine with ⟨hHeadEq, hArgs⟩
  have hRightHead :
      (appSpineRev rhs).1 = Term.DtSel s d i j := by
    rw [← hHeadEq]
    exact hHead
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · rw [eo_to_smt_appSpineRev_dt_sel s d i j t hHead,
      eo_to_smt_appSpineRev_dt_sel s d i j rhs hRightHead]
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type t rhs hEqBool
    have hLeftNN :
        __smtx_typeof
            (mkSmtAppSpineRev (__eo_to_smt (Term.DtSel s d i j))
              ((appSpineRev t).2.map __eo_to_smt)) ≠ SmtType.None := by
      simpa [eo_to_smt_appSpineRev_dt_sel s d i j t hHead] using hTypes.2
    exact
      (smt_app_spine_type_eq_and_rel_of_listRel_true_dt_sel M hM
        s d i j hArgs hLeftNN).2

private theorem congTrueSpine_var_apply_inv
    (M : SmtModel) (s : native_String) (T x rhs : Term) :
    CongTrueSpine M (Term.Apply (Term.Var (Term.String s) T) x) rhs ->
      ∃ y, rhs = Term.Apply (Term.Var (Term.String s) T) y ∧
        EqTrueOrSame M x y := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg _ =>
      cases hHead with
      | refl _ =>
          exact ⟨_, rfl, Or.inr hArg⟩

private theorem congTypeSpine_var_apply_inv
    (s : native_String) (T x rhs : Term) :
    CongTypeSpine (Term.Apply (Term.Var (Term.String s) T) x) rhs ->
      ∃ y, rhs = Term.Apply (Term.Var (Term.String s) T) y ∧
        EqBoolOrSame x y := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg =>
      cases hHead with
      | refl _ =>
          exact ⟨_, rfl, Or.inr hArg⟩

private theorem congTrueSpine_uconst_apply_inv
    (M : SmtModel) (i : native_Nat) (T x rhs : Term) :
    CongTrueSpine M (Term.Apply (Term.UConst i T) x) rhs ->
      ∃ y, rhs = Term.Apply (Term.UConst i T) y ∧
        EqTrueOrSame M x y := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg _ =>
      cases hHead with
      | refl _ =>
          exact ⟨_, rfl, Or.inr hArg⟩

private theorem congTrueSpine_var_apply_apply_inv
    (M : SmtModel) (s : native_String) (T x₁ x₂ rhs : Term) :
    CongTrueSpine M
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) rhs ->
      ∃ y₁ y₂,
        rhs = Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂ ∧
          EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₂ _ =>
      rcases congTrueSpine_var_apply_inv M s T x₁ _ hHead with
        ⟨y₁, hHeadEq, hArg₁⟩
      subst hHeadEq
      exact ⟨y₁, _, rfl, hArg₁, Or.inr hArg₂⟩

private theorem congTrueSpine_uconst_apply_apply_inv
    (M : SmtModel) (i : native_Nat) (T x₁ x₂ rhs : Term) :
    CongTrueSpine M
        (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) rhs ->
      ∃ y₁ y₂,
        rhs = Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂ ∧
          EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₂ _ =>
      rcases congTrueSpine_uconst_apply_inv M i T x₁ _ hHead with
        ⟨y₁, hHeadEq, hArg₁⟩
      subst hHeadEq
      exact ⟨y₁, _, rfl, hArg₁, Or.inr hArg₂⟩

private theorem congTypeSpine_uconst_apply_inv
    (i : native_Nat) (T x rhs : Term) :
    CongTypeSpine (Term.Apply (Term.UConst i T) x) rhs ->
      ∃ y, rhs = Term.Apply (Term.UConst i T) y ∧
        EqBoolOrSame x y := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg =>
      cases hHead with
      | refl _ =>
          exact ⟨_, rfl, Or.inr hArg⟩

private theorem congTypeSpine_var_apply_apply_inv
    (s : native_String) (T x₁ x₂ rhs : Term) :
    CongTypeSpine
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) rhs ->
      ∃ y₁ y₂,
        rhs = Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂ ∧
          EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₂ =>
      rcases congTypeSpine_var_apply_inv s T x₁ _ hHead with
        ⟨y₁, hHeadEq, hArg₁⟩
      subst hHeadEq
      exact ⟨y₁, _, rfl, hArg₁, Or.inr hArg₂⟩

private theorem congTypeSpine_uconst_apply_apply_inv
    (i : native_Nat) (T x₁ x₂ rhs : Term) :
    CongTypeSpine (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) rhs ->
      ∃ y₁ y₂,
        rhs = Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂ ∧
          EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₂ =>
      rcases congTypeSpine_uconst_apply_inv i T x₁ _ hHead with
        ⟨y₁, hHeadEq, hArg₁⟩
      subst hHeadEq
      exact ⟨y₁, _, rfl, hArg₁, Or.inr hArg₂⟩

private theorem congTrueSpine_var_apply_apply_apply_inv
    (M : SmtModel) (s : native_String) (T x₁ x₂ x₃ rhs : Term) :
    CongTrueSpine M
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
          x₃) rhs ->
      ∃ y₁ y₂ y₃,
        rhs =
          Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
            y₃ ∧
          EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ ∧
            EqTrueOrSame M x₃ y₃ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₃ _ =>
      rcases congTrueSpine_var_apply_apply_inv M s T x₁ x₂ _ hHead with
        ⟨y₁, y₂, hHeadEq, hArg₁, hArg₂⟩
      subst hHeadEq
      exact ⟨y₁, y₂, _, rfl, hArg₁, hArg₂, Or.inr hArg₃⟩

private theorem congTrueSpine_uconst_apply_apply_apply_inv
    (M : SmtModel) (i : native_Nat) (T x₁ x₂ x₃ rhs : Term) :
    CongTrueSpine M
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
        rhs ->
      ∃ y₁ y₂ y₃,
        rhs = Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂) y₃ ∧
          EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ ∧
            EqTrueOrSame M x₃ y₃ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₃ _ =>
      rcases congTrueSpine_uconst_apply_apply_inv M i T x₁ x₂ _ hHead with
        ⟨y₁, y₂, hHeadEq, hArg₁, hArg₂⟩
      subst hHeadEq
      exact ⟨y₁, y₂, _, rfl, hArg₁, hArg₂, Or.inr hArg₃⟩

private theorem congTypeSpine_var_apply_apply_apply_inv
    (s : native_String) (T x₁ x₂ x₃ rhs : Term) :
    CongTypeSpine
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
          x₃) rhs ->
      ∃ y₁ y₂ y₃,
        rhs =
          Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
            y₃ ∧
          EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ ∧
            EqBoolOrSame x₃ y₃ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₃ =>
      rcases congTypeSpine_var_apply_apply_inv s T x₁ x₂ _ hHead with
        ⟨y₁, y₂, hHeadEq, hArg₁, hArg₂⟩
      subst hHeadEq
      exact ⟨y₁, y₂, _, rfl, hArg₁, hArg₂, Or.inr hArg₃⟩

private theorem congTypeSpine_uconst_apply_apply_apply_inv
    (i : native_Nat) (T x₁ x₂ x₃ rhs : Term) :
    CongTypeSpine
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
        rhs ->
      ∃ y₁ y₂ y₃,
        rhs = Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂) y₃ ∧
          EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ ∧
            EqBoolOrSame x₃ y₃ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₃ =>
      rcases congTypeSpine_uconst_apply_apply_inv i T x₁ x₂ _ hHead with
        ⟨y₁, y₂, hHeadEq, hArg₁, hArg₂⟩
      subst hHeadEq
      exact ⟨y₁, y₂, _, rfl, hArg₁, hArg₂, Or.inr hArg₃⟩

private theorem congTrueSpine_var_apply_apply_apply_apply_inv
    (M : SmtModel) (s : native_String) (T x₁ x₂ x₃ x₄ rhs : Term) :
    CongTrueSpine M
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
            x₃) x₄) rhs ->
      ∃ y₁ y₂ y₃ y₄,
        rhs =
          Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
              y₃) y₄ ∧
          EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ ∧
            EqTrueOrSame M x₃ y₃ ∧ EqTrueOrSame M x₄ y₄ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, rfl, Or.inl rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₄ _ =>
      rcases congTrueSpine_var_apply_apply_apply_inv M s T x₁ x₂ x₃ _
          hHead with
        ⟨y₁, y₂, y₃, hHeadEq, hArg₁, hArg₂, hArg₃⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, _, rfl, hArg₁, hArg₂, hArg₃, Or.inr hArg₄⟩

private theorem congTrueSpine_uconst_apply_apply_apply_apply_inv
    (M : SmtModel) (i : native_Nat) (T x₁ x₂ x₃ x₄ rhs : Term) :
    CongTrueSpine M
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
            x₃) x₄) rhs ->
      ∃ y₁ y₂ y₃ y₄,
        rhs =
          Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
              y₃) y₄ ∧
          EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ ∧
            EqTrueOrSame M x₃ y₃ ∧ EqTrueOrSame M x₄ y₄ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, rfl, Or.inl rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₄ _ =>
      rcases congTrueSpine_uconst_apply_apply_apply_inv M i T x₁ x₂ x₃ _
          hHead with
        ⟨y₁, y₂, y₃, hHeadEq, hArg₁, hArg₂, hArg₃⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, _, rfl, hArg₁, hArg₂, hArg₃, Or.inr hArg₄⟩

private theorem congTypeSpine_var_apply_apply_apply_apply_inv
    (s : native_String) (T x₁ x₂ x₃ x₄ rhs : Term) :
    CongTypeSpine
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
            x₃) x₄) rhs ->
      ∃ y₁ y₂ y₃ y₄,
        rhs =
          Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
              y₃) y₄ ∧
          EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ ∧
            EqBoolOrSame x₃ y₃ ∧ EqBoolOrSame x₄ y₄ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, rfl, Or.inl rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₄ =>
      rcases congTypeSpine_var_apply_apply_apply_inv s T x₁ x₂ x₃ _
          hHead with
        ⟨y₁, y₂, y₃, hHeadEq, hArg₁, hArg₂, hArg₃⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, _, rfl, hArg₁, hArg₂, hArg₃, Or.inr hArg₄⟩

private theorem congTypeSpine_uconst_apply_apply_apply_apply_inv
    (i : native_Nat) (T x₁ x₂ x₃ x₄ rhs : Term) :
    CongTypeSpine
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
            x₃) x₄) rhs ->
      ∃ y₁ y₂ y₃ y₄,
        rhs =
          Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
              y₃) y₄ ∧
          EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ ∧
            EqBoolOrSame x₃ y₃ ∧ EqBoolOrSame x₄ y₄ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, rfl, Or.inl rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₄ =>
      rcases congTypeSpine_uconst_apply_apply_apply_inv i T x₁ x₂ x₃ _
          hHead with
        ⟨y₁, y₂, y₃, hHeadEq, hArg₁, hArg₂, hArg₃⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, _, rfl, hArg₁, hArg₂, hArg₃, Or.inr hArg₄⟩

private theorem congTrueSpine_var_apply_apply_apply_apply_apply_inv
    (M : SmtModel) (s : native_String) (T x₁ x₂ x₃ x₄ x₅ rhs : Term) :
    CongTrueSpine M
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
              x₃) x₄) x₅) rhs ->
      ∃ y₁ y₂ y₃ y₄ y₅,
        rhs =
          Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
                y₃) y₄) y₅ ∧
          EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ ∧
            EqTrueOrSame M x₃ y₃ ∧ EqTrueOrSame M x₄ y₄ ∧
              EqTrueOrSame M x₅ y₅ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, x₅, rfl, Or.inl rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₅ _ =>
      rcases congTrueSpine_var_apply_apply_apply_apply_inv M s T x₁ x₂ x₃
          x₄ _ hHead with
        ⟨y₁, y₂, y₃, y₄, hHeadEq, hArg₁, hArg₂, hArg₃, hArg₄⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, y₄, _, rfl, hArg₁, hArg₂, hArg₃, hArg₄,
        Or.inr hArg₅⟩

private theorem congTrueSpine_uconst_apply_apply_apply_apply_apply_inv
    (M : SmtModel) (i : native_Nat) (T x₁ x₂ x₃ x₄ x₅ rhs : Term) :
    CongTrueSpine M
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
              x₃) x₄) x₅) rhs ->
      ∃ y₁ y₂ y₃ y₄ y₅,
        rhs =
          Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
                y₃) y₄) y₅ ∧
          EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ ∧
            EqTrueOrSame M x₃ y₃ ∧ EqTrueOrSame M x₄ y₄ ∧
              EqTrueOrSame M x₅ y₅ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, x₅, rfl, Or.inl rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₅ _ =>
      rcases congTrueSpine_uconst_apply_apply_apply_apply_inv M i T x₁ x₂ x₃
          x₄ _ hHead with
        ⟨y₁, y₂, y₃, y₄, hHeadEq, hArg₁, hArg₂, hArg₃, hArg₄⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, y₄, _, rfl, hArg₁, hArg₂, hArg₃, hArg₄,
        Or.inr hArg₅⟩

private theorem congTypeSpine_var_apply_apply_apply_apply_apply_inv
    (s : native_String) (T x₁ x₂ x₃ x₄ x₅ rhs : Term) :
    CongTypeSpine
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
              x₃) x₄) x₅) rhs ->
      ∃ y₁ y₂ y₃ y₄ y₅,
        rhs =
          Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
                y₃) y₄) y₅ ∧
          EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ ∧
            EqBoolOrSame x₃ y₃ ∧ EqBoolOrSame x₄ y₄ ∧
              EqBoolOrSame x₅ y₅ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, x₅, rfl, Or.inl rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₅ =>
      rcases congTypeSpine_var_apply_apply_apply_apply_inv s T x₁ x₂ x₃
          x₄ _ hHead with
        ⟨y₁, y₂, y₃, y₄, hHeadEq, hArg₁, hArg₂, hArg₃, hArg₄⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, y₄, _, rfl, hArg₁, hArg₂, hArg₃, hArg₄,
        Or.inr hArg₅⟩

private theorem congTypeSpine_uconst_apply_apply_apply_apply_apply_inv
    (i : native_Nat) (T x₁ x₂ x₃ x₄ x₅ rhs : Term) :
    CongTypeSpine
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
              x₃) x₄) x₅) rhs ->
      ∃ y₁ y₂ y₃ y₄ y₅,
        rhs =
          Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
                y₃) y₄) y₅ ∧
          EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ ∧
            EqBoolOrSame x₃ y₃ ∧ EqBoolOrSame x₄ y₄ ∧
              EqBoolOrSame x₅ y₅ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, x₅, rfl, Or.inl rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₅ =>
      rcases congTypeSpine_uconst_apply_apply_apply_apply_inv i T x₁ x₂ x₃
          x₄ _ hHead with
        ⟨y₁, y₂, y₃, y₄, hHeadEq, hArg₁, hArg₂, hArg₃, hArg₄⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, y₄, _, rfl, hArg₁, hArg₂, hArg₃, hArg₄,
        Or.inr hArg₅⟩

theorem congTrueSpine_var_apply_apply_apply_apply_apply_apply_inv
    (M : SmtModel)
    (s : native_String) (T x₁ x₂ x₃ x₄ x₅ x₆ rhs : Term) :
    CongTrueSpine M
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
                x₃) x₄) x₅) x₆) rhs ->
      ∃ y₁ y₂ y₃ y₄ y₅ y₆,
        rhs =
          Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
                  y₃) y₄) y₅) y₆ ∧
          EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ ∧
            EqTrueOrSame M x₃ y₃ ∧ EqTrueOrSame M x₄ y₄ ∧
              EqTrueOrSame M x₅ y₅ ∧ EqTrueOrSame M x₆ y₆ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, x₅, x₆, rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₆ _ =>
      rcases congTrueSpine_var_apply_apply_apply_apply_apply_inv M s T
          x₁ x₂ x₃ x₄ x₅ _ hHead with
        ⟨y₁, y₂, y₃, y₄, y₅, hHeadEq, hArg₁, hArg₂, hArg₃, hArg₄,
          hArg₅⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, y₄, y₅, _, rfl, hArg₁, hArg₂, hArg₃,
        hArg₄, hArg₅, Or.inr hArg₆⟩

theorem congTrueSpine_uconst_apply_apply_apply_apply_apply_apply_inv
    (M : SmtModel) (i : native_Nat) (T x₁ x₂ x₃ x₄ x₅ x₆ rhs : Term) :
    CongTrueSpine M
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
                x₃) x₄) x₅) x₆) rhs ->
      ∃ y₁ y₂ y₃ y₄ y₅ y₆,
        rhs =
          Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
                  y₃) y₄) y₅) y₆ ∧
          EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ ∧
            EqTrueOrSame M x₃ y₃ ∧ EqTrueOrSame M x₄ y₄ ∧
              EqTrueOrSame M x₅ y₅ ∧ EqTrueOrSame M x₆ y₆ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, x₅, x₆, rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₆ _ =>
      rcases congTrueSpine_uconst_apply_apply_apply_apply_apply_inv M i T
          x₁ x₂ x₃ x₄ x₅ _ hHead with
        ⟨y₁, y₂, y₃, y₄, y₅, hHeadEq, hArg₁, hArg₂, hArg₃, hArg₄,
          hArg₅⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, y₄, y₅, _, rfl, hArg₁, hArg₂, hArg₃,
        hArg₄, hArg₅, Or.inr hArg₆⟩

private theorem congTypeSpine_var_apply_apply_apply_apply_apply_apply_inv
    (s : native_String) (T x₁ x₂ x₃ x₄ x₅ x₆ rhs : Term) :
    CongTypeSpine
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
                x₃) x₄) x₅) x₆) rhs ->
      ∃ y₁ y₂ y₃ y₄ y₅ y₆,
        rhs =
          Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
                  y₃) y₄) y₅) y₆ ∧
          EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ ∧
            EqBoolOrSame x₃ y₃ ∧ EqBoolOrSame x₄ y₄ ∧
              EqBoolOrSame x₅ y₅ ∧ EqBoolOrSame x₆ y₆ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, x₅, x₆, rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₆ =>
      rcases congTypeSpine_var_apply_apply_apply_apply_apply_inv s T
          x₁ x₂ x₃ x₄ x₅ _ hHead with
        ⟨y₁, y₂, y₃, y₄, y₅, hHeadEq, hArg₁, hArg₂, hArg₃, hArg₄,
          hArg₅⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, y₄, y₅, _, rfl, hArg₁, hArg₂, hArg₃,
        hArg₄, hArg₅, Or.inr hArg₆⟩

private theorem congTypeSpine_uconst_apply_apply_apply_apply_apply_apply_inv
    (i : native_Nat) (T x₁ x₂ x₃ x₄ x₅ x₆ rhs : Term) :
    CongTypeSpine
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
                x₃) x₄) x₅) x₆) rhs ->
      ∃ y₁ y₂ y₃ y₄ y₅ y₆,
        rhs =
          Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
                  y₃) y₄) y₅) y₆ ∧
          EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ ∧
            EqBoolOrSame x₃ y₃ ∧ EqBoolOrSame x₄ y₄ ∧
              EqBoolOrSame x₅ y₅ ∧ EqBoolOrSame x₆ y₆ := by
  intro hSpine
  cases hSpine with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, x₅, x₆, rfl, Or.inl rfl,
        Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₆ =>
      rcases congTypeSpine_uconst_apply_apply_apply_apply_apply_inv i T
          x₁ x₂ x₃ x₄ x₅ _ hHead with
        ⟨y₁, y₂, y₃, y₄, y₅, hHeadEq, hArg₁, hArg₂, hArg₃, hArg₄,
          hArg₅⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, y₄, y₅, _, rfl, hArg₁, hArg₂, hArg₃,
        hArg₄, hArg₅, Or.inr hArg₆⟩

theorem congTypeSpine_var_apply_eq_has_bool_type
    (s : native_String) (T x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Var (Term.String s) T) x) ->
    CongTypeSpine (Term.Apply (Term.Var (Term.String s) T) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Var (Term.String s) T) x) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_var_apply_inv s T x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  have hArgTy :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof (__eo_to_smt y) :=
    smt_type_eq_of_eq_bool_or_same x y hArg
  have hAppTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Var (Term.String s) T) x)) =
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Var (Term.String s) T) y)) := by
    change
      __smtx_typeof
          (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt x)) =
        __smtx_typeof
          (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt y))
    simp [__smtx_typeof, hArgTy]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Var (Term.String s) T) x)
    (Term.Apply (Term.Var (Term.String s) T) y)
    hAppTy hTrans

theorem congTypeSpine_uconst_apply_eq_has_bool_type
    (i : native_Nat) (T x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UConst i T) x) ->
    CongTypeSpine (Term.Apply (Term.UConst i T) x) rhs ->
    RuleProofs.eo_has_bool_type (mkEq (Term.Apply (Term.UConst i T) x) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_uconst_apply_inv i T x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  have hArgTy :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof (__eo_to_smt y) :=
    smt_type_eq_of_eq_bool_or_same x y hArg
  have hAppTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UConst i T) x)) =
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.UConst i T) y)) := by
    change
      __smtx_typeof
          (SmtTerm.Apply (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            (__eo_to_smt x)) =
        __smtx_typeof
          (SmtTerm.Apply (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            (__eo_to_smt y))
    simp [__smtx_typeof, hArgTy]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UConst i T) x)
    (Term.Apply (Term.UConst i T) y)
    hAppTy hTrans

theorem congTypeSpine_var_apply_apply_eq_has_bool_type
    (s : native_String) (T x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
        rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_var_apply_apply_inv s T x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  have hArgTy₁ :
      __smtx_typeof (__eo_to_smt x₁) =
        __smtx_typeof (__eo_to_smt y₁) :=
    smt_type_eq_of_eq_bool_or_same x₁ y₁ hArg₁
  have hArgTy₂ :
      __smtx_typeof (__eo_to_smt x₂) =
        __smtx_typeof (__eo_to_smt y₂) :=
    smt_type_eq_of_eq_bool_or_same x₂ y₂ hArg₂
  have hAppTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)) := by
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T))
              (__eo_to_smt x₁))
            (__eo_to_smt x₂)) =
        __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T))
              (__eo_to_smt y₁))
            (__eo_to_smt y₂))
    simp [__smtx_typeof, hArgTy₁, hArgTy₂]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
    (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
    hAppTy hTrans

theorem congTypeSpine_uconst_apply_apply_eq_has_bool_type
    (i : native_Nat) (T x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) ->
    CongTypeSpine (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_uconst_apply_apply_inv i T x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  have hArgTy₁ :
      __smtx_typeof (__eo_to_smt x₁) =
        __smtx_typeof (__eo_to_smt y₁) :=
    smt_type_eq_of_eq_bool_or_same x₁ y₁ hArg₁
  have hArgTy₂ :
      __smtx_typeof (__eo_to_smt x₂) =
        __smtx_typeof (__eo_to_smt y₂) :=
    smt_type_eq_of_eq_bool_or_same x₂ y₂ hArg₂
  have hAppTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)) =
        __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)) := by
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
              (__eo_to_smt x₁))
            (__eo_to_smt x₂)) =
        __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
              (__eo_to_smt y₁))
            (__eo_to_smt y₂))
    simp [__smtx_typeof, hArgTy₁, hArgTy₂]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
    (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
    hAppTy hTrans

theorem congTypeSpine_var_apply_apply_apply_eq_has_bool_type
    (s : native_String) (T x₁ x₂ x₃ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
        x₃) ->
    CongTypeSpine
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
        x₃) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
          x₃) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_var_apply_apply_apply_inv s T x₁ x₂ x₃ rhs hSpine with
    ⟨y₁, y₂, y₃, hRhs, hArg₁, hArg₂, hArg₃⟩
  subst hRhs
  have hArgTy₁ :
      __smtx_typeof (__eo_to_smt x₁) =
        __smtx_typeof (__eo_to_smt y₁) :=
    smt_type_eq_of_eq_bool_or_same x₁ y₁ hArg₁
  have hArgTy₂ :
      __smtx_typeof (__eo_to_smt x₂) =
        __smtx_typeof (__eo_to_smt y₂) :=
    smt_type_eq_of_eq_bool_or_same x₂ y₂ hArg₂
  have hArgTy₃ :
      __smtx_typeof (__eo_to_smt x₃) =
        __smtx_typeof (__eo_to_smt y₃) :=
    smt_type_eq_of_eq_bool_or_same x₃ y₃ hArg₃
  have hAppTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
              x₃)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
              y₃)) := by
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T))
                (__eo_to_smt x₁))
              (__eo_to_smt x₂))
            (__eo_to_smt x₃)) =
        __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T))
                (__eo_to_smt y₁))
              (__eo_to_smt y₂))
            (__eo_to_smt y₃))
    simp [__smtx_typeof, hArgTy₁, hArgTy₂, hArgTy₃]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply
      (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) x₃)
    (Term.Apply
      (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂) y₃)
    hAppTy hTrans

theorem congTypeSpine_uconst_apply_apply_apply_eq_has_bool_type
    (i : native_Nat) (T x₁ x₂ x₃ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
        rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_uconst_apply_apply_apply_inv i T x₁ x₂ x₃ rhs
      hSpine with
    ⟨y₁, y₂, y₃, hRhs, hArg₁, hArg₂, hArg₃⟩
  subst hRhs
  have hArgTy₁ :
      __smtx_typeof (__eo_to_smt x₁) =
        __smtx_typeof (__eo_to_smt y₁) :=
    smt_type_eq_of_eq_bool_or_same x₁ y₁ hArg₁
  have hArgTy₂ :
      __smtx_typeof (__eo_to_smt x₂) =
        __smtx_typeof (__eo_to_smt y₂) :=
    smt_type_eq_of_eq_bool_or_same x₂ y₂ hArg₂
  have hArgTy₃ :
      __smtx_typeof (__eo_to_smt x₃) =
        __smtx_typeof (__eo_to_smt y₃) :=
    smt_type_eq_of_eq_bool_or_same x₃ y₃ hArg₃
  have hAppTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
              x₃)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
              y₃)) := by
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.Apply
                (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
                (__eo_to_smt x₁))
              (__eo_to_smt x₂))
            (__eo_to_smt x₃)) =
        __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.Apply
                (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
                (__eo_to_smt y₁))
              (__eo_to_smt y₂))
            (__eo_to_smt y₃))
    simp [__smtx_typeof, hArgTy₁, hArgTy₂, hArgTy₃]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
    (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂) y₃)
    hAppTy hTrans

theorem congTypeSpine_var_apply_apply_apply_apply_eq_has_bool_type
    (s : native_String) (T x₁ x₂ x₃ x₄ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
          x₃) x₄) ->
    CongTypeSpine
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
          x₃) x₄) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
            x₃) x₄) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_var_apply_apply_apply_apply_inv
      s T x₁ x₂ x₃ x₄ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, hRhs, hArg₁, hArg₂, hArg₃, hArg₄⟩
  subst hRhs
  have hArgTy₁ :
      __smtx_typeof (__eo_to_smt x₁) =
        __smtx_typeof (__eo_to_smt y₁) :=
    smt_type_eq_of_eq_bool_or_same x₁ y₁ hArg₁
  have hArgTy₂ :
      __smtx_typeof (__eo_to_smt x₂) =
        __smtx_typeof (__eo_to_smt y₂) :=
    smt_type_eq_of_eq_bool_or_same x₂ y₂ hArg₂
  have hArgTy₃ :
      __smtx_typeof (__eo_to_smt x₃) =
        __smtx_typeof (__eo_to_smt y₃) :=
    smt_type_eq_of_eq_bool_or_same x₃ y₃ hArg₃
  have hArgTy₄ :
      __smtx_typeof (__eo_to_smt x₄) =
        __smtx_typeof (__eo_to_smt y₄) :=
    smt_type_eq_of_eq_bool_or_same x₄ y₄ hArg₄
  have hAppTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
                x₃) x₄)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
                y₃) y₄)) := by
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T))
                  (__eo_to_smt x₁))
                (__eo_to_smt x₂))
              (__eo_to_smt x₃))
            (__eo_to_smt x₄)) =
        __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T))
                  (__eo_to_smt y₁))
                (__eo_to_smt y₂))
              (__eo_to_smt y₃))
            (__eo_to_smt y₄))
    simp [__smtx_typeof, hArgTy₁, hArgTy₂, hArgTy₃, hArgTy₄]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
        x₃) x₄)
    (Term.Apply
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
        y₃) y₄)
    hAppTy hTrans

theorem congTypeSpine_uconst_apply_apply_apply_apply_eq_has_bool_type
    (i : native_Nat) (T x₁ x₂ x₃ x₄ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
          x₃) x₄) ->
    CongTypeSpine
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
          x₃) x₄) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
            x₃) x₄) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_uconst_apply_apply_apply_apply_inv
      i T x₁ x₂ x₃ x₄ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, hRhs, hArg₁, hArg₂, hArg₃, hArg₄⟩
  subst hRhs
  have hArgTy₁ :
      __smtx_typeof (__eo_to_smt x₁) =
        __smtx_typeof (__eo_to_smt y₁) :=
    smt_type_eq_of_eq_bool_or_same x₁ y₁ hArg₁
  have hArgTy₂ :
      __smtx_typeof (__eo_to_smt x₂) =
        __smtx_typeof (__eo_to_smt y₂) :=
    smt_type_eq_of_eq_bool_or_same x₂ y₂ hArg₂
  have hArgTy₃ :
      __smtx_typeof (__eo_to_smt x₃) =
        __smtx_typeof (__eo_to_smt y₃) :=
    smt_type_eq_of_eq_bool_or_same x₃ y₃ hArg₃
  have hArgTy₄ :
      __smtx_typeof (__eo_to_smt x₄) =
        __smtx_typeof (__eo_to_smt y₄) :=
    smt_type_eq_of_eq_bool_or_same x₄ y₄ hArg₄
  have hAppTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
                x₃) x₄)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
                y₃) y₄)) := by
    change
      __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.Apply
                (SmtTerm.Apply
                  (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
                  (__eo_to_smt x₁))
                (__eo_to_smt x₂))
              (__eo_to_smt x₃))
            (__eo_to_smt x₄)) =
        __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.Apply
                (SmtTerm.Apply
                  (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
                  (__eo_to_smt y₁))
                (__eo_to_smt y₂))
              (__eo_to_smt y₃))
            (__eo_to_smt y₄))
    simp [__smtx_typeof, hArgTy₁, hArgTy₂, hArgTy₃, hArgTy₄]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply
      (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
        x₃) x₄)
    (Term.Apply
      (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
        y₃) y₄)
    hAppTy hTrans

theorem congTypeSpine_var_apply_apply_apply_apply_apply_eq_has_bool_type
    (s : native_String) (T x₁ x₂ x₃ x₄ x₅ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
            x₃) x₄) x₅) ->
    CongTypeSpine
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
            x₃) x₄) x₅) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
              x₃) x₄) x₅) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_var_apply_apply_apply_apply_apply_inv
      s T x₁ x₂ x₃ x₄ x₅ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, y₅, hRhs, hArg₁, hArg₂, hArg₃, hArg₄, hArg₅⟩
  subst hRhs
  have hAppTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁)
                    x₂) x₃) x₄) x₅)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁)
                    y₂) y₃) y₄) y₅)) := by
    change
      __smtx_typeof
          (mkSmtAppSpineRev (SmtTerm.Var s (__eo_to_smt_type T))
            [__eo_to_smt x₅, __eo_to_smt x₄, __eo_to_smt x₃,
              __eo_to_smt x₂, __eo_to_smt x₁]) =
        __smtx_typeof
          (mkSmtAppSpineRev (SmtTerm.Var s (__eo_to_smt_type T))
            [__eo_to_smt y₅, __eo_to_smt y₄, __eo_to_smt y₃,
              __eo_to_smt y₂, __eo_to_smt y₁])
    exact smt_app_spine_type_eq_of_listRel_bool rfl
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (ListRel.cons hArg₅
        (ListRel.cons hArg₄
          (ListRel.cons hArg₃
            (ListRel.cons hArg₂
              (ListRel.cons hArg₁ ListRel.nil)))))
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
          x₃) x₄) x₅)
    (Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
          y₃) y₄) y₅)
    hAppTy hTrans

theorem congTypeSpine_uconst_apply_apply_apply_apply_apply_eq_has_bool_type
    (i : native_Nat) (T x₁ x₂ x₃ x₄ x₅ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
            x₃) x₄) x₅) ->
    CongTypeSpine
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
            x₃) x₄) x₅) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
              x₃) x₄) x₅) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_uconst_apply_apply_apply_apply_apply_inv
      i T x₁ x₂ x₃ x₄ x₅ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, y₅, hRhs, hArg₁, hArg₂, hArg₃, hArg₄, hArg₅⟩
  subst hRhs
  have hAppTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁)
                  x₂) x₃) x₄) x₅)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁)
                  y₂) y₃) y₄) y₅)) := by
    change
      __smtx_typeof
          (mkSmtAppSpineRev
            (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            [__eo_to_smt x₅, __eo_to_smt x₄, __eo_to_smt x₃,
              __eo_to_smt x₂, __eo_to_smt x₁]) =
        __smtx_typeof
          (mkSmtAppSpineRev
            (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            [__eo_to_smt y₅, __eo_to_smt y₄, __eo_to_smt y₃,
              __eo_to_smt y₂, __eo_to_smt y₁])
    exact smt_app_spine_type_eq_of_listRel_bool rfl
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (ListRel.cons hArg₅
        (ListRel.cons hArg₄
          (ListRel.cons hArg₃
            (ListRel.cons hArg₂
              (ListRel.cons hArg₁ ListRel.nil)))))
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
          x₃) x₄) x₅)
    (Term.Apply
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
          y₃) y₄) y₅)
    hAppTy hTrans

theorem congTypeSpine_var_apply_apply_apply_apply_apply_apply_eq_has_bool_type
    (s : native_String) (T x₁ x₂ x₃ x₄ x₅ x₆ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
              x₃) x₄) x₅) x₆) ->
    CongTypeSpine
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
              x₃) x₄) x₅) x₆) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
                x₃) x₄) x₅) x₆) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_var_apply_apply_apply_apply_apply_apply_inv
      s T x₁ x₂ x₃ x₄ x₅ x₆ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, y₅, y₆, hRhs, hArg₁, hArg₂, hArg₃, hArg₄, hArg₅,
      hArg₆⟩
  subst hRhs
  have hAppTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁)
                      x₂) x₃) x₄) x₅) x₆)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁)
                      y₂) y₃) y₄) y₅) y₆)) := by
    change
      __smtx_typeof
          (mkSmtAppSpineRev (SmtTerm.Var s (__eo_to_smt_type T))
            [__eo_to_smt x₆, __eo_to_smt x₅, __eo_to_smt x₄,
              __eo_to_smt x₃, __eo_to_smt x₂, __eo_to_smt x₁]) =
        __smtx_typeof
          (mkSmtAppSpineRev (SmtTerm.Var s (__eo_to_smt_type T))
            [__eo_to_smt y₆, __eo_to_smt y₅, __eo_to_smt y₄,
              __eo_to_smt y₃, __eo_to_smt y₂, __eo_to_smt y₁])
    exact smt_app_spine_type_eq_of_listRel_bool rfl
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (ListRel.cons hArg₆
        (ListRel.cons hArg₅
          (ListRel.cons hArg₄
            (ListRel.cons hArg₃
              (ListRel.cons hArg₂
                (ListRel.cons hArg₁ ListRel.nil))))))
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
            x₃) x₄) x₅) x₆)
    (Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
            y₃) y₄) y₅) y₆)
    hAppTy hTrans

theorem congTypeSpine_uconst_apply_apply_apply_apply_apply_apply_eq_has_bool_type
    (i : native_Nat) (T x₁ x₂ x₃ x₄ x₅ x₆ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
              x₃) x₄) x₅) x₆) ->
    CongTypeSpine
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
              x₃) x₄) x₅) x₆) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
                x₃) x₄) x₅) x₆) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_uconst_apply_apply_apply_apply_apply_apply_inv
      i T x₁ x₂ x₃ x₄ x₅ x₆ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, y₅, y₆, hRhs, hArg₁, hArg₂, hArg₃, hArg₄, hArg₅,
      hArg₆⟩
  subst hRhs
  have hAppTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁)
                    x₂) x₃) x₄) x₅) x₆)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁)
                    y₂) y₃) y₄) y₅) y₆)) := by
    change
      __smtx_typeof
          (mkSmtAppSpineRev
            (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            [__eo_to_smt x₆, __eo_to_smt x₅, __eo_to_smt x₄,
              __eo_to_smt x₃, __eo_to_smt x₂, __eo_to_smt x₁]) =
        __smtx_typeof
          (mkSmtAppSpineRev
            (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            [__eo_to_smt y₆, __eo_to_smt y₅, __eo_to_smt y₄,
              __eo_to_smt y₃, __eo_to_smt y₂, __eo_to_smt y₁])
    exact smt_app_spine_type_eq_of_listRel_bool rfl
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      (ListRel.cons hArg₆
        (ListRel.cons hArg₅
          (ListRel.cons hArg₄
            (ListRel.cons hArg₃
              (ListRel.cons hArg₂
                (ListRel.cons hArg₁ ListRel.nil))))))
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
            x₃) x₄) x₅) x₆)
    (Term.Apply
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
            y₃) y₄) y₅) y₆)
    hAppTy hTrans

theorem congTrueSpine_var_apply_eq_true
    (M : SmtModel) (hM : model_wf M)
    (s : native_String) (T x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Var (Term.String s) T) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.Var (Term.String s) T) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Var (Term.String s) T) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_var_apply_inv M s T x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Var (Term.String s) T) x)
        (Term.Apply (Term.Var (Term.String s) T) y) hEqBool
    have hLeftNN :
        __smtx_typeof
          (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt x)) ≠
            SmtType.None := by
      exact hTypes.2
    have hAppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)))
            (__smtx_typeof (__eo_to_smt x)) ≠ SmtType.None := by
      simpa [__smtx_typeof] using hLeftNN
    have hArgTy :
        __smtx_typeof (__eo_to_smt x) =
          __smtx_typeof (__eo_to_smt y) :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    have hArgRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)) :=
      smt_value_rel_of_eq_true_or_same M x y hArg
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt x)))
        (__smtx_model_eval M
          (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt y)))
    simpa [__smtx_model_eval] using
      smt_value_rel_model_eval_apply_of_rel_core M hM
      (SmtTerm.Var s (__eo_to_smt_type T))
      (SmtTerm.Var s (__eo_to_smt_type T))
      (__eo_to_smt x) (__eo_to_smt y)
      hAppNN rfl hArgTy (RuleProofs.smt_value_rel_refl _) hArgRel

theorem congTrueSpine_uconst_apply_eq_true
    (M : SmtModel) (hM : model_wf M)
    (i : native_Nat) (T x rhs : Term) :
    RuleProofs.eo_has_bool_type (mkEq (Term.Apply (Term.UConst i T) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UConst i T) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UConst i T) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_uconst_apply_inv M i T x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UConst i T) x)
        (Term.Apply (Term.UConst i T) y) hEqBool
    have hLeftNN :
        __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            (__eo_to_smt x)) ≠ SmtType.None := by
      exact hTypes.2
    have hAppNN :
        __smtx_typeof_apply
            (__smtx_typeof
              (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)))
            (__smtx_typeof (__eo_to_smt x)) ≠ SmtType.None := by
      simpa [__smtx_typeof] using hLeftNN
    have hArgTy :
        __smtx_typeof (__eo_to_smt x) =
          __smtx_typeof (__eo_to_smt y) :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    have hArgRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)) :=
      smt_value_rel_of_eq_true_or_same M x y hArg
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.Apply
            (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            (__eo_to_smt x)))
        (__smtx_model_eval M
          (SmtTerm.Apply
            (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            (__eo_to_smt y)))
    simpa [__smtx_model_eval] using
      smt_value_rel_model_eval_apply_of_rel_core M hM
      (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
      (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
      (__eo_to_smt x) (__eo_to_smt y)
      hAppNN rfl hArgTy (RuleProofs.smt_value_rel_refl _) hArgRel

theorem congTrueSpine_var_apply_apply_eq_true
    (M : SmtModel) (hM : model_wf M)
    (s : native_String) (T x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
        rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_var_apply_apply_inv M s T x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm := SmtTerm.Var s (__eo_to_smt_type T)
    let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
        hEqBool
    have hOuterLeftNN :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) ≠
          SmtType.None := by
      exact hTypes.2
    have hOuterAppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Apply F X₁)) (__smtx_typeof X₂) ≠
          SmtType.None := by
      simpa [__smtx_typeof] using hOuterLeftNN
    have hInnerNN :
        __smtx_typeof (SmtTerm.Apply F X₁) ≠ SmtType.None := by
      rcases typeof_apply_non_none_cases hOuterAppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      exact smt_type_ne_none_of_apply_head hHead
    have hInnerAppNN :
        __smtx_typeof_apply (__smtx_typeof F) (__smtx_typeof X₁) ≠
          SmtType.None := by
      simpa [__smtx_typeof] using hInnerNN
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ := by
      exact smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ := by
      exact smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgRel₁ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₁) (__smtx_model_eval M Y₁) := by
      exact smt_value_rel_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) := by
      exact smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hInnerTy :
        __smtx_typeof (SmtTerm.Apply F X₁) =
          __smtx_typeof (SmtTerm.Apply F Y₁) := by
      simp [__smtx_typeof, hArgTy₁]
    have hInnerRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.Apply F X₁))
          (__smtx_model_eval M (SmtTerm.Apply F Y₁)) := by
      simpa [__smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM F F X₁ Y₁
          hInnerAppNN rfl hArgTy₁
          (RuleProofs.smt_value_rel_refl _) hArgRel₁
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂))
        (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂))
    simpa [__smtx_model_eval] using
      smt_value_rel_model_eval_apply_of_rel_core M hM
        (SmtTerm.Apply F X₁) (SmtTerm.Apply F Y₁) X₂ Y₂
        hOuterAppNN hInnerTy hArgTy₂ hInnerRel hArgRel₂

theorem congTrueSpine_uconst_apply_apply_eq_true
    (M : SmtModel) (hM : model_wf M)
    (i : native_Nat) (T x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) rhs) ->
    CongTrueSpine M (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_uconst_apply_apply_inv M i T x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm :=
      SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)
    let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
        (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂) hEqBool
    have hOuterLeftNN :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) ≠
          SmtType.None := by
      exact hTypes.2
    have hOuterAppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Apply F X₁)) (__smtx_typeof X₂) ≠
          SmtType.None := by
      simpa [__smtx_typeof] using hOuterLeftNN
    have hInnerNN :
        __smtx_typeof (SmtTerm.Apply F X₁) ≠ SmtType.None := by
      rcases typeof_apply_non_none_cases hOuterAppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      exact smt_type_ne_none_of_apply_head hHead
    have hInnerAppNN :
        __smtx_typeof_apply (__smtx_typeof F) (__smtx_typeof X₁) ≠
          SmtType.None := by
      simpa [__smtx_typeof] using hInnerNN
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ := by
      exact smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ := by
      exact smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgRel₁ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₁) (__smtx_model_eval M Y₁) := by
      exact smt_value_rel_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) := by
      exact smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hInnerTy :
        __smtx_typeof (SmtTerm.Apply F X₁) =
          __smtx_typeof (SmtTerm.Apply F Y₁) := by
      simp [__smtx_typeof, hArgTy₁]
    have hInnerRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.Apply F X₁))
          (__smtx_model_eval M (SmtTerm.Apply F Y₁)) := by
      simpa [__smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM F F X₁ Y₁
          hInnerAppNN rfl hArgTy₁
          (RuleProofs.smt_value_rel_refl _) hArgRel₁
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂))
        (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂))
    simpa [__smtx_model_eval] using
      smt_value_rel_model_eval_apply_of_rel_core M hM
        (SmtTerm.Apply F X₁) (SmtTerm.Apply F Y₁) X₂ Y₂
        hOuterAppNN hInnerTy hArgTy₂ hInnerRel hArgRel₂

theorem congTrueSpine_var_apply_apply_apply_eq_true
    (M : SmtModel) (hM : model_wf M)
    (s : native_String) (T x₁ x₂ x₃ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
          x₃) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
        x₃) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
          x₃) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_var_apply_apply_apply_inv M s T x₁ x₂ x₃ rhs
      hSpine with
    ⟨y₁, y₂, y₃, hRhs, hArg₁, hArg₂, hArg₃⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm := SmtTerm.Var s (__eo_to_smt_type T)
    let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
          x₃)
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
          y₃) hEqBool
    have hOuterLeftNN :
        __smtx_typeof
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃) ≠
          SmtType.None := by
      exact hTypes.2
    have hOuterAppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂))
            (__smtx_typeof X₃) ≠ SmtType.None := by
      simpa [__smtx_typeof] using hOuterLeftNN
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ := by
      exact smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ := by
      exact smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgTy₃ : __smtx_typeof X₃ = __smtx_typeof Y₃ := by
      exact smt_type_eq_of_eq_true_or_same M x₃ y₃ hArg₃
    have hArgRel₁ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₁) (__smtx_model_eval M Y₁) := by
      exact smt_value_rel_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) := by
      exact smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgRel₃ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₃) (__smtx_model_eval M Y₃) := by
      exact smt_value_rel_of_eq_true_or_same M x₃ y₃ hArg₃
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃))
        (__smtx_model_eval M
          (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) Y₃))
    have hMidNN :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) ≠
          SmtType.None := by
      rcases typeof_apply_non_none_cases hOuterAppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      exact smt_type_ne_none_of_apply_head hHead
    have hMidAppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Apply F X₁)) (__smtx_typeof X₂) ≠
          SmtType.None := by
      simpa [__smtx_typeof] using hMidNN
    have hInnerNN :
        __smtx_typeof (SmtTerm.Apply F X₁) ≠ SmtType.None := by
      rcases typeof_apply_non_none_cases hMidAppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      exact smt_type_ne_none_of_apply_head hHead
    have hInnerAppNN :
        __smtx_typeof_apply (__smtx_typeof F) (__smtx_typeof X₁) ≠
          SmtType.None := by
      simpa [F, __smtx_typeof] using hInnerNN
    have hInnerTy :
        __smtx_typeof (SmtTerm.Apply F X₁) =
          __smtx_typeof (SmtTerm.Apply F Y₁) := by
      simp [F, __smtx_typeof, hArgTy₁]
    have hInnerRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.Apply F X₁))
          (__smtx_model_eval M (SmtTerm.Apply F Y₁)) := by
      simpa [F, __smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM F F X₁ Y₁
          hInnerAppNN rfl hArgTy₁
          (RuleProofs.smt_value_rel_refl _) hArgRel₁
    have hMidTy :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) =
          __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) := by
      simp [__smtx_typeof, hInnerTy, hArgTy₂]
    have hMidRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂))
          (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂)) := by
      simpa [__smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM
          (SmtTerm.Apply F X₁) (SmtTerm.Apply F Y₁) X₂ Y₂
          hMidAppNN hInnerTy hArgTy₂ hInnerRel hArgRel₂
    simpa [__smtx_model_eval] using
      smt_value_rel_model_eval_apply_of_rel_core M hM
        (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂)
        (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) X₃ Y₃
        hOuterAppNN hMidTy hArgTy₃ hMidRel hArgRel₃

theorem congTrueSpine_uconst_apply_apply_apply_eq_true
    (M : SmtModel) (hM : model_wf M)
    (i : native_Nat) (T x₁ x₂ x₃ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
      rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
        rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_uconst_apply_apply_apply_inv M i T x₁ x₂ x₃ rhs
      hSpine with
    ⟨y₁, y₂, y₃, hRhs, hArg₁, hArg₂, hArg₃⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm :=
      SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)
    let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂) x₃)
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂) y₃)
        hEqBool
    have hOuterLeftNN :
        __smtx_typeof
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃) ≠
          SmtType.None := by
      exact hTypes.2
    have hOuterAppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂))
            (__smtx_typeof X₃) ≠ SmtType.None := by
      simpa [__smtx_typeof] using hOuterLeftNN
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ := by
      exact smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ := by
      exact smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgTy₃ : __smtx_typeof X₃ = __smtx_typeof Y₃ := by
      exact smt_type_eq_of_eq_true_or_same M x₃ y₃ hArg₃
    have hArgRel₁ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₁) (__smtx_model_eval M Y₁) := by
      exact smt_value_rel_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) := by
      exact smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgRel₃ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₃) (__smtx_model_eval M Y₃) := by
      exact smt_value_rel_of_eq_true_or_same M x₃ y₃ hArg₃
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃))
        (__smtx_model_eval M
          (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) Y₃))
    have hMidNN :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) ≠
          SmtType.None := by
      rcases typeof_apply_non_none_cases hOuterAppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      exact smt_type_ne_none_of_apply_head hHead
    have hMidAppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Apply F X₁)) (__smtx_typeof X₂) ≠
          SmtType.None := by
      simpa [__smtx_typeof] using hMidNN
    have hInnerNN :
        __smtx_typeof (SmtTerm.Apply F X₁) ≠ SmtType.None := by
      rcases typeof_apply_non_none_cases hMidAppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      exact smt_type_ne_none_of_apply_head hHead
    have hInnerAppNN :
        __smtx_typeof_apply (__smtx_typeof F) (__smtx_typeof X₁) ≠
          SmtType.None := by
      simpa [F, __smtx_typeof] using hInnerNN
    have hInnerTy :
        __smtx_typeof (SmtTerm.Apply F X₁) =
          __smtx_typeof (SmtTerm.Apply F Y₁) := by
      simp [F, __smtx_typeof, hArgTy₁]
    have hInnerRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.Apply F X₁))
          (__smtx_model_eval M (SmtTerm.Apply F Y₁)) := by
      simpa [F, __smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM F F X₁ Y₁
          hInnerAppNN rfl hArgTy₁
          (RuleProofs.smt_value_rel_refl _) hArgRel₁
    have hMidTy :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) =
          __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) := by
      simp [__smtx_typeof, hInnerTy, hArgTy₂]
    have hMidRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂))
          (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂)) := by
      simpa [__smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM
          (SmtTerm.Apply F X₁) (SmtTerm.Apply F Y₁) X₂ Y₂
          hMidAppNN hInnerTy hArgTy₂ hInnerRel hArgRel₂
    simpa [__smtx_model_eval] using
      smt_value_rel_model_eval_apply_of_rel_core M hM
        (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂)
        (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) X₃ Y₃
        hOuterAppNN hMidTy hArgTy₃ hMidRel hArgRel₃

theorem congTrueSpine_var_apply_apply_apply_apply_eq_true
    (M : SmtModel) (hM : model_wf M)
    (s : native_String) (T x₁ x₂ x₃ x₄ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
            x₃) x₄) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
          x₃) x₄) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
            x₃) x₄) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_var_apply_apply_apply_apply_inv M s T x₁ x₂ x₃ x₄
      rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, hRhs, hArg₁, hArg₂, hArg₃, hArg₄⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm := SmtTerm.Var s (__eo_to_smt_type T)
    let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let X₄ : SmtTerm := __eo_to_smt x₄
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    let Y₄ : SmtTerm := __eo_to_smt y₄
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
            x₃) x₄)
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
            y₃) y₄) hEqBool
    have hOuterLeftNN :
        __smtx_typeof
            (SmtTerm.Apply
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃)
              X₄) ≠ SmtType.None := by
      exact hTypes.2
    have hOuterAppNN :
        __smtx_typeof_apply
            (__smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃))
            (__smtx_typeof X₄) ≠ SmtType.None := by
      simpa [__smtx_typeof] using hOuterLeftNN
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ := by
      exact smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ := by
      exact smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgTy₃ : __smtx_typeof X₃ = __smtx_typeof Y₃ := by
      exact smt_type_eq_of_eq_true_or_same M x₃ y₃ hArg₃
    have hArgTy₄ : __smtx_typeof X₄ = __smtx_typeof Y₄ := by
      exact smt_type_eq_of_eq_true_or_same M x₄ y₄ hArg₄
    have hArgRel₁ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₁) (__smtx_model_eval M Y₁) := by
      exact smt_value_rel_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) := by
      exact smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgRel₃ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₃) (__smtx_model_eval M Y₃) := by
      exact smt_value_rel_of_eq_true_or_same M x₃ y₃ hArg₃
    have hArgRel₄ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₄) (__smtx_model_eval M Y₄) := by
      exact smt_value_rel_of_eq_true_or_same M x₄ y₄ hArg₄
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.Apply
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃)
            X₄))
        (__smtx_model_eval M
          (SmtTerm.Apply
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) Y₃)
            Y₄))
    have hMid3NN :
        __smtx_typeof
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃) ≠
          SmtType.None := by
      rcases typeof_apply_non_none_cases hOuterAppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      exact smt_type_ne_none_of_apply_head hHead
    have hMid3AppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂))
            (__smtx_typeof X₃) ≠ SmtType.None := by
      simpa [__smtx_typeof] using hMid3NN
    have hMid2NN :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) ≠
          SmtType.None := by
      rcases typeof_apply_non_none_cases hMid3AppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      exact smt_type_ne_none_of_apply_head hHead
    have hMid2AppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Apply F X₁)) (__smtx_typeof X₂) ≠
          SmtType.None := by
      simpa [__smtx_typeof] using hMid2NN
    have hInnerNN :
        __smtx_typeof (SmtTerm.Apply F X₁) ≠ SmtType.None := by
      rcases typeof_apply_non_none_cases hMid2AppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      exact smt_type_ne_none_of_apply_head hHead
    have hInnerAppNN :
        __smtx_typeof_apply (__smtx_typeof F) (__smtx_typeof X₁) ≠
          SmtType.None := by
      simpa [F, __smtx_typeof] using hInnerNN
    have hInnerTy :
        __smtx_typeof (SmtTerm.Apply F X₁) =
          __smtx_typeof (SmtTerm.Apply F Y₁) := by
      simp [F, __smtx_typeof, hArgTy₁]
    have hInnerRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.Apply F X₁))
          (__smtx_model_eval M (SmtTerm.Apply F Y₁)) := by
      simpa [F, __smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM F F X₁ Y₁
          hInnerAppNN rfl hArgTy₁
          (RuleProofs.smt_value_rel_refl _) hArgRel₁
    have hMid2Ty :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) =
          __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) := by
      simp [__smtx_typeof, hInnerTy, hArgTy₂]
    have hMid2Rel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂))
          (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂)) := by
      simpa [__smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM
          (SmtTerm.Apply F X₁) (SmtTerm.Apply F Y₁) X₂ Y₂
          hMid2AppNN hInnerTy hArgTy₂ hInnerRel hArgRel₂
    have hMid3Ty :
        __smtx_typeof
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃) =
          __smtx_typeof
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) Y₃) := by
      simp [__smtx_typeof, hArgTy₁, hArgTy₂, hArgTy₃]
    have hMid3Rel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃))
          (__smtx_model_eval M
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) Y₃)) := by
      simpa [__smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM
          (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂)
          (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) X₃ Y₃
          hMid3AppNN hMid2Ty hArgTy₃ hMid2Rel hArgRel₃
    simpa [__smtx_model_eval] using
      smt_value_rel_model_eval_apply_of_rel_core M hM
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃)
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) Y₃)
        X₄ Y₄ hOuterAppNN hMid3Ty hArgTy₄ hMid3Rel hArgRel₄

theorem congTrueSpine_uconst_apply_apply_apply_apply_eq_true
    (M : SmtModel) (hM : model_wf M)
    (i : native_Nat) (T x₁ x₂ x₃ x₄ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
            x₃) x₄) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
          x₃) x₄) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
            x₃) x₄) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_uconst_apply_apply_apply_apply_inv M i T x₁ x₂ x₃
      x₄ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, hRhs, hArg₁, hArg₂, hArg₃, hArg₄⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm :=
      SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)
    let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let X₄ : SmtTerm := __eo_to_smt x₄
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    let Y₄ : SmtTerm := __eo_to_smt y₄
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
            x₃) x₄)
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
            y₃) y₄) hEqBool
    have hOuterLeftNN :
        __smtx_typeof
            (SmtTerm.Apply
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃)
              X₄) ≠ SmtType.None := by
      exact hTypes.2
    have hOuterAppNN :
        __smtx_typeof_apply
            (__smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃))
            (__smtx_typeof X₄) ≠ SmtType.None := by
      simpa [__smtx_typeof] using hOuterLeftNN
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ := by
      exact smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ := by
      exact smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgTy₃ : __smtx_typeof X₃ = __smtx_typeof Y₃ := by
      exact smt_type_eq_of_eq_true_or_same M x₃ y₃ hArg₃
    have hArgTy₄ : __smtx_typeof X₄ = __smtx_typeof Y₄ := by
      exact smt_type_eq_of_eq_true_or_same M x₄ y₄ hArg₄
    have hArgRel₁ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₁) (__smtx_model_eval M Y₁) := by
      exact smt_value_rel_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) := by
      exact smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgRel₃ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₃) (__smtx_model_eval M Y₃) := by
      exact smt_value_rel_of_eq_true_or_same M x₃ y₃ hArg₃
    have hArgRel₄ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₄) (__smtx_model_eval M Y₄) := by
      exact smt_value_rel_of_eq_true_or_same M x₄ y₄ hArg₄
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.Apply
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃)
            X₄))
        (__smtx_model_eval M
          (SmtTerm.Apply
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) Y₃)
            Y₄))
    have hMid3NN :
        __smtx_typeof
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃) ≠
          SmtType.None := by
      rcases typeof_apply_non_none_cases hOuterAppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      exact smt_type_ne_none_of_apply_head hHead
    have hMid3AppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂))
            (__smtx_typeof X₃) ≠ SmtType.None := by
      simpa [__smtx_typeof] using hMid3NN
    have hMid2NN :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) ≠
          SmtType.None := by
      rcases typeof_apply_non_none_cases hMid3AppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      exact smt_type_ne_none_of_apply_head hHead
    have hMid2AppNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.Apply F X₁)) (__smtx_typeof X₂) ≠
          SmtType.None := by
      simpa [__smtx_typeof] using hMid2NN
    have hInnerNN :
        __smtx_typeof (SmtTerm.Apply F X₁) ≠ SmtType.None := by
      rcases typeof_apply_non_none_cases hMid2AppNN with
        ⟨A, B, hHead, _hX, _hA, _hB⟩
      exact smt_type_ne_none_of_apply_head hHead
    have hInnerAppNN :
        __smtx_typeof_apply (__smtx_typeof F) (__smtx_typeof X₁) ≠
          SmtType.None := by
      simpa [F, __smtx_typeof] using hInnerNN
    have hInnerTy :
        __smtx_typeof (SmtTerm.Apply F X₁) =
          __smtx_typeof (SmtTerm.Apply F Y₁) := by
      simp [F, __smtx_typeof, hArgTy₁]
    have hInnerRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.Apply F X₁))
          (__smtx_model_eval M (SmtTerm.Apply F Y₁)) := by
      simpa [F, __smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM F F X₁ Y₁
          hInnerAppNN rfl hArgTy₁
          (RuleProofs.smt_value_rel_refl _) hArgRel₁
    have hMid2Ty :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) =
          __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) := by
      simp [__smtx_typeof, hInnerTy, hArgTy₂]
    have hMid2Rel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂))
          (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂)) := by
      simpa [__smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM
          (SmtTerm.Apply F X₁) (SmtTerm.Apply F Y₁) X₂ Y₂
          hMid2AppNN hInnerTy hArgTy₂ hInnerRel hArgRel₂
    have hMid3Ty :
        __smtx_typeof
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃) =
          __smtx_typeof
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) Y₃) := by
      simp [__smtx_typeof, hArgTy₁, hArgTy₂, hArgTy₃]
    have hMid3Rel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃))
          (__smtx_model_eval M
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) Y₃)) := by
      simpa [__smtx_model_eval] using
        smt_value_rel_model_eval_apply_of_rel_core M hM
          (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂)
          (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) X₃ Y₃
          hMid3AppNN hMid2Ty hArgTy₃ hMid2Rel hArgRel₃
    simpa [__smtx_model_eval] using
      smt_value_rel_model_eval_apply_of_rel_core M hM
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F X₁) X₂) X₃)
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply F Y₁) Y₂) Y₃)
        X₄ Y₄ hOuterAppNN hMid3Ty hArgTy₄ hMid3Rel hArgRel₄

theorem congTrueSpine_var_apply_apply_apply_apply_apply_eq_true
    (M : SmtModel) (hM : model_wf M)
    (s : native_String) (T x₁ x₂ x₃ x₄ x₅ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
              x₃) x₄) x₅) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
            x₃) x₄) x₅) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
              x₃) x₄) x₅) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_var_apply_apply_apply_apply_apply_inv M s T x₁ x₂ x₃
      x₄ x₅ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, y₅, hRhs, hArg₁, hArg₂, hArg₃, hArg₄, hArg₅⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm := SmtTerm.Var s (__eo_to_smt_type T)
    let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let X₄ : SmtTerm := __eo_to_smt x₄
    let X₅ : SmtTerm := __eo_to_smt x₅
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    let Y₄ : SmtTerm := __eo_to_smt y₄
    let Y₅ : SmtTerm := __eo_to_smt y₅
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) x₁) x₂)
              x₃) x₄) x₅)
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.Var (Term.String s) T) y₁) y₂)
              y₃) y₄) y₅) hEqBool
    have hLeftNN :
        __smtx_typeof
          (mkSmtAppSpineRev F [X₅, X₄, X₃, X₂, X₁]) ≠ SmtType.None := by
      exact hTypes.2
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (mkSmtAppSpineRev F [X₅, X₄, X₃, X₂, X₁]))
        (__smtx_model_eval M (mkSmtAppSpineRev F [Y₅, Y₄, Y₃, Y₂, Y₁]))
    exact
      (smt_app_spine_type_eq_and_rel_of_listRel_true M hM rfl
        (RuleProofs.smt_value_rel_refl _)
        (by intro s d i j h; simp [F] at h)
        (by intro s d i h; simp [F] at h)
        (by intro s d i j h; simp [F] at h)
        (by intro s d i h; simp [F] at h)
        (ListRel.cons hArg₅
          (ListRel.cons hArg₄
            (ListRel.cons hArg₃
              (ListRel.cons hArg₂
                (ListRel.cons hArg₁ ListRel.nil)))))
        hLeftNN).2

theorem congTrueSpine_uconst_apply_apply_apply_apply_apply_eq_true
    (M : SmtModel) (hM : model_wf M)
    (i : native_Nat) (T x₁ x₂ x₃ x₄ x₅ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
              x₃) x₄) x₅) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
            x₃) x₄) x₅) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
              x₃) x₄) x₅) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_uconst_apply_apply_apply_apply_apply_inv M i T x₁ x₂
      x₃ x₄ x₅ rhs hSpine with
    ⟨y₁, y₂, y₃, y₄, y₅, hRhs, hArg₁, hArg₂, hArg₃, hArg₄, hArg₅⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm :=
      SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)
    let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let X₄ : SmtTerm := __eo_to_smt x₄
    let X₅ : SmtTerm := __eo_to_smt x₅
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    let Y₄ : SmtTerm := __eo_to_smt y₄
    let Y₅ : SmtTerm := __eo_to_smt y₅
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) x₁) x₂)
              x₃) x₄) x₅)
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.Apply (Term.UConst i T) y₁) y₂)
              y₃) y₄) y₅) hEqBool
    have hLeftNN :
        __smtx_typeof
          (mkSmtAppSpineRev F [X₅, X₄, X₃, X₂, X₁]) ≠ SmtType.None := by
      exact hTypes.2
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (mkSmtAppSpineRev F [X₅, X₄, X₃, X₂, X₁]))
        (__smtx_model_eval M (mkSmtAppSpineRev F [Y₅, Y₄, Y₃, Y₂, Y₁]))
    exact
      (smt_app_spine_type_eq_and_rel_of_listRel_true M hM rfl
        (RuleProofs.smt_value_rel_refl _)
        (by intro s d i j h; simp [F] at h)
        (by intro s d i h; simp [F] at h)
        (by intro s d i j h; simp [F] at h)
        (by intro s d i h; simp [F] at h)
        (ListRel.cons hArg₅
          (ListRel.cons hArg₄
            (ListRel.cons hArg₃
              (ListRel.cons hArg₂
                (ListRel.cons hArg₁ ListRel.nil)))))
        hLeftNN).2


end CongSupport
