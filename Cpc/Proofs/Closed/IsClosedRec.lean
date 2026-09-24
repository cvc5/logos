module

import Lean
public import Cpc.Proofs.Common
import all Cpc.Proofs.Common
public import Cpc.Proofs.Assumptions
import all Cpc.Proofs.Assumptions
public import Cpc.Proofs.Closed.Support
import all Cpc.Proofs.Closed.Support
public import Cpc.Proofs.TypePreservation.Full
import all Cpc.Proofs.TypePreservation.Full

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

/-- Raw EO binder lists do not themselves translate to well-typed SMT terms. -/
theorem smtx_typeof_eo_list_cons_eq_none (v vs : Term) :
  __smtx_typeof
      (__eo_to_smt (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) =
    SmtType.None :=
by
  change
    __smtx_typeof
        (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt v))
          (__eo_to_smt vs)) =
      SmtType.None
  exact TranslationProofs.typeof_apply_apply_none_head_eq
    (__eo_to_smt v) (__eo_to_smt vs)

/-- The unfolded SMT translation of a raw EO binder list has type `None`. -/
theorem smtx_typeof_unfolded_eo_list_cons_eq_none (v vs : Term) :
  __smtx_typeof
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt v))
        (__eo_to_smt vs)) =
    SmtType.None :=
by
  exact TranslationProofs.typeof_apply_apply_none_head_eq
    (__eo_to_smt v) (__eo_to_smt vs)

/-- Datatype constructors with a `None` field are not well-formed. -/
theorem smtx_dt_cons_wf_rec_cons_none_eq_false
    (dd : SmtDatatypeDecl) (c : SmtDatatypeCons) :
  __smtx_dt_cons_wf_rec dd (SmtDatatypeCons.cons SmtType.None c) =
    false :=
by
  rfl

set_option maxHeartbeats 50000000 in
/--
Non-quantifier `UOp` heads cannot translate to a well-typed SMT term when
the first argument is the raw EO binder-list shape used by `__is_closed_rec`.
-/
theorem smtx_typeof_uop_eo_list_cons_apply_eq_none
    {op : UserOp} (hForall : op ≠ UserOp.forall)
    (hExists : op ≠ UserOp.exists) (v vs body : Term) :
  __smtx_typeof
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) =
    SmtType.None :=
by
  cases op
  case «forall» =>
    exact False.elim (hForall rfl)
  case «exists» =>
    exact False.elim (hExists rfl)
  all_goals
    have hNeg : native_zleq 0 (native_zneg 1) = false := by
      native_decide
    dsimp only [__eo_to_smt]
    simp [smtx_typeof_unfolded_eo_list_cons_eq_none, __smtx_typeof,
      __smtx_typeof_apply, __smtx_typeof_eq, __smtx_typeof_guard,
      __smtx_typeof_guard_wf, __smtx_typeof_ite, __smtx_typeof_bv_op_1,
      __smtx_typeof_bv_op_1_ret, __smtx_typeof_bv_op_2,
      __smtx_typeof_bv_op_2_ret, __smtx_typeof_arith_overload_op_1,
      __smtx_typeof_arith_overload_op_2,
      __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_seq_op_1,
      __smtx_typeof_seq_op_1_ret, __smtx_typeof_seq_op_2,
      __smtx_typeof_seq_op_2_ret, __smtx_typeof_seq_op_3,
      __smtx_typeof_sets_op_2, __smtx_typeof_sets_op_2_ret,
      __smtx_typeof_select, __smtx_typeof_store, __smtx_typeof_concat,
      __smtx_typeof_str_substr, __smtx_typeof_str_indexof,
      __smtx_typeof_str_at, __smtx_typeof_str_update,
      __smtx_typeof_re_exp, __smtx_typeof_re_loop, __smtx_typeof_seq_nth,
      __smtx_typeof_set_member, __smtx_typeof_map_diff,
      __smtx_typeof_seq_diff,
      __smtx_typeof_int_to_bv,
      __eo_to_smt_array_deq_diff,
      __eo_to_smt_sets_deq_diff, __eo_to_smt_set_insert,
      __eo_to_smt_tuple_prepend, __eo_to_smt_tuple_prepend_of_type,
      __eo_to_smt_set_elem_type, __eo_to_smt_typed_list_elem_type,
      __eo_to_smt_bv_size, __smtx_type_wf, __smtx_type_wf_component,
      __smtx_type_wf_rec, __smtx_dt_wf_rec, __smtx_dt_cons_wf_rec,
      __smtx_typeof_dt_cons_rec, smtx_dt_cons_wf_rec_cons_none_eq_false,
      hNeg, native_ite, native_Teq, native_and]
  case _at_strings_stoi_result =>
    by_cases hBodyNone :
        __smtx_typeof (__eo_to_smt body) = SmtType.None
    · simp [hBodyNone]
    · by_cases hBodyInt :
          __smtx_typeof (__eo_to_smt body) = SmtType.Int
      · simp [hBodyNone, hBodyInt]
      · simp [hBodyNone, hBodyInt]
  case _at_strings_itos_result =>
    by_cases hBodyNone :
        __smtx_typeof (__eo_to_smt body) = SmtType.None
    · simp [hBodyNone]
    · by_cases hBodyInt :
          __smtx_typeof (__eo_to_smt body) = SmtType.Int
      · simp [hBodyNone, hBodyInt]
      · simp [hBodyNone, hBodyInt]
  case tuple_unit =>
    generalize hHead :
      (if _ = true ∧ _ = true ∧ _ = true then (_ : SmtType)
       else SmtType.None) = head
    cases head <;> simp
    case FunType T U => cases T <;> simp
    case DtcAppType T U => cases T <;> simp
  case tuple =>
    cases hBody : __smtx_typeof (__eo_to_smt body)
    all_goals
      try
        simp [hBody, smtx_typeof_unfolded_eo_list_cons_eq_none,
          smtx_dt_cons_wf_rec_cons_none_eq_false, __smtx_typeof, native_ite,
          native_Teq, native_and]
    case Datatype s d =>
      cases d with
      | nil =>
          simp [hBody, smtx_typeof_unfolded_eo_list_cons_eq_none,
            smtx_dt_cons_wf_rec_cons_none_eq_false, __smtx_typeof,
            native_ite, native_Teq, native_and]
      | cons s2 body rest =>
          cases rest with
          | cons s3 body3 rest3 =>
              simp [hBody, smtx_typeof_unfolded_eo_list_cons_eq_none,
                smtx_dt_cons_wf_rec_cons_none_eq_false, __smtx_typeof,
                native_ite, native_Teq, native_and]
          | nil =>
              cases body with
              | null =>
                  simp [hBody, smtx_typeof_unfolded_eo_list_cons_eq_none,
                    smtx_dt_cons_wf_rec_cons_none_eq_false, __smtx_typeof,
                    native_ite, native_Teq, native_and]
              | sum c dTail =>
                  cases dTail <;>
                    simp [hBody, smtx_typeof_unfolded_eo_list_cons_eq_none,
                      smtx_dt_cons_wf_rec_cons_none_eq_false, __smtx_typeof,
                      __eo_to_smt_tuple_decl, __smtx_decl_wf_rec,
                      __smtx_dt_wf_rec, native_ite, native_Teq, native_and]
  case set_member =>
    cases hBody : __smtx_typeof (__eo_to_smt body)
    all_goals simp [hBody, native_Teq]
    case Set a =>
      have hBodyNonNone : term_has_non_none_type (__eo_to_smt body) := by
        unfold term_has_non_none_type
        rw [hBody]
        intro hNone
        cases hNone
      have hNoNone :=
        term_type_has_no_none_components_of_non_none
          (__eo_to_smt body) hBodyNonNone
      have hElemNoNone : type_has_no_none_components a := by
        simpa [hBody, type_has_no_none_components] using hNoNone
      intro hNone
      exact type_has_no_none_components_non_none hElemNoNone hNone.symm

/--
If the broad `__is_closed_rec` binder-list branch sees a term that has a
well-typed SMT translation, then its head is an actual quantifier.
-/
theorem is_closed_rec_uop_list_branch_head_quantifier_of_has_smt_translation
    {op : UserOp} {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  op = UserOp.forall ∨ op = UserOp.exists :=
by
  by_cases hForall : op = UserOp.forall
  · exact Or.inl hForall
  by_cases hExists : op = UserOp.exists
  · exact Or.inr hExists
  exfalso
  unfold eoHasSmtTranslation at hTrans
  exact hTrans
    (smtx_typeof_uop_eo_list_cons_apply_eq_none hForall hExists v vs body)

theorem is_closed_rec_uop_list_branch_head_term_quantifier_of_has_smt_translation
    {op : UserOp} {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  Term.UOp op = Term.UOp UserOp.forall ∨
    Term.UOp op = Term.UOp UserOp.exists :=
by
  rcases
    is_closed_rec_uop_list_branch_head_quantifier_of_has_smt_translation
      hTrans with hForall | hExists
  · exact Or.inl (by rw [hForall])
  · exact Or.inr (by rw [hExists])

/--
On a well-formed EO variable environment, the raw list-indexing test used by
`__is_closed_rec` agrees with `__eo_is_closed_rec`'s direct recursive lookup.
-/
theorem eo_list_find_rec_var_nonneg_eq_eo_is_closed_rec
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (s : native_String) (T : Term) (n : native_Int)
    (hNonneg : 0 ≤ n) :
  __eo_not
      (__eo_is_neg
        (__eo_list_find_rec env (Term.Var (Term.String s) T)
          (Term.Numeral n))) =
    __eo_is_closed_rec (Term.Var (Term.String s) T) env :=
by
  induction hEnv generalizing n with
  | nil =>
      simp [__eo_list_find_rec, __eo_is_neg, __eo_not,
        __eo_is_closed_rec, native_zlt, native_not]
  | cons hTail ih =>
      rename_i s' T' env' vars'
      by_cases hVarEq :
          Term.Var (Term.String s') T' =
            Term.Var (Term.String s) T
      · have hNotLtProp : ¬ n < 0 := by
          exact Int.not_lt_of_ge hNonneg
        have hNotLt : native_zlt n 0 = false := by
          simp [native_zlt, hNotLtProp]
        have hFindEq :
            __eo_eq (Term.Var (Term.String s') T')
                (Term.Var (Term.String s) T) =
              Term.Boolean true := by
          simp [__eo_eq, native_teq, hVarEq.symm]
        have hClosedEq :
            __eo_eq (Term.Var (Term.String s) T)
                (Term.Var (Term.String s') T') =
              Term.Boolean true := by
          simp [__eo_eq, native_teq, hVarEq]
        simp [__eo_list_find_rec, __eo_is_closed_rec, hFindEq,
          hClosedEq, __eo_ite, __eo_is_neg, __eo_not, native_ite,
          native_teq, native_not, hNotLt]
      · have hVarEqSymm :
            Term.Var (Term.String s) T ≠
              Term.Var (Term.String s') T' := by
          intro h
          exact hVarEq h.symm
        have hFindEq :
            __eo_eq (Term.Var (Term.String s') T')
                (Term.Var (Term.String s) T) =
              Term.Boolean false := by
          simp [__eo_eq, native_teq, hVarEqSymm]
        have hClosedEq :
            __eo_eq (Term.Var (Term.String s) T)
                (Term.Var (Term.String s') T') =
              Term.Boolean false := by
          simp [__eo_eq, native_teq, hVarEq]
        have hSuccNonneg : 0 ≤ native_zplus n 1 := by
          simpa [native_zplus] using
            Int.add_nonneg hNonneg (by decide : (0 : Int) ≤ 1)
        simpa [__eo_list_find_rec, __eo_is_closed_rec, __eo_ite,
          __eo_add, native_ite, native_teq, hFindEq, hClosedEq]
          using ih (native_zplus n 1) hSuccNonneg

/--
For variables and well-formed EO variable environments, `__is_closed_rec` and
`__eo_is_closed_rec` are definitionally different but extensionally identical.
-/
theorem is_closed_rec_var_eq_eo_is_closed_rec_var
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (s : native_String) (T : Term) :
  __is_closed_rec (Term.Var (Term.String s) T) env =
    __eo_is_closed_rec (Term.Var (Term.String s) T) env :=
by
  cases hEnv with
  | nil =>
      have hEnvNil : EoSmtVarEnv Term.__eo_List_nil [] :=
        EoSmtVarEnv.nil
      have hList := hEnvNil.is_list
      simpa [__is_closed_rec, __eo_list_find, __eo_requires, hList,
        native_ite, native_teq, native_not]
        using
          eo_list_find_rec_var_nonneg_eq_eo_is_closed_rec
            hEnvNil s T 0
            (show (0 : native_Int) ≤ (0 : native_Int) by
              exact Int.le_refl 0)
  | cons hTail =>
      rename_i s' T' env' vars'
      have hEnvCons :
          EoSmtVarEnv
            (Term.Apply
              (Term.Apply Term.__eo_List_cons
                (Term.Var (Term.String s') T')) env')
            ((s', __eo_to_smt_type T') :: vars') :=
        EoSmtVarEnv.cons hTail
      have hList := hEnvCons.is_list
      simpa [__is_closed_rec, __eo_list_find, __eo_requires, hList,
        native_ite, native_teq, native_not]
        using
          eo_list_find_rec_var_nonneg_eq_eo_is_closed_rec
            hEnvCons s T 0
            (show (0 : native_Int) ≤ (0 : native_Int) by
              exact Int.le_refl 0)

theorem eo_is_closed_rec_var_is_boolean
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (s : native_String) (T : Term) :
  ∃ b,
    __eo_is_closed_rec (Term.Var (Term.String s) T) env =
      Term.Boolean b :=
by
  induction hEnv with
  | nil =>
      exact ⟨false, by simp [__eo_is_closed_rec]⟩
  | cons hTail ih =>
      rename_i s' T' env' vars'
      by_cases hVarEq :
          Term.Var (Term.String s') T' =
            Term.Var (Term.String s) T
      · have hClosedEq :
            __eo_eq (Term.Var (Term.String s) T)
                (Term.Var (Term.String s') T') =
              Term.Boolean true := by
          simp [__eo_eq, native_teq, hVarEq]
        exact ⟨true, by
          simp [__eo_is_closed_rec, __eo_ite, hClosedEq, native_ite,
            native_teq]⟩
      · have hClosedEq :
            __eo_eq (Term.Var (Term.String s) T)
                (Term.Var (Term.String s') T') =
              Term.Boolean false := by
          simp [__eo_eq, native_teq, hVarEq]
        rcases ih with ⟨b, hb⟩
        exact ⟨b, by
          simp [__eo_is_closed_rec, __eo_ite, hClosedEq, hb, native_ite,
            native_teq]⟩

theorem is_closed_rec_var_eq_and_bool
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (s : native_String) (T : Term) :
  __is_closed_rec (Term.Var (Term.String s) T) env =
    __eo_is_closed_rec (Term.Var (Term.String s) T) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Var (Term.String s) T) env =
        Term.Boolean b :=
by
  exact ⟨is_closed_rec_var_eq_eo_is_closed_rec_var hEnv s T,
    eo_is_closed_rec_var_is_boolean hEnv s T⟩

theorem eo_list_find_rec_var_nonneg_eq_eo_is_closed_rec_any
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (name T : Term) (n : native_Int)
    (hNonneg : 0 ≤ n) :
  __eo_not
      (__eo_is_neg
        (__eo_list_find_rec env (Term.Var name T)
          (Term.Numeral n))) =
    __eo_is_closed_rec (Term.Var name T) env :=
by
  induction hEnv generalizing n with
  | nil =>
      simp [__eo_list_find_rec, __eo_is_neg, __eo_not,
        __eo_is_closed_rec, native_zlt, native_not]
  | cons hTail ih =>
      rename_i s' T' env' vars'
      by_cases hVarEq :
          Term.Var (Term.String s') T' = Term.Var name T
      · have hNotLtProp : ¬ n < 0 := by
          exact Int.not_lt_of_ge hNonneg
        have hNotLt : native_zlt n 0 = false := by
          simp [native_zlt, hNotLtProp]
        have hFindEq :
            __eo_eq (Term.Var (Term.String s') T') (Term.Var name T) =
              Term.Boolean true := by
          simp [__eo_eq, native_teq, hVarEq.symm]
        have hClosedEq :
            __eo_eq (Term.Var name T) (Term.Var (Term.String s') T') =
              Term.Boolean true := by
          simp [__eo_eq, native_teq, hVarEq]
        simp [__eo_list_find_rec, __eo_is_closed_rec, hFindEq,
          hClosedEq, __eo_ite, __eo_is_neg, __eo_not, native_ite,
          native_teq, native_not, hNotLt]
      · have hVarEqSymm :
            Term.Var name T ≠ Term.Var (Term.String s') T' := by
          intro h
          exact hVarEq h.symm
        have hFindEq :
            __eo_eq (Term.Var (Term.String s') T') (Term.Var name T) =
              Term.Boolean false := by
          simp [__eo_eq, native_teq, hVarEqSymm]
        have hClosedEq :
            __eo_eq (Term.Var name T) (Term.Var (Term.String s') T') =
              Term.Boolean false := by
          simp [__eo_eq, native_teq, hVarEq]
        have hSuccNonneg : 0 ≤ native_zplus n 1 := by
          simpa [native_zplus] using
            Int.add_nonneg hNonneg (by decide : (0 : Int) ≤ 1)
        simpa [__eo_list_find_rec, __eo_is_closed_rec, __eo_ite,
          __eo_add, native_ite, native_teq, hFindEq, hClosedEq]
          using ih (native_zplus n 1) hSuccNonneg

theorem is_closed_rec_var_eq_eo_is_closed_rec_var_any
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (name T : Term) :
  __is_closed_rec (Term.Var name T) env =
    __eo_is_closed_rec (Term.Var name T) env :=
by
  cases hEnv with
  | nil =>
      have hEnvNil : EoSmtVarEnv Term.__eo_List_nil [] :=
        EoSmtVarEnv.nil
      have hList := hEnvNil.is_list
      simpa [__is_closed_rec, __eo_list_find, __eo_requires, hList,
        native_ite, native_teq, native_not]
        using
          eo_list_find_rec_var_nonneg_eq_eo_is_closed_rec_any
            hEnvNil name T 0
            (show (0 : native_Int) ≤ (0 : native_Int) by
              exact Int.le_refl 0)
  | cons hTail =>
      rename_i s' T' env' vars'
      have hEnvCons :
          EoSmtVarEnv
            (Term.Apply
              (Term.Apply Term.__eo_List_cons
                (Term.Var (Term.String s') T')) env')
            ((s', __eo_to_smt_type T') :: vars') :=
        EoSmtVarEnv.cons hTail
      have hList := hEnvCons.is_list
      simpa [__is_closed_rec, __eo_list_find, __eo_requires, hList,
        native_ite, native_teq, native_not]
        using
          eo_list_find_rec_var_nonneg_eq_eo_is_closed_rec_any
            hEnvCons name T 0
            (show (0 : native_Int) ≤ (0 : native_Int) by
              exact Int.le_refl 0)

theorem eo_is_closed_rec_var_is_boolean_any
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (name T : Term) :
  ∃ b,
    __eo_is_closed_rec (Term.Var name T) env =
      Term.Boolean b :=
by
  induction hEnv with
  | nil =>
      exact ⟨false, by simp [__eo_is_closed_rec]⟩
  | cons hTail ih =>
      rename_i s' T' env' vars'
      by_cases hVarEq :
          Term.Var (Term.String s') T' = Term.Var name T
      · have hClosedEq :
            __eo_eq (Term.Var name T) (Term.Var (Term.String s') T') =
              Term.Boolean true := by
          simp [__eo_eq, native_teq, hVarEq]
        exact ⟨true, by
          simp [__eo_is_closed_rec, __eo_ite, hClosedEq, native_ite,
            native_teq]⟩
      · have hClosedEq :
            __eo_eq (Term.Var name T) (Term.Var (Term.String s') T') =
              Term.Boolean false := by
          simp [__eo_eq, native_teq, hVarEq]
        rcases ih with ⟨b, hb⟩
        exact ⟨b, by
          simp [__eo_is_closed_rec, __eo_ite, hClosedEq, hb, native_ite,
            native_teq]⟩

theorem is_closed_rec_var_eq_and_bool_any
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (name T : Term) :
  __is_closed_rec (Term.Var name T) env =
    __eo_is_closed_rec (Term.Var name T) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Var name T) env =
        Term.Boolean b :=
by
  exact ⟨is_closed_rec_var_eq_eo_is_closed_rec_var_any hEnv name T,
    eo_is_closed_rec_var_is_boolean_any hEnv name T⟩

/--
A Boolean SMT existential chain can only have come from an EO list of variables.
This strengthens `eo_typeof_var_list_of_exists_bool` with the exact environment
relation used by the closedness proofs.
-/
theorem eo_smt_var_env_of_eo_to_smt_exists_bool
    (xs : Term) (body : SmtTerm) :
  __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
    ∃ vars, EoSmtVarEnv xs vars :=
by
  intro hTy
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    exact ⟨[], EoSmtVarEnv.nil⟩
  case Apply f a =>
    subst hxs
    cases hf : f
    case Apply g y =>
      subst hf
      cases hg : g
      case __eo_List_cons =>
        subst hg
        cases hy : y
        case Var name T =>
          subst hy
          cases hname : name
          case String s =>
            subst hname
            have hExistsTy :
                __smtx_typeof
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists a body)) =
                  SmtType.Bool := by
              simpa [__eo_to_smt_exists] using hTy
            have hNN :
                term_has_non_none_type
                  (SmtTerm.exists s (__eo_to_smt_type T)
                    (__eo_to_smt_exists a body)) := by
              unfold term_has_non_none_type
              rw [hExistsTy]
              simp
            have hSub :
                __smtx_typeof (__eo_to_smt_exists a body) =
                  SmtType.Bool := by
              simpa using exists_body_bool_of_non_none hNN
            rcases eo_smt_var_env_of_eo_to_smt_exists_bool a body hSub with
              ⟨vars, hEnv⟩
            exact ⟨(s, __eo_to_smt_type T) :: vars,
              EoSmtVarEnv.cons hEnv⟩
          all_goals
            subst hname
            have hNone := hTy
            simp [__eo_to_smt_exists, __smtx_typeof] at hNone
        all_goals
          subst hy
          have hNone := hTy
          simp [__eo_to_smt_exists, __smtx_typeof] at hNone
      all_goals
        subst hg
        have hNone := hTy
        simp [__eo_to_smt_exists, __smtx_typeof] at hNone
    all_goals
      subst hf
      have hNone := hTy
      simp [__eo_to_smt_exists, __smtx_typeof] at hNone
  all_goals
    subst hxs
    have hNone := hTy
    simp [__eo_to_smt_exists, __smtx_typeof] at hNone

theorem smtx_typeof_exists_eq_bool_of_non_none
    {s : native_String} {T : SmtType} {body : SmtTerm}
    (hNonNone :
      __smtx_typeof (SmtTerm.exists s T body) ≠ SmtType.None) :
  __smtx_typeof (SmtTerm.exists s T body) = SmtType.Bool :=
by
  exact exists_term_typeof_of_non_none (by
    unfold term_has_non_none_type
    exact hNonNone)

/--
For a nonempty raw EO binder list, non-`None` SMT existential-chain typing
recovers the corresponding EO/SMT variable environment.
-/
theorem eo_smt_var_env_of_eo_to_smt_exists_cons_non_none
    (v vs : Term) (body : SmtTerm)
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) body) ≠
        SmtType.None) :
  ∃ vars,
    EoSmtVarEnv
      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) vars :=
by
  cases v
  case Var name T =>
    cases name
    case String s =>
      have hBool :
          __smtx_typeof
              (__eo_to_smt_exists
                (Term.Apply
                  (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) vs) body) =
            SmtType.Bool := by
        change
          __smtx_typeof
              (SmtTerm.exists s (__eo_to_smt_type T)
                (__eo_to_smt_exists vs body)) =
            SmtType.Bool
        exact smtx_typeof_exists_eq_bool_of_non_none hNonNone
      exact
        eo_smt_var_env_of_eo_to_smt_exists_bool
          (Term.Apply
            (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) vs)
          body hBool
    all_goals
      exfalso
      apply hNonNone
      simp [__eo_to_smt_exists, __smtx_typeof]
  all_goals
    exfalso
    apply hNonNone
    simp [__eo_to_smt_exists, __smtx_typeof]

theorem smtx_typeof_eo_to_smt_exists_cons_eq_bool_of_non_none
    (v vs : Term) (body : SmtTerm)
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) body) ≠
        SmtType.None) :
  __smtx_typeof
      (__eo_to_smt_exists
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) body) =
    SmtType.Bool :=
by
  cases v
  case Var name T =>
    cases name
    case String s =>
      change
        __smtx_typeof
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists vs body)) =
          SmtType.Bool
      exact smtx_typeof_exists_eq_bool_of_non_none hNonNone
    all_goals
      exfalso
      apply hNonNone
      simp [__eo_to_smt_exists, __smtx_typeof]
  all_goals
    exfalso
    apply hNonNone
    simp [__eo_to_smt_exists, __smtx_typeof]

theorem smtx_typeof_not_eq_bool_of_non_none
    (t : SmtTerm)
    (hNonNone : __smtx_typeof (SmtTerm.not t) ≠ SmtType.None) :
  __smtx_typeof (SmtTerm.not t) = SmtType.Bool :=
by
  cases hTy : __smtx_typeof t <;>
    rw [typeof_not_eq] at hNonNone ⊢ <;>
    simp [hTy, native_ite, native_Teq] at hNonNone ⊢

theorem smtx_typeof_not_arg_eq_bool
    (t : SmtTerm)
    (hTy : __smtx_typeof (SmtTerm.not t) = SmtType.Bool) :
  __smtx_typeof t = SmtType.Bool :=
by
  cases hArg : __smtx_typeof t <;>
    rw [typeof_not_eq] at hTy <;>
    simp [hArg, native_ite, native_Teq] at hTy ⊢

theorem eo_smt_var_env_of_exists_list_branch_has_smt_translation
    {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.exists)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  ∃ vars,
    EoSmtVarEnv
      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) vars :=
by
  unfold eoHasSmtTranslation at hTrans
  exact
    eo_smt_var_env_of_eo_to_smt_exists_cons_non_none
      v vs (__eo_to_smt body) (by
        change
          __smtx_typeof
              (__eo_to_smt_exists
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
                (__eo_to_smt body)) ≠
            SmtType.None at hTrans
        exact hTrans)

theorem eo_smt_var_env_of_forall_list_branch_has_smt_translation
    {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.forall)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  ∃ vars,
    EoSmtVarEnv
      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) vars :=
by
  unfold eoHasSmtTranslation at hTrans
  have hNotBool :
      __smtx_typeof
          (SmtTerm.not
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
              (SmtTerm.not (__eo_to_smt body)))) =
        SmtType.Bool :=
    smtx_typeof_not_eq_bool_of_non_none
      (__eo_to_smt_exists
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
        (SmtTerm.not (__eo_to_smt body)))
      (by
        change
          __smtx_typeof
              (SmtTerm.not
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
                  (SmtTerm.not (__eo_to_smt body)))) ≠
            SmtType.None at hTrans
        exact hTrans)
  have hExistsBool :
      __smtx_typeof
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            (SmtTerm.not (__eo_to_smt body))) =
        SmtType.Bool :=
    smtx_typeof_not_arg_eq_bool
      (__eo_to_smt_exists
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
        (SmtTerm.not (__eo_to_smt body)))
      hNotBool
  exact
    eo_smt_var_env_of_eo_to_smt_exists_bool
      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
      (SmtTerm.not (__eo_to_smt body)) hExistsBool

theorem eo_smt_var_env_of_uop_list_branch_has_smt_translation
    {op : UserOp} {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  ∃ vars,
    EoSmtVarEnv
      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) vars :=
by
  rcases
    is_closed_rec_uop_list_branch_head_quantifier_of_has_smt_translation
      hTrans with hForall | hExists
  · subst op
    exact eo_smt_var_env_of_forall_list_branch_has_smt_translation hTrans
  · subst op
    exact eo_smt_var_env_of_exists_list_branch_has_smt_translation hTrans

theorem eo_smt_var_env_concat_of_uop_list_branch_has_smt_translation
    {op : UserOp} {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  ∃ vars',
    EoSmtVarEnv
      (__eo_list_concat Term.__eo_List_cons
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env)
      vars' :=
by
  rcases
    eo_smt_var_env_of_uop_list_branch_has_smt_translation hTrans with
    ⟨binderVars, hBinderEnv⟩
  exact ⟨binderVars ++ vars, EoSmtVarEnv.concat hBinderEnv hEnv⟩

theorem body_has_smt_translation_of_exists_list_branch_has_smt_translation
    {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.exists)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  eoHasSmtTranslation body :=
by
  unfold eoHasSmtTranslation at hTrans ⊢
  have hExistsBool :
      __smtx_typeof
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            (__eo_to_smt body)) =
        SmtType.Bool :=
    smtx_typeof_eo_to_smt_exists_cons_eq_bool_of_non_none
      v vs (__eo_to_smt body) (by
        change
          __smtx_typeof
              (__eo_to_smt_exists
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
                (__eo_to_smt body)) ≠
            SmtType.None at hTrans
        exact hTrans)
  have hBodyBool :
      __smtx_typeof (__eo_to_smt body) = SmtType.Bool :=
    TranslationProofs.eo_to_smt_exists_body_bool_of_bool
      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
      (__eo_to_smt body) hExistsBool
  rw [hBodyBool]
  intro h
  cases h

theorem body_has_smt_translation_of_forall_list_branch_has_smt_translation
    {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.forall)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  eoHasSmtTranslation body :=
by
  unfold eoHasSmtTranslation at hTrans ⊢
  have hNotBool :
      __smtx_typeof
          (SmtTerm.not
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
              (SmtTerm.not (__eo_to_smt body)))) =
        SmtType.Bool :=
    smtx_typeof_not_eq_bool_of_non_none
      (__eo_to_smt_exists
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
        (SmtTerm.not (__eo_to_smt body)))
      (by
        change
          __smtx_typeof
              (SmtTerm.not
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
                  (SmtTerm.not (__eo_to_smt body)))) ≠
            SmtType.None at hTrans
        exact hTrans)
  have hExistsBool :
      __smtx_typeof
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            (SmtTerm.not (__eo_to_smt body))) =
        SmtType.Bool :=
    smtx_typeof_not_arg_eq_bool
      (__eo_to_smt_exists
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
        (SmtTerm.not (__eo_to_smt body)))
      hNotBool
  have hBodyNotBool :
      __smtx_typeof (SmtTerm.not (__eo_to_smt body)) =
        SmtType.Bool :=
    TranslationProofs.eo_to_smt_exists_body_bool_of_bool
      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
      (SmtTerm.not (__eo_to_smt body)) hExistsBool
  have hBodyBool :
      __smtx_typeof (__eo_to_smt body) = SmtType.Bool :=
    smtx_typeof_not_arg_eq_bool (__eo_to_smt body) hBodyNotBool
  rw [hBodyBool]
  intro h
  cases h

theorem body_has_smt_translation_of_uop_list_branch_has_smt_translation
    {op : UserOp} {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  eoHasSmtTranslation body :=
by
  rcases
    is_closed_rec_uop_list_branch_head_quantifier_of_has_smt_translation
      hTrans with hForall | hExists
  · subst op
    exact body_has_smt_translation_of_forall_list_branch_has_smt_translation
      hTrans
  · subst op
    exact body_has_smt_translation_of_exists_list_branch_has_smt_translation
      hTrans

theorem body_obligations_of_uop_list_branch_has_smt_translation
    {op : UserOp} {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  eoHasSmtTranslation body ∧
    ∃ vars',
      EoSmtVarEnv
        (__eo_list_concat Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env)
        vars' :=
by
  exact
    ⟨body_has_smt_translation_of_uop_list_branch_has_smt_translation
        hTrans,
      eo_smt_var_env_concat_of_uop_list_branch_has_smt_translation
        hEnv hTrans⟩

theorem eo_and_true_left_eq_of_boolean
    {x : Term} {b : Bool} (h : x = Term.Boolean b) :
  __eo_and (Term.Boolean true) x = x :=
by
  subst x
  cases b <;> simp [__eo_and, native_and]

theorem eo_and_true_right_eq_of_boolean
    {x : Term} {b : Bool} (h : x = Term.Boolean b) :
  __eo_and x (Term.Boolean true) = x :=
by
  subst x
  cases b <;> simp [__eo_and, native_and]

theorem eo_and_true_true :
  __eo_and (Term.Boolean true) (Term.Boolean true) =
    Term.Boolean true :=
by
  simp [__eo_and, native_and]

theorem eo_and_eq_boolean_of_boolean
    {x y : Term} {bx bz : Bool}
    (hx : x = Term.Boolean bx) (hy : y = Term.Boolean bz) :
  ∃ b, __eo_and x y = Term.Boolean b :=
by
  subst x
  subst y
  cases bx <;> cases bz <;>
    simp [__eo_and, native_and]

theorem eo_is_closed_rec_eq_true_of_nat_is_valid
    {idx env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hValid : __eo_to_smt_nat_is_valid idx = true) :
  __eo_is_closed_rec idx env = Term.Boolean true :=
by
  cases idx <;> simp [__eo_to_smt_nat_is_valid] at hValid
  case Numeral n =>
    cases hEnv <;> simp [__eo_is_closed_rec]

theorem eo_is_closed_rec_eq_true_of_eo_to_smt_numeral
    {idx env : Term} {vars : List SmtVarKey} {i : native_Int}
    (hEnv : EoSmtVarEnv env vars)
    (hIdx : __eo_to_smt idx = SmtTerm.Numeral i) :
  __eo_is_closed_rec idx env = Term.Boolean true :=
by
  have hIdxTerm : idx = Term.Numeral i :=
    TranslationProofs.eo_to_smt_eq_numeral idx i hIdx
  subst idx
  cases hEnv <;> simp [__eo_is_closed_rec]

theorem eo_is_closed_rec_eq_true_of_eo_to_smt_eq_dt_sel
    {idx env : Term} {vars : List SmtVarKey}
    {s : native_String} {d : SmtDatatypeDecl} {i j : native_Nat}
    (hEnv : EoSmtVarEnv env vars)
    (hSel : __eo_to_smt idx = SmtTerm.DtSel s d i j) :
  __eo_is_closed_rec idx env = Term.Boolean true :=
by
  rcases TranslationProofs.eo_to_smt_eq_dt_sel_cases
      idx s d i j hSel with
    ⟨d0, hd, hIdx, _hReserved⟩ | ⟨z, hIdx, hz⟩
  · subst idx
    cases hEnv <;> simp [__eo_is_closed_rec]
  · subst idx
    change SmtTerm._at_purify (__eo_to_smt z) =
      SmtTerm.DtSel s d i j at hSel
    cases hSel

theorem eo_is_closed_rec_eq_true_of_eo_to_smt_eq_dt_cons
    {idx env : Term} {vars : List SmtVarKey}
    {s : native_String} {d : SmtDatatypeDecl} {i : native_Nat}
    (hEnv : EoSmtVarEnv env vars)
    (hCons : __eo_to_smt idx = SmtTerm.DtCons s d i) :
  __eo_is_closed_rec idx env = Term.Boolean true :=
by
  rcases TranslationProofs.eo_to_smt_eq_dt_cons_cases
      idx s d i hCons with
    ⟨d0, hd, hIdx, _hReserved⟩ | ⟨hs, hd, hi, hIdx⟩
  · subst idx
    cases hEnv <;> simp [__eo_is_closed_rec]
  · subst idx
    cases hEnv <;> simp [__eo_is_closed_rec]

theorem eo_type_valid_rec_seq_arg
    {refs : List native_String} {x : Term}
    (h :
      TranslationProofs.eo_type_valid_rec refs
        (Term.Apply (Term.UOp UserOp.Seq) x)) :
    TranslationProofs.eo_type_valid_rec [] x := by
  unfold TranslationProofs.eo_type_valid_rec at h ⊢
  cases hx : __eo_to_smt_type x <;>
    simp [__eo_to_smt_type, hx, TranslationProofs.noNoneTy,
      __smtx_typeof_guard,
      native_ite, native_Teq, native_and] at h ⊢
  all_goals assumption

theorem eo_type_valid_rec_set_arg
    {refs : List native_String} {x : Term}
    (h :
      TranslationProofs.eo_type_valid_rec refs
        (Term.Apply (Term.UOp UserOp.Set) x)) :
    TranslationProofs.eo_type_valid_rec [] x := by
  unfold TranslationProofs.eo_type_valid_rec at h ⊢
  cases hx : __eo_to_smt_type x <;>
    simp [__eo_to_smt_type, hx, TranslationProofs.noNoneTy,
      __smtx_typeof_guard,
      native_ite, native_Teq, native_and] at h ⊢
  all_goals assumption

theorem eo_type_valid_rec_fun_args
    {refs : List native_String} {x y : Term}
    (h :
      TranslationProofs.eo_type_valid_rec refs
        (Term.Apply (Term.Apply Term.FunType y) x)) :
    TranslationProofs.eo_type_valid_rec [] y ∧
      TranslationProofs.eo_type_valid_rec [] x := by
  unfold TranslationProofs.eo_type_valid_rec at h ⊢
  cases hy : __eo_to_smt_type y <;>
    cases hx : __eo_to_smt_type x <;>
      simp [__eo_to_smt_type, hy, hx, TranslationProofs.noNoneTy,
        __smtx_typeof_guard,
        native_ite, native_Teq, native_and] at h ⊢
  all_goals assumption

theorem eo_type_valid_rec_array_args
    {refs : List native_String} {x y : Term}
    (h :
      TranslationProofs.eo_type_valid_rec refs
        (Term.Apply (Term.Apply (Term.UOp UserOp.Array) y) x)) :
    TranslationProofs.eo_type_valid_rec [] y ∧
      TranslationProofs.eo_type_valid_rec [] x := by
  unfold TranslationProofs.eo_type_valid_rec at h ⊢
  cases hy : __eo_to_smt_type y <;>
    cases hx : __eo_to_smt_type x <;>
      simp [__eo_to_smt_type, hy, hx, TranslationProofs.noNoneTy,
        __smtx_typeof_guard,
        native_ite, native_Teq, native_and] at h ⊢
  all_goals assumption

theorem eo_type_valid_rec_tuple_args
    {refs : List native_String} {x y : Term}
    (h :
      TranslationProofs.eo_type_valid_rec refs
        (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) y) x)) :
    TranslationProofs.eo_type_valid_rec [] y ∧
      TranslationProofs.eo_type_valid_rec [] x ∧
        __smtx_type_wf
            (__eo_to_smt_type_tuple
              (__eo_to_smt_type y) (__eo_to_smt_type x)) =
          true := by
  unfold TranslationProofs.eo_type_valid_rec at h ⊢
  let R :=
    __eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)
  have hWf : __smtx_type_wf R = true := by
    cases hw : __smtx_type_wf R
    · simp [__eo_to_smt_type, R, hw, TranslationProofs.noNoneTy,
        native_ite] at h
    · rfl
  have hRNoNone : TranslationProofs.noNoneTy R = true := by
    simpa [__eo_to_smt_type, R, hWf, native_ite] using h
  refine ⟨?_, ?_, hWf⟩
  · cases hx : __eo_to_smt_type x <;>
      simp [R, hx, __eo_to_smt_type_tuple,
        TranslationProofs.noNoneTy, TranslationProofs.noNoneDecl,
        TranslationProofs.noNoneDt, TranslationProofs.noNoneDtc,
        __eo_to_smt_tuple_decl, native_ite, native_streq,
        native_and] at hRNoNone
    case Datatype s dd =>
      cases dd with
      | nil =>
          simp [R, hx, __eo_to_smt_type_tuple,
            TranslationProofs.noNoneTy] at hRNoNone
      | cons s2 body rest =>
          cases rest with
          | cons s3 body3 rest3 =>
              simp [R, hx, __eo_to_smt_type_tuple,
                TranslationProofs.noNoneTy] at hRNoNone
          | nil =>
              cases body with
              | null =>
                  simp [R, hx, __eo_to_smt_type_tuple,
                    TranslationProofs.noNoneTy] at hRNoNone
              | sum c tail =>
                  cases tail with
                  | sum c2 tail2 =>
                      simp [R, hx, __eo_to_smt_type_tuple,
                        TranslationProofs.noNoneTy] at hRNoNone
                  | null =>
                      by_cases hs : s = native_string_lit "@Tuple"
                      · subst s
                        by_cases hs2 : s2 = native_string_lit "@Tuple"
                        · subst s2
                          have hComp :
                              __smtx_type_wf_component
                                  (__eo_to_smt_type y) =
                                true := by
                            cases hc :
                                __smtx_type_wf_component
                                  (__eo_to_smt_type y)
                            · simp [R, hx, __eo_to_smt_type_tuple, hc,
                                TranslationProofs.noNoneTy, native_streq,
                                native_and, native_ite] at hRNoNone
                            · rfl
                          have hParts :
                              TranslationProofs.noNoneTy
                                    (__eo_to_smt_type y) =
                                  true ∧
                                TranslationProofs.noNoneDtc c = true := by
                            simpa [R, hx, __eo_to_smt_type_tuple,
                              __eo_to_smt_tuple_decl,
                              TranslationProofs.noNoneTy,
                              TranslationProofs.noNoneDecl,
                              TranslationProofs.noNoneDt,
                              TranslationProofs.noNoneDtc, hComp,
                              native_ite, native_streq, native_and] using
                              hRNoNone
                          exact hParts.1
                        · simp [R, hx, __eo_to_smt_type_tuple, hs2,
                            TranslationProofs.noNoneTy, native_streq,
                            native_and, native_ite] at hRNoNone
                      · simp [R, hx, __eo_to_smt_type_tuple, hs,
                          TranslationProofs.noNoneTy, native_streq,
                          native_and, native_ite] at hRNoNone
  · cases hx : __eo_to_smt_type x <;>
      simp [R, hx, __eo_to_smt_type_tuple,
        TranslationProofs.noNoneTy, TranslationProofs.noNoneDecl,
        TranslationProofs.noNoneDt, TranslationProofs.noNoneDtc,
        __eo_to_smt_tuple_decl, native_ite, native_streq,
        native_and] at hRNoNone ⊢
    case Datatype s dd =>
      cases dd with
      | nil =>
          simp [R, hx, __eo_to_smt_type_tuple,
            TranslationProofs.noNoneTy] at hRNoNone
      | cons s2 body rest =>
          cases rest with
          | cons s3 body3 rest3 =>
              simp [R, hx, __eo_to_smt_type_tuple,
                TranslationProofs.noNoneTy] at hRNoNone
          | nil =>
              cases body with
              | null =>
                  simp [R, hx, __eo_to_smt_type_tuple,
                    TranslationProofs.noNoneTy] at hRNoNone
              | sum c tail =>
                  cases tail with
                  | sum c2 tail2 =>
                      simp [R, hx, __eo_to_smt_type_tuple,
                        TranslationProofs.noNoneTy] at hRNoNone
                  | null =>
                      by_cases hs : s = native_string_lit "@Tuple"
                      · subst s
                        by_cases hs2 : s2 = native_string_lit "@Tuple"
                        · subst s2
                          have hComp :
                              __smtx_type_wf_component
                                  (__eo_to_smt_type y) =
                                true := by
                            cases hc :
                                __smtx_type_wf_component
                                  (__eo_to_smt_type y)
                            · simp [R, hx, __eo_to_smt_type_tuple, hc,
                                TranslationProofs.noNoneTy, native_streq,
                                native_and, native_ite] at hRNoNone
                            · rfl
                          have hParts :
                              TranslationProofs.noNoneTy
                                    (__eo_to_smt_type y) =
                                  true ∧
                                TranslationProofs.noNoneDtc c = true := by
                            simpa [R, hx, __eo_to_smt_type_tuple,
                              __eo_to_smt_tuple_decl,
                              TranslationProofs.noNoneTy,
                              TranslationProofs.noNoneDecl,
                              TranslationProofs.noNoneDt,
                              TranslationProofs.noNoneDtc, hComp,
                              native_ite, native_streq, native_and] using
                              hRNoNone
                          simpa [hx, TranslationProofs.noNoneTy,
                            TranslationProofs.noNoneDecl,
                            TranslationProofs.noNoneDt, native_and] using
                            hParts.2
                        · simp [R, hx, __eo_to_smt_type_tuple, hs2,
                            TranslationProofs.noNoneTy, native_streq,
                            native_and, native_ite] at hRNoNone
                      · simp [R, hx, __eo_to_smt_type_tuple, hs,
                          TranslationProofs.noNoneTy, native_streq,
                          native_and, native_ite] at hRNoNone

theorem eo_is_closed_rec_eq_true_of_eo_type_valid_rec
    {refs : List native_String} {T env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hValid : TranslationProofs.eo_type_valid_rec refs T) :
  __eo_is_closed_rec T env = Term.Boolean true :=
by
  let rec go (T : Term) :
      ∀ {refs : List native_String} {env : Term} {vars : List SmtVarKey},
        EoSmtVarEnv env vars ->
          TranslationProofs.eo_type_valid_rec refs T ->
            __eo_is_closed_rec T env = Term.Boolean true :=
  by
    intro refs env vars hEnv hValid
    cases T with
    | Bool =>
        cases hEnv <;> simp [__eo_is_closed_rec]
    | DatatypeType s d =>
        cases hEnv <;> simp [__eo_is_closed_rec]
    | DatatypeTypeRef s =>
        cases hEnv <;> simp [__eo_is_closed_rec]
    | DtcAppType T U =>
        cases hEnv <;> simp [__eo_is_closed_rec]
    | USort i =>
        cases hEnv <;> simp [__eo_is_closed_rec]
    | UOp op =>
        cases op <;> cases hEnv <;>
          simp [TranslationProofs.eo_type_valid_rec,
            __eo_is_closed_rec] at hValid ⊢
    | Apply f x =>
        cases f with
        | UOp op =>
            cases op <;>
              cases hEnv <;>
                simp [TranslationProofs.eo_type_valid_rec,
                  __eo_to_smt_type, TranslationProofs.noNoneTy,
                  __eo_is_closed_rec, native_ite] at hValid ⊢
            case BitVec.nil =>
              cases x <;>
                simp [TranslationProofs.eo_type_valid_rec,
                  __eo_to_smt_type, TranslationProofs.noNoneTy,
                  __eo_is_closed_rec, __eo_and, native_ite, native_and] at hValid ⊢
            case BitVec.cons =>
              cases x <;>
                simp [TranslationProofs.eo_type_valid_rec,
                  __eo_to_smt_type, TranslationProofs.noNoneTy,
                  __eo_is_closed_rec, __eo_and, native_ite, native_and] at hValid ⊢
            case Seq.nil =>
              have hx := go x EoSmtVarEnv.nil
                (eo_type_valid_rec_seq_arg (refs := refs) hValid)
              simp [__eo_is_closed_rec, hx, eo_and_true_true]
            case Seq.cons hTail =>
              rename_i s' T' env' vars'
              have hEnvCons := EoSmtVarEnv.cons (s := s') (T := T') hTail
              have hx := go x hEnvCons
                (eo_type_valid_rec_seq_arg (refs := refs) hValid)
              simp [__eo_is_closed_rec, hx, eo_and_true_true]
            case Set.nil =>
              have hx := go x EoSmtVarEnv.nil
                (eo_type_valid_rec_set_arg (refs := refs) hValid)
              simp [__eo_is_closed_rec, hx, eo_and_true_true]
            case Set.cons hTail =>
              rename_i s' T' env' vars'
              have hEnvCons := EoSmtVarEnv.cons (s := s') (T := T') hTail
              have hx := go x hEnvCons
                (eo_type_valid_rec_set_arg (refs := refs) hValid)
              simp [__eo_is_closed_rec, hx, eo_and_true_true]
        | Apply g y =>
            cases g with
            | FunType =>
                rcases eo_type_valid_rec_fun_args (refs := refs) hValid with
                  ⟨hyValid, hxValid⟩
                cases hEnv with
                | nil =>
                    have hy := go y EoSmtVarEnv.nil hyValid
                    have hx := go x EoSmtVarEnv.nil hxValid
                    simp [__eo_is_closed_rec, hy, hx, eo_and_true_true]
                | cons hTail =>
                    rename_i s' T' env' vars'
                    have hEnvCons :=
                      EoSmtVarEnv.cons (s := s') (T := T') hTail
                    have hy := go y hEnvCons hyValid
                    have hx := go x hEnvCons hxValid
                    simp [__eo_is_closed_rec, hy, hx, eo_and_true_true]
            | UOp op =>
                cases op <;>
                  cases hEnv <;>
                    simp [TranslationProofs.eo_type_valid_rec,
                      __eo_to_smt_type, TranslationProofs.noNoneTy,
                      __eo_is_closed_rec, native_ite] at hValid ⊢
                case Array.nil =>
                  rcases eo_type_valid_rec_array_args (refs := refs) hValid with
                    ⟨hyValid, hxValid⟩
                  have hy := go y EoSmtVarEnv.nil hyValid
                  have hx := go x EoSmtVarEnv.nil hxValid
                  simp [__eo_is_closed_rec, hy, hx, eo_and_true_true]
                case Array.cons hTail =>
                  rename_i s' T' env' vars'
                  rcases eo_type_valid_rec_array_args (refs := refs) hValid with
                    ⟨hyValid, hxValid⟩
                  have hEnvCons :=
                    EoSmtVarEnv.cons (s := s') (T := T') hTail
                  have hy := go y hEnvCons hyValid
                  have hx := go x hEnvCons hxValid
                  simp [__eo_is_closed_rec, hy, hx, eo_and_true_true]
                case Tuple.nil =>
                  rcases eo_type_valid_rec_tuple_args (refs := refs) hValid with
                    ⟨hyValid, hxValid, _hWf⟩
                  have hy := go y EoSmtVarEnv.nil hyValid
                  have hx := go x EoSmtVarEnv.nil hxValid
                  simp [__eo_is_closed_rec, hy, hx, eo_and_true_true]
                case Tuple.cons hTail =>
                  rename_i s' T' env' vars'
                  rcases eo_type_valid_rec_tuple_args (refs := refs) hValid with
                    ⟨hyValid, hxValid, _hWf⟩
                  have hEnvCons :=
                    EoSmtVarEnv.cons (s := s') (T := T') hTail
                  have hy := go y hEnvCons hyValid
                  have hx := go x hEnvCons hxValid
                  simp [__eo_is_closed_rec, hy, hx, eo_and_true_true]
            | _ =>
                cases hEnv <;>
                  simp [TranslationProofs.eo_type_valid_rec,
                    __eo_to_smt_type, TranslationProofs.noNoneTy,
                    __eo_is_closed_rec, native_ite] at hValid
        | _ =>
            cases hEnv <;>
              simp [TranslationProofs.eo_type_valid_rec,
                __eo_to_smt_type, TranslationProofs.noNoneTy,
                __eo_is_closed_rec, native_ite] at hValid
    | _ =>
        cases hEnv <;>
          simp [TranslationProofs.eo_type_valid_rec,
            __eo_to_smt_type, TranslationProofs.noNoneTy,
            __eo_is_closed_rec, native_ite] at hValid
  exact go T hEnv hValid

theorem eo_is_closed_rec_eq_true_of_eo_type_valid
    {T env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hValid : TranslationProofs.eo_type_valid T) :
  __eo_is_closed_rec T env = Term.Boolean true :=
by
  cases T with
  | UOp op =>
      cases op with
      | RegLan =>
          cases hEnv <;> simp [__eo_is_closed_rec]
      | _ =>
          exact eo_is_closed_rec_eq_true_of_eo_type_valid_rec
            (refs := []) hEnv
            (by simpa only [TranslationProofs.eo_type_valid,
                TranslationProofs.eo_type_valid_rec] using hValid)
  | _ =>
      exact eo_is_closed_rec_eq_true_of_eo_type_valid_rec
        (refs := []) hEnv
        (by simpa only [TranslationProofs.eo_type_valid,
            TranslationProofs.eo_type_valid_rec] using hValid)

theorem is_closed_rec_apply_eq_of_not_list_branch
    {f x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotList :
      ∀ q v vs,
        f ≠
          Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) :
  __is_closed_rec (Term.Apply f x) env =
    __eo_and (__is_closed_rec f env) (__is_closed_rec x env) :=
by
  cases hEnv <;> cases f <;> simp [__is_closed_rec]

theorem eo_type_valid_rec_not_eo_list_cons
    {refs : List native_String} {T : Term}
    (hValid : TranslationProofs.eo_type_valid_rec refs T) :
    ∀ v vs, T ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs :=
by
  intro v vs hEq
  subst T
  simp [TranslationProofs.eo_type_valid_rec, __eo_to_smt_type,
    TranslationProofs.noNoneTy] at hValid

theorem apply_head_not_list_branch_of_arg_not_list
    {h y : Term}
    (hy : ∀ v vs, y ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs) :
    ∀ q v vs,
      Term.Apply h y ≠
        Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) :=
by
  intro q v vs hEq
  cases hEq
  exact hy v vs rfl

theorem is_closed_rec_eq_true_of_eo_type_valid_rec
    {refs : List native_String} {T env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hValid : TranslationProofs.eo_type_valid_rec refs T) :
  __is_closed_rec T env = Term.Boolean true :=
by
  let rec go (T : Term) :
      ∀ {refs : List native_String} {env : Term} {vars : List SmtVarKey},
        EoSmtVarEnv env vars ->
          TranslationProofs.eo_type_valid_rec refs T ->
            __is_closed_rec T env = Term.Boolean true :=
  by
    intro refs env vars hEnv hValid
    cases T with
    | Bool =>
        cases hEnv <;> simp [__is_closed_rec]
    | DatatypeType s d =>
        cases hEnv <;> simp [__is_closed_rec]
    | DatatypeTypeRef s =>
        cases hEnv <;> simp [__is_closed_rec]
    | DtcAppType T U =>
        cases hEnv <;> simp [__is_closed_rec]
    | USort i =>
        cases hEnv <;> simp [__is_closed_rec]
    | UOp op =>
        cases op <;> cases hEnv <;>
          simp [TranslationProofs.eo_type_valid_rec,
            __is_closed_rec] at hValid ⊢
    | Apply f x =>
        cases f with
        | UOp op =>
            cases op <;>
              cases hEnv <;>
                simp [TranslationProofs.eo_type_valid_rec,
                  __eo_to_smt_type, TranslationProofs.noNoneTy,
                  __is_closed_rec, native_ite] at hValid ⊢
            case BitVec.nil =>
              cases x <;>
                simp [TranslationProofs.eo_type_valid_rec,
                  __eo_to_smt_type, TranslationProofs.noNoneTy,
                  __is_closed_rec, __eo_and, native_ite, native_and] at hValid ⊢
            case BitVec.cons =>
              cases x <;>
                simp [TranslationProofs.eo_type_valid_rec,
                  __eo_to_smt_type, TranslationProofs.noNoneTy,
                  __is_closed_rec, __eo_and, native_ite, native_and] at hValid ⊢
            case Seq.nil =>
              have hx := go x EoSmtVarEnv.nil
                (eo_type_valid_rec_seq_arg (refs := refs) hValid)
              simp [__is_closed_rec, hx, eo_and_true_true]
            case Seq.cons hTail =>
              rename_i s' T' env' vars'
              have hEnvCons := EoSmtVarEnv.cons (s := s') (T := T') hTail
              have hx := go x hEnvCons
                (eo_type_valid_rec_seq_arg (refs := refs) hValid)
              simp [__is_closed_rec, hx, eo_and_true_true]
            case Set.nil =>
              have hx := go x EoSmtVarEnv.nil
                (eo_type_valid_rec_set_arg (refs := refs) hValid)
              simp [__is_closed_rec, hx, eo_and_true_true]
            case Set.cons hTail =>
              rename_i s' T' env' vars'
              have hEnvCons := EoSmtVarEnv.cons (s := s') (T := T') hTail
              have hx := go x hEnvCons
                (eo_type_valid_rec_set_arg (refs := refs) hValid)
              simp [__is_closed_rec, hx, eo_and_true_true]
        | Apply g y =>
            cases g with
            | FunType =>
                rcases eo_type_valid_rec_fun_args (refs := refs) hValid with
                  ⟨hyValid, hxValid⟩
                cases hEnv with
                | nil =>
                    have hy := go y EoSmtVarEnv.nil hyValid
                    have hx := go x EoSmtVarEnv.nil hxValid
                    have hyNotList :=
                      eo_type_valid_rec_not_eo_list_cons hyValid
                    have hOuterNotList :
                        ∀ q v vs,
                          Term.Apply Term.FunType y ≠
                            Term.Apply q
                              (Term.Apply
                                (Term.Apply Term.__eo_List_cons v) vs) :=
                      apply_head_not_list_branch_of_arg_not_list hyNotList
                    have hInnerNotList :
                        ∀ q v vs,
                          Term.FunType ≠
                            Term.Apply q
                              (Term.Apply
                                (Term.Apply Term.__eo_List_cons v) vs) := by
                      intro q v vs hEq
                      cases hEq
                    rw [is_closed_rec_apply_eq_of_not_list_branch
                      EoSmtVarEnv.nil hOuterNotList]
                    rw [is_closed_rec_apply_eq_of_not_list_branch
                      EoSmtVarEnv.nil hInnerNotList]
                    simp [__is_closed_rec, hy, hx, eo_and_true_true]
                | cons hTail =>
                    rename_i s' T' env' vars'
                    have hEnvCons :=
                      EoSmtVarEnv.cons (s := s') (T := T') hTail
                    have hy := go y hEnvCons hyValid
                    have hx := go x hEnvCons hxValid
                    have hyNotList :=
                      eo_type_valid_rec_not_eo_list_cons hyValid
                    have hOuterNotList :
                        ∀ q v vs,
                          Term.Apply Term.FunType y ≠
                            Term.Apply q
                              (Term.Apply
                                (Term.Apply Term.__eo_List_cons v) vs) :=
                      apply_head_not_list_branch_of_arg_not_list hyNotList
                    have hInnerNotList :
                        ∀ q v vs,
                          Term.FunType ≠
                            Term.Apply q
                              (Term.Apply
                                (Term.Apply Term.__eo_List_cons v) vs) := by
                      intro q v vs hEq
                      cases hEq
                    rw [is_closed_rec_apply_eq_of_not_list_branch
                      hEnvCons hOuterNotList]
                    rw [is_closed_rec_apply_eq_of_not_list_branch
                      hEnvCons hInnerNotList]
                    simp [__is_closed_rec, hy, hx, eo_and_true_true]
            | UOp op =>
                cases op <;>
                  cases hEnv <;>
                    simp [TranslationProofs.eo_type_valid_rec,
                      __eo_to_smt_type, TranslationProofs.noNoneTy,
                      __is_closed_rec, native_ite] at hValid ⊢
                case Array.nil =>
                  rcases eo_type_valid_rec_array_args (refs := refs) hValid with
                    ⟨hyValid, hxValid⟩
                  have hy := go y EoSmtVarEnv.nil hyValid
                  have hx := go x EoSmtVarEnv.nil hxValid
                  have hyNotList :=
                    eo_type_valid_rec_not_eo_list_cons hyValid
                  have hOuterNotList :
                      ∀ q v vs,
                        Term.Apply (Term.UOp UserOp.Array) y ≠
                          Term.Apply q
                            (Term.Apply
                              (Term.Apply Term.__eo_List_cons v) vs) :=
                    apply_head_not_list_branch_of_arg_not_list hyNotList
                  have hInnerNotList :
                      ∀ q v vs,
                        Term.UOp UserOp.Array ≠
                          Term.Apply q
                            (Term.Apply
                              (Term.Apply Term.__eo_List_cons v) vs) := by
                    intro q v vs hEq
                    cases hEq
                  rw [is_closed_rec_apply_eq_of_not_list_branch
                    EoSmtVarEnv.nil hOuterNotList]
                  rw [is_closed_rec_apply_eq_of_not_list_branch
                    EoSmtVarEnv.nil hInnerNotList]
                  simp [__is_closed_rec, hy, hx, eo_and_true_true]
                case Array.cons hTail =>
                  rename_i s' T' env' vars'
                  rcases eo_type_valid_rec_array_args (refs := refs) hValid with
                    ⟨hyValid, hxValid⟩
                  have hEnvCons :=
                    EoSmtVarEnv.cons (s := s') (T := T') hTail
                  have hy := go y hEnvCons hyValid
                  have hx := go x hEnvCons hxValid
                  have hyNotList :=
                    eo_type_valid_rec_not_eo_list_cons hyValid
                  have hOuterNotList :
                      ∀ q v vs,
                        Term.Apply (Term.UOp UserOp.Array) y ≠
                          Term.Apply q
                            (Term.Apply
                              (Term.Apply Term.__eo_List_cons v) vs) :=
                    apply_head_not_list_branch_of_arg_not_list hyNotList
                  have hInnerNotList :
                      ∀ q v vs,
                        Term.UOp UserOp.Array ≠
                          Term.Apply q
                            (Term.Apply
                              (Term.Apply Term.__eo_List_cons v) vs) := by
                    intro q v vs hEq
                    cases hEq
                  rw [is_closed_rec_apply_eq_of_not_list_branch
                    hEnvCons hOuterNotList]
                  rw [is_closed_rec_apply_eq_of_not_list_branch
                    hEnvCons hInnerNotList]
                  simp [__is_closed_rec, hy, hx, eo_and_true_true]
                case Tuple.nil =>
                  rcases eo_type_valid_rec_tuple_args (refs := refs) hValid with
                    ⟨hyValid, hxValid, _hWf⟩
                  have hy := go y EoSmtVarEnv.nil hyValid
                  have hx := go x EoSmtVarEnv.nil hxValid
                  have hyNotList :=
                    eo_type_valid_rec_not_eo_list_cons hyValid
                  have hOuterNotList :
                      ∀ q v vs,
                        Term.Apply (Term.UOp UserOp.Tuple) y ≠
                          Term.Apply q
                            (Term.Apply
                              (Term.Apply Term.__eo_List_cons v) vs) :=
                    apply_head_not_list_branch_of_arg_not_list hyNotList
                  have hInnerNotList :
                      ∀ q v vs,
                        Term.UOp UserOp.Tuple ≠
                          Term.Apply q
                            (Term.Apply
                              (Term.Apply Term.__eo_List_cons v) vs) := by
                    intro q v vs hEq
                    cases hEq
                  rw [is_closed_rec_apply_eq_of_not_list_branch
                    EoSmtVarEnv.nil hOuterNotList]
                  rw [is_closed_rec_apply_eq_of_not_list_branch
                    EoSmtVarEnv.nil hInnerNotList]
                  simp [__is_closed_rec, hy, hx, eo_and_true_true]
                case Tuple.cons hTail =>
                  rename_i s' T' env' vars'
                  rcases eo_type_valid_rec_tuple_args (refs := refs) hValid with
                    ⟨hyValid, hxValid, _hWf⟩
                  have hEnvCons :=
                    EoSmtVarEnv.cons (s := s') (T := T') hTail
                  have hy := go y hEnvCons hyValid
                  have hx := go x hEnvCons hxValid
                  have hyNotList :=
                    eo_type_valid_rec_not_eo_list_cons hyValid
                  have hOuterNotList :
                      ∀ q v vs,
                        Term.Apply (Term.UOp UserOp.Tuple) y ≠
                          Term.Apply q
                            (Term.Apply
                              (Term.Apply Term.__eo_List_cons v) vs) :=
                    apply_head_not_list_branch_of_arg_not_list hyNotList
                  have hInnerNotList :
                      ∀ q v vs,
                        Term.UOp UserOp.Tuple ≠
                          Term.Apply q
                            (Term.Apply
                              (Term.Apply Term.__eo_List_cons v) vs) := by
                    intro q v vs hEq
                    cases hEq
                  rw [is_closed_rec_apply_eq_of_not_list_branch
                    hEnvCons hOuterNotList]
                  rw [is_closed_rec_apply_eq_of_not_list_branch
                    hEnvCons hInnerNotList]
                  simp [__is_closed_rec, hy, hx, eo_and_true_true]
            | _ =>
                cases hEnv <;>
                  simp [TranslationProofs.eo_type_valid_rec,
                    __eo_to_smt_type, TranslationProofs.noNoneTy,
                    __is_closed_rec, native_ite] at hValid
        | _ =>
            cases hEnv <;>
              simp [TranslationProofs.eo_type_valid_rec,
                __eo_to_smt_type, TranslationProofs.noNoneTy,
                __is_closed_rec, native_ite] at hValid
    | _ =>
        cases hEnv <;>
          simp [TranslationProofs.eo_type_valid_rec,
            __eo_to_smt_type, TranslationProofs.noNoneTy,
            __is_closed_rec, native_ite] at hValid
  exact go T hEnv hValid

theorem is_closed_rec_eq_true_of_eo_type_valid
    {T env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hValid : TranslationProofs.eo_type_valid T) :
  __is_closed_rec T env = Term.Boolean true :=
by
  cases T with
  | UOp op =>
      cases op with
      | RegLan =>
          cases hEnv <;> simp [__is_closed_rec]
      | _ =>
          exact is_closed_rec_eq_true_of_eo_type_valid_rec
            (refs := []) hEnv
            (by simpa only [TranslationProofs.eo_type_valid,
                TranslationProofs.eo_type_valid_rec] using hValid)
  | _ =>
      exact is_closed_rec_eq_true_of_eo_type_valid_rec
        (refs := []) hEnv
        (by simpa only [TranslationProofs.eo_type_valid,
            TranslationProofs.eo_type_valid_rec] using hValid)

theorem eo_type_valid_of_seq_empty_has_smt_translation
    {T : Term}
    (hTrans : eoHasSmtTranslation (Term.UOp1 UserOp1.seq_empty T)) :
  TranslationProofs.eo_type_valid T :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type T)) ≠
        SmtType.None at hTrans
  cases hTy : __eo_to_smt_type T <;> rw [hTy] at hTrans <;>
    simp [__eo_to_smt_seq_empty] at hTrans
  case Seq A =>
    have hSeqWF : __smtx_type_wf (SmtType.Seq A) = true :=
      Smtm.smtx_typeof_guard_wf_wf_of_non_none
        (SmtType.Seq A) (SmtType.Seq A) (by
          simpa [__smtx_typeof] using hTrans)
    exact TranslationProofs.eo_type_valid_of_smt_wf T
      (by simpa [hTy] using hSeqWF)

theorem eo_type_valid_of_set_empty_has_smt_translation
    {T : Term}
    (hTrans : eoHasSmtTranslation (Term.UOp1 UserOp1.set_empty T)) :
  TranslationProofs.eo_type_valid T :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof (__eo_to_smt_set_empty (__eo_to_smt_type T)) ≠
        SmtType.None at hTrans
  cases hTy : __eo_to_smt_type T <;> rw [hTy] at hTrans <;>
    simp [__eo_to_smt_set_empty] at hTrans
  case Set A =>
    have hSetWF : __smtx_type_wf (SmtType.Set A) = true :=
      Smtm.smtx_typeof_guard_wf_wf_of_non_none
        (SmtType.Set A) (SmtType.Set A) (by
          simpa [__smtx_typeof] using hTrans)
    exact TranslationProofs.eo_type_valid_of_smt_wf T
      (by simpa [hTy] using hSetWF)

theorem is_closed_rec_seq_empty_eq_eo_is_closed_rec_of_has_smt_translation
    {T env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans : eoHasSmtTranslation (Term.UOp1 UserOp1.seq_empty T)) :
  __is_closed_rec (Term.UOp1 UserOp1.seq_empty T) env =
    __eo_is_closed_rec (Term.UOp1 UserOp1.seq_empty T) env :=
by
  have hClosed :
      __eo_is_closed_rec T env = Term.Boolean true :=
    eo_is_closed_rec_eq_true_of_eo_type_valid hEnv
      (eo_type_valid_of_seq_empty_has_smt_translation hTrans)
  cases hEnv with
  | nil =>
      simp [__is_closed_rec, __eo_is_closed_rec, hClosed]
  | cons hTail =>
      simp [__is_closed_rec, __eo_is_closed_rec, hClosed]

theorem is_closed_rec_set_empty_eq_eo_is_closed_rec_of_has_smt_translation
    {T env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans : eoHasSmtTranslation (Term.UOp1 UserOp1.set_empty T)) :
  __is_closed_rec (Term.UOp1 UserOp1.set_empty T) env =
    __eo_is_closed_rec (Term.UOp1 UserOp1.set_empty T) env :=
by
  have hClosed :
      __eo_is_closed_rec T env = Term.Boolean true :=
    eo_is_closed_rec_eq_true_of_eo_type_valid hEnv
      (eo_type_valid_of_set_empty_has_smt_translation hTrans)
  cases hEnv with
  | nil =>
      simp [__is_closed_rec, __eo_is_closed_rec, hClosed]
  | cons hTail =>
      simp [__is_closed_rec, __eo_is_closed_rec, hClosed]

theorem is_closed_rec_uop1_eq_and_bool_of_has_smt_translation
    {op : UserOp1} {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans : eoHasSmtTranslation (Term.UOp1 op x)) :
  __is_closed_rec (Term.UOp1 op x) env =
    __eo_is_closed_rec (Term.UOp1 op x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.UOp1 op x) env = Term.Boolean b :=
by
  cases op
  case seq_empty =>
    refine
      ⟨is_closed_rec_seq_empty_eq_eo_is_closed_rec_of_has_smt_translation
          hEnv hTrans,
        ?_⟩
    have hClosed :
        __eo_is_closed_rec x env = Term.Boolean true :=
      eo_is_closed_rec_eq_true_of_eo_type_valid hEnv
        (eo_type_valid_of_seq_empty_has_smt_translation hTrans)
    exact ⟨true, by
      cases hEnv <;> simp [__eo_is_closed_rec, hClosed]⟩
  case set_empty =>
    refine
      ⟨is_closed_rec_set_empty_eq_eo_is_closed_rec_of_has_smt_translation
          hEnv hTrans,
        ?_⟩
    have hClosed :
        __eo_is_closed_rec x env = Term.Boolean true :=
      eo_is_closed_rec_eq_true_of_eo_type_valid hEnv
        (eo_type_valid_of_set_empty_has_smt_translation hTrans)
    exact ⟨true, by
      cases hEnv <;> simp [__eo_is_closed_rec, hClosed]⟩
  all_goals
    exfalso
    unfold eoHasSmtTranslation at hTrans
    change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
    exact hTrans TranslationProofs.smtx_typeof_none

theorem re_unfold_pos_component_zero_args_of_non_none
    (s r1 r2 : SmtTerm)
    (hNN :
      term_has_non_none_type
        (__eo_to_smt_re_unfold_pos_component s (SmtTerm.re_concat r1 r2)
          native_nat_zero)) :
  __smtx_typeof s = SmtType.Seq SmtType.Char ∧
    __smtx_typeof (SmtTerm.re_concat r1 r2) = SmtType.RegLan :=
by
  have hTermNN :
      term_has_non_none_type
        (SmtTerm.str_substr s (SmtTerm.Numeral 0)
          (SmtTerm.str_indexof_re_split s r1 r2)) := by
    simpa [__eo_to_smt_re_unfold_pos_component] using hNN
  rcases str_substr_args_of_non_none hTermNN with
    ⟨T, hS, hStart, hLen⟩
  have hSplitNN :
      term_has_non_none_type (SmtTerm.str_indexof_re_split s r1 r2) := by
    unfold term_has_non_none_type
    rw [hLen]
    simp
  have hSplitArgs := str_indexof_re_split_args_of_non_none hSplitNN
  have hR :
      __smtx_typeof (SmtTerm.re_concat r1 r2) = SmtType.RegLan := by
    rw [typeof_re_concat_eq]
    simp [hSplitArgs.2.1, hSplitArgs.2.2, native_ite, native_Teq]
  exact ⟨hSplitArgs.1, hR⟩

theorem re_unfold_pos_component_args_of_non_none
    (s r : SmtTerm) (n : native_Nat)
    (hNN :
      term_has_non_none_type
        (__eo_to_smt_re_unfold_pos_component s r n)) :
  __smtx_typeof s = SmtType.Seq SmtType.Char ∧
    __smtx_typeof r = SmtType.RegLan :=
by
  induction n generalizing s r with
  | zero =>
      cases r <;> simp [__eo_to_smt_re_unfold_pos_component] at hNN
      case re_concat r1 r2 =>
        exact re_unfold_pos_component_zero_args_of_non_none s r1 r2 (by
          simpa [__eo_to_smt_re_unfold_pos_component] using hNN)
      all_goals
        exfalso
        unfold term_has_non_none_type at hNN
        exact hNN TranslationProofs.smtx_typeof_none
  | succ n ih =>
      cases r <;> simp [__eo_to_smt_re_unfold_pos_component] at hNN
      case re_concat r1 r2 =>
        let v0 := SmtTerm.str_indexof_re_split s r1 r2
        let newS :=
          SmtTerm.str_substr s v0 (SmtTerm.neg (SmtTerm.str_len s) v0)
        have hRecArgs :
            __smtx_typeof newS = SmtType.Seq SmtType.Char ∧
              __smtx_typeof r2 = SmtType.RegLan := by
          exact ih newS r2 (by
            simpa [newS, v0, __eo_to_smt_re_unfold_pos_component]
              using hNN)
        have hNewSNN : term_has_non_none_type newS := by
          unfold term_has_non_none_type
          rw [hRecArgs.1]
          simp
        rcases str_substr_args_of_non_none hNewSNN with
          ⟨T, hSRaw, hV0, hLen⟩
        have hSplitNN : term_has_non_none_type v0 := by
          unfold term_has_non_none_type
          rw [hV0]
          simp
        have hSplitArgs := str_indexof_re_split_args_of_non_none hSplitNN
        have hR :
            __smtx_typeof (SmtTerm.re_concat r1 r2) = SmtType.RegLan := by
          rw [typeof_re_concat_eq]
          simp [hSplitArgs.2.1, hSplitArgs.2.2, native_ite, native_Teq]
        exact ⟨hSplitArgs.1, hR⟩
      all_goals
        exfalso
        unfold term_has_non_none_type at hNN
        exact hNN TranslationProofs.smtx_typeof_none

theorem re_unfold_pos_component_parts_have_smt_translation
    {s r idx : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx)) :
  eoHasSmtTranslation s ∧ eoHasSmtTranslation r :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (native_ite (__eo_to_smt_nat_is_valid idx)
            (__eo_to_smt_re_unfold_pos_component
              (__eo_to_smt s) (__eo_to_smt r) (__eo_to_smt_nat idx))
            SmtTerm.None) ≠
        SmtType.None at hTrans
  cases hValid : __eo_to_smt_nat_is_valid idx
  · exfalso
    exact hTrans (by
      simp [hValid, native_ite, TranslationProofs.smtx_typeof_none])
  · have hCompNN :
        term_has_non_none_type
          (__eo_to_smt_re_unfold_pos_component
            (__eo_to_smt s) (__eo_to_smt r) (__eo_to_smt_nat idx)) := by
      unfold term_has_non_none_type
      intro hNone
      exact hTrans (by simp [hValid, native_ite, hNone])
    have hArgs :=
      re_unfold_pos_component_args_of_non_none
        (__eo_to_smt s) (__eo_to_smt r) (__eo_to_smt_nat idx) hCompNN
    constructor
    · unfold eoHasSmtTranslation
      rw [hArgs.1]
      intro h
      cases h
    · unfold eoHasSmtTranslation
      rw [hArgs.2]
      intro h
      cases h

theorem nat_is_valid_of_re_unfold_pos_component_has_smt_translation
    {s r idx : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx)) :
  __eo_to_smt_nat_is_valid idx = true :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (native_ite (__eo_to_smt_nat_is_valid idx)
            (__eo_to_smt_re_unfold_pos_component
              (__eo_to_smt s) (__eo_to_smt r) (__eo_to_smt_nat idx))
            SmtTerm.None) ≠
        SmtType.None at hTrans
  cases hValid : __eo_to_smt_nat_is_valid idx
  · exfalso
    exact hTrans (by simp [hValid, native_ite, __smtx_typeof])
  · rfl

theorem nat_is_valid_of_quantifiers_skolemize_forall_has_smt_translation
    {vs body idx : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          idx)) :
  __eo_to_smt_nat_is_valid idx = true :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (native_ite (__eo_to_smt_nat_is_valid idx)
            (__eo_to_smt_quantifiers_skolemize vs
              (SmtTerm.not (__eo_to_smt body))
              (__eo_to_smt_nat idx))
            SmtTerm.None) ≠
        SmtType.None at hTrans
  cases hValid : __eo_to_smt_nat_is_valid idx
  · exfalso
    exact hTrans (by simp [hValid, native_ite, __smtx_typeof])
  · rfl

/-- Splits a well-typed `choice` into its body-`Bool` and binder-well-formed
components (the new skolemize head shape). -/
theorem closed_choice_non_none_split
    (s : native_String) (U : SmtType) (C : SmtTerm)
    (hNN : __smtx_typeof (SmtTerm.choice s U C) ≠ SmtType.None) :
  __smtx_typeof C = SmtType.Bool ∧ __smtx_type_wf U = true :=
by
  have hEq :
      __smtx_typeof (SmtTerm.choice s U C) =
        native_ite (native_Teq (__smtx_typeof C) SmtType.Bool)
          (__smtx_typeof_guard_wf U U) SmtType.None := by
    rw [__smtx_typeof.eq_def] <;> simp only
  rw [hEq] at hNN
  by_cases hT : native_Teq (__smtx_typeof C) SmtType.Bool = true
  · have hCBool : __smtx_typeof C = SmtType.Bool := by
      simpa [native_Teq] using hT
    refine ⟨hCBool, ?_⟩
    have hGuardNN : __smtx_typeof_guard_wf U U ≠ SmtType.None := by
      simpa [hT, native_ite] using hNN
    exact Smtm.smtx_typeof_guard_wf_wf_of_non_none U U hGuardNN
  · exfalso
    have hF : native_Teq (__smtx_typeof C) SmtType.Bool = false := by
      cases hh : native_Teq (__smtx_typeof C) SmtType.Bool <;> simp_all
    simp [hF, native_ite] at hNN

/-- Builds a `Bool`-typed `exists` layer from a well-formed binder type and a
`Bool`-typed body. -/
theorem closed_exists_cons_bool
    (s : native_String) (U : SmtType) (C : SmtTerm)
    (hWf : __smtx_type_wf U = true)
    (hC : __smtx_typeof C = SmtType.Bool) :
  __smtx_typeof (SmtTerm.exists s U C) = SmtType.Bool :=
by
  have hEq :
      __smtx_typeof (SmtTerm.exists s U C) =
        native_ite (native_Teq (__smtx_typeof C) SmtType.Bool)
          (__smtx_typeof_guard_wf U SmtType.Bool) SmtType.None := by
    rw [__smtx_typeof.eq_def] <;> simp only
  rw [hEq, hC]
  simp [native_Teq, native_ite, __smtx_typeof_guard_wf, hWf]

/-- Peels every binder of an `exists` chain: if the whole chain is `Bool`, so is
its innermost body.  (`Eo.Term` is mutually inductive, so this is written as a
structural recursion over the binder list rather than via `induction`.) -/
theorem closed_smtx_typeof_exists_body_bool :
    ∀ (vs : Term) (X : SmtTerm),
      __smtx_typeof (__eo_to_smt_exists vs X) = SmtType.Bool ->
      __smtx_typeof X = SmtType.Bool
  | Term.Apply f a, X, h => by
      cases f <;> try exact absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
      case Apply g y =>
        cases g <;> try exact absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
        case __eo_List_cons =>
          cases y <;> try exact absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
          case Var name T =>
            cases name <;> try exact absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
            case String s =>
              rw [TranslationProofs.eo_to_smt_exists_cons] at h
              have hNN :
                  term_has_non_none_type
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists a X)) := by
                unfold term_has_non_none_type
                rw [h]
                simp
              exact
                closed_smtx_typeof_exists_body_bool a X
                  (exists_body_bool_of_non_none hNN)
  | Term.__eo_List_nil, X, h => by simpa [__eo_to_smt_exists] using h
  | Term.UOp _, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.UOp1 _ _, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.UOp2 _ _ _, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.UOp3 _ _ _ _, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.__eo_List, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.__eo_List_cons, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.Bool, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.Boolean _, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.Numeral _, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.Rational _, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.String _, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.Binary _ _, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.Type, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.Stuck, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.FunType, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.Var _ _, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.DatatypeType _ _, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.DatatypeTypeRef _, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.DtcAppType _ _, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.DtCons _ _ _, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.DtSel _ _ _ _, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.USort _, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])
  | Term.UConst _ _, X, h => absurd (show __smtx_typeof SmtTerm.None = SmtType.Bool from h) (by simp [TranslationProofs.smtx_typeof_none])

theorem closed_smtx_typeof_eo_to_smt_exists_cons_bool_of_tail_bool
    (s : native_String) (T a : Term) (body : SmtTerm)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hTailBool : __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool) :
  __smtx_typeof
      (__eo_to_smt_exists
        (Term.Apply
          (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) a)
        body) =
    SmtType.Bool :=
by
  rw [TranslationProofs.eo_to_smt_exists_cons]
  change
    __smtx_typeof
        (SmtTerm.exists s (__eo_to_smt_type T)
          (__eo_to_smt_exists a body)) =
      SmtType.Bool
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [hTailBool, native_ite, native_Teq, __smtx_typeof_guard_wf, hWf]

theorem closed_eo_to_smt_exists_bool_of_quantifiers_skolemize_non_none :
    ∀ (n : native_Nat) (vs : Term) (G : SmtTerm),
      __smtx_typeof (__eo_to_smt_quantifiers_skolemize vs G n) ≠
          SmtType.None ->
      __smtx_typeof (__eo_to_smt_exists vs G) = SmtType.Bool := by
  intro n
  induction n with
  | zero =>
      intro vs G hNN
      cases vs <;>
        try exact absurd rfl (show SmtType.None ≠ SmtType.None from hNN)
      case Apply f a =>
        cases f <;>
          try exact absurd rfl (show SmtType.None ≠ SmtType.None from hNN)
        case Apply g y =>
          cases g <;>
            try exact absurd rfl (show SmtType.None ≠ SmtType.None from hNN)
          case __eo_List_cons =>
            cases y <;>
              try exact absurd rfl (show SmtType.None ≠ SmtType.None from hNN)
            case Var name T =>
              cases name <;>
                try exact absurd rfl (show SmtType.None ≠ SmtType.None from hNN)
              case String s =>
                rw [TranslationProofs.eo_to_smt_quantifiers_skolemize_zero]
                  at hNN
                obtain ⟨hCBool, hWf⟩ :=
                  closed_choice_non_none_split s (__eo_to_smt_type T)
                    (__eo_to_smt_exists a G) hNN
                rw [TranslationProofs.eo_to_smt_exists_cons]
                exact closed_exists_cons_bool s (__eo_to_smt_type T)
                  (__eo_to_smt_exists a G) hWf hCBool
  | succ n ih =>
      intro vs G hNN
      cases vs <;>
        try exact absurd rfl (show SmtType.None ≠ SmtType.None from hNN)
      case Apply f a =>
        cases f <;>
          try exact absurd rfl (show SmtType.None ≠ SmtType.None from hNN)
        case Apply g y =>
          cases g <;>
            try exact absurd rfl (show SmtType.None ≠ SmtType.None from hNN)
          case __eo_List_cons =>
            cases y <;>
              try exact absurd rfl (show SmtType.None ≠ SmtType.None from hNN)
            case Var name T =>
              cases name <;>
                try exact absurd rfl (show SmtType.None ≠ SmtType.None from hNN)
              case String s =>
                -- New skolemize succ: recurse on the tail `a` with the body
                -- wrapped in a `bind`/`choice` layer.
                have hNN' :
                    __smtx_typeof
                        (__eo_to_smt_quantifiers_skolemize a
                          (SmtTerm.bind s (__eo_to_smt_type T)
                            (SmtTerm.choice s (__eo_to_smt_type T)
                              (__eo_to_smt_exists a G)) G) n) ≠
                      SmtType.None := hNN
                have hExRestBool :
                    __smtx_typeof
                        (__eo_to_smt_exists a
                          (SmtTerm.bind s (__eo_to_smt_type T)
                            (SmtTerm.choice s (__eo_to_smt_type T)
                              (__eo_to_smt_exists a G)) G)) =
                      SmtType.Bool :=
                  ih a _ hNN'
                have hG'Bool :
                    __smtx_typeof
                        (SmtTerm.bind s (__eo_to_smt_type T)
                          (SmtTerm.choice s (__eo_to_smt_type T)
                            (__eo_to_smt_exists a G)) G) =
                      SmtType.Bool :=
                  closed_smtx_typeof_exists_body_bool a _ hExRestBool
                have hBindNN :
                    term_has_non_none_type
                      (SmtTerm.bind s (__eo_to_smt_type T)
                        (SmtTerm.choice s (__eo_to_smt_type T)
                          (__eo_to_smt_exists a G)) G) := by
                  unfold term_has_non_none_type
                  rw [hG'Bool]
                  simp
                have hWf : __smtx_type_wf (__eo_to_smt_type T) = true :=
                  bind_binder_type_wf_of_non_none hBindNN
                have hcU :
                    __smtx_typeof
                        (SmtTerm.choice s (__eo_to_smt_type T)
                          (__eo_to_smt_exists a G)) =
                      __eo_to_smt_type T :=
                  bind_arg1_type_of_non_none hBindNN
                have hcNN :
                    __smtx_typeof
                        (SmtTerm.choice s (__eo_to_smt_type T)
                          (__eo_to_smt_exists a G)) ≠
                      SmtType.None := by
                  rw [hcU]
                  intro hUNone
                  rw [hUNone] at hWf
                  exact absurd hWf (by native_decide)
                obtain ⟨hRestBool, _⟩ :=
                  closed_choice_non_none_split s (__eo_to_smt_type T)
                    (__eo_to_smt_exists a G) hcNN
                rw [TranslationProofs.eo_to_smt_exists_cons]
                exact closed_exists_cons_bool s (__eo_to_smt_type T)
                  (__eo_to_smt_exists a G) hWf hRestBool

theorem quantifiers_skolemize_forall_term_has_smt_translation
    {vs body idx : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          idx)) :
  eoHasSmtTranslation
    (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body) :=
by
  unfold eoHasSmtTranslation at hTrans ⊢
  have hValid :
      __eo_to_smt_nat_is_valid idx = true :=
    nat_is_valid_of_quantifiers_skolemize_forall_has_smt_translation
      hTrans
  have hSkolemNN :
      __smtx_typeof
          (__eo_to_smt_quantifiers_skolemize vs
            (SmtTerm.not (__eo_to_smt body))
            (__eo_to_smt_nat idx)) ≠
        SmtType.None := by
    intro hNone
    apply hTrans
    change
      __smtx_typeof
          (native_ite (__eo_to_smt_nat_is_valid idx)
            (__eo_to_smt_quantifiers_skolemize vs
              (SmtTerm.not (__eo_to_smt body))
              (__eo_to_smt_nat idx))
            SmtTerm.None) =
        SmtType.None
    simp [hValid, hNone, native_ite]
  have hExistsBool :
      __smtx_typeof
          (__eo_to_smt_exists vs (SmtTerm.not (__eo_to_smt body))) =
        SmtType.Bool :=
    closed_eo_to_smt_exists_bool_of_quantifiers_skolemize_non_none
      (__eo_to_smt_nat idx) vs (SmtTerm.not (__eo_to_smt body))
      hSkolemNN
  cases vs
  case __eo_List_nil =>
      exfalso
      exact hTrans (by
        change
          __smtx_typeof
              (native_ite (__eo_to_smt_nat_is_valid idx)
                (__eo_to_smt_quantifiers_skolemize Term.__eo_List_nil
                  (SmtTerm.not (__eo_to_smt body))
                  (__eo_to_smt_nat idx))
                SmtTerm.None) =
            SmtType.None
        simp [hValid, __eo_to_smt_quantifiers_skolemize, native_ite,
          TranslationProofs.smtx_typeof_none])
  all_goals
    change
      __smtx_typeof
          (SmtTerm.not
            (__eo_to_smt_exists _ (SmtTerm.not (__eo_to_smt body)))) ≠
        SmtType.None
    rw [typeof_not_eq]
    simp [hExistsBool, native_ite, native_Teq]

theorem is_closed_rec_re_unfold_pos_component_eq_of_has_smt_translation_and_parts
    {s r idx env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx))
    (hS :
      __is_closed_rec s env = __eo_is_closed_rec s env)
    (hR :
      __is_closed_rec r env = __eo_is_closed_rec r env)
    (hSBool : ∃ b, __eo_is_closed_rec s env = Term.Boolean b)
    (hRBool : ∃ b, __eo_is_closed_rec r env = Term.Boolean b) :
  __is_closed_rec
      (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx) env =
    __eo_is_closed_rec
      (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx) env :=
by
  rcases hSBool with ⟨bs, hSBool⟩
  rcases hRBool with ⟨br, hRBool⟩
  have hIdx :
      __eo_is_closed_rec idx env = Term.Boolean true :=
    eo_is_closed_rec_eq_true_of_nat_is_valid hEnv
      (nat_is_valid_of_re_unfold_pos_component_has_smt_translation hTrans)
  rcases eo_and_eq_boolean_of_boolean hSBool hRBool with
    ⟨bsr, hSRBool⟩
  cases hEnv with
  | nil =>
      simpa [__is_closed_rec, __eo_is_closed_rec, hS, hR, hIdx,
        hSRBool] using
          (eo_and_true_right_eq_of_boolean hSRBool).symm
  | cons hTail =>
      simpa [__is_closed_rec, __eo_is_closed_rec, hS, hR, hIdx,
        hSRBool] using
          (eo_and_true_right_eq_of_boolean hSRBool).symm

theorem is_closed_rec_quantifiers_skolemize_forall_eq_of_has_smt_translation_and_term
    {vs body idx env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          idx))
    (hQ :
      __is_closed_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          env =
        __eo_is_closed_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          env)
    (hQBool :
      ∃ b,
        __eo_is_closed_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
            env =
          Term.Boolean b) :
  __is_closed_rec
      (Term.UOp2 UserOp2._at_quantifiers_skolemize
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
        idx)
      env =
    __eo_is_closed_rec
      (Term.UOp2 UserOp2._at_quantifiers_skolemize
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
        idx)
      env :=
by
  rcases hQBool with ⟨bq, hQBool⟩
  have hIdx :
      __eo_is_closed_rec idx env = Term.Boolean true :=
    eo_is_closed_rec_eq_true_of_nat_is_valid hEnv
      (nat_is_valid_of_quantifiers_skolemize_forall_has_smt_translation
        hTrans)
  cases hEnv with
  | nil =>
      simpa [__is_closed_rec, __eo_is_closed_rec, hQ, hIdx]
        using (eo_and_true_right_eq_of_boolean hQBool).symm
  | cons hTail =>
      simpa [__is_closed_rec, __eo_is_closed_rec, hQ, hIdx]
        using (eo_and_true_right_eq_of_boolean hQBool).symm

theorem is_closed_rec_quantifiers_skolemize_forall_eq_and_bool_of_has_smt_translation_and_term
    {vs body idx env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          idx))
    (hQ :
      __is_closed_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          env =
        __eo_is_closed_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          env)
    (hQBool :
      ∃ b,
        __eo_is_closed_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
            env =
          Term.Boolean b) :
  __is_closed_rec
      (Term.UOp2 UserOp2._at_quantifiers_skolemize
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
        idx)
      env =
    __eo_is_closed_rec
      (Term.UOp2 UserOp2._at_quantifiers_skolemize
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
        idx)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          idx)
        env =
      Term.Boolean b :=
by
  refine
    ⟨is_closed_rec_quantifiers_skolemize_forall_eq_of_has_smt_translation_and_term
        hEnv hTrans hQ hQBool,
      ?_⟩
  rcases hQBool with ⟨bq, hQBool⟩
  have hIdx :
      __eo_is_closed_rec idx env = Term.Boolean true :=
    eo_is_closed_rec_eq_true_of_nat_is_valid hEnv
      (nat_is_valid_of_quantifiers_skolemize_forall_has_smt_translation
        hTrans)
  exact ⟨bq, by
    cases hEnv <;>
      simpa [__eo_is_closed_rec, hIdx] using
        (eo_and_true_right_eq_of_boolean hQBool).trans hQBool⟩

theorem is_closed_rec_quantifiers_skolemize_forall_eq_and_bool_of_has_smt_translation
    {vs body idx env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          idx))
    (ihQ :
      eoHasSmtTranslation
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body) ->
        __is_closed_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
            env =
          __eo_is_closed_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
            env ∧
          ∃ b,
            __eo_is_closed_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
                env =
              Term.Boolean b) :
  __is_closed_rec
      (Term.UOp2 UserOp2._at_quantifiers_skolemize
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
        idx)
      env =
    __eo_is_closed_rec
      (Term.UOp2 UserOp2._at_quantifiers_skolemize
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
        idx)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          idx)
        env =
      Term.Boolean b :=
by
  have hQTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body) :=
    quantifiers_skolemize_forall_term_has_smt_translation hTrans
  exact
    is_closed_rec_quantifiers_skolemize_forall_eq_and_bool_of_has_smt_translation_and_term
      hEnv hTrans (ihQ hQTrans).1 (ihQ hQTrans).2

theorem is_closed_rec_uop2_eq_and_bool_of_has_smt_translation
    {op : UserOp2} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans : eoHasSmtTranslation (Term.UOp2 op x y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.UOp2 op x y) env =
    __eo_is_closed_rec (Term.UOp2 op x y) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.UOp2 op x y) env =
        Term.Boolean b :=
by
  cases op
  case _at_quantifiers_skolemize =>
    cases x
    case Apply f body =>
      cases f
      case Apply q vs =>
        cases q
        case UOp qOp =>
          cases qOp
          case «forall» =>
            exact
              is_closed_rec_quantifiers_skolemize_forall_eq_and_bool_of_has_smt_translation
                hEnv hTrans ihX
          all_goals
            exfalso
            unfold eoHasSmtTranslation at hTrans
            change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
            exact hTrans TranslationProofs.smtx_typeof_none
        all_goals
          exfalso
          unfold eoHasSmtTranslation at hTrans
          change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
          exact hTrans TranslationProofs.smtx_typeof_none
      all_goals
        exfalso
        unfold eoHasSmtTranslation at hTrans
        change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
        exact hTrans TranslationProofs.smtx_typeof_none
    all_goals
      exfalso
      unfold eoHasSmtTranslation at hTrans
      change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
      exact hTrans TranslationProofs.smtx_typeof_none
  case _at_const =>
    unfold eoHasSmtTranslation at hTrans
    cases hValid : __eo_to_smt_nat_is_valid x
    · rw [TranslationProofs.eo_to_smt_at_const_of_invalid hValid] at hTrans
      exact False.elim (hTrans TranslationProofs.smtx_typeof_none)
    · rw [TranslationProofs.eo_to_smt_at_const_of_valid hValid] at hTrans
      have hYWF : __smtx_type_wf (__eo_to_smt_type y) = true :=
        Smtm.smtx_typeof_guard_wf_wf_of_non_none
          (__eo_to_smt_type y) (__eo_to_smt_type y) (by
            simpa [__smtx_typeof] using hTrans)
      have hYValid : TranslationProofs.eo_type_valid y :=
        TranslationProofs.eo_type_valid_of_smt_wf y hYWF
      have hYClosed := eo_is_closed_rec_eq_true_of_eo_type_valid hEnv hYValid
      obtain ⟨n, rfl⟩ :=
        TranslationProofs.eo_to_smt_nat_is_valid_eq_numeral hValid
      refine ⟨?_, ⟨true, ?_⟩⟩
      · cases hEnv <;>
          simp [__is_closed_rec, __eo_is_closed_rec, hYClosed, __eo_and,
            native_and]
      · cases hEnv <;>
          simp [__eo_is_closed_rec, hYClosed, __eo_and, native_and]
  all_goals
    exfalso
    unfold eoHasSmtTranslation at hTrans
    change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
    exact hTrans TranslationProofs.smtx_typeof_none

theorem is_closed_rec_re_unfold_pos_component_eq_and_bool_of_has_smt_translation_and_parts
    {s r idx env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx))
    (hS :
      __is_closed_rec s env = __eo_is_closed_rec s env ∧
        ∃ b, __eo_is_closed_rec s env = Term.Boolean b)
    (hR :
      __is_closed_rec r env = __eo_is_closed_rec r env ∧
        ∃ b, __eo_is_closed_rec r env = Term.Boolean b) :
  __is_closed_rec
      (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx) env =
    __eo_is_closed_rec
      (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx) env =
      Term.Boolean b :=
by
  rcases hS with ⟨hSEq, hSBool⟩
  rcases hR with ⟨hREq, hRBool⟩
  refine
    ⟨is_closed_rec_re_unfold_pos_component_eq_of_has_smt_translation_and_parts
        hEnv hTrans hSEq hREq hSBool hRBool,
      ?_⟩
  rcases hSBool with ⟨bs, hSBool⟩
  rcases hRBool with ⟨br, hRBool⟩
  have hIdx :
      __eo_is_closed_rec idx env = Term.Boolean true :=
    eo_is_closed_rec_eq_true_of_nat_is_valid hEnv
      (nat_is_valid_of_re_unfold_pos_component_has_smt_translation hTrans)
  rcases eo_and_eq_boolean_of_boolean hSBool hRBool with
    ⟨bsr, hSRBool⟩
  exact ⟨bsr, by
    cases hEnv <;>
      simpa [__eo_is_closed_rec, hIdx, hSRBool] using
        (eo_and_true_right_eq_of_boolean hSRBool).trans hSRBool⟩

theorem is_closed_rec_re_unfold_pos_component_eq_and_bool_of_has_smt_translation
    {s r idx env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx))
    (ihS :
      eoHasSmtTranslation s ->
        __is_closed_rec s env = __eo_is_closed_rec s env ∧
          ∃ b, __eo_is_closed_rec s env = Term.Boolean b)
    (ihR :
      eoHasSmtTranslation r ->
        __is_closed_rec r env = __eo_is_closed_rec r env ∧
          ∃ b, __eo_is_closed_rec r env = Term.Boolean b) :
  __is_closed_rec
      (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx) env =
    __eo_is_closed_rec
      (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx) env =
      Term.Boolean b :=
by
  rcases re_unfold_pos_component_parts_have_smt_translation hTrans with
    ⟨hSTrans, hRTrans⟩
  exact
    is_closed_rec_re_unfold_pos_component_eq_and_bool_of_has_smt_translation_and_parts
      hEnv hTrans (ihS hSTrans) (ihR hRTrans)

theorem nat_is_valid_of_witness_string_length_len_has_smt_translation
    {T len id : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp3 UserOp3._at_witness_string_length T len id)) :
  __eo_to_smt_nat_is_valid len = true :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (native_ite (__eo_to_smt_nat_is_valid len)
            (native_ite (__eo_to_smt_nat_is_valid id)
              (SmtTerm.choice (native_string_lit "@x")
                (__eo_to_smt_type T)
                (SmtTerm.eq
                  (SmtTerm.str_len
                    (SmtTerm.Var (native_string_lit "@x")
                      (__eo_to_smt_type T)))
                  (__eo_to_smt len)))
              SmtTerm.None)
            SmtTerm.None) ≠
        SmtType.None at hTrans
  cases hValid : __eo_to_smt_nat_is_valid len
  · exfalso
    exact hTrans (by
      simp [hValid, native_ite, TranslationProofs.smtx_typeof_none])
  · rfl

theorem nat_is_valid_of_witness_string_length_id_has_smt_translation
    {T len id : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp3 UserOp3._at_witness_string_length T len id)) :
  __eo_to_smt_nat_is_valid id = true :=
by
  have hLen :
      __eo_to_smt_nat_is_valid len = true :=
    nat_is_valid_of_witness_string_length_len_has_smt_translation hTrans
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (native_ite (__eo_to_smt_nat_is_valid len)
            (native_ite (__eo_to_smt_nat_is_valid id)
              (SmtTerm.choice (native_string_lit "@x")
                (__eo_to_smt_type T)
                (SmtTerm.eq
                  (SmtTerm.str_len
                    (SmtTerm.Var (native_string_lit "@x")
                      (__eo_to_smt_type T)))
                  (__eo_to_smt len)))
              SmtTerm.None)
            SmtTerm.None) ≠
        SmtType.None at hTrans
  cases hValid : __eo_to_smt_nat_is_valid id
  · exfalso
    exact hTrans (by
      simp [hLen, hValid, native_ite, TranslationProofs.smtx_typeof_none])
  · rfl

theorem eo_type_valid_of_witness_string_length_has_smt_translation
    {T len id : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp3 UserOp3._at_witness_string_length T len id)) :
  TranslationProofs.eo_type_valid T :=
by
  have hLen :
      __eo_to_smt_nat_is_valid len = true :=
    nat_is_valid_of_witness_string_length_len_has_smt_translation hTrans
  have hId :
      __eo_to_smt_nat_is_valid id = true :=
    nat_is_valid_of_witness_string_length_id_has_smt_translation hTrans
  unfold eoHasSmtTranslation at hTrans
  let ST := __eo_to_smt_type T
  let body :=
    SmtTerm.eq
      (SmtTerm.str_len (SmtTerm.Var (native_string_lit "@x") ST))
      (__eo_to_smt len)
  have hChoiceNN :
      term_has_non_none_type
        (SmtTerm.choice (native_string_lit "@x") ST body) := by
    unfold term_has_non_none_type
    intro hNone
    apply hTrans
    change
      __smtx_typeof
          (native_ite (__eo_to_smt_nat_is_valid len)
            (native_ite (__eo_to_smt_nat_is_valid id)
              (SmtTerm.choice (native_string_lit "@x") ST body)
              SmtTerm.None)
            SmtTerm.None) =
        SmtType.None
    simp [hLen, hId, hNone, native_ite]
  have hChoiceGuard :
      __smtx_typeof
          (SmtTerm.choice (native_string_lit "@x") ST body) =
        __smtx_typeof_guard_wf ST ST :=
    choice_term_guard_type_of_non_none hChoiceNN
  have hGuardNN : __smtx_typeof_guard_wf ST ST ≠ SmtType.None := by
    intro hNone
    unfold term_has_non_none_type at hChoiceNN
    exact hChoiceNN (by rw [hChoiceGuard, hNone])
  have hTWF : __smtx_type_wf ST = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none ST ST hGuardNN
  exact TranslationProofs.eo_type_valid_of_smt_wf T
    (by simpa [ST] using hTWF)

theorem is_closed_rec_witness_string_length_eq_and_bool_of_has_smt_translation
    {T len id env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp3 UserOp3._at_witness_string_length T len id)) :
  __is_closed_rec
      (Term.UOp3 UserOp3._at_witness_string_length T len id) env =
    __eo_is_closed_rec
      (Term.UOp3 UserOp3._at_witness_string_length T len id) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.UOp3 UserOp3._at_witness_string_length T len id) env =
      Term.Boolean b :=
by
  have hTClosed :
      __eo_is_closed_rec T env = Term.Boolean true :=
    eo_is_closed_rec_eq_true_of_eo_type_valid hEnv
      (eo_type_valid_of_witness_string_length_has_smt_translation hTrans)
  have hLenClosed :
      __eo_is_closed_rec len env = Term.Boolean true :=
    eo_is_closed_rec_eq_true_of_nat_is_valid hEnv
      (nat_is_valid_of_witness_string_length_len_has_smt_translation hTrans)
  have hIdClosed :
      __eo_is_closed_rec id env = Term.Boolean true :=
    eo_is_closed_rec_eq_true_of_nat_is_valid hEnv
      (nat_is_valid_of_witness_string_length_id_has_smt_translation hTrans)
  refine ⟨?_, ?_⟩
  · cases hEnv <;>
      simp [__is_closed_rec, __eo_is_closed_rec, hTClosed, hLenClosed,
        hIdClosed, __eo_and, native_and]
  · exact ⟨true, by
      cases hEnv <;>
        simp [__eo_is_closed_rec, hTClosed, hLenClosed, hIdClosed,
          __eo_and, native_and]⟩

theorem is_closed_rec_uop3_eq_and_bool_of_has_smt_translation
    {op : UserOp3} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans : eoHasSmtTranslation (Term.UOp3 op x y z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.UOp3 op x y z) env =
    __eo_is_closed_rec (Term.UOp3 op x y z) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.UOp3 op x y z) env =
        Term.Boolean b :=
by
  cases op
  case _at_re_unfold_pos_component =>
    exact
      is_closed_rec_re_unfold_pos_component_eq_and_bool_of_has_smt_translation
        hEnv hTrans ihX ihY
  case _at_witness_string_length =>
    exact
      is_closed_rec_witness_string_length_eq_and_bool_of_has_smt_translation
        hEnv hTrans

theorem is_closed_rec_apply_uop_eq_and_bool_of_arg
    {op : UserOp} {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hX :
      __is_closed_rec x env = __eo_is_closed_rec x env ∧
        ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp op) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env =
        Term.Boolean b :=
by
  rcases hX with ⟨hXEq, ⟨b, hXBool⟩⟩
  refine ⟨?_, ?_⟩
  · have hEq := eo_and_true_left_eq_of_boolean hXBool
    cases hEnv <;>
      simp [__is_closed_rec, __eo_is_closed_rec, hXEq, hEq]
  · exact ⟨b, by
      have hEq := (eo_and_true_left_eq_of_boolean hXBool).trans hXBool
      cases hEnv <;>
        simp [__eo_is_closed_rec, hEq]⟩

theorem term_has_non_none_type_of_eo_has_smt_translation
    {t : Term}
    (hTrans : eoHasSmtTranslation t) :
  term_has_non_none_type (__eo_to_smt t) :=
by
  unfold eoHasSmtTranslation at hTrans
  unfold term_has_non_none_type
  exact hTrans

theorem eo_has_smt_translation_of_smt_type_eq
    {x : Term} {T : SmtType}
    (hTy : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T ≠ SmtType.None) :
  eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation
  rw [hTy]
  exact hT

theorem term_has_non_none_type_of_type_eq_closed
    {t : SmtTerm} {T : SmtType}
    (h : __smtx_typeof t = T) (hT : T ≠ SmtType.None) :
  term_has_non_none_type t :=
by
  unfold term_has_non_none_type
  rw [h]
  exact hT

theorem eo_has_smt_translation_of_term_has_non_none_type
    {x : Term}
    (hNN : term_has_non_none_type (__eo_to_smt x)) :
  eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation
  unfold term_has_non_none_type at hNN
  exact hNN

theorem not_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.not) x)) :
  eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans ⊢
  change __smtx_typeof (SmtTerm.not (__eo_to_smt x)) ≠ SmtType.None
    at hTrans
  rw [typeof_not_eq] at hTrans
  cases hX : __smtx_typeof (__eo_to_smt x) <;>
    simp [native_ite, native_Teq, hX] at hTrans ⊢

theorem to_real_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.to_real) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.to_real (__eo_to_smt x)) at hNN
  have hXTy := to_real_arg_of_non_none hNN
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem to_int_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.to_int) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.to_int (__eo_to_smt x)) at hNN
  have hXTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.to_int)
      (typeof_to_int_eq (__eo_to_smt x)) hNN
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem is_int_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.is_int) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.is_int (__eo_to_smt x)) at hNN
  have hXTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.is_int)
      (typeof_is_int_eq (__eo_to_smt x)) hNN
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem abs_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.abs) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.abs (__eo_to_smt x)) at hNN
  rcases abs_arg_of_non_none hNN with hXTy | hXTy
  · exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)
  · exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem uneg_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.uneg (__eo_to_smt x)) at hNN
  rcases
      arith_unop_arg_of_non_none (op := SmtTerm.uneg)
        (typeof_uneg_eq (__eo_to_smt x)) hNN with hXTy | hXTy
  · exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)
  · exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem int_pow2_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.int_pow2) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.int_pow2 (__eo_to_smt x)) at hNN
  have hXTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
    int_ret_arg_of_non_none (op := SmtTerm.int_pow2)
      (typeof_int_pow2_eq (__eo_to_smt x)) hNN
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem int_log2_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.int_log2) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.int_log2 (__eo_to_smt x)) at hNN
  have hXTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
    int_ret_arg_of_non_none (op := SmtTerm.int_log2)
      (typeof_int_log2_eq (__eo_to_smt x)) hNN
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem int_ispow2_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.int_ispow2) x)) :
  eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  let tx := __eo_to_smt x
  let left := SmtTerm.geq tx (SmtTerm.Numeral 0)
  let right := SmtTerm.eq tx (SmtTerm.int_pow2 (SmtTerm.int_log2 tx))
  change __smtx_typeof (SmtTerm.and left right) ≠ SmtType.None at hTrans
  have hNN : term_has_non_none_type (SmtTerm.and left right) := by
    unfold term_has_non_none_type
    exact hTrans
  rcases bool_binop_args_bool_of_non_none
      (op := SmtTerm.and) (typeof_and_eq left right) hNN with
    ⟨hLeftTy, hRightTy⟩
  have hLeftNN : term_has_non_none_type left :=
    term_has_non_none_type_of_type_eq_closed hLeftTy (by simp)
  have hLeftTyEq :
      __smtx_typeof (SmtTerm.geq tx (SmtTerm.Numeral 0)) =
        __smtx_typeof_arith_overload_op_2_ret
          (__smtx_typeof tx) (__smtx_typeof (SmtTerm.Numeral 0))
          SmtType.Bool := by
    rw [typeof_geq_eq]
  rcases
      arith_binop_ret_bool_args_of_non_none
        (op := SmtTerm.geq) hLeftTyEq (by simpa [left] using hLeftNN) with
    hInt | hReal
  · exact eo_has_smt_translation_of_smt_type_eq (by simpa [tx] using hInt.1)
      (by simp)
  · have hZeroTy : __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int := by
      rw [__smtx_typeof.eq_def] <;> simp only
    rw [hZeroTy] at hReal
    cases hReal.2

theorem int_div_by_zero_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x)) :
  eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof (SmtTerm.div (__eo_to_smt x) (SmtTerm.Numeral 0)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.div (__eo_to_smt x) (SmtTerm.Numeral 0)) := by
    unfold term_has_non_none_type
    exact hTrans
  have hArgs :=
    int_binop_args_of_non_none (op := SmtTerm.div)
      (R := SmtType.Int)
      (typeof_div_eq (__eo_to_smt x) (SmtTerm.Numeral 0)) hNN
  exact eo_has_smt_translation_of_smt_type_eq hArgs.1 (by simp)

theorem mod_by_zero_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x)) :
  eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof (SmtTerm.mod (__eo_to_smt x) (SmtTerm.Numeral 0)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.mod (__eo_to_smt x) (SmtTerm.Numeral 0)) := by
    unfold term_has_non_none_type
    exact hTrans
  have hArgs :=
    int_binop_args_of_non_none (op := SmtTerm.mod)
      (R := SmtType.Int)
      (typeof_mod_eq (__eo_to_smt x) (SmtTerm.Numeral 0)) hNN
  exact eo_has_smt_translation_of_smt_type_eq hArgs.1 (by simp)

theorem qdiv_by_zero_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp._at_div_by_zero) x)) :
  eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  let zero := SmtTerm.Rational (native_mk_rational 0 1)
  change __smtx_typeof (SmtTerm.qdiv (__eo_to_smt x) zero) ≠
    SmtType.None at hTrans
  have hNN :
      term_has_non_none_type (SmtTerm.qdiv (__eo_to_smt x) zero) := by
    unfold term_has_non_none_type
    exact hTrans
  rcases
      arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv)
        (R := SmtType.Real)
        (typeof_qdiv_eq (__eo_to_smt x) zero) hNN with
    hInt | hReal
  · have hZeroTy : __smtx_typeof zero = SmtType.Real := by
      rw [__smtx_typeof.eq_def] <;> simp only
    rw [hZeroTy] at hInt
    cases hInt.2
  · exact eo_has_smt_translation_of_smt_type_eq hReal.1 (by simp)

theorem typeof_bvnot_eq_closed
    (t : SmtTerm) :
  __smtx_typeof (SmtTerm.bvnot t) =
    __smtx_typeof_bv_op_1 (__smtx_typeof t) :=
by
  rw [__smtx_typeof.eq_39]

theorem bvnot_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.bvnot) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.bvnot (__eo_to_smt x)) at hNN
  rcases
      bv_unop_arg_of_non_none (op := SmtTerm.bvnot)
        (typeof_bvnot_eq_closed (__eo_to_smt x)) hNN with ⟨w, hXTy⟩
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem typeof_bvneg_eq_closed
    (t : SmtTerm) :
  __smtx_typeof (SmtTerm.bvneg t) =
    __smtx_typeof_bv_op_1 (__smtx_typeof t) :=
by
  rw [__smtx_typeof.eq_47]

theorem typeof_bvnego_eq_closed
    (t : SmtTerm) :
  __smtx_typeof (SmtTerm.bvnego t) =
    __smtx_typeof_bv_op_1_ret (__smtx_typeof t) SmtType.Bool :=
by
  rw [__smtx_typeof.eq_72]

theorem bvneg_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.bvneg) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.bvneg (__eo_to_smt x)) at hNN
  rcases
      bv_unop_arg_of_non_none (op := SmtTerm.bvneg)
        (typeof_bvneg_eq_closed (__eo_to_smt x)) hNN with ⟨w, hXTy⟩
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem bvnego_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.bvnego) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.bvnego (__eo_to_smt x)) at hNN
  rcases
      bv_unop_ret_arg_of_non_none (op := SmtTerm.bvnego)
        (ret := SmtType.Bool)
        (typeof_bvnego_eq_closed (__eo_to_smt x)) hNN with ⟨w, hXTy⟩
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem ubv_to_int_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.ubv_to_int) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.ubv_to_int (__eo_to_smt x)) at hNN
  rcases
      bv_unop_ret_arg_of_non_none (op := SmtTerm.ubv_to_int)
        (ret := SmtType.Int)
        (show
          __smtx_typeof (SmtTerm.ubv_to_int (__eo_to_smt x)) =
            __smtx_typeof_bv_op_1_ret
              (__smtx_typeof (__eo_to_smt x)) SmtType.Int by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hNN with
    ⟨w, hXTy⟩
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem sbv_to_int_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.sbv_to_int) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.sbv_to_int (__eo_to_smt x)) at hNN
  rcases
      bv_unop_ret_arg_of_non_none (op := SmtTerm.sbv_to_int)
        (ret := SmtType.Int)
        (show
          __smtx_typeof (SmtTerm.sbv_to_int (__eo_to_smt x)) =
            __smtx_typeof_bv_op_1_ret
              (__smtx_typeof (__eo_to_smt x)) SmtType.Int by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hNN with
    ⟨w, hXTy⟩
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem bvsize_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp._at_bvsize) x)) :
  eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (let _v0 := __eo_to_smt_bv_size
            (__smtx_typeof (__eo_to_smt x))
           native_ite (native_zleq 0 _v0)
             (SmtTerm._at_purify (SmtTerm.Numeral _v0))
             SmtTerm.None) ≠
        SmtType.None at hTrans
  rcases
      TranslationProofs.smtx_bv_sizeof_term_non_none
        (__eo_to_smt x) hTrans with
    ⟨w, hXTy⟩
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem str_len_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_len) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.str_len (__eo_to_smt x)) at hNN
  rcases
      seq_arg_of_non_none_ret (op := SmtTerm.str_len)
        (R := SmtType.Int)
        (typeof_str_len_eq (__eo_to_smt x)) hNN with ⟨T, hXTy⟩
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem str_rev_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_rev) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.str_rev (__eo_to_smt x)) at hNN
  rcases
      seq_arg_of_non_none (op := SmtTerm.str_rev)
        (typeof_str_rev_eq (__eo_to_smt x)) hNN with ⟨T, hXTy⟩
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem seq_char_unary_arg_has_smt_translation
    {x : Term} {op : SmtTerm -> SmtTerm} {ret : SmtType}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x))
            (SmtType.Seq SmtType.Char))
          ret SmtType.None)
    (hNN : term_has_non_none_type (op (__eo_to_smt x))) :
  eoHasSmtTranslation x :=
by
  have hXTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := op) (ret := ret) hTy hNN
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem str_to_lower_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_to_lower) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.str_to_lower (__eo_to_smt x)) at hNN
  exact
    seq_char_unary_arg_has_smt_translation
      (typeof_str_to_lower_eq (__eo_to_smt x)) hNN

theorem str_to_upper_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_to_upper) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.str_to_upper (__eo_to_smt x)) at hNN
  exact
    seq_char_unary_arg_has_smt_translation
      (typeof_str_to_upper_eq (__eo_to_smt x)) hNN

theorem str_to_code_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_to_code) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.str_to_code (__eo_to_smt x)) at hNN
  exact
    seq_char_unary_arg_has_smt_translation
      (typeof_str_to_code_eq (__eo_to_smt x)) hNN

theorem str_is_digit_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_is_digit) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.str_is_digit (__eo_to_smt x)) at hNN
  exact
    seq_char_unary_arg_has_smt_translation
      (typeof_str_is_digit_eq (__eo_to_smt x)) hNN

theorem str_to_int_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_to_int) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.str_to_int (__eo_to_smt x)) at hNN
  exact
    seq_char_unary_arg_has_smt_translation
      (typeof_str_to_int_eq (__eo_to_smt x)) hNN

theorem str_to_re_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_to_re) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.str_to_re (__eo_to_smt x)) at hNN
  exact
    seq_char_unary_arg_has_smt_translation
      (typeof_str_to_re_eq (__eo_to_smt x)) hNN

theorem str_from_code_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_from_code) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.str_from_code (__eo_to_smt x)) at hNN
  have hXTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
    int_arg_of_non_none_ret (op := SmtTerm.str_from_code)
      (ret := SmtType.Seq SmtType.Char)
      (typeof_str_from_code_eq (__eo_to_smt x)) hNN
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem str_from_int_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_from_int) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.str_from_int (__eo_to_smt x)) at hNN
  have hXTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
    int_arg_of_non_none_ret (op := SmtTerm.str_from_int)
      (ret := SmtType.Seq SmtType.Char)
      (typeof_str_from_int_eq (__eo_to_smt x)) hNN
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem reglan_unary_arg_has_smt_translation
    {x : Term} {op : SmtTerm -> SmtTerm}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.RegLan)
          SmtType.RegLan SmtType.None)
    (hNN : term_has_non_none_type (op (__eo_to_smt x))) :
  eoHasSmtTranslation x :=
by
  have hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
    reglan_arg_of_non_none (op := op) hTy hNN
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem re_mult_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.re_mult) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.re_mult (__eo_to_smt x)) at hNN
  exact reglan_unary_arg_has_smt_translation
    (typeof_re_mult_eq (__eo_to_smt x)) hNN

theorem re_plus_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.re_plus) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.re_plus (__eo_to_smt x)) at hNN
  exact reglan_unary_arg_has_smt_translation
    (typeof_re_plus_eq (__eo_to_smt x)) hNN

theorem re_opt_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.re_opt) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.re_opt (__eo_to_smt x)) at hNN
  exact reglan_unary_arg_has_smt_translation
    (typeof_re_opt_eq (__eo_to_smt x)) hNN

theorem re_comp_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.re_comp) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.re_comp (__eo_to_smt x)) at hNN
  exact reglan_unary_arg_has_smt_translation
    (typeof_re_comp_eq (__eo_to_smt x)) hNN

theorem typeof_seq_unit_eq_closed
    (t : SmtTerm) :
  __smtx_typeof (SmtTerm.seq_unit t) =
    __smtx_typeof_guard_wf (SmtType.Seq (__smtx_typeof t))
      (SmtType.Seq (__smtx_typeof t)) :=
by
  rw [__smtx_typeof.eq_def] <;> simp only

theorem typeof_set_singleton_eq_closed
    (t : SmtTerm) :
  __smtx_typeof (SmtTerm.set_singleton t) =
    __smtx_typeof_guard_wf (SmtType.Set (__smtx_typeof t))
      (SmtType.Set (__smtx_typeof t)) :=
by
  rw [__smtx_typeof.eq_def] <;> simp only

theorem seq_unit_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.seq_unit) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.seq_unit (__eo_to_smt x)) at hNN
  unfold term_has_non_none_type at hNN
  unfold eoHasSmtTranslation
  by_cases hNone : __smtx_typeof (__eo_to_smt x) = SmtType.None
  · exfalso
    apply hNN
    simp [typeof_seq_unit_eq_closed, hNone, __smtx_typeof_guard_wf,
      __smtx_type_wf, __smtx_type_wf_rec, __smtx_type_wf_component,
      native_and, native_ite]
  · exact hNone

theorem set_singleton_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.set_singleton) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.set_singleton (__eo_to_smt x)) at hNN
  unfold term_has_non_none_type at hNN
  unfold eoHasSmtTranslation
  by_cases hNone : __smtx_typeof (__eo_to_smt x) = SmtType.None
  · exfalso
    apply hNN
    simp [typeof_set_singleton_eq_closed, hNone, __smtx_typeof_guard_wf,
      __smtx_type_wf, __smtx_type_wf_rec, __smtx_type_wf_component,
      native_and, native_ite]
  · exact hNone

theorem set_choose_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.set_choose) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change
      term_has_non_none_type
        (SmtTerm.map_diff (__eo_to_smt x)
          (SmtTerm.set_empty
            (__eo_to_smt_set_elem_type
              (__smtx_typeof (__eo_to_smt x))))) at hNN
  rcases map_diff_args_of_non_none hNN with hMap | hSet
  · rcases hMap with ⟨A, B, hXTy, _hEmptyTy, _hDiffTy⟩
    exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)
  · rcases hSet with ⟨A, hXTy, _hEmptyTy, _hDiffTy⟩
    exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem set_is_empty_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.set_is_empty) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change
      term_has_non_none_type
        (SmtTerm.eq (__eo_to_smt x)
          (SmtTerm.set_empty
            (__eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt x))))) at hNN
  unfold term_has_non_none_type at hNN
  rw [typeof_eq_eq] at hNN
  unfold eoHasSmtTranslation
  intro hXNone
  exact hNN (by
    simp [__smtx_typeof_eq, __smtx_typeof_guard, hXNone, native_ite,
      native_Teq])

theorem set_is_singleton_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp UserOp.set_is_singleton) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change
      term_has_non_none_type
        (SmtTerm.eq (__eo_to_smt x)
          (SmtTerm.set_singleton
            (SmtTerm.map_diff (__eo_to_smt x)
              (SmtTerm.set_empty
                (__eo_to_smt_set_elem_type
                  (__smtx_typeof (__eo_to_smt x))))))) at hNN
  unfold term_has_non_none_type at hNN
  rw [typeof_eq_eq] at hNN
  unfold eoHasSmtTranslation
  intro hXNone
  exact hNN (by
    simp [__smtx_typeof_eq, __smtx_typeof_guard, hXNone, native_ite,
      native_Teq])

theorem is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
    {op : UserOp} {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hXTrans : eoHasSmtTranslation x)
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp op) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env =
        Term.Boolean b :=
by
  exact is_closed_rec_apply_uop_eq_and_bool_of_arg hEnv (ihX hXTrans)

theorem is_closed_rec_apply_uop_eq_and_bool_of_has_smt_translation_and_arg
    {op : UserOp} {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans : eoHasSmtTranslation (Term.Apply (Term.UOp op) x))
    (hArg :
      eoHasSmtTranslation (Term.Apply (Term.UOp op) x) ->
        eoHasSmtTranslation x)
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp op) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv (hArg hTrans) ihX

theorem is_closed_rec_apply_not_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.not) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.not) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.not) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.not) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (not_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_to_real_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.to_real) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.to_real) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.to_real) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.to_real) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (to_real_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_to_int_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.to_int) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.to_int) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.to_int) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.to_int) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (to_int_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_is_int_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.is_int) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.is_int) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.is_int) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.is_int) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (is_int_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_abs_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.abs) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.abs) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.abs) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.abs) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (abs_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_eoo_neg_2_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (uneg_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_int_pow2_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.int_pow2) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.int_pow2) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.int_pow2) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.int_pow2) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (int_pow2_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_int_log2_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.int_log2) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.int_log2) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.int_log2) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.int_log2) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (int_log2_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_bvnot_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.bvnot) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.bvnot) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.bvnot) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.bvnot) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (bvnot_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_bvneg_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.bvneg) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.bvneg) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.bvneg) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.bvneg) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (bvneg_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_bvnego_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.bvnego) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.bvnego) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.bvnego) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.bvnego) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (bvnego_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_str_len_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_len) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.str_len) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.str_len) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.str_len) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (str_len_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_str_rev_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_rev) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.str_rev) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.str_rev) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.str_rev) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (str_rev_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_str_to_lower_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp UserOp.str_to_lower) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.str_to_lower) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp UserOp.str_to_lower) x) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.UOp UserOp.str_to_lower) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (str_to_lower_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_str_to_upper_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp UserOp.str_to_upper) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.str_to_upper) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp UserOp.str_to_upper) x) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.UOp UserOp.str_to_upper) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (str_to_upper_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_str_to_code_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp UserOp.str_to_code) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.str_to_code) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp UserOp.str_to_code) x) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.UOp UserOp.str_to_code) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (str_to_code_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_str_from_code_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp UserOp.str_from_code) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.str_from_code) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp UserOp.str_from_code) x) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.UOp UserOp.str_from_code) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (str_from_code_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_str_is_digit_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp UserOp.str_is_digit) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.str_is_digit) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp UserOp.str_is_digit) x) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.UOp UserOp.str_is_digit) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (str_is_digit_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_str_to_int_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp UserOp.str_to_int) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.str_to_int) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp UserOp.str_to_int) x) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.UOp UserOp.str_to_int) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (str_to_int_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_str_from_int_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp UserOp.str_from_int) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.str_from_int) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp UserOp.str_from_int) x) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.UOp UserOp.str_from_int) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (str_from_int_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_str_to_re_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_to_re) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.str_to_re) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.str_to_re) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.str_to_re) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (str_to_re_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_re_mult_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.re_mult) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.re_mult) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.re_mult) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.re_mult) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (re_mult_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_re_plus_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.re_plus) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.re_plus) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.re_plus) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.re_plus) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (re_plus_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_re_opt_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.re_opt) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.re_opt) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.re_opt) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.re_opt) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (re_opt_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_re_comp_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.re_comp) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.re_comp) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.re_comp) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.re_comp) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (re_comp_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_seq_unit_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.seq_unit) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.seq_unit) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.seq_unit) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.seq_unit) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (seq_unit_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_set_singleton_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp UserOp.set_singleton) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.set_singleton) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp UserOp.set_singleton) x) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.UOp UserOp.set_singleton) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (set_singleton_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_set_choose_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp UserOp.set_choose) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.set_choose) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp UserOp.set_choose) x) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.UOp UserOp.set_choose) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (set_choose_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_set_is_empty_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp UserOp.set_is_empty) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.set_is_empty) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp UserOp.set_is_empty) x) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.UOp UserOp.set_is_empty) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (set_is_empty_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_set_is_singleton_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp UserOp.set_is_singleton) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.UOp UserOp.set_is_singleton) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp UserOp.set_is_singleton) x) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.UOp UserOp.set_is_singleton) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (set_is_singleton_arg_has_smt_translation_of_has_smt_translation
        hTrans)
      ihX

theorem native_zleq_zero_of_one_zleq {i : native_Int}
    (hi : native_zleq 1 i = true) :
  native_zleq 0 i = true :=
by
  have hiProp : (1 : Int) ≤ i := by
    simpa [native_zleq] using hi
  have h0Prop : (0 : Int) ≤ i := by
    calc
      (0 : Int) ≤ 1 := by decide
      _ ≤ i := hiProp
  simpa [native_zleq] using h0Prop

theorem native_zleq_zero_of_zleq_chain {i j : native_Int}
    (hj : native_zleq 0 j = true)
    (hji : native_zleq j i = true) :
  native_zleq 0 i = true :=
by
  have hjProp : (0 : Int) ≤ j := by
    simpa [native_zleq] using hj
  have hjiProp : j ≤ i := by
    simpa [native_zleq] using hji
  have hiProp : (0 : Int) ≤ i := by
    calc
      (0 : Int) ≤ j := hjProp
      _ ≤ i := hjiProp
  simpa [native_zleq] using hiProp

theorem eo_to_smt_nat_is_valid_of_smt_numeral_nonneg
    {idx : Term} {i : native_Int}
    (hIdx : __eo_to_smt idx = SmtTerm.Numeral i)
    (hi : native_zleq 0 i = true) :
  __eo_to_smt_nat_is_valid idx = true :=
by
  have hIdxTerm : idx = Term.Numeral i :=
    TranslationProofs.eo_to_smt_eq_numeral idx i hIdx
  subst idx
  simp [__eo_to_smt_nat_is_valid, hi]

theorem smtx_typeof_binary_one_eq :
    __smtx_typeof (SmtTerm.Binary 1 1) = SmtType.BitVec 1 :=
by
  have hNN : __smtx_typeof (SmtTerm.Binary 1 1) ≠ SmtType.None := by
    unfold __smtx_typeof
    simp [native_ite, SmtEval.native_and, native_zleq, native_zeq,
      native_mod_total, native_int_pow2]
    rfl
  have hNat : native_int_to_nat 1 = 1 := by native_decide
  simpa [hNat] using TranslationProofs.smtx_typeof_binary_of_non_none 1 1 hNN

theorem smtx_typeof_eq_non_none_closed
    {T U : SmtType}
    (h : __smtx_typeof_eq T U ≠ SmtType.None) :
    T = U ∧ T ≠ SmtType.None :=
by
  by_cases hNone : T = SmtType.None
  · subst hNone
    exfalso
    exact h (by
      simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
        native_Teq])
  · by_cases hEq : T = U
    · exact ⟨hEq, hNone⟩
    · exfalso
      exact h (by
        simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
          native_Teq, hNone, hEq])

theorem purify_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp._at_purify) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm._at_purify (__eo_to_smt x)) at hNN
  unfold eoHasSmtTranslation
  unfold term_has_non_none_type at hNN
  simpa [__smtx_typeof] using hNN

theorem bvite_args_have_smt_translation_of_has_smt_translation
    {x y z : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) x) y) z)) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.ite
            (SmtTerm.eq (__eo_to_smt x) (SmtTerm.Binary 1 1))
            (__eo_to_smt y) (__eo_to_smt z)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.ite
          (SmtTerm.eq (__eo_to_smt x) (SmtTerm.Binary 1 1))
          (__eo_to_smt y) (__eo_to_smt z)) := by
    unfold term_has_non_none_type
    exact hTrans
  rcases ite_args_of_non_none hNN with ⟨T, hCond, hY, hZ, hT⟩
  have hCondNN :
      __smtx_typeof
          (SmtTerm.eq (__eo_to_smt x) (SmtTerm.Binary 1 1)) ≠
        SmtType.None := by
    rw [hCond]
    simp
  have hEqNN :
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt x))
          (SmtType.BitVec 1) ≠
        SmtType.None := by
    rw [typeof_eq_eq, smtx_typeof_binary_one_eq] at hCondNN
    exact hCondNN
  have hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec 1 :=
    (smtx_typeof_eq_non_none_closed hEqNN).1
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hY hT,
    eo_has_smt_translation_of_smt_type_eq hZ hT⟩

theorem bvite_args_have_smt_translation_of_non_none
    {x y z : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.ite
          (SmtTerm.eq (__eo_to_smt x) (SmtTerm.Binary 1 1))
          (__eo_to_smt y) (__eo_to_smt z))) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  exact
    bvite_args_have_smt_translation_of_has_smt_translation
      (by
        unfold eoHasSmtTranslation
        change
          __smtx_typeof
              (SmtTerm.ite
                (SmtTerm.eq (__eo_to_smt x) (SmtTerm.Binary 1 1))
                (__eo_to_smt y) (__eo_to_smt z)) ≠
            SmtType.None
        exact hNN)

theorem bv_cmp_to_bv_args_have_smt_translation_of_non_none
    {smtCmp : SmtTerm -> SmtTerm -> SmtTerm} {x y : Term}
    (hTy :
      __smtx_typeof (smtCmp (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_bv_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) SmtType.Bool)
    (hNN :
      term_has_non_none_type
        (SmtTerm.ite (smtCmp (__eo_to_smt x) (__eo_to_smt y))
          (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases ite_args_of_non_none hNN with ⟨T, hCond, hThen, hElse, hT⟩
  have hCondNN :
      term_has_non_none_type (smtCmp (__eo_to_smt x) (__eo_to_smt y)) :=
    term_has_non_none_type_of_type_eq_closed hCond (by simp)
  rcases
      bv_binop_ret_args_of_non_none (op := smtCmp)
        (ret := SmtType.Bool) hTy hCondNN with
    ⟨w, hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem bvultbv_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvultbv) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.ite (SmtTerm.bvult (__eo_to_smt x) (__eo_to_smt y))
            (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.ite (SmtTerm.bvult (__eo_to_smt x) (__eo_to_smt y))
          (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) := by
    unfold term_has_non_none_type
    exact hTrans
  exact
    bv_cmp_to_bv_args_have_smt_translation_of_non_none
      (smtCmp := SmtTerm.bvult)
      (show
        __smtx_typeof (SmtTerm.bvult (__eo_to_smt x) (__eo_to_smt y)) =
          __smtx_typeof_bv_op_2_ret
            (__smtx_typeof (__eo_to_smt x))
            (__smtx_typeof (__eo_to_smt y)) SmtType.Bool by
        rw [__smtx_typeof.eq_def] <;> simp only)
      hNN

theorem bvsltbv_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvsltbv) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.ite (SmtTerm.bvslt (__eo_to_smt x) (__eo_to_smt y))
            (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.ite (SmtTerm.bvslt (__eo_to_smt x) (__eo_to_smt y))
          (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) := by
    unfold term_has_non_none_type
    exact hTrans
  exact
    bv_cmp_to_bv_args_have_smt_translation_of_non_none
      (smtCmp := SmtTerm.bvslt)
      (show
        __smtx_typeof (SmtTerm.bvslt (__eo_to_smt x) (__eo_to_smt y)) =
          __smtx_typeof_bv_op_2_ret
            (__smtx_typeof (__eo_to_smt x))
            (__smtx_typeof (__eo_to_smt y)) SmtType.Bool by
        rw [__smtx_typeof.eq_def] <;> simp only)
      hNN

theorem bvredand_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.bvredand) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change
      term_has_non_none_type
        (SmtTerm.bvcomp (__eo_to_smt x)
          (SmtTerm.bvnot
            (SmtTerm.Binary
              (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))) 0))) at hNN
  rcases
      bv_binop_ret_args_of_non_none (op := SmtTerm.bvcomp)
        (ret := SmtType.BitVec 1)
        (show
          __smtx_typeof
              (SmtTerm.bvcomp (__eo_to_smt x)
                (SmtTerm.bvnot
                  (SmtTerm.Binary
                    (__eo_to_smt_bv_size
                      (__smtx_typeof (__eo_to_smt x))) 0))) =
            __smtx_typeof_bv_op_2_ret
              (__smtx_typeof (__eo_to_smt x))
              (__smtx_typeof
                (SmtTerm.bvnot
                  (SmtTerm.Binary
                    (__eo_to_smt_bv_size
                      (__smtx_typeof (__eo_to_smt x))) 0)))
              (SmtType.BitVec 1) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hNN with
    ⟨w, hXTy, hOtherTy⟩
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem bvredor_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.bvredor) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change
      term_has_non_none_type
        (SmtTerm.bvnot
          (SmtTerm.bvcomp (__eo_to_smt x)
            (SmtTerm.Binary
              (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))) 0))) at hNN
  rcases
      bv_unop_arg_of_non_none (op := SmtTerm.bvnot)
        (show
          __smtx_typeof
              (SmtTerm.bvnot
                (SmtTerm.bvcomp (__eo_to_smt x)
                  (SmtTerm.Binary
                    (__eo_to_smt_bv_size
                      (__smtx_typeof (__eo_to_smt x))) 0))) =
            __smtx_typeof_bv_op_1
              (__smtx_typeof
                (SmtTerm.bvcomp (__eo_to_smt x)
                  (SmtTerm.Binary
                    (__eo_to_smt_bv_size
                      (__smtx_typeof (__eo_to_smt x))) 0))) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hNN with
    ⟨wNot, hCompTy⟩
  have hCompNN :
      term_has_non_none_type
        (SmtTerm.bvcomp (__eo_to_smt x)
          (SmtTerm.Binary
            (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))) 0)) :=
    term_has_non_none_type_of_type_eq_closed hCompTy (by simp)
  rcases
      bv_binop_ret_args_of_non_none (op := SmtTerm.bvcomp)
        (ret := SmtType.BitVec 1)
        (show
          __smtx_typeof
              (SmtTerm.bvcomp (__eo_to_smt x)
                (SmtTerm.Binary
                  (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))) 0)) =
            __smtx_typeof_bv_op_2_ret
              (__smtx_typeof (__eo_to_smt x))
              (__smtx_typeof
                (SmtTerm.Binary
                  (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))) 0))
              (SmtType.BitVec 1) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hCompNN with
    ⟨w, hXTy, hOtherTy⟩
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem from_bools_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  let bit :=
    SmtTerm.ite (__eo_to_smt x) (SmtTerm.Binary 1 1)
      (SmtTerm.Binary 1 0)
  have hTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x) y) =
        SmtTerm.concat (__eo_to_smt y) bit := by
    rfl
  have hNN :
      term_has_non_none_type (SmtTerm.concat (__eo_to_smt y) bit) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans
  rcases bv_concat_args_of_non_none hNN with ⟨w1, w2, hYTy, hBitTy⟩
  have hBitNN : term_has_non_none_type bit :=
    term_has_non_none_type_of_type_eq_closed hBitTy (by simp)
  rcases ite_args_of_non_none hBitNN with ⟨T, hXTy, hThen, hElse, hT⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
    {op : UserOp1} {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hIdx : __eo_is_closed_rec idx env = Term.Boolean true)
    (hX :
      __is_closed_rec x env = __eo_is_closed_rec x env ∧
        ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp1 op idx) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp1 op idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp1 op idx) x) env =
        Term.Boolean b :=
by
  rcases hX with ⟨hXEq, ⟨b, hXBool⟩⟩
  refine ⟨?_, ?_⟩
  · have hEq := eo_and_true_left_eq_of_boolean hXBool
    cases hEnv <;>
      simp [__is_closed_rec, __eo_is_closed_rec, hIdx, hXEq, hEq]
  · exact ⟨b, by
      have hEq := (eo_and_true_left_eq_of_boolean hXBool).trans hXBool
      cases hEnv <;>
        simp [__eo_is_closed_rec, hIdx, hEq]⟩

theorem repeat_index_nat_valid_and_arg_has_smt_translation
    {idx x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp1 UserOp1.repeat idx) x)) :
  __eo_to_smt_nat_is_valid idx = true ∧ eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.repeat (__eo_to_smt idx) (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.repeat (__eo_to_smt idx) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hTrans
  rcases repeat_args_of_non_none hNN with ⟨i, w, hIdxNum, hXTy, hi⟩
  constructor
  · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hIdxNum
      (native_zleq_zero_of_one_zleq hi)
  · unfold eoHasSmtTranslation
    rw [hXTy]
    intro h
    cases h

theorem zero_extend_index_nat_valid_and_arg_has_smt_translation
    {idx x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.zero_extend idx) x)) :
  __eo_to_smt_nat_is_valid idx = true ∧ eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.zero_extend (__eo_to_smt idx) (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.zero_extend (__eo_to_smt idx) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hTrans
  rcases zero_extend_args_of_non_none hNN with ⟨i, w, hIdxNum, hXTy, hi⟩
  constructor
  · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hIdxNum hi
  · unfold eoHasSmtTranslation
    rw [hXTy]
    intro h
    cases h

theorem sign_extend_index_nat_valid_and_arg_has_smt_translation
    {idx x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.sign_extend idx) x)) :
  __eo_to_smt_nat_is_valid idx = true ∧ eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.sign_extend (__eo_to_smt idx) (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.sign_extend (__eo_to_smt idx) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hTrans
  rcases sign_extend_args_of_non_none hNN with ⟨i, w, hIdxNum, hXTy, hi⟩
  constructor
  · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hIdxNum hi
  · unfold eoHasSmtTranslation
    rw [hXTy]
    intro h
    cases h

theorem rotate_left_index_nat_valid_and_arg_has_smt_translation
    {idx x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.rotate_left idx) x)) :
  __eo_to_smt_nat_is_valid idx = true ∧ eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.rotate_left (__eo_to_smt idx) (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.rotate_left (__eo_to_smt idx) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hTrans
  rcases rotate_left_args_of_non_none hNN with ⟨i, w, hIdxNum, hXTy, hi⟩
  constructor
  · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hIdxNum hi
  · unfold eoHasSmtTranslation
    rw [hXTy]
    intro h
    cases h

theorem rotate_right_index_nat_valid_and_arg_has_smt_translation
    {idx x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.rotate_right idx) x)) :
  __eo_to_smt_nat_is_valid idx = true ∧ eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.rotate_right (__eo_to_smt idx) (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.rotate_right (__eo_to_smt idx) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hTrans
  rcases rotate_right_args_of_non_none hNN with ⟨i, w, hIdxNum, hXTy, hi⟩
  constructor
  · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hIdxNum hi
  · unfold eoHasSmtTranslation
    rw [hXTy]
    intro h
    cases h

theorem int_to_bv_index_nat_valid_and_arg_has_smt_translation
    {idx x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv idx) x)) :
  __eo_to_smt_nat_is_valid idx = true ∧ eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.int_to_bv (__eo_to_smt idx) (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.int_to_bv (__eo_to_smt idx) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hTrans
  rcases int_to_bv_args_of_non_none hNN with ⟨i, hIdxNum, hXTy, hi⟩
  constructor
  · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hIdxNum hi
  · unfold eoHasSmtTranslation
    rw [hXTy]
    intro h
    cases h

theorem re_exp_index_nat_valid_and_arg_has_smt_translation
    {idx x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp1 UserOp1.re_exp idx) x)) :
  __eo_to_smt_nat_is_valid idx = true ∧ eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.re_exp (__eo_to_smt idx) (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.re_exp (__eo_to_smt idx) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hTrans
  cases hIdx : __eo_to_smt idx with
  | Numeral i =>
      have hNN' :
          term_has_non_none_type
            (SmtTerm.re_exp (SmtTerm.Numeral i) (__eo_to_smt x)) := by
        simpa [hIdx] using hNN
      rcases re_exp_arg_of_non_none hNN' with ⟨hi, hXTy⟩
      constructor
      · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hIdx hi
      · unfold eoHasSmtTranslation
        rw [hXTy]
        intro h
        cases h
  | _ =>
      exfalso
      unfold term_has_non_none_type at hNN
      exact hNN (by
        simp [hIdx, __smtx_typeof, __smtx_typeof_re_exp])

theorem at_bit_index_nat_valid_and_arg_has_smt_translation
    {idx x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp1 UserOp1._at_bit idx) x)) :
  __eo_to_smt_nat_is_valid idx = true ∧ eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.eq
            (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
              (__eo_to_smt x))
            (SmtTerm.Binary 1 1)) ≠
        SmtType.None at hTrans
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.eq
          (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
            (__eo_to_smt x))
          (SmtTerm.Binary 1 1)) := by
    unfold term_has_non_none_type
    exact hTrans
  have hEqNN :
      __smtx_typeof_eq
          (__smtx_typeof
            (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
              (__eo_to_smt x)))
          (SmtType.BitVec 1) ≠
        SmtType.None := by
    unfold term_has_non_none_type at hApplyNN
    rw [typeof_eq_eq, smtx_typeof_binary_one_eq] at hApplyNN
    exact hApplyNN
  have hExtTy :
      __smtx_typeof
          (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
            (__eo_to_smt x)) =
        SmtType.BitVec 1 :=
  by
    by_cases hNone :
        __smtx_typeof
            (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
              (__eo_to_smt x)) =
          SmtType.None
    · exfalso
      exact hEqNN (by
        rw [hNone]
        simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
          native_Teq])
    · by_cases hEq :
        __smtx_typeof
            (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
              (__eo_to_smt x)) =
          SmtType.BitVec 1
      · exact hEq
      · exfalso
        exact hEqNN (by
          simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
            native_Teq, hNone, hEq])
  have hExtNN :
      term_has_non_none_type
        (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
          (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hExtTy]
    simp
  rcases extract_args_of_non_none hExtNN with
    ⟨_i, j, w, _hIdxHigh, hIdxLow, hXTy, hj0, _hji, _hiw⟩
  constructor
  · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hIdxLow hj0
  · unfold eoHasSmtTranslation
    rw [hXTy]
    intro h
    cases h

theorem tuple_select_index_nat_valid_and_arg_has_smt_translation
    {idx x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x)) :
  __eo_to_smt_nat_is_valid idx = true ∧ eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (__eo_to_smt_tuple_select
            (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt idx)
            (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  cases hTy : __smtx_typeof (__eo_to_smt x) with
  | Datatype s dd =>
      cases dd with
      | nil =>
          exfalso
          exact hTrans (by
            rw [hTy]
            cases __eo_to_smt idx <;>
              simp [__eo_to_smt_tuple_select])
      | cons s2 d rest =>
          cases rest with
          | cons s3 d3 rest3 =>
              exfalso
              exact hTrans (by
                rw [hTy]
                cases __eo_to_smt idx <;>
                  simp [__eo_to_smt_tuple_select])
          | nil =>
              by_cases hTuple : s = native_string_lit "@Tuple"
              · subst s
                by_cases hTupleDecl :
                    s2 = native_string_lit "@Tuple"
                · subst s2
                  cases hIdx : __eo_to_smt idx with
                  | Numeral n =>
                      cases hNonneg : native_zleq 0 n
                      · exfalso
                        exact hTrans (by
                          rw [hTy, hIdx]
                          simp [__eo_to_smt_tuple_select, hNonneg,
                            native_streq, native_and, native_ite])
                      · constructor
                        · exact
                            eo_to_smt_nat_is_valid_of_smt_numeral_nonneg
                              hIdx hNonneg
                        · unfold eoHasSmtTranslation
                          rw [hTy]
                          intro h
                          cases h
                  | _ =>
                      exfalso
                      exact hTrans (by
                        rw [hTy, hIdx]
                        simp [__eo_to_smt_tuple_select])
                · exfalso
                  exact hTrans (by
                    rw [hTy]
                    cases __eo_to_smt idx <;>
                      simp [__eo_to_smt_tuple_select, hTupleDecl,
                        native_streq, native_and, native_ite])
              · exfalso
                exact hTrans (by
                  rw [hTy]
                  cases __eo_to_smt idx <;>
                    simp [__eo_to_smt_tuple_select, hTuple,
                      native_streq, native_and, native_ite])
  | _ =>
      exfalso
      exact hTrans (by
        rw [hTy]
        simp [__eo_to_smt_tuple_select])

theorem tuple_update_index_nat_valid_and_args_have_smt_translation
    {idx x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y)) :
  __eo_to_smt_nat_is_valid idx = true ∧
    eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (__eo_to_smt_tuple_update
            (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt idx)
            (__eo_to_smt x) (__eo_to_smt y)) ≠
        SmtType.None at hTrans
  cases hTy : __smtx_typeof (__eo_to_smt x) with
  | Datatype s dd =>
      cases dd with
      | nil =>
          exfalso
          exact hTrans (by
            rw [hTy]
            cases __eo_to_smt idx <;>
              simp [__eo_to_smt_tuple_update])
      | cons s2 d rest =>
          cases rest with
          | cons s3 d3 rest3 =>
              exfalso
              exact hTrans (by
                rw [hTy]
                cases __eo_to_smt idx <;>
                  simp [__eo_to_smt_tuple_update])
          | nil =>
              by_cases hTuple : s = native_string_lit "@Tuple"
              · subst s
                by_cases hTupleDecl :
                    s2 = native_string_lit "@Tuple"
                · subst s2
                  let tupleDecl := __eo_to_smt_tuple_decl d
                  cases hIdx : __eo_to_smt idx with
                  | Numeral n =>
                      cases hNonneg : native_zleq 0 n
                      · exfalso
                        exact hTrans (by
                          rw [hTy, hIdx]
                          simp [__eo_to_smt_tuple_update, hNonneg,
                            native_streq, native_and, native_ite])
                      · have hUpdaterNN :
                            __smtx_typeof
                                (__eo_to_smt_updater
                                  (SmtTerm.DtSel
                                    (native_string_lit "@Tuple")
                                    tupleDecl native_nat_zero
                                    (native_int_to_nat n))
                                  (__eo_to_smt x) (__eo_to_smt y)) ≠
                              SmtType.None := by
                          simpa [tupleDecl, __eo_to_smt_tuple_update,
                            hTy, hIdx, hNonneg, native_streq, native_and,
                            native_ite] using hTrans
                        have hIdxLt :
                            native_zlt
                                (native_nat_to_int (native_int_to_nat n))
                                (native_nat_to_int
                                  (__smtx_dt_num_sels
                                    (__smtx_dd_lookup
                                      (native_string_lit "@Tuple")
                                      tupleDecl)
                                    native_nat_zero)) =
                              true :=
                          TranslationProofs.eo_to_smt_updater_dt_sel_guard_of_non_none
                            (native_string_lit "@Tuple") tupleDecl
                            native_nat_zero (native_int_to_nat n)
                            (__eo_to_smt x) (__eo_to_smt y) hUpdaterNN
                        have hIteNN :
                            term_has_non_none_type
                              (SmtTerm.ite
                                (SmtTerm.Apply
                                  (SmtTerm.DtTester
                                    (native_string_lit "@Tuple")
                                    tupleDecl native_nat_zero)
                                  (__eo_to_smt x))
                                (__eo_to_smt_updater_rec
                                  (SmtTerm.DtSel
                                    (native_string_lit "@Tuple")
                                    tupleDecl native_nat_zero
                                    (native_int_to_nat n))
                                  (__smtx_dt_num_sels
                                    (__smtx_dd_lookup
                                      (native_string_lit "@Tuple")
                                      tupleDecl)
                                    native_nat_zero)
                                  (__eo_to_smt x) (__eo_to_smt y)
                                  (SmtTerm.DtCons
                                    (native_string_lit "@Tuple")
                                    tupleDecl native_nat_zero))
                                (__eo_to_smt x)) := by
                          unfold term_has_non_none_type
                          simpa [__eo_to_smt_updater, native_ite,
                            hIdxLt] using hUpdaterNN
                        rcases ite_args_of_non_none hIteNN with
                          ⟨T, _hCond, hThen, _hElse, hT⟩
                        have hRecNN :
                            __smtx_typeof
                                (__eo_to_smt_updater_rec
                                  (SmtTerm.DtSel
                                    (native_string_lit "@Tuple")
                                    tupleDecl native_nat_zero
                                    (native_int_to_nat n))
                                  (__smtx_dt_num_sels
                                    (__smtx_dd_lookup
                                      (native_string_lit "@Tuple")
                                      tupleDecl)
                                    native_nat_zero)
                                  (__eo_to_smt x) (__eo_to_smt y)
                                  (SmtTerm.DtCons
                                    (native_string_lit "@Tuple")
                                    tupleDecl native_nat_zero)) ≠
                              SmtType.None := by
                          rw [hThen]
                          exact hT
                        refine ⟨?_, ?_, ?_⟩
                        · exact
                            eo_to_smt_nat_is_valid_of_smt_numeral_nonneg
                              hIdx hNonneg
                        · unfold eoHasSmtTranslation
                          rw [hTy]
                          intro h
                          cases h
                        · exact
                            TranslationProofs.eo_to_smt_updater_rec_update_arg_non_none_of_non_none
                              (native_string_lit "@Tuple") tupleDecl
                              native_nat_zero (native_int_to_nat n)
                              (__smtx_dt_num_sels
                                (__smtx_dd_lookup
                                  (native_string_lit "@Tuple") tupleDecl)
                                native_nat_zero)
                              (__eo_to_smt x) (__eo_to_smt y)
                              (SmtTerm.DtCons
                                (native_string_lit "@Tuple") tupleDecl
                                native_nat_zero)
                              (by intro s d i j h; cases h)
                              (by intro s d i h; cases h)
                              hIdxLt hRecNN
                  | _ =>
                      exfalso
                      exact hTrans (by
                        rw [hTy, hIdx]
                        simp [__eo_to_smt_tuple_update])
                · exfalso
                  exact hTrans (by
                    rw [hTy]
                    cases __eo_to_smt idx <;>
                      simp [__eo_to_smt_tuple_update, hTupleDecl,
                        native_streq, native_and, native_ite])
              · exfalso
                exact hTrans (by
                  rw [hTy]
                  cases __eo_to_smt idx <;>
                    simp [__eo_to_smt_tuple_update, hTuple,
                      native_streq, native_and, native_ite])
  | _ =>
      exfalso
      exact hTrans (by
        rw [hTy]
        simp [__eo_to_smt_tuple_update])

theorem update_index_sel_and_args_have_smt_translation
    {idx x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) x) y)) :
  (∃ s d i j, __eo_to_smt idx = SmtTerm.DtSel s d i j) ∧
    eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (__eo_to_smt_updater (__eo_to_smt idx) (__eo_to_smt x)
            (__eo_to_smt y)) ≠
        SmtType.None at hTrans
  cases hIdx : __eo_to_smt idx with
  | DtSel s d i j =>
      have hIdxLt :
          native_zlt (native_nat_to_int j)
              (native_nat_to_int
                (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)) =
            true :=
        TranslationProofs.eo_to_smt_updater_dt_sel_guard_of_non_none
          s d i j (__eo_to_smt x) (__eo_to_smt y) (by
            simpa [hIdx] using hTrans)
      have hIteNN :
          term_has_non_none_type
            (SmtTerm.ite
              (SmtTerm.Apply (SmtTerm.DtTester s d i) (__eo_to_smt x))
              (__eo_to_smt_updater_rec
                (SmtTerm.DtSel s d i j)
                (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)
                (__eo_to_smt x) (__eo_to_smt y) (SmtTerm.DtCons s d i))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        simpa [__eo_to_smt_updater, hIdx, native_ite, hIdxLt] using
          hTrans
      rcases ite_args_of_non_none hIteNN with
        ⟨T, _hCond, hThen, hElse, hT⟩
      have hRecNN :
          __smtx_typeof
              (__eo_to_smt_updater_rec
                (SmtTerm.DtSel s d i j)
                (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)
                (__eo_to_smt x) (__eo_to_smt y) (SmtTerm.DtCons s d i)) ≠
            SmtType.None := by
        rw [hThen]
        exact hT
      refine ⟨⟨s, d, i, j, rfl⟩, ?_, ?_⟩
      · unfold eoHasSmtTranslation
        rw [hElse]
        exact hT
      · exact
          TranslationProofs.eo_to_smt_updater_rec_update_arg_non_none_of_non_none
            s d i j (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)
            (__eo_to_smt x)
            (__eo_to_smt y) (SmtTerm.DtCons s d i)
            (by intro s d i j h; cases h)
            (by intro s d i h; cases h)
            hIdxLt hRecNN
  | _ =>
      exfalso
      exact hTrans (by
        rw [hIdx]
        simp [__eo_to_smt_updater])

theorem is_index_cons_and_arg_has_smt_translation
    {idx x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp1 UserOp1.is idx) x)) :
  (∃ s d i, __eo_to_smt idx = SmtTerm.DtCons s d i) ∧
    eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt idx))
            (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  cases hIdx : __eo_to_smt idx with
  | DtCons s d i =>
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.DtTester s d i) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        simpa [hIdx, __eo_to_smt_tester] using hTrans
      have hXTy :
          __smtx_typeof (__eo_to_smt x) = SmtType.Datatype s d :=
        dt_tester_arg_datatype_of_non_none hApplyNN
      refine ⟨⟨s, d, i, rfl⟩, ?_⟩
      exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)
  | _ =>
      exfalso
      exact hTrans (by
        rw [hIdx]
        simp [__eo_to_smt_tester, TranslationProofs.typeof_apply_none_eq])

theorem is_closed_rec_apply_repeat_eq_and_bool_of_has_smt_translation
    {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp1 UserOp1.repeat idx) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp1 UserOp1.repeat idx) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp1 UserOp1.repeat idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp1 UserOp1.repeat idx) x) env =
        Term.Boolean b :=
by
  rcases repeat_index_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hIdxValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hIdxValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_zero_extend_eq_and_bool_of_has_smt_translation
    {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.zero_extend idx) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp1 UserOp1.zero_extend idx) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp1 UserOp1.zero_extend idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp1 UserOp1.zero_extend idx) x) env =
        Term.Boolean b :=
by
  rcases zero_extend_index_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hIdxValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hIdxValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_sign_extend_eq_and_bool_of_has_smt_translation
    {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.sign_extend idx) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp1 UserOp1.sign_extend idx) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp1 UserOp1.sign_extend idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp1 UserOp1.sign_extend idx) x) env =
        Term.Boolean b :=
by
  rcases sign_extend_index_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hIdxValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hIdxValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_rotate_left_eq_and_bool_of_has_smt_translation
    {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.rotate_left idx) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp1 UserOp1.rotate_left idx) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp1 UserOp1.rotate_left idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp1 UserOp1.rotate_left idx) x) env =
        Term.Boolean b :=
by
  rcases rotate_left_index_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hIdxValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hIdxValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_rotate_right_eq_and_bool_of_has_smt_translation
    {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.rotate_right idx) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp1 UserOp1.rotate_right idx) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp1 UserOp1.rotate_right idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp1 UserOp1.rotate_right idx) x) env =
        Term.Boolean b :=
by
  rcases rotate_right_index_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hIdxValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hIdxValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_int_to_bv_eq_and_bool_of_has_smt_translation
    {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv idx) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp1 UserOp1.int_to_bv idx) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp1 UserOp1.int_to_bv idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv idx) x) env =
        Term.Boolean b :=
by
  rcases int_to_bv_index_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hIdxValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hIdxValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_re_exp_eq_and_bool_of_has_smt_translation
    {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp1 UserOp1.re_exp idx) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp1 UserOp1.re_exp idx) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp1 UserOp1.re_exp idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp1 UserOp1.re_exp idx) x) env =
        Term.Boolean b :=
by
  rcases re_exp_index_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hIdxValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hIdxValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_at_bit_eq_and_bool_of_has_smt_translation
    {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp1 UserOp1._at_bit idx) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp1 UserOp1._at_bit idx) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp1 UserOp1._at_bit idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp1 UserOp1._at_bit idx) x) env =
        Term.Boolean b :=
by
  rcases at_bit_index_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hIdxValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hIdxValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_tuple_select_eq_and_bool_of_has_smt_translation
    {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x) env =
        Term.Boolean b :=
by
  rcases tuple_select_index_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hIdxValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hIdxValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_uop2_eq_and_bool_of_indices_true_and_arg
    {op : UserOp2} {i j x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hHead : __is_closed_rec (Term.UOp2 op i j) env = Term.Boolean true)
    (hI : __eo_is_closed_rec i env = Term.Boolean true)
    (hJ : __eo_is_closed_rec j env = Term.Boolean true)
    (hX :
      __is_closed_rec x env = __eo_is_closed_rec x env ∧
        ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp2 op i j) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp2 op i j) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp2 op i j) x) env =
        Term.Boolean b :=
by
  rcases hX with ⟨hXEq, ⟨b, hXBool⟩⟩
  refine ⟨?_, ?_⟩
  · have hEq := eo_and_true_left_eq_of_boolean hXBool
    cases hEnv <;>
      simp [__is_closed_rec, __eo_is_closed_rec, hHead, hI, hJ, hXEq,
        eo_and_true_true, hEq]
  · exact ⟨b, by
      have hEq := (eo_and_true_left_eq_of_boolean hXBool).trans hXBool
      cases hEnv <;>
        simp [__eo_is_closed_rec, hI, hJ, eo_and_true_true, hEq]⟩

theorem extract_indices_nat_valid_and_arg_has_smt_translation
    {hi lo x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp2 UserOp2.extract hi lo) x)) :
  (∃ i : native_Int, __eo_to_smt hi = SmtTerm.Numeral i) ∧
    __eo_to_smt_nat_is_valid lo = true ∧
      eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.extract (__eo_to_smt hi) (__eo_to_smt lo)
            (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.extract (__eo_to_smt hi) (__eo_to_smt lo)
          (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hTrans
  rcases extract_args_of_non_none hNN with
    ⟨i, j, w, hHiNum, hLoNum, hXTy, hj0, _hWidth, _hiw⟩
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨i, hHiNum⟩
  · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hLoNum hj0
  · unfold eoHasSmtTranslation
    rw [hXTy]
    intro h
    cases h

theorem re_loop_indices_nat_valid_and_arg_has_smt_translation
    {lo hi x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x)) :
  __eo_to_smt_nat_is_valid lo = true ∧
    __eo_to_smt_nat_is_valid hi = true ∧
      eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.re_loop (__eo_to_smt lo) (__eo_to_smt hi)
            (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.re_loop (__eo_to_smt lo) (__eo_to_smt hi)
          (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hTrans
  cases hLo : __eo_to_smt lo with
  | Numeral n1 =>
      cases hHi : __eo_to_smt hi with
      | Numeral n2 =>
          have hNN' :
              term_has_non_none_type
                (SmtTerm.re_loop (SmtTerm.Numeral n1)
                  (SmtTerm.Numeral n2) (__eo_to_smt x)) := by
            simpa [hLo, hHi] using hNN
          rcases re_loop_arg_of_non_none hNN' with ⟨hn1, hn2, hXTy⟩
          refine ⟨?_, ?_, ?_⟩
          · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hLo hn1
          · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hHi hn2
          · unfold eoHasSmtTranslation
            rw [hXTy]
            intro h
            cases h
      | _ =>
          exfalso
          unfold term_has_non_none_type at hNN
          exact hNN (by
            simp [hLo, hHi, __smtx_typeof, __smtx_typeof_re_loop])
  | _ =>
      exfalso
      unfold term_has_non_none_type at hNN
      exact hNN (by
        simp [hLo, __smtx_typeof, __smtx_typeof_re_loop])

theorem is_closed_rec_apply_extract_eq_and_bool_of_has_smt_translation
    {hi lo x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp2 UserOp2.extract hi lo) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp2 UserOp2.extract hi lo) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp2 UserOp2.extract hi lo) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp2 UserOp2.extract hi lo) x) env =
        Term.Boolean b :=
by
  rcases extract_indices_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨⟨_hiVal, hHiNum⟩, hLoValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop2_eq_and_bool_of_indices_true_and_arg
      hEnv
      (by cases hEnv <;> simp [__is_closed_rec])
      (eo_is_closed_rec_eq_true_of_eo_to_smt_numeral hEnv hHiNum)
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hLoValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_re_loop_eq_and_bool_of_has_smt_translation
    {lo hi x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x) env =
        Term.Boolean b :=
by
  rcases re_loop_indices_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hLoValid, hHiValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop2_eq_and_bool_of_indices_true_and_arg
      hEnv
      (by cases hEnv <;> simp [__is_closed_rec])
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hLoValid)
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hHiValid)
      (ihX hXTrans)

theorem eo_is_closed_rec_apply_eq_of_not_quantifier
    {f x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall :
      ∀ vs, f ≠ Term.Apply (Term.UOp UserOp.forall) vs)
    (hNotExists :
      ∀ vs, f ≠ Term.Apply (Term.UOp UserOp.exists) vs) :
  __eo_is_closed_rec (Term.Apply f x) env =
    __eo_and (__eo_is_closed_rec f env) (__eo_is_closed_rec x env) :=
by
  cases hEnv <;> cases f <;> simp [__eo_is_closed_rec]

theorem is_closed_rec_apply_generic_eq_and_bool_of_parts
    {f x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotList :
      ∀ q v vs,
        f ≠
          Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hNotForall :
      ∀ vs, f ≠ Term.Apply (Term.UOp UserOp.forall) vs)
    (hNotExists :
      ∀ vs, f ≠ Term.Apply (Term.UOp UserOp.exists) vs)
    (hF :
      __is_closed_rec f env = __eo_is_closed_rec f env ∧
        ∃ b, __eo_is_closed_rec f env = Term.Boolean b)
    (hX :
      __is_closed_rec x env = __eo_is_closed_rec x env ∧
        ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply f x) env =
    __eo_is_closed_rec (Term.Apply f x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply f x) env = Term.Boolean b :=
by
  rcases hF with ⟨hFEq, hFBool⟩
  rcases hX with ⟨hXEq, hXBool⟩
  refine ⟨?_, ?_⟩
  · calc
      __is_closed_rec (Term.Apply f x) env =
          __eo_and (__is_closed_rec f env) (__is_closed_rec x env) := by
            exact is_closed_rec_apply_eq_of_not_list_branch hEnv hNotList
      _ = __eo_and (__eo_is_closed_rec f env)
            (__eo_is_closed_rec x env) := by
            rw [hFEq, hXEq]
      _ = __eo_is_closed_rec (Term.Apply f x) env := by
            exact
              (eo_is_closed_rec_apply_eq_of_not_quantifier
                hEnv hNotForall hNotExists).symm
  · rcases hFBool with ⟨bf, hFBool⟩
    rcases hXBool with ⟨bx, hXBool⟩
    rw [eo_is_closed_rec_apply_eq_of_not_quantifier
      hEnv hNotForall hNotExists]
    exact eo_and_eq_boolean_of_boolean hFBool hXBool

theorem apply_args_have_smt_translation_of_non_none
    {f x : Term}
    (hTy :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) =
        __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
          (__smtx_typeof (__eo_to_smt x)))
    (hNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))) :
  eoHasSmtTranslation f ∧ eoHasSmtTranslation x :=
by
  unfold term_has_non_none_type at hNN
  have hApplyNN :
      __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
          (__smtx_typeof (__eo_to_smt x)) ≠
        SmtType.None := by
    intro hNone
    exact hNN (by rw [hTy, hNone])
  rcases typeof_apply_non_none_cases hApplyNN with
    ⟨A, B, hF, hX, hA, hB⟩
  refine ⟨?_, ?_⟩
  · unfold eoHasSmtTranslation
    rcases hF with hFun | hDtc
    · rw [hFun]
      simp
    · rw [hDtc]
      simp
  · unfold eoHasSmtTranslation
    rw [hX]
    exact hA

theorem is_closed_rec_apply_generic_eq_and_bool_of_has_smt_translation
    {f x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotList :
      ∀ q v vs,
        f ≠
          Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hNotForall :
      ∀ vs, f ≠ Term.Apply (Term.UOp UserOp.forall) vs)
    (hNotExists :
      ∀ vs, f ≠ Term.Apply (Term.UOp UserOp.exists) vs)
    (hTranslate :
      __eo_to_smt (Term.Apply f x) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))
    (hTy :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) =
        __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
          (__smtx_typeof (__eo_to_smt x)))
    (hTrans : eoHasSmtTranslation (Term.Apply f x))
    (ihF :
      eoHasSmtTranslation f ->
        __is_closed_rec f env = __eo_is_closed_rec f env ∧
          ∃ b, __eo_is_closed_rec f env = Term.Boolean b)
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply f x) env =
    __eo_is_closed_rec (Term.Apply f x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply f x) env = Term.Boolean b :=
by
  have hNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans
  rcases apply_args_have_smt_translation_of_non_none hTy hNN with
    ⟨hFTrans, hXTrans⟩
  exact
    is_closed_rec_apply_generic_eq_and_bool_of_parts
      hEnv hNotList hNotForall hNotExists
      (ihF hFTrans) (ihX hXTrans)

theorem eo_to_smt_quant_skolemize_ne_dt_sel_closed
    (vs : Term) (G : SmtTerm) (n : native_Nat) (s : native_String)
    (d : SmtDatatypeDecl) (i j : native_Nat) :
    __eo_to_smt_quantifiers_skolemize vs G n ≠ SmtTerm.DtSel s d i j :=
by
  induction n generalizing vs G with
  | zero =>
      intro h
      unfold __eo_to_smt_quantifiers_skolemize at h
      split at h <;> simp_all
  | succ k ih =>
      intro h
      unfold __eo_to_smt_quantifiers_skolemize at h
      split at h <;> first | exact ih _ _ h | simp_all

theorem eo_to_smt_quant_skolemize_ne_dt_tester_closed
    (vs : Term) (G : SmtTerm) (n : native_Nat) (s : native_String)
    (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt_quantifiers_skolemize vs G n ≠ SmtTerm.DtTester s d i :=
by
  induction n generalizing vs G with
  | zero =>
      intro h
      unfold __eo_to_smt_quantifiers_skolemize at h
      split at h <;> simp_all
  | succ k ih =>
      intro h
      unfold __eo_to_smt_quantifiers_skolemize at h
      split at h <;> first | exact ih _ _ h | simp_all

theorem eo_to_smt_quant_skolemize_top_ne_dt_sel_closed
    (q idx : Term) (s : native_String) (d : SmtDatatypeDecl)
    (i j : native_Nat) :
    __eo_to_smt (Term._at_quantifiers_skolemize q idx) ≠
      SmtTerm.DtSel s d i j :=
by
  intro h
  cases q <;> try cases h
  case Apply f body =>
    cases f <;> try cases h
    case Apply g xs =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> try cases h
        case «forall» =>
          change
              native_ite (__eo_to_smt_nat_is_valid idx)
                (__eo_to_smt_quantifiers_skolemize
                  xs (SmtTerm.not (__eo_to_smt body))
                  (__eo_to_smt_nat idx))
                SmtTerm.None =
              SmtTerm.DtSel s d i j at h
          unfold native_ite at h
          split at h <;> try cases h
          exact
            eo_to_smt_quant_skolemize_ne_dt_sel_closed
              xs (SmtTerm.not (__eo_to_smt body))
              (__eo_to_smt_nat idx) s d i j h

theorem eo_to_smt_quant_skolemize_top_ne_dt_tester_closed
    (q idx : Term) (s : native_String) (d : SmtDatatypeDecl)
    (i : native_Nat) :
    __eo_to_smt (Term._at_quantifiers_skolemize q idx) ≠
      SmtTerm.DtTester s d i :=
by
  intro h
  cases q <;> try cases h
  case Apply f body =>
    cases f <;> try cases h
    case Apply g xs =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> try cases h
        case «forall» =>
          change
              native_ite (__eo_to_smt_nat_is_valid idx)
                (__eo_to_smt_quantifiers_skolemize
                  xs (SmtTerm.not (__eo_to_smt body))
                  (__eo_to_smt_nat idx))
                SmtTerm.None =
              SmtTerm.DtTester s d i at h
          unfold native_ite at h
          split at h <;> try cases h
          exact
            eo_to_smt_quant_skolemize_ne_dt_tester_closed
              xs (SmtTerm.not (__eo_to_smt body))
              (__eo_to_smt_nat idx) s d i h

theorem quant_skolemize_apply_generic_type
    (q idx x : Term) :
    __smtx_typeof
        (SmtTerm.Apply (__eo_to_smt (Term._at_quantifiers_skolemize q idx))
          (__eo_to_smt x)) =
      __smtx_typeof_apply
        (__smtx_typeof (__eo_to_smt (Term._at_quantifiers_skolemize q idx)))
        (__smtx_typeof (__eo_to_smt x)) :=
by
  change
    generic_apply_type (__eo_to_smt (Term._at_quantifiers_skolemize q idx))
      (__eo_to_smt x)
  unfold generic_apply_type
  cases hHead : __eo_to_smt (Term._at_quantifiers_skolemize q idx)
  <;> simp [__smtx_typeof]
  · exact
      (eo_to_smt_quant_skolemize_top_ne_dt_sel_closed q idx _ _ _ _
        hHead).elim
  · exact
      (eo_to_smt_quant_skolemize_top_ne_dt_tester_closed q idx _ _ _
        hHead).elim

theorem at_const_apply_generic_type
    (i j x : Term) :
    __smtx_typeof
        (SmtTerm.Apply (__eo_to_smt (Term.UOp2 UserOp2._at_const i j))
          (__eo_to_smt x)) =
      __smtx_typeof_apply
        (__smtx_typeof (__eo_to_smt (Term.UOp2 UserOp2._at_const i j)))
        (__smtx_typeof (__eo_to_smt x)) :=
by
  change
    generic_apply_type (__eo_to_smt (Term.UOp2 UserOp2._at_const i j))
      (__eo_to_smt x)
  unfold generic_apply_type
  cases hHead : __eo_to_smt (Term.UOp2 UserOp2._at_const i j)
  <;> simp [__smtx_typeof]
  · exact
      (TranslationProofs.eo_to_smt_at_const_ne_dt_sel i j _ _ _ _ hHead).elim
  · exact
      (TranslationProofs.eo_to_smt_at_const_ne_dt_tester i j _ _ _ hHead).elim

theorem false_of_apply_uop2_translate_apply_none {P : Prop}
    {op : UserOp2} {i j x : Term}
    (hTrans : eoHasSmtTranslation (Term.Apply (Term.UOp2 op i j) x))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.UOp2 op i j) x) =
        SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) : P :=
by
  exfalso
  unfold eoHasSmtTranslation at hTrans
  rw [hTranslate] at hTrans
  exact hTrans (TranslationProofs.typeof_apply_none_eq (__eo_to_smt x))

theorem is_closed_rec_apply_uop2_any_eq_and_bool_of_has_smt_translation
    (root : Term)
    {op : UserOp2} {i j x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hHeadLt : sizeOf (Term.UOp2 op i j) < sizeOf root)
    (hXLt : sizeOf x < sizeOf root)
    (hTrans : eoHasSmtTranslation (Term.Apply (Term.UOp2 op i j) x))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp2 op i j) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp2 op i j) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp2 op i j) x) env =
        Term.Boolean b :=
by
  cases op
  case extract =>
    exact
      is_closed_rec_apply_extract_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
  case re_loop =>
    exact
      is_closed_rec_apply_re_loop_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
  case _at_const =>
    exact
      is_closed_rec_apply_generic_eq_and_bool_of_has_smt_translation
        hEnv
        (by intro q v vs hEq; cases hEq)
        (by intro vs hEq; cases hEq)
        (by intro vs hEq; cases hEq)
        (by rfl)
        (at_const_apply_generic_type i j x)
        hTrans
        (fun hHeadTrans => ih hHeadLt hEnv hHeadTrans)
        (fun hXTrans => ih hXLt hEnv hXTrans)
  case _at_quantifiers_skolemize =>
    exact
      is_closed_rec_apply_generic_eq_and_bool_of_has_smt_translation
        hEnv
        (by intro q v vs hEq; cases hEq)
        (by intro vs hEq; cases hEq)
        (by intro vs hEq; cases hEq)
        (by rfl)
        (quant_skolemize_apply_generic_type i j x)
        hTrans
        (fun hHeadTrans => ih hHeadLt hEnv hHeadTrans)
        (fun hXTrans => ih hXLt hEnv hXTrans)

theorem generic_apply_type_of_non_special_head_closed
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    generic_apply_type f x :=
by
  unfold generic_apply_type
  cases f
  case DtSel s d i j => exact absurd rfl (hSel s d i j)
  case DtTester s d i => exact absurd rfl (hTester s d i)
  all_goals simp [__smtx_typeof]

theorem typeof_generic_apply_non_function_head_eq_none_closed
    (f x : SmtTerm)
    (hGeneric : generic_apply_type f x)
    (hFun : ∀ A B, __smtx_typeof f ≠ SmtType.FunType A B)
    (hDtc : ∀ A B, __smtx_typeof f ≠ SmtType.DtcAppType A B) :
    __smtx_typeof (SmtTerm.Apply f x) = SmtType.None :=
by
  rw [hGeneric]
  cases hF : __smtx_typeof f <;> try rfl
  · exact False.elim (hFun _ _ hF)
  · exact False.elim (hDtc _ _ hF)

theorem smtx_typeof_apply_arg_none_eq_none_closed
    (F : SmtType) :
    __smtx_typeof_apply F SmtType.None = SmtType.None :=
by
  cases F <;>
    simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite,
      native_Teq]
  · rename_i A B
    cases A <;>
      simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite,
        native_Teq]
  · rename_i A B
    cases A <;>
      simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite,
        native_Teq]

theorem smtx_typeof_guard_none_eq_none_closed
    (T : SmtType) :
    __smtx_typeof_guard T SmtType.None = SmtType.None :=
by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

theorem smtx_typeof_guard_wf_none_eq_none_closed
    (T : SmtType) :
    __smtx_typeof_guard_wf T SmtType.None = SmtType.None :=
by
  cases T <;>
    simp [__smtx_typeof_guard_wf, __smtx_typeof_guard, native_ite,
      native_Teq]

theorem smtx_typeof_smt_apply_arg_none_eq_none_closed
    (f x : SmtTerm)
    (hx : __smtx_typeof x = SmtType.None) :
    __smtx_typeof (SmtTerm.Apply f x) = SmtType.None :=
by
  cases f <;>
    simp [__smtx_typeof, hx, smtx_typeof_apply_arg_none_eq_none_closed,
      smtx_typeof_guard_none_eq_none_closed,
      smtx_typeof_guard_wf_none_eq_none_closed]

theorem false_of_apply_apply_generic_raw_list_has_smt_translation
    {P : Prop} {q v vs body : Term}
    (hInnerTranslate :
      __eo_to_smt
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) =
        SmtTerm.Apply (__eo_to_smt q)
          (__eo_to_smt (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
    (hOuterTranslate :
      __eo_to_smt
          (Term.Apply
            (Term.Apply q
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            body) =
        SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply q
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
          (__eo_to_smt body))
    (hOuterGeneric :
      generic_apply_type
        (__eo_to_smt
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
        (__eo_to_smt body))
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  P :=
by
  exfalso
  unfold eoHasSmtTranslation at hTrans
  apply hTrans
  rw [hOuterTranslate]
  have hInnerNone :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply q
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))) =
        SmtType.None := by
    rw [hInnerTranslate]
    exact
      smtx_typeof_smt_apply_arg_none_eq_none_closed
        (__eo_to_smt q)
        (__eo_to_smt (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
        (smtx_typeof_eo_list_cons_eq_none v vs)
  rw [hOuterGeneric, hInnerNone]
  rfl

theorem smtx_typeof_generic_apply_eo_list_cons_arg_eq_none_closed
    (f : SmtTerm) (v vs : Term)
    (hGeneric :
      generic_apply_type f
        (__eo_to_smt (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))) :
    __smtx_typeof
        (SmtTerm.Apply f
          (__eo_to_smt (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))) =
      SmtType.None :=
by
  rw [hGeneric, smtx_typeof_eo_list_cons_eq_none]
  exact smtx_typeof_apply_arg_none_eq_none_closed (__smtx_typeof f)

theorem apply_uop2_arg_has_smt_translation_of_has_smt_translation
    {op : UserOp2} {i j x : Term}
    (hTrans : eoHasSmtTranslation (Term.Apply (Term.UOp2 op i j) x)) :
  eoHasSmtTranslation x :=
by
  cases op
  case extract =>
    exact (extract_indices_nat_valid_and_arg_has_smt_translation hTrans).2.2
  case re_loop =>
    exact (re_loop_indices_nat_valid_and_arg_has_smt_translation hTrans).2.2
  case _at_const =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.UOp2 UserOp2._at_const i j) x) =
          SmtTerm.Apply
            (__eo_to_smt (Term.UOp2 UserOp2._at_const i j))
            (__eo_to_smt x) := by
      rfl
    have hTy :
        __smtx_typeof
            (SmtTerm.Apply
              (__eo_to_smt (Term.UOp2 UserOp2._at_const i j))
              (__eo_to_smt x)) =
          __smtx_typeof_apply
            (__smtx_typeof
              (__eo_to_smt (Term.UOp2 UserOp2._at_const i j)))
            (__smtx_typeof (__eo_to_smt x)) :=
      at_const_apply_generic_type i j x
    have hNN :
        term_has_non_none_type
          (SmtTerm.Apply
            (__eo_to_smt (Term.UOp2 UserOp2._at_const i j))
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hTrans
    exact (apply_args_have_smt_translation_of_non_none hTy hNN).2
  case _at_quantifiers_skolemize =>
    have hTranslate :
        __eo_to_smt
            (Term.Apply
              (Term.UOp2 UserOp2._at_quantifiers_skolemize i j) x) =
          SmtTerm.Apply
            (__eo_to_smt
              (Term.UOp2 UserOp2._at_quantifiers_skolemize i j))
            (__eo_to_smt x) := by
      rfl
    have hTy :
        __smtx_typeof
            (SmtTerm.Apply
              (__eo_to_smt
                (Term.UOp2 UserOp2._at_quantifiers_skolemize i j))
              (__eo_to_smt x)) =
          __smtx_typeof_apply
            (__smtx_typeof
              (__eo_to_smt
                (Term.UOp2 UserOp2._at_quantifiers_skolemize i j)))
            (__smtx_typeof (__eo_to_smt x)) :=
      quant_skolemize_apply_generic_type i j x
    have hNN :
        term_has_non_none_type
          (SmtTerm.Apply
            (__eo_to_smt
              (Term.UOp2 UserOp2._at_quantifiers_skolemize i j))
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hTrans
    exact (apply_args_have_smt_translation_of_non_none hTy hNN).2

theorem false_of_apply_apply_uop2_raw_list_has_smt_translation
    {P : Prop} {op : UserOp2} {i j v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp2 op i j)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  P :=
by
  exfalso
  have hTranslate :
      __eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp2 op i j)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            body) =
        SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.UOp2 op i j)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
          (__eo_to_smt body) := by
    cases op <;> rfl
  have hTy :
      __smtx_typeof
          (SmtTerm.Apply
            (__eo_to_smt
              (Term.Apply (Term.UOp2 op i j)
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            (__eo_to_smt body)) =
        __smtx_typeof_apply
          (__smtx_typeof
            (__eo_to_smt
              (Term.Apply (Term.UOp2 op i j)
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))))
          (__smtx_typeof (__eo_to_smt body)) := by
    exact
      generic_apply_type_of_non_special_head_closed _ _
        (by
          intro s d i' j' h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_sel
              _ _ s d i' j' h)
        (by
          intro s d i' h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_tester
              _ _ s d i' h)
  have hNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.UOp2 op i j)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
          (__eo_to_smt body)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans
  rcases apply_args_have_smt_translation_of_non_none hTy hNN with
    ⟨hHeadTrans, _hBodyTrans⟩
  have hRawTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) :=
    apply_uop2_arg_has_smt_translation_of_has_smt_translation hHeadTrans
  unfold eoHasSmtTranslation at hRawTrans
  rw [smtx_typeof_eo_list_cons_eq_none] at hRawTrans
  exact hRawTrans rfl

theorem eo_to_smt_re_unfold_ne_dt_sel_closed
    (str re : SmtTerm) (n : native_Nat)
    (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat) :
    __eo_to_smt_re_unfold_pos_component str re n ≠
      SmtTerm.DtSel s d i j :=
by
  induction n generalizing str re with
  | zero =>
      intro h
      cases re <;> simp [__eo_to_smt_re_unfold_pos_component] at h
  | succ n ih =>
      intro h
      cases re <;> simp [__eo_to_smt_re_unfold_pos_component] at h
      case re_concat r1 r2 =>
        exact ih _ _ h

theorem eo_to_smt_re_unfold_ne_dt_tester_closed
    (str re : SmtTerm) (n : native_Nat)
    (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __eo_to_smt_re_unfold_pos_component str re n ≠
      SmtTerm.DtTester s d i :=
by
  induction n generalizing str re with
  | zero =>
      intro h
      cases re <;> simp [__eo_to_smt_re_unfold_pos_component] at h
  | succ n ih =>
      intro h
      cases re <;> simp [__eo_to_smt_re_unfold_pos_component] at h
      case re_concat r1 r2 =>
        exact ih _ _ h

theorem smtx_typeof_re_unfold_pos_component_of_non_none_closed
    (s r : SmtTerm)
    (n : native_Nat)
    (hNN :
      __smtx_typeof (__eo_to_smt_re_unfold_pos_component s r n) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt_re_unfold_pos_component s r n) =
      SmtType.Seq SmtType.Char :=
by
  induction n generalizing s r with
  | zero =>
      cases r <;> simp [__eo_to_smt_re_unfold_pos_component] at hNN ⊢
      case re_concat r1 r2 =>
        have hTermNN :
            term_has_non_none_type
              (SmtTerm.str_substr s (SmtTerm.Numeral 0)
                (SmtTerm.str_indexof_re_split s r1 r2)) := by
          unfold term_has_non_none_type
          simpa [__eo_to_smt_re_unfold_pos_component] using hNN
        rcases str_substr_args_of_non_none hTermNN with
          ⟨T, hS, hStart, hLen⟩
        have hSplitNN :
            term_has_non_none_type (SmtTerm.str_indexof_re_split s r1 r2) := by
          unfold term_has_non_none_type
          rw [hLen]
          simp
        have hSplitArgs := str_indexof_re_split_args_of_non_none hSplitNN
        have hT : T = SmtType.Char := by
          cases hS.symm.trans hSplitArgs.1
          rfl
        rw [typeof_str_substr_eq, hS, hStart, hLen, hT]
        simp [__smtx_typeof_str_substr]
  | succ n ih =>
      cases r <;> simp [__eo_to_smt_re_unfold_pos_component] at hNN ⊢
      case re_concat r1 r2 =>
        exact ih _ r2 hNN

theorem typeof_apply_re_unfold_pos_component_head_eq_none_closed
    (s r : SmtTerm) (n : native_Nat) (x : SmtTerm) :
    __smtx_typeof
        (SmtTerm.Apply (__eo_to_smt_re_unfold_pos_component s r n) x) =
      SmtType.None :=
by
  exact
    typeof_generic_apply_non_function_head_eq_none_closed _ _
      (generic_apply_type_of_non_special_head_closed _ _
        (by
          intro s' d i j h
          exact eo_to_smt_re_unfold_ne_dt_sel_closed s r n s' d i j h)
        (by
          intro s' d i h
          exact eo_to_smt_re_unfold_ne_dt_tester_closed s r n s' d i h))
      (by
        intro A B hFun
        have hNN :
            __smtx_typeof (__eo_to_smt_re_unfold_pos_component s r n) ≠
              SmtType.None := by
          rw [hFun]
          simp
        have hTy :=
          smtx_typeof_re_unfold_pos_component_of_non_none_closed s r n hNN
        rw [hTy] at hFun
        cases hFun)
      (by
        intro A B hDtc
        have hNN :
            __smtx_typeof (__eo_to_smt_re_unfold_pos_component s r n) ≠
              SmtType.None := by
          rw [hDtc]
          simp
        have hTy :=
          smtx_typeof_re_unfold_pos_component_of_non_none_closed s r n hNN
        rw [hTy] at hDtc
        cases hDtc)

theorem typeof_apply_re_unfold_top_eq_none_closed
    (t r idx x : Term) :
    __smtx_typeof
        (SmtTerm.Apply (__eo_to_smt (Term._at_re_unfold_pos_component t r idx))
          (__eo_to_smt x)) =
      SmtType.None :=
by
  change
    __smtx_typeof
        (SmtTerm.Apply
          (native_ite (__eo_to_smt_nat_is_valid idx)
            (__eo_to_smt_re_unfold_pos_component (__eo_to_smt t) (__eo_to_smt r)
              (__eo_to_smt_nat idx))
            SmtTerm.None)
          (__eo_to_smt x)) =
      SmtType.None
  cases hValid : __eo_to_smt_nat_is_valid idx <;>
    simp [native_ite, TranslationProofs.typeof_apply_none_eq,
      typeof_apply_re_unfold_pos_component_head_eq_none_closed]

theorem witness_string_length_apply_generic_type
    (T len id x : Term) :
    __smtx_typeof
        (SmtTerm.Apply
          (__eo_to_smt
            (Term.UOp3 UserOp3._at_witness_string_length T len id))
          (__eo_to_smt x)) =
      __smtx_typeof_apply
        (__smtx_typeof
          (__eo_to_smt
            (Term.UOp3 UserOp3._at_witness_string_length T len id)))
        (__smtx_typeof (__eo_to_smt x)) :=
by
  change
    generic_apply_type
      (native_ite (__eo_to_smt_nat_is_valid len)
        (native_ite (__eo_to_smt_nat_is_valid id)
          (SmtTerm.choice (native_string_lit "@x") (__eo_to_smt_type T)
            (SmtTerm.eq
              (SmtTerm.str_len
                (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type T)))
              (__eo_to_smt len)))
          SmtTerm.None)
        SmtTerm.None)
      (__eo_to_smt x)
  unfold generic_apply_type
  cases hLen : __eo_to_smt_nat_is_valid len <;>
    cases hId : __eo_to_smt_nat_is_valid id <;>
      simp [native_ite, hLen, hId, __smtx_typeof]

theorem false_of_apply_re_unfold_pos_component {P : Prop}
    {t r idx x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp3 UserOp3._at_re_unfold_pos_component t r idx)
          x)) :
  P :=
by
  exfalso
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.Apply
            (__eo_to_smt (Term._at_re_unfold_pos_component t r idx))
            (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  exact hTrans (typeof_apply_re_unfold_top_eq_none_closed t r idx x)

theorem apply_uop3_arg_has_smt_translation_of_has_smt_translation
    {op : UserOp3} {a b c x : Term}
    (hTrans : eoHasSmtTranslation (Term.Apply (Term.UOp3 op a b c) x)) :
  eoHasSmtTranslation x :=
by
  cases op
  case _at_re_unfold_pos_component =>
    exact false_of_apply_re_unfold_pos_component hTrans
  case _at_witness_string_length =>
    have hTranslate :
        __eo_to_smt
            (Term.Apply
              (Term.UOp3 UserOp3._at_witness_string_length a b c) x) =
          SmtTerm.Apply
            (__eo_to_smt
              (Term.UOp3 UserOp3._at_witness_string_length a b c))
            (__eo_to_smt x) := by
      rfl
    have hTy :
        __smtx_typeof
            (SmtTerm.Apply
              (__eo_to_smt
                (Term.UOp3 UserOp3._at_witness_string_length a b c))
              (__eo_to_smt x)) =
          __smtx_typeof_apply
            (__smtx_typeof
              (__eo_to_smt
                (Term.UOp3 UserOp3._at_witness_string_length a b c)))
            (__smtx_typeof (__eo_to_smt x)) :=
      witness_string_length_apply_generic_type a b c x
    have hNN :
        term_has_non_none_type
          (SmtTerm.Apply
            (__eo_to_smt
              (Term.UOp3 UserOp3._at_witness_string_length a b c))
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hTrans
    exact (apply_args_have_smt_translation_of_non_none hTy hNN).2

theorem false_of_apply_apply_uop3_raw_list_has_smt_translation
    {P : Prop} {op : UserOp3} {a b c v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp3 op a b c)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  P :=
by
  exfalso
  have hTranslate :
      __eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp3 op a b c)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            body) =
        SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.UOp3 op a b c)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
          (__eo_to_smt body) := by
    cases op <;> rfl
  have hTy :
      __smtx_typeof
          (SmtTerm.Apply
            (__eo_to_smt
              (Term.Apply (Term.UOp3 op a b c)
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            (__eo_to_smt body)) =
        __smtx_typeof_apply
          (__smtx_typeof
            (__eo_to_smt
              (Term.Apply (Term.UOp3 op a b c)
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))))
          (__smtx_typeof (__eo_to_smt body)) := by
    exact
      generic_apply_type_of_non_special_head_closed _ _
        (by
          intro s d i' j' h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_sel
              _ _ s d i' j' h)
        (by
          intro s d i' h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_tester
              _ _ s d i' h)
  have hNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.UOp3 op a b c)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
          (__eo_to_smt body)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans
  rcases apply_args_have_smt_translation_of_non_none hTy hNN with
    ⟨hHeadTrans, _hBodyTrans⟩
  have hRawTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) :=
    apply_uop3_arg_has_smt_translation_of_has_smt_translation hHeadTrans
  unfold eoHasSmtTranslation at hRawTrans
  rw [smtx_typeof_eo_list_cons_eq_none] at hRawTrans
  exact hRawTrans rfl

theorem is_closed_rec_apply_uop3_any_eq_and_bool_of_has_smt_translation
    (root : Term)
    {op : UserOp3} {a b c x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hHeadLt : sizeOf (Term.UOp3 op a b c) < sizeOf root)
    (hXLt : sizeOf x < sizeOf root)
    (hTrans : eoHasSmtTranslation (Term.Apply (Term.UOp3 op a b c) x))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ bb, __eo_is_closed_rec t env = Term.Boolean bb) :
  __is_closed_rec (Term.Apply (Term.UOp3 op a b c) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp3 op a b c) x) env ∧
    ∃ bb,
      __eo_is_closed_rec (Term.Apply (Term.UOp3 op a b c) x) env =
        Term.Boolean bb :=
by
  cases op
  case _at_re_unfold_pos_component =>
    exact false_of_apply_re_unfold_pos_component hTrans
  case _at_witness_string_length =>
    exact
      is_closed_rec_apply_generic_eq_and_bool_of_has_smt_translation
        hEnv
        (by intro q v vs hEq; cases hEq)
        (by intro vs hEq; cases hEq)
        (by intro vs hEq; cases hEq)
        (by rfl)
        (witness_string_length_apply_generic_type a b c x)
        hTrans
        (fun hHeadTrans => ih hHeadLt hEnv hHeadTrans)
        (fun hXTrans => ih hXLt hEnv hXTrans)

theorem term_not_eo_list_cons_of_has_smt_translation
    {x : Term}
    (hTrans : eoHasSmtTranslation x) :
  ∀ v vs,
    x ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs :=
by
  intro v vs hEq
  subst x
  unfold eoHasSmtTranslation at hTrans
  rw [smtx_typeof_eo_list_cons_eq_none] at hTrans
  exact hTrans rfl

theorem is_closed_rec_typed_list_eq_and_bool_of_elem_type_non_none
    (root : Term)
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b)
    {xs env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hLt : sizeOf xs < sizeOf root)
    (hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None) :
  __is_closed_rec xs env = __eo_is_closed_rec xs env ∧
    ∃ b, __eo_is_closed_rec xs env = Term.Boolean b :=
by
  let rec go (xs : Term) :
      ∀ {env : Term} {vars : List SmtVarKey},
        EoSmtVarEnv env vars ->
          sizeOf xs < sizeOf root ->
            __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
              __is_closed_rec xs env = __eo_is_closed_rec xs env ∧
                ∃ b, __eo_is_closed_rec xs env = Term.Boolean b :=
  by
    intro env vars hEnv hLt hElemNN
    cases xs with
    | Apply f x =>
        cases f with
        | UOp op =>
            cases op
            case _at__at_TypedList_nil =>
              have hWf : __smtx_type_wf (__eo_to_smt_type x) = true := by
                by_cases hWf : __smtx_type_wf (__eo_to_smt_type x) = true
                · exact hWf
                · exfalso
                  exact hElemNN (by
                    simp [__eo_to_smt_typed_list_elem_type, native_ite, hWf])
              have hXValid : TranslationProofs.eo_type_valid x :=
                TranslationProofs.eo_type_valid_of_smt_wf x hWf
              have hXIs : __is_closed_rec x env = Term.Boolean true :=
                is_closed_rec_eq_true_of_eo_type_valid hEnv hXValid
              have hXEo : __eo_is_closed_rec x env = Term.Boolean true :=
                eo_is_closed_rec_eq_true_of_eo_type_valid hEnv hXValid
              have hXClosed :
                  __is_closed_rec x env = __eo_is_closed_rec x env ∧
                    ∃ b, __eo_is_closed_rec x env = Term.Boolean b := by
                refine ⟨?_, ⟨true, hXEo⟩⟩
                rw [hXIs, hXEo]
              exact is_closed_rec_apply_uop_eq_and_bool_of_arg hEnv hXClosed
            all_goals
              exact False.elim
                (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
        | Apply g t =>
            cases g with
            | UOp op =>
                cases op
                case _at__at_TypedList_cons =>
                  let headTy := __smtx_typeof (__eo_to_smt t)
                  let tailTy := __eo_to_smt_typed_list_elem_type x
                  have hGuard : native_Teq headTy tailTy = true := by
                    by_cases hGuard : native_Teq headTy tailTy = true
                    · exact hGuard
                    · exfalso
                      exact hElemNN (by
                        simp [__eo_to_smt_typed_list_elem_type, headTy, tailTy,
                          native_ite, hGuard])
                  have hHeadNN : headTy ≠ SmtType.None := by
                    change
                      (native_ite (native_Teq headTy tailTy) headTy
                          SmtType.None) ≠
                        SmtType.None at hElemNN
                    rw [hGuard] at hElemNN
                    exact hElemNN
                  have hTailNN : tailTy ≠ SmtType.None := by
                    intro hTailNone
                    cases hHead : headTy <;>
                      simp [headTy, tailTy, hHead, hTailNone, native_Teq] at hGuard hHeadNN
                  have hHeadTrans : eoHasSmtTranslation t := by
                    unfold eoHasSmtTranslation
                    simpa [headTy] using hHeadNN
                  have hHeadLt : sizeOf t < sizeOf root := by
                    simp at hLt
                    omega
                  have hTailLt : sizeOf x < sizeOf root := by
                    simp at hLt
                    omega
                  have hHeadClosed := ih hHeadLt hEnv hHeadTrans
                  have hTailClosed :=
                    go x hEnv hTailLt (by simpa [tailTy] using hTailNN)
                  have hInner :
                      __is_closed_rec
                          (Term.Apply
                            (Term.UOp UserOp._at__at_TypedList_cons) t)
                          env =
                        __eo_is_closed_rec
                          (Term.Apply
                            (Term.UOp UserOp._at__at_TypedList_cons) t)
                          env ∧
                        ∃ b,
                          __eo_is_closed_rec
                              (Term.Apply
                                (Term.UOp UserOp._at__at_TypedList_cons) t)
                              env =
                            Term.Boolean b :=
                    is_closed_rec_apply_uop_eq_and_bool_of_arg
                      hEnv hHeadClosed
                  exact
                    is_closed_rec_apply_generic_eq_and_bool_of_parts
                      hEnv
                      (by
                        intro q v vs hEq
                        cases hEq
                        exact term_not_eo_list_cons_of_has_smt_translation
                          hHeadTrans v vs rfl)
                      (by
                        intro vs hEq
                        cases hEq)
                      (by
                        intro vs hEq
                        cases hEq)
                      hInner
                      hTailClosed
                all_goals
                  exact False.elim
                    (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
            | _ =>
                exact False.elim
                  (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
        | _ =>
            exact False.elim
              (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
    | _ =>
        exact False.elim
          (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
  exact go xs hEnv hLt hElemNN

theorem typed_list_elem_type_non_none_of_distinct_has_smt_translation
    {xs : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.distinct) xs)) :
  __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (native_ite
            (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
            SmtTerm.None (__eo_to_smt_distinct xs)) ≠
        SmtType.None at hTrans
  intro hNone
  have hTeq : native_Teq SmtType.None SmtType.None = true := by
    simp [native_Teq]
  exact hTrans (by
    simp [hNone, hTeq, native_ite, TranslationProofs.smtx_typeof_none])

theorem is_closed_rec_apply_distinct_eq_and_bool_of_has_smt_translation
    (root : Term)
    {xs env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hLt : sizeOf xs < sizeOf root)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.distinct) xs))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.distinct) xs) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.distinct) xs) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.distinct) xs) env =
        Term.Boolean b :=
by
  have hElemNN :=
    typed_list_elem_type_non_none_of_distinct_has_smt_translation hTrans
  have hXsClosed :=
    is_closed_rec_typed_list_eq_and_bool_of_elem_type_non_none
      root ih hEnv hLt hElemNN
  exact is_closed_rec_apply_uop_eq_and_bool_of_arg hEnv hXsClosed

theorem typed_list_elem_type_non_none_not_eo_list_cons
    {xs : Term}
    (hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None) :
  ∀ v vs, xs ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs :=
by
  intro v vs hEq
  subst xs
  exact hElemNN (by simp [__eo_to_smt_typed_list_elem_type])

theorem eo_to_smt_set_insert_shape_of_non_none :
    ∀ xs base,
      __smtx_typeof (__eo_to_smt_set_insert xs base) ≠ SmtType.None ->
        ∃ A,
          __smtx_typeof (__eo_to_smt_set_insert xs base) = SmtType.Set A ∧
          __smtx_typeof base = SmtType.Set A ∧
          __eo_to_smt_typed_list_elem_type xs = A ∧
          A ≠ SmtType.None :=
by
  intro xs base hNonNone
  cases xs
  all_goals
    try
      exfalso
      apply hNonNone
      simp [__eo_to_smt_set_insert, TranslationProofs.smtx_typeof_none]
  case Apply f tail =>
    cases f
    all_goals
      try
        exfalso
        apply hNonNone
        simp [__eo_to_smt_set_insert, TranslationProofs.smtx_typeof_none]
    case UOp op =>
      cases op
      case _at__at_TypedList_nil =>
        cases hGuard :
            native_Teq (__smtx_typeof base)
              (SmtType.Set (__eo_to_smt_type tail))
        · exfalso
          apply hNonNone
          simp [__eo_to_smt_set_insert, hGuard, native_ite,
            TranslationProofs.smtx_typeof_none]
        · have hBase :
              __smtx_typeof base = SmtType.Set (__eo_to_smt_type tail) := by
            simpa [native_Teq] using hGuard
          have hBaseNN : term_has_non_none_type base := by
            unfold term_has_non_none_type
            rw [hBase]
            simp
          have hSetWf :
              __smtx_type_wf (SmtType.Set (__eo_to_smt_type tail)) = true :=
            smt_term_set_type_wf_of_non_none base hBaseNN hBase
          have hTailWf : __smtx_type_wf (__eo_to_smt_type tail) = true :=
            set_type_wf_component_of_wf hSetWf
          have hTailNN : __eo_to_smt_type tail ≠ SmtType.None :=
            type_wf_non_none hTailWf
          refine ⟨__eo_to_smt_type tail, ?_, hBase, ?_, hTailNN⟩
          · simpa [__eo_to_smt_set_insert, hGuard, native_ite] using hBase
          · simp [__eo_to_smt_typed_list_elem_type, native_ite, hTailWf]
      all_goals
        exfalso
        apply hNonNone
        simp [__eo_to_smt_set_insert, TranslationProofs.smtx_typeof_none]
    case Apply f' head =>
      cases f'
      all_goals
        try
          exfalso
          apply hNonNone
          simp [__eo_to_smt_set_insert, TranslationProofs.smtx_typeof_none]
      case UOp op =>
        cases op
        case _at__at_TypedList_cons =>
          have hNNUnion : term_has_non_none_type
              (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                (__eo_to_smt_set_insert tail base)) := by
            unfold term_has_non_none_type
            change
              __smtx_typeof
                  (__eo_to_smt_set_insert
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                        head)
                      tail) base) ≠ SmtType.None at hNonNone
            simpa [__eo_to_smt_set_insert] using hNonNone
          rcases set_binop_args_of_non_none (op := SmtTerm.set_union)
              (typeof_set_union_eq
                (SmtTerm.set_singleton (__eo_to_smt head))
                (__eo_to_smt_set_insert tail base))
              hNNUnion with
            ⟨A, hHeadSet, hTailSet⟩
          have hTailNN :
              __smtx_typeof (__eo_to_smt_set_insert tail base) ≠
                SmtType.None := by
            rw [hTailSet]
            simp
          rcases eo_to_smt_set_insert_shape_of_non_none tail base hTailNN
              with
            ⟨B, hTailSmt, hBase, hTailElem, hBNN⟩
          have hAB : A = B := by
            have hSetEq : SmtType.Set A = SmtType.Set B :=
              hTailSet.symm.trans hTailSmt
            cases hSetEq
            rfl
          have hBaseA : __smtx_typeof base = SmtType.Set A := by
            rw [hAB]
            exact hBase
          have hTailElemA : __eo_to_smt_typed_list_elem_type tail = A :=
            hTailElem.trans hAB.symm
          have hHeadArg := set_singleton_type_eq_arg_of_eq hHeadSet
          have hSmt :
              __smtx_typeof
                  (__eo_to_smt_set_insert
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                        head)
                      tail) base) = SmtType.Set A := by
            change
              __smtx_typeof
                  (SmtTerm.set_union
                    (SmtTerm.set_singleton (__eo_to_smt head))
                    (__eo_to_smt_set_insert tail base)) = SmtType.Set A
            rw [typeof_set_union_eq, hHeadSet, hTailSet]
            simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]
          have hElem :
              __eo_to_smt_typed_list_elem_type
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                      head)
                    tail) = A := by
            change
              native_ite
                (native_Teq (__smtx_typeof (__eo_to_smt head))
                  (__eo_to_smt_typed_list_elem_type tail))
                (__smtx_typeof (__eo_to_smt head)) SmtType.None = A
            rw [hHeadArg.1, hTailElemA]
            simp [native_Teq, native_ite]
          exact ⟨A, hSmt, hBaseA, hElem, hHeadArg.2⟩
        all_goals
          exfalso
          apply hNonNone
          simp [__eo_to_smt_set_insert, TranslationProofs.smtx_typeof_none]
termination_by xs base _ => sizeOf xs

theorem typeof_apply_set_insert_raw_base_eq_none_closed
    (xs v vs z : Term) :
    __smtx_typeof
        (SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
          (__eo_to_smt z)) =
      SmtType.None :=
by
  exact
    typeof_generic_apply_non_function_head_eq_none_closed _ _
      (generic_apply_type_of_non_special_head_closed _ _
        (by
          intro s d i j h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_sel
              _ _ s d i j h)
        (by
          intro s d i h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_tester
              _ _ s d i h))
      (by
        intro A B hFun
        have hNN :
            __smtx_typeof
                (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs)
                    (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))) ≠
              SmtType.None := by
          rw [hFun]
          simp
        change
            __smtx_typeof
                (__eo_to_smt_set_insert xs
                  (__eo_to_smt
                    (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))) ≠
              SmtType.None at hNN
        rcases
            eo_to_smt_set_insert_shape_of_non_none xs
              (__eo_to_smt (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
              hNN with
          ⟨C, hSet, _hBase, _hElem, _hCNN⟩
        change
            __smtx_typeof
                (__eo_to_smt_set_insert xs
                  (__eo_to_smt
                    (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))) =
              SmtType.FunType A B at hFun
        rw [hFun] at hSet
        cases hSet)
      (by
        intro A B hDtc
        have hNN :
            __smtx_typeof
                (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs)
                    (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))) ≠
              SmtType.None := by
          rw [hDtc]
          simp
        change
            __smtx_typeof
                (__eo_to_smt_set_insert xs
                  (__eo_to_smt
                    (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))) ≠
              SmtType.None at hNN
        rcases
            eo_to_smt_set_insert_shape_of_non_none xs
              (__eo_to_smt (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
              hNN with
          ⟨C, hSet, _hBase, _hElem, _hCNN⟩
        change
            __smtx_typeof
                (__eo_to_smt_set_insert xs
                  (__eo_to_smt
                    (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))) =
              SmtType.DtcAppType A B at hDtc
        rw [hDtc] at hSet
        cases hSet)

theorem false_of_apply_apply_apply_set_insert_middle_list_has_smt_translation
    {P : Prop} {xs v vs z : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.set_insert) xs)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          z)) :
  P :=
by
  exfalso
  unfold eoHasSmtTranslation at hTrans
  apply hTrans
  change
    __smtx_typeof
        (SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
          (__eo_to_smt z)) =
      SmtType.None
  exact typeof_apply_set_insert_raw_base_eq_none_closed xs v vs z

theorem set_insert_base_has_smt_translation_and_typed_list_elem_type_non_none
    {xs base : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) base)) :
  eoHasSmtTranslation base ∧
    __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof (__eo_to_smt_set_insert xs (__eo_to_smt base)) ≠
        SmtType.None at hTrans
  rcases eo_to_smt_set_insert_shape_of_non_none xs (__eo_to_smt base)
      hTrans with
    ⟨A, _hSet, hBase, hElem, hANN⟩
  refine ⟨?_, ?_⟩
  · unfold eoHasSmtTranslation
    rw [hBase]
    simp
  · rw [hElem]
    exact hANN

theorem is_closed_rec_apply_apply_set_insert_eq_and_bool_of_has_smt_translation
    (root : Term)
    {xs base env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hXsLt : sizeOf xs < sizeOf root)
    (hBaseLt : sizeOf base < sizeOf root)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) base))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs)
      base) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) base) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) base)
        env =
      Term.Boolean b :=
by
  rcases
      set_insert_base_has_smt_translation_and_typed_list_elem_type_non_none
        hTrans with
    ⟨hBaseTrans, hElemNN⟩
  have hXsClosed :=
    is_closed_rec_typed_list_eq_and_bool_of_elem_type_non_none
      root ih hEnv hXsLt hElemNN
  have hBaseClosed := ih hBaseLt hEnv hBaseTrans
  have hInner :
      __is_closed_rec (Term.Apply (Term.UOp UserOp.set_insert) xs) env =
        __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.set_insert) xs)
          env ∧
        ∃ b,
          __eo_is_closed_rec
              (Term.Apply (Term.UOp UserOp.set_insert) xs) env =
            Term.Boolean b :=
    is_closed_rec_apply_uop_eq_and_bool_of_arg hEnv hXsClosed
  exact
    is_closed_rec_apply_generic_eq_and_bool_of_parts
      hEnv
      (by
        intro q v vs hEq
        cases hEq
        exact typed_list_elem_type_non_none_not_eo_list_cons hElemNN v vs
          rfl)
      (by
        intro vs hEq
        cases hEq)
      (by
        intro vs hEq
        cases hEq)
      hInner
      hBaseClosed

theorem is_closed_rec_apply_apply_apply_set_insert_eq_and_bool_of_has_smt_translation
    (root : Term)
    {xs base z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hXsLt : sizeOf xs < sizeOf root)
    (hBaseLt : sizeOf base < sizeOf root)
    (hZLt : sizeOf z < sizeOf root)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) base)
          z))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) base)
        z) env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) base)
        z) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) base)
          z) env =
        Term.Boolean b :=
by
  have hTranslate :
      __eo_to_smt
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) base)
            z) =
        SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs)
              base))
          (__eo_to_smt z) := by
    rfl
  have hTy :
      __smtx_typeof
          (SmtTerm.Apply
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs)
                base))
            (__eo_to_smt z)) =
        __smtx_typeof_apply
          (__smtx_typeof
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs)
                base)))
          (__smtx_typeof (__eo_to_smt z)) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j h
        exact
          TranslationProofs.eo_to_smt_apply_ne_dt_sel
            _ _ s d i j h)
      (by
        intro s d i h
        exact
          TranslationProofs.eo_to_smt_apply_ne_dt_tester
            _ _ s d i h)
  have hNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs)
              base))
          (__eo_to_smt z)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans
  rcases apply_args_have_smt_translation_of_non_none hTy hNN with
    ⟨hHeadTrans, hZTrans⟩
  have hHeadClosed :
      __is_closed_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs)
            base) env =
        __eo_is_closed_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs)
            base) env ∧
        ∃ b,
          __eo_is_closed_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs)
              base) env =
            Term.Boolean b :=
    is_closed_rec_apply_apply_set_insert_eq_and_bool_of_has_smt_translation
      root hEnv hXsLt hBaseLt hHeadTrans ih
  exact
    is_closed_rec_apply_generic_eq_and_bool_of_parts
      hEnv
      (by
        intro q v vs hEq
        cases hEq
        exact
          false_of_apply_apply_apply_set_insert_middle_list_has_smt_translation
            hTrans)
      (by
        intro vs hEq
        cases hEq)
      (by
        intro vs hEq
        cases hEq)
      hHeadClosed
      (ih hZLt hEnv hZTrans)

theorem is_closed_rec_apply_is_eq_and_bool_of_has_smt_translation
    {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp1 UserOp1.is idx) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp1 UserOp1.is idx) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp1 UserOp1.is idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp1 UserOp1.is idx) x) env =
        Term.Boolean b :=
by
  rcases is_index_cons_and_arg_has_smt_translation hTrans with
    ⟨⟨s, d, i, hCons⟩, hXTrans⟩
  exact
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_eo_to_smt_eq_dt_cons hEnv hCons)
      (ihX hXTrans)

theorem false_of_apply_uop1_translate_apply_none {P : Prop}
    {op : UserOp1} {idx x : Term}
    (hTrans : eoHasSmtTranslation (Term.Apply (Term.UOp1 op idx) x))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.UOp1 op idx) x) =
        SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) : P :=
by
  exfalso
  unfold eoHasSmtTranslation at hTrans
  rw [hTranslate] at hTrans
  exact hTrans (TranslationProofs.typeof_apply_none_eq (__eo_to_smt x))

theorem false_of_apply_seq_empty {P : Prop} {idx x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.seq_empty idx) x)) : P :=
by
  exfalso
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt_seq_empty (__eo_to_smt_type idx))
            (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  exact hTrans
    (TranslationProofs.typeof_apply_eo_to_smt_seq_empty_eq_none
      (__eo_to_smt_type idx) (__eo_to_smt x))

theorem false_of_apply_set_empty {P : Prop} {idx x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.set_empty idx) x)) : P :=
by
  exfalso
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt_set_empty (__eo_to_smt_type idx))
            (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  exact hTrans
    (TranslationProofs.typeof_apply_eo_to_smt_set_empty_eq_none
      (__eo_to_smt_type idx) (__eo_to_smt x))

theorem apply_uop1_arg_has_smt_translation_of_has_smt_translation
    {op : UserOp1} {idx x : Term}
    (hTrans : eoHasSmtTranslation (Term.Apply (Term.UOp1 op idx) x)) :
  eoHasSmtTranslation x :=
by
  cases op
  case «repeat» =>
    exact (repeat_index_nat_valid_and_arg_has_smt_translation hTrans).2
  case zero_extend =>
    exact (zero_extend_index_nat_valid_and_arg_has_smt_translation hTrans).2
  case sign_extend =>
    exact (sign_extend_index_nat_valid_and_arg_has_smt_translation hTrans).2
  case rotate_left =>
    exact (rotate_left_index_nat_valid_and_arg_has_smt_translation hTrans).2
  case rotate_right =>
    exact (rotate_right_index_nat_valid_and_arg_has_smt_translation hTrans).2
  case _at_bit =>
    exact (at_bit_index_nat_valid_and_arg_has_smt_translation hTrans).2
  case re_exp =>
    exact (re_exp_index_nat_valid_and_arg_has_smt_translation hTrans).2
  case is =>
    exact (is_index_cons_and_arg_has_smt_translation hTrans).2
  case tuple_select =>
    exact (tuple_select_index_nat_valid_and_arg_has_smt_translation hTrans).2
  case int_to_bv =>
    exact (int_to_bv_index_nat_valid_and_arg_has_smt_translation hTrans).2
  case seq_empty =>
    exact false_of_apply_seq_empty hTrans
  case set_empty =>
    exact false_of_apply_set_empty hTrans
  all_goals
    exact false_of_apply_uop1_translate_apply_none hTrans rfl

theorem false_of_apply_apply_uop1_raw_list_has_smt_translation
    {P : Prop} {op : UserOp1} {idx v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp1 op idx)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  P :=
by
  exfalso
  by_cases hUpdate : op = UserOp1.update
  · subst op
    rcases update_index_sel_and_args_have_smt_translation hTrans with
      ⟨_hIdx, hRawTrans, _hBodyTrans⟩
    exact term_not_eo_list_cons_of_has_smt_translation hRawTrans v vs rfl
  by_cases hTupleUpdate : op = UserOp1.tuple_update
  · subst op
    rcases tuple_update_index_nat_valid_and_args_have_smt_translation
        hTrans with
      ⟨_hIdx, hRawTrans, _hBodyTrans⟩
    exact term_not_eo_list_cons_of_has_smt_translation hRawTrans v vs rfl
  have hTranslate :
      __eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp1 op idx)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            body) =
        SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.UOp1 op idx)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
          (__eo_to_smt body) := by
    cases op <;> try rfl
    · exact False.elim (hUpdate rfl)
    · exact False.elim (hTupleUpdate rfl)
  have hTy :
      __smtx_typeof
          (SmtTerm.Apply
            (__eo_to_smt
              (Term.Apply (Term.UOp1 op idx)
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            (__eo_to_smt body)) =
        __smtx_typeof_apply
          (__smtx_typeof
            (__eo_to_smt
              (Term.Apply (Term.UOp1 op idx)
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))))
          (__smtx_typeof (__eo_to_smt body)) := by
    exact
      generic_apply_type_of_non_special_head_closed _ _
        (by
          intro s d i j h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_sel
              _ _ s d i j h)
        (by
          intro s d i h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_tester
              _ _ s d i h)
  have hNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.UOp1 op idx)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
          (__eo_to_smt body)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans
  rcases apply_args_have_smt_translation_of_non_none hTy hNN with
    ⟨hHeadTrans, _hBodyTrans⟩
  have hRawTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) :=
    apply_uop1_arg_has_smt_translation_of_has_smt_translation hHeadTrans
  exact term_not_eo_list_cons_of_has_smt_translation hRawTrans v vs rfl

theorem false_of_apply_apply_apply_uop1_middle_raw_list_has_smt_translation
    {P : Prop} {op : UserOp1} {idx x v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp1 op idx) x)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  P :=
by
  exfalso
  by_cases hUpdate : op = UserOp1.update
  · subst op
    have hTranslate :
        __eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp1 UserOp1.update idx) x)
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
              body) =
          SmtTerm.Apply
            (__eo_to_smt
              (Term.Apply
                (Term.Apply (Term.UOp1 UserOp1.update idx) x)
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            (__eo_to_smt body) := by
      rfl
    have hTy :
        __smtx_typeof
            (SmtTerm.Apply
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp1 UserOp1.update idx) x)
                  (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
              (__eo_to_smt body)) =
          __smtx_typeof_apply
            (__smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp1 UserOp1.update idx) x)
                  (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))))
            (__smtx_typeof (__eo_to_smt body)) :=
      generic_apply_type_of_non_special_head_closed _ _
        (by
          intro s d i j h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_sel
              _ _ s d i j h)
        (by
          intro s d i h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_tester
              _ _ s d i h)
    have hNN :
        term_has_non_none_type
          (SmtTerm.Apply
            (__eo_to_smt
              (Term.Apply
                (Term.Apply (Term.UOp1 UserOp1.update idx) x)
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            (__eo_to_smt body)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hTrans
    rcases apply_args_have_smt_translation_of_non_none hTy hNN with
      ⟨hHeadTrans, _hBodyTrans⟩
    rcases update_index_sel_and_args_have_smt_translation hHeadTrans with
      ⟨_hIdx, _hXTrans, hRawTrans⟩
    exact term_not_eo_list_cons_of_has_smt_translation hRawTrans v vs rfl
  by_cases hTupleUpdate : op = UserOp1.tuple_update
  · subst op
    have hTranslate :
        __eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x)
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
              body) =
          SmtTerm.Apply
            (__eo_to_smt
              (Term.Apply
                (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x)
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            (__eo_to_smt body) := by
      rfl
    have hTy :
        __smtx_typeof
            (SmtTerm.Apply
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x)
                  (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
              (__eo_to_smt body)) =
          __smtx_typeof_apply
            (__smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x)
                  (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))))
            (__smtx_typeof (__eo_to_smt body)) :=
      generic_apply_type_of_non_special_head_closed _ _
        (by
          intro s d i j h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_sel
              _ _ s d i j h)
        (by
          intro s d i h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_tester
              _ _ s d i h)
    have hNN :
        term_has_non_none_type
          (SmtTerm.Apply
            (__eo_to_smt
              (Term.Apply
                (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x)
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            (__eo_to_smt body)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hTrans
    rcases apply_args_have_smt_translation_of_non_none hTy hNN with
      ⟨hHeadTrans, _hBodyTrans⟩
    rcases tuple_update_index_nat_valid_and_args_have_smt_translation
        hHeadTrans with
      ⟨_hIdx, _hXTrans, hRawTrans⟩
    exact term_not_eo_list_cons_of_has_smt_translation hRawTrans v vs rfl
  exact
    false_of_apply_apply_generic_raw_list_has_smt_translation
      (q := Term.Apply (Term.UOp1 op idx) x)
      (body := body)
      (by
        cases op
        case update =>
          exact False.elim (hUpdate rfl)
        case tuple_update =>
          exact False.elim (hTupleUpdate rfl)
        all_goals rfl)
      (by
        cases op <;> rfl)
      (generic_apply_type_of_non_special_head_closed _ _
        (by
          intro s d i j h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_sel
              _ _ s d i j h)
        (by
          intro s d i h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_tester
              _ _ s d i h))
      hTrans

theorem is_closed_rec_apply_uop1_any_eq_and_bool_of_has_smt_translation
    (root : Term)
    {op : UserOp1} {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hLt : sizeOf x < sizeOf root)
    (hTrans : eoHasSmtTranslation (Term.Apply (Term.UOp1 op idx) x))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp1 op idx) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp1 op idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp1 op idx) x) env =
        Term.Boolean b :=
by
  cases op
  case «repeat» =>
    exact
      is_closed_rec_apply_repeat_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case zero_extend =>
    exact
      is_closed_rec_apply_zero_extend_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case sign_extend =>
    exact
      is_closed_rec_apply_sign_extend_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case rotate_left =>
    exact
      is_closed_rec_apply_rotate_left_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case rotate_right =>
    exact
      is_closed_rec_apply_rotate_right_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case _at_bit =>
    exact
      is_closed_rec_apply_at_bit_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case re_exp =>
    exact
      is_closed_rec_apply_re_exp_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case is =>
    exact
      is_closed_rec_apply_is_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case tuple_select =>
    exact
      is_closed_rec_apply_tuple_select_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case int_to_bv =>
    exact
      is_closed_rec_apply_int_to_bv_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case seq_empty =>
    exact false_of_apply_seq_empty hTrans
  case set_empty =>
    exact false_of_apply_set_empty hTrans
  all_goals
    exact false_of_apply_uop1_translate_apply_none hTrans rfl

theorem is_closed_rec_apply_apply_update_eq_and_bool_of_has_smt_translation
    {idx x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) x) y)
      env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) x) y)
          env =
        Term.Boolean b :=
by
  rcases update_index_sel_and_args_have_smt_translation hTrans with
    ⟨⟨s, d, i, j, hSel⟩, hXTrans, hYTrans⟩
  have hInner :
      __is_closed_rec (Term.Apply (Term.UOp1 UserOp1.update idx) x)
          env =
        __eo_is_closed_rec (Term.Apply (Term.UOp1 UserOp1.update idx) x)
          env ∧
        ∃ b,
          __eo_is_closed_rec
              (Term.Apply (Term.UOp1 UserOp1.update idx) x) env =
            Term.Boolean b :=
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_eo_to_smt_eq_dt_sel hEnv hSel)
      (ihX hXTrans)
  exact
    is_closed_rec_apply_generic_eq_and_bool_of_parts
      hEnv
      (by
        intro q v vs hEq
        have hXEq :
            x = Term.Apply (Term.Apply Term.__eo_List_cons v) vs := by
          injection hEq
        exact term_not_eo_list_cons_of_has_smt_translation hXTrans v vs
          hXEq)
      (by
        intro vs hEq
        cases hEq)
      (by
        intro vs hEq
        cases hEq)
      hInner
      (ihY hYTrans)

theorem is_closed_rec_apply_apply_tuple_update_eq_and_bool_of_has_smt_translation
    {idx x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y)
      env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x)
            y)
          env =
        Term.Boolean b :=
by
  rcases tuple_update_index_nat_valid_and_args_have_smt_translation
      hTrans with
    ⟨hIdxValid, hXTrans, hYTrans⟩
  have hInner :
      __is_closed_rec (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x)
          env =
        __eo_is_closed_rec
          (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) env ∧
        ∃ b,
          __eo_is_closed_rec
              (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) env =
            Term.Boolean b :=
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hIdxValid)
      (ihX hXTrans)
  exact
    is_closed_rec_apply_generic_eq_and_bool_of_parts
      hEnv
      (by
        intro q v vs hEq
        have hXEq :
            x = Term.Apply (Term.Apply Term.__eo_List_cons v) vs := by
          injection hEq
        exact term_not_eo_list_cons_of_has_smt_translation hXTrans v vs
          hXEq)
      (by
        intro vs hEq
        cases hEq)
      (by
        intro vs hEq
        cases hEq)
      hInner
      (ihY hYTrans)

theorem is_closed_rec_apply_apply_uop1_any_eq_and_bool_of_has_smt_translation
    (root : Term)
    {op : UserOp1} {idx x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) env =
        Term.Boolean b :=
by
  by_cases hUpdate : op = UserOp1.update
  · subst op
    exact
      is_closed_rec_apply_apply_update_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  by_cases hTupleUpdate : op = UserOp1.tuple_update
  · subst op
    exact
      is_closed_rec_apply_apply_tuple_update_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  have hTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) =
        SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.UOp1 op idx) x))
          (__eo_to_smt y) := by
    cases op <;> try rfl
    · exact False.elim (hUpdate rfl)
    · exact False.elim (hTupleUpdate rfl)
  have hTy :
      __smtx_typeof
          (SmtTerm.Apply
            (__eo_to_smt (Term.Apply (Term.UOp1 op idx) x))
            (__eo_to_smt y)) =
        __smtx_typeof_apply
          (__smtx_typeof
            (__eo_to_smt (Term.Apply (Term.UOp1 op idx) x)))
          (__smtx_typeof (__eo_to_smt y)) := by
    exact
      generic_apply_type_of_non_special_head_closed _ _
        (by
          intro s d i j h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_sel
              _ _ s d i j h)
        (by
          intro s d i h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_tester
              _ _ s d i h)
  have hNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.UOp1 op idx) x))
          (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans
  rcases apply_args_have_smt_translation_of_non_none hTy hNN with
    ⟨hHeadTrans, hYTrans⟩
  have hXTrans :
      eoHasSmtTranslation x :=
    apply_uop1_arg_has_smt_translation_of_has_smt_translation hHeadTrans
  exact
    is_closed_rec_apply_generic_eq_and_bool_of_parts
      hEnv
      (by
        intro q v vs hEq
        have hXEq :
            x = Term.Apply (Term.Apply Term.__eo_List_cons v) vs := by
          injection hEq
        exact
          term_not_eo_list_cons_of_has_smt_translation hXTrans v vs hXEq)
      (by
        intro vs hEq
        cases hEq)
      (by
        intro vs hEq
        cases hEq)
      (is_closed_rec_apply_uop1_any_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hHeadTrans ih)
      (ih hYLt hEnv hYTrans)

theorem is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_args
    {op : UserOp} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hXNotList :
      ∀ v vs,
        x ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
    (hYNotList :
      ∀ v vs,
        y ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
    (hX :
      __is_closed_rec x env = __eo_is_closed_rec x env ∧
        ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (hY :
      __is_closed_rec y env = __eo_is_closed_rec y env ∧
        ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (hZ :
      __is_closed_rec z env = __eo_is_closed_rec z env ∧
        ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
        env =
        Term.Boolean b :=
by
  have hHead1 :
      __is_closed_rec (Term.Apply (Term.UOp op) x) env =
        __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env ∧
        ∃ b,
          __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env =
            Term.Boolean b :=
    is_closed_rec_apply_uop_eq_and_bool_of_arg hEnv hX
  have hMidNotList :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) :=
  by
    intro q v vs hEq
    cases hEq
    exact hXNotList v vs rfl
  have hMidNotForall :
      ∀ vs,
        Term.Apply (Term.UOp op) x ≠
          Term.Apply (Term.UOp UserOp.forall) vs :=
  by
    intro vs hEq
    cases hEq
    exact hNotForall rfl
  have hMidNotExists :
      ∀ vs,
        Term.Apply (Term.UOp op) x ≠
          Term.Apply (Term.UOp UserOp.exists) vs :=
  by
    intro vs hEq
    cases hEq
    exact hNotExists rfl
  have hHead2 :
      __is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y)
          env =
        __eo_is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y)
          env ∧
        ∃ b,
          __eo_is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y)
            env =
            Term.Boolean b :=
    is_closed_rec_apply_generic_eq_and_bool_of_parts
      hEnv hMidNotList hMidNotForall hMidNotExists hHead1 hY
  have hOuterNotList :
      ∀ q v vs,
        Term.Apply (Term.Apply (Term.UOp op) x) y ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) :=
  by
    intro q v vs hEq
    cases hEq
    exact hYNotList v vs rfl
  have hOuterNotForall :
      ∀ vs,
        Term.Apply (Term.Apply (Term.UOp op) x) y ≠
          Term.Apply (Term.UOp UserOp.forall) vs :=
  by
    intro vs hEq
    cases hEq
  have hOuterNotExists :
      ∀ vs,
        Term.Apply (Term.Apply (Term.UOp op) x) y ≠
          Term.Apply (Term.UOp UserOp.exists) vs :=
  by
    intro vs hEq
    cases hEq
  exact
    is_closed_rec_apply_generic_eq_and_bool_of_parts
      hEnv hOuterNotList hOuterNotForall hOuterNotExists hHead2 hZ

theorem is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
    {op : UserOp} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hXTrans : eoHasSmtTranslation x)
    (hYTrans : eoHasSmtTranslation y)
    (hZTrans : eoHasSmtTranslation z)
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
        env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_args
      hEnv hNotForall hNotExists
      (term_not_eo_list_cons_of_has_smt_translation hXTrans)
      (term_not_eo_list_cons_of_has_smt_translation hYTrans)
      (ihX hXTrans) (ihY hYTrans) (ihZ hZTrans)

theorem is_closed_rec_apply_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_arg_trans
    {op : UserOp} {w z y x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hWTrans : eoHasSmtTranslation w)
    (hZTrans : eoHasSmtTranslation z)
    (hYTrans : eoHasSmtTranslation y)
    (hXTrans : eoHasSmtTranslation x)
    (ihW :
      eoHasSmtTranslation w ->
        __is_closed_rec w env = __eo_is_closed_rec w env ∧
          ∃ b, __eo_is_closed_rec w env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp op) w) z)
          y)
        x)
      env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp op) w) z)
          y)
        x)
      env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp op) w) z)
              y)
            x)
          env =
        Term.Boolean b :=
by
  have hHead :
      __is_closed_rec
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp op) w) z)
            y)
          env =
        __eo_is_closed_rec
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp op) w) z)
            y)
          env ∧
        ∃ b,
          __eo_is_closed_rec
              (Term.Apply
                (Term.Apply (Term.Apply (Term.UOp op) w) z)
                y)
              env =
            Term.Boolean b :=
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv hNotForall hNotExists hWTrans hZTrans hYTrans
      ihW ihZ ihY
  exact
    is_closed_rec_apply_generic_eq_and_bool_of_parts
      hEnv
      (by
        intro q v vs hEq
        cases hEq
        exact term_not_eo_list_cons_of_has_smt_translation hYTrans v vs rfl)
      (by intro vs hEq; cases hEq)
      (by intro vs hEq; cases hEq)
      hHead (ihX hXTrans)

theorem ite_args_have_smt_translation_of_has_smt_translation
    {c x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)) :
  eoHasSmtTranslation c ∧
    eoHasSmtTranslation x ∧
      eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt x) (__eo_to_smt y)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt x)
          (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hTrans
  rcases ite_args_of_non_none hNN with ⟨T, hC, hX, hY, hT⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hC (by simp),
    eo_has_smt_translation_of_smt_type_eq hX hT,
    eo_has_smt_translation_of_smt_type_eq hY hT⟩

theorem ite_args_have_smt_translation_of_non_none
    {c x y : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt x)
          (__eo_to_smt y))) :
  eoHasSmtTranslation c ∧
    eoHasSmtTranslation x ∧
      eoHasSmtTranslation y :=
by
  exact
    ite_args_have_smt_translation_of_has_smt_translation
      (by
        unfold eoHasSmtTranslation
        change
            __smtx_typeof
                (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt x)
                  (__eo_to_smt y)) ≠
              SmtType.None
        exact hNN)

theorem is_closed_rec_apply_apply_apply_ite_eq_and_bool_of_has_smt_translation
    {c x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y))
    (ihC :
      eoHasSmtTranslation c ->
        __is_closed_rec c env = __eo_is_closed_rec c env ∧
          ∃ b, __eo_is_closed_rec c env = Term.Boolean b)
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)
        env =
        Term.Boolean b :=
by
  rcases ite_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hCTrans, hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hCTrans hXTrans hYTrans ihC ihX ihY

theorem is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_args
    {op : UserOp} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hXNotList :
      ∀ v vs,
        x ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
    (hX :
      __is_closed_rec x env = __eo_is_closed_rec x env ∧
        ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (hY :
      __is_closed_rec y env = __eo_is_closed_rec y env ∧
        ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
    __eo_is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
        Term.Boolean b :=
by
  have hHead :
      __is_closed_rec (Term.Apply (Term.UOp op) x) env =
        __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env ∧
        ∃ b,
          __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env =
            Term.Boolean b :=
    is_closed_rec_apply_uop_eq_and_bool_of_arg hEnv hX
  have hOuterNotList :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) :=
  by
    intro q v vs hEq
    cases hEq
    exact hXNotList v vs rfl
  have hOuterNotForall :
      ∀ vs,
        Term.Apply (Term.UOp op) x ≠
          Term.Apply (Term.UOp UserOp.forall) vs :=
  by
    intro vs hEq
    cases hEq
    exact hNotForall rfl
  have hOuterNotExists :
      ∀ vs,
        Term.Apply (Term.UOp op) x ≠
          Term.Apply (Term.UOp UserOp.exists) vs :=
  by
    intro vs hEq
    cases hEq
    exact hNotExists rfl
  exact
    is_closed_rec_apply_generic_eq_and_bool_of_parts
      hEnv hOuterNotList hOuterNotForall hOuterNotExists hHead hY

theorem apply_apply_uop_arg_not_list_of_nonquantifier_has_smt_translation
    {op : UserOp} {x y : Term}
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x) y)) :
  ∀ v vs,
    x ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs :=
by
  intro v vs hX
  subst x
  unfold eoHasSmtTranslation at hTrans
  exact hTrans
    (smtx_typeof_uop_eo_list_cons_apply_eq_none
      hNotForall hNotExists v vs y)

theorem is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_args
    {op : UserOp} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x) y))
    (hX :
      __is_closed_rec x env = __eo_is_closed_rec x env ∧
        ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (hY :
      __is_closed_rec y env = __eo_is_closed_rec y env ∧
        ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
    __eo_is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_args
      hEnv hNotForall hNotExists
      (apply_apply_uop_arg_not_list_of_nonquantifier_has_smt_translation
        hNotForall hNotExists hTrans)
      hX hY

theorem is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
    {op : UserOp} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x) y))
    (hXTrans : eoHasSmtTranslation x)
    (hYTrans : eoHasSmtTranslation y)
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
    __eo_is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_args
      hEnv hNotForall hNotExists hTrans (ihX hXTrans) (ihY hYTrans)

theorem is_closed_rec_apply_purify_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp._at_purify) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp._at_purify) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp._at_purify) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp._at_purify) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (purify_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_bvredand_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.bvredand) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.bvredand) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.bvredand) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.bvredand) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (bvredand_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_bvredor_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.bvredor) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.bvredor) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.bvredor) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.bvredor) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (bvredor_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_ubv_to_int_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.ubv_to_int) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.ubv_to_int) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.ubv_to_int) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.ubv_to_int) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (ubv_to_int_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_sbv_to_int_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.sbv_to_int) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.sbv_to_int) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.sbv_to_int) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.sbv_to_int) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (sbv_to_int_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_bvsize_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp._at_bvsize) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp._at_bvsize) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp._at_bvsize) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp._at_bvsize) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (bvsize_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_int_ispow2_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.int_ispow2) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.int_ispow2) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.int_ispow2) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.int_ispow2) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (int_ispow2_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_int_div_by_zero_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (int_div_by_zero_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_mod_by_zero_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x)
      env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x)
        env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (mod_by_zero_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_qdiv_by_zero_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp._at_div_by_zero) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp._at_div_by_zero) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp._at_div_by_zero) x)
      env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp._at_div_by_zero) x)
        env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (qdiv_by_zero_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem false_of_apply_translate_apply_none {P : Prop}
    {op : UserOp} {x : Term}
    (hTrans : eoHasSmtTranslation (Term.Apply (Term.UOp op) x))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.UOp op) x) =
        SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) : P :=
by
  exfalso
  unfold eoHasSmtTranslation at hTrans
  rw [hTranslate] at hTrans
  exact hTrans (TranslationProofs.typeof_apply_none_eq (__eo_to_smt x))

theorem false_of_apply_re_allchar {P : Prop} {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.re_allchar) x)) : P :=
by
  exfalso
  unfold eoHasSmtTranslation at hTrans
  change
    __smtx_typeof (SmtTerm.Apply SmtTerm.re_allchar (__eo_to_smt x)) ≠
      SmtType.None at hTrans
  exact hTrans (by
    simp [__smtx_typeof, __smtx_typeof_apply, __smtx_typeof_guard,
      native_ite])

theorem false_of_apply_re_none {P : Prop} {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.re_none) x)) : P :=
by
  exfalso
  unfold eoHasSmtTranslation at hTrans
  change
    __smtx_typeof (SmtTerm.Apply SmtTerm.re_none (__eo_to_smt x)) ≠
      SmtType.None at hTrans
  exact hTrans (by
    simp [__smtx_typeof, __smtx_typeof_apply, __smtx_typeof_guard,
      native_ite])

theorem false_of_apply_re_all {P : Prop} {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.re_all) x)) : P :=
by
  exfalso
  unfold eoHasSmtTranslation at hTrans
  change
    __smtx_typeof (SmtTerm.Apply SmtTerm.re_all (__eo_to_smt x)) ≠
      SmtType.None at hTrans
  exact hTrans (by
    simp [__smtx_typeof, __smtx_typeof_apply, __smtx_typeof_guard,
      native_ite])

theorem false_of_apply_tuple_unit {P : Prop} {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.tuple_unit) x)) :
  P :=
by
  exfalso
  unfold eoHasSmtTranslation at hTrans
  change
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null))
            0)
          (__eo_to_smt x)) ≠
      SmtType.None at hTrans
  apply hTrans
  have hGeneric :
      generic_apply_type
        (SmtTerm.DtCons (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)) 0)
        (__eo_to_smt x) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric]
  simp [__eo_to_smt_tuple_decl,
    TranslationProofs.smtx_typeof_tuple_unit_translation]
  rfl

theorem strings_stoi_non_digit_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp UserOp._at_strings_stoi_non_digit) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change
      term_has_non_none_type
        (SmtTerm.str_indexof_re (__eo_to_smt x)
          (SmtTerm.re_comp
            (SmtTerm.re_range (SmtTerm.String (native_string_lit "0"))
              (SmtTerm.String (native_string_lit "9"))))
          (SmtTerm.Numeral 0)) at hNN
  rcases str_indexof_re_args_of_non_none hNN with
    ⟨hXTy, _hReTy, _hZeroTy⟩
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem is_closed_rec_apply_uop_any_eq_and_bool_of_has_smt_translation
    (root : Term)
    {op : UserOp} {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hLt : sizeOf x < sizeOf root)
    (hTrans : eoHasSmtTranslation (Term.Apply (Term.UOp op) x))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp op) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env =
        Term.Boolean b :=
by
  cases op
  case not =>
    exact
      is_closed_rec_apply_not_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case distinct =>
    exact
      is_closed_rec_apply_distinct_eq_and_bool_of_has_smt_translation
        root hEnv hLt hTrans ih
  case _at_purify =>
    exact
      is_closed_rec_apply_purify_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case to_real =>
    exact
      is_closed_rec_apply_to_real_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case to_int =>
    exact
      is_closed_rec_apply_to_int_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case is_int =>
    exact
      is_closed_rec_apply_is_int_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case abs =>
    exact
      is_closed_rec_apply_abs_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case __eoo_neg_2 =>
    exact
      is_closed_rec_apply_eoo_neg_2_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case int_pow2 =>
    exact
      is_closed_rec_apply_int_pow2_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case int_log2 =>
    exact
      is_closed_rec_apply_int_log2_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case int_ispow2 =>
    exact
      is_closed_rec_apply_int_ispow2_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case _at_int_div_by_zero =>
    exact
      is_closed_rec_apply_int_div_by_zero_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case _at_mod_by_zero =>
    exact
      is_closed_rec_apply_mod_by_zero_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case _at_div_by_zero =>
    exact
      is_closed_rec_apply_qdiv_by_zero_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case _at_bvsize =>
    exact
      is_closed_rec_apply_bvsize_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case bvnot =>
    exact
      is_closed_rec_apply_bvnot_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case bvneg =>
    exact
      is_closed_rec_apply_bvneg_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case bvnego =>
    exact
      is_closed_rec_apply_bvnego_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case bvredand =>
    exact
      is_closed_rec_apply_bvredand_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case bvredor =>
    exact
      is_closed_rec_apply_bvredor_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case str_len =>
    exact
      is_closed_rec_apply_str_len_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case str_rev =>
    exact
      is_closed_rec_apply_str_rev_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case str_to_lower =>
    exact
      is_closed_rec_apply_str_to_lower_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case str_to_upper =>
    exact
      is_closed_rec_apply_str_to_upper_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case str_to_code =>
    exact
      is_closed_rec_apply_str_to_code_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case str_from_code =>
    exact
      is_closed_rec_apply_str_from_code_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case str_is_digit =>
    exact
      is_closed_rec_apply_str_is_digit_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case str_to_int =>
    exact
      is_closed_rec_apply_str_to_int_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case str_from_int =>
    exact
      is_closed_rec_apply_str_from_int_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case _at_strings_stoi_non_digit =>
    exact
      is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
        hEnv
        (strings_stoi_non_digit_arg_has_smt_translation_of_has_smt_translation
          hTrans)
        (fun hx => ih hLt hEnv hx)
  case str_to_re =>
    exact
      is_closed_rec_apply_str_to_re_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case re_mult =>
    exact
      is_closed_rec_apply_re_mult_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case re_plus =>
    exact
      is_closed_rec_apply_re_plus_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case re_opt =>
    exact
      is_closed_rec_apply_re_opt_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case re_comp =>
    exact
      is_closed_rec_apply_re_comp_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case seq_unit =>
    exact
      is_closed_rec_apply_seq_unit_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case set_singleton =>
    exact
      is_closed_rec_apply_set_singleton_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case set_choose =>
    exact
      is_closed_rec_apply_set_choose_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case set_is_empty =>
    exact
      is_closed_rec_apply_set_is_empty_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case set_is_singleton =>
    exact
      is_closed_rec_apply_set_is_singleton_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case ubv_to_int =>
    exact
      is_closed_rec_apply_ubv_to_int_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case sbv_to_int =>
    exact
      is_closed_rec_apply_sbv_to_int_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hLt hEnv hx)
  case re_allchar =>
    exact false_of_apply_re_allchar hTrans
  case re_none =>
    exact false_of_apply_re_none hTrans
  case re_all =>
    exact false_of_apply_re_all hTrans
  case tuple_unit =>
    exact false_of_apply_tuple_unit hTrans
  all_goals
    exact false_of_apply_translate_apply_none hTrans rfl

theorem is_closed_rec_apply_apply_apply_bvite_eq_and_bool_of_has_smt_translation
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) x) y) z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) x) y) z)
        env =
        Term.Boolean b :=
by
  rcases bvite_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans, hZTrans⟩
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hXTrans hYTrans hZTrans ihX ihY ihZ

theorem is_closed_rec_apply_apply_bvultbv_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvultbv) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.bvultbv) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvultbv) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvultbv) x) y) env =
        Term.Boolean b :=
by
  rcases bvultbv_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_bvsltbv_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvsltbv) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.bvsltbv) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvsltbv) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvsltbv) x) y) env =
        Term.Boolean b :=
by
  rcases bvsltbv_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_from_bools_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x) y)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x) y)
        env =
        Term.Boolean b :=
by
  rcases from_bools_args_have_smt_translation_of_has_smt_translation hTrans
    with ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem bool_binop_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Bool)
          (native_ite (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.Bool)
            SmtType.Bool SmtType.None)
          SmtType.None)
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases bool_binop_args_bool_of_non_none hTy hNN with ⟨hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem and_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof (SmtTerm.and (__eo_to_smt x) (__eo_to_smt y)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.and (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hTrans
  exact bool_binop_args_have_smt_translation_of_non_none
    (typeof_and_eq (__eo_to_smt x) (__eo_to_smt y)) hNN

theorem or_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof (SmtTerm.or (__eo_to_smt x) (__eo_to_smt y)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.or (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hTrans
  exact bool_binop_args_have_smt_translation_of_non_none
    (typeof_or_eq (__eo_to_smt x) (__eo_to_smt y)) hNN

theorem imp_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof (SmtTerm.imp (__eo_to_smt x) (__eo_to_smt y)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.imp (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hTrans
  exact bool_binop_args_have_smt_translation_of_non_none
    (typeof_imp_eq (__eo_to_smt x) (__eo_to_smt y)) hNN

theorem xor_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof (SmtTerm.xor (__eo_to_smt x) (__eo_to_smt y)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.xor (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hTrans
  exact bool_binop_args_have_smt_translation_of_non_none
    (typeof_xor_eq (__eo_to_smt x) (__eo_to_smt y)) hNN

theorem eq_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  have hEqNN :
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) ≠
        SmtType.None := by
    change
        __smtx_typeof (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) ≠
          SmtType.None at hTrans
    rw [typeof_eq_eq] at hTrans
    exact hTrans
  unfold __smtx_typeof_eq __smtx_typeof_guard at hEqNN
  constructor
  · unfold eoHasSmtTranslation
    intro hX
    exact hEqNN (by simp [hX, native_ite, native_Teq])
  · unfold eoHasSmtTranslation
    intro hY
    cases hX : __smtx_typeof (__eo_to_smt x) <;>
      simp [hX, hY, native_ite, native_Teq] at hEqNN

theorem is_closed_rec_apply_apply_and_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y) env =
        Term.Boolean b :=
by
  rcases and_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_or_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y) env =
        Term.Boolean b :=
by
  rcases or_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_imp_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y) env =
        Term.Boolean b :=
by
  rcases imp_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_xor_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y) env =
        Term.Boolean b :=
by
  rcases xor_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_eq_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) env =
        Term.Boolean b :=
by
  rcases eq_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {x y : Term}
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hArgs :
      term_has_non_none_type (smtOp (__eo_to_smt x) (__eo_to_smt y)) ->
        eoHasSmtTranslation x ∧ eoHasSmtTranslation y)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp eoOp) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  have hNN :
      term_has_non_none_type (smtOp (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans
  exact hArgs hNN

theorem is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hArgs :
      term_has_non_none_type (smtOp (__eo_to_smt x) (__eo_to_smt y)) ->
        eoHasSmtTranslation x ∧ eoHasSmtTranslation y)
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  rcases
      apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
        hTranslate hArgs hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv hNotForall hNotExists hTrans hXTrans hYTrans ihX ihY

theorem apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
    {eoOp : UserOp}
    {smtOp : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm}
    {x y z : Term}
    (hTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z) =
        smtOp (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z))
    (hArgs :
      term_has_non_none_type
          (smtOp (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z)) ->
        eoHasSmtTranslation x ∧
          eoHasSmtTranslation y ∧
            eoHasSmtTranslation z)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  unfold eoHasSmtTranslation at hTrans
  have hNN :
      term_has_non_none_type
        (smtOp (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans
  exact hArgs hNN

theorem is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_triop_non_none
    {eoOp : UserOp}
    {smtOp : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm}
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z))
    (hTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z) =
        smtOp (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z))
    (hArgs :
      term_has_non_none_type
          (smtOp (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z)) ->
        eoHasSmtTranslation x ∧
          eoHasSmtTranslation y ∧
            eoHasSmtTranslation z)
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
        env =
        Term.Boolean b :=
by
  rcases
      apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
        hTranslate hArgs hTrans with
    ⟨hXTrans, hYTrans, hZTrans⟩
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv hNotForall hNotExists hXTrans hYTrans hZTrans ihX ihY ihZ

theorem arith_binop_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_arith_overload_op_2
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)))
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases arith_binop_args_of_non_none hTy hNN with hArgs | hArgs
  · exact ⟨eo_has_smt_translation_of_smt_type_eq hArgs.1 (by simp),
      eo_has_smt_translation_of_smt_type_eq hArgs.2 (by simp)⟩
  · exact ⟨eo_has_smt_translation_of_smt_type_eq hArgs.1 (by simp),
      eo_has_smt_translation_of_smt_type_eq hArgs.2 (by simp)⟩

theorem arith_binop_ret_bool_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_arith_overload_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) SmtType.Bool)
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases arith_binop_ret_bool_args_of_non_none hTy hNN with hArgs | hArgs
  · exact ⟨eo_has_smt_translation_of_smt_type_eq hArgs.1 (by simp),
      eo_has_smt_translation_of_smt_type_eq hArgs.2 (by simp)⟩
  · exact ⟨eo_has_smt_translation_of_smt_type_eq hArgs.1 (by simp),
      eo_has_smt_translation_of_smt_type_eq hArgs.2 (by simp)⟩

theorem arith_binop_ret_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {ret : SmtType} {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_arith_overload_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) ret)
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases arith_binop_ret_args_of_non_none hTy hNN with hArgs | hArgs
  · exact ⟨eo_has_smt_translation_of_smt_type_eq hArgs.1 (by simp),
      eo_has_smt_translation_of_smt_type_eq hArgs.2 (by simp)⟩
  · exact ⟨eo_has_smt_translation_of_smt_type_eq hArgs.1 (by simp),
      eo_has_smt_translation_of_smt_type_eq hArgs.2 (by simp)⟩

theorem int_binop_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {ret : SmtType} {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Int)
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.Int)
            ret SmtType.None)
          SmtType.None)
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases int_binop_args_of_non_none (op := op) (R := ret) hTy hNN with
    ⟨hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem map_type_components_non_none_of_eo_type_eq
    {x : Term} {A B : SmtType}
    (hTy : __smtx_typeof (__eo_to_smt x) = SmtType.Map A B) :
  A ≠ SmtType.None ∧ B ≠ SmtType.None :=
by
  have hNN : term_has_non_none_type (__eo_to_smt x) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hNoNone :
      type_has_no_none_components (__smtx_typeof (__eo_to_smt x)) :=
    term_type_has_no_none_components_of_non_none (__eo_to_smt x) hNN
  have hMapNoNone : type_has_no_none_components (SmtType.Map A B) := by
    simpa [hTy] using hNoNone
  exact ⟨type_has_no_none_components_non_none hMapNoNone.1,
    type_has_no_none_components_non_none hMapNoNone.2⟩

theorem select_args_have_smt_translation_of_non_none
    {x y : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.select (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases select_args_of_non_none hNN with ⟨A, B, hXTy, hYTy⟩
  have hComponents :
      A ≠ SmtType.None ∧ B ≠ SmtType.None :=
    map_type_components_non_none_of_eo_type_eq hXTy
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy hComponents.1⟩

theorem store_args_have_smt_translation_of_non_none
    {x y z : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.store (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt z))) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  rcases store_args_of_non_none hNN with
    ⟨A, B, hXTy, hYTy, hZTy⟩
  have hComponents :
      A ≠ SmtType.None ∧ B ≠ SmtType.None :=
    map_type_components_non_none_of_eo_type_eq hXTy
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy hComponents.1,
    eo_has_smt_translation_of_smt_type_eq hZTy hComponents.2⟩

theorem set_type_component_non_none_of_eo_type_eq
    {x : Term} {A : SmtType}
    (hTy : __smtx_typeof (__eo_to_smt x) = SmtType.Set A) :
  A ≠ SmtType.None :=
by
  have hNN : term_has_non_none_type (__eo_to_smt x) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hNoNone :
      type_has_no_none_components (__smtx_typeof (__eo_to_smt x)) :=
    term_type_has_no_none_components_of_non_none (__eo_to_smt x) hNN
  have hSetNoNone : type_has_no_none_components (SmtType.Set A) := by
    simpa [hTy] using hNoNone
  exact type_has_no_none_components_non_none hSetNoNone

theorem seq_binop_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_seq_op_2
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)))
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases seq_binop_args_of_non_none (op := op) hTy hNN with
    ⟨T, hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem seq_binop_ret_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {ret : SmtType}
    {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_seq_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) ret)
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases seq_binop_args_of_non_none_ret (op := op) (R := ret) hTy hNN with
    ⟨T, hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem seq_triop_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm} {x y z : Term}
    (hTy :
      __smtx_typeof
          (op (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z)) =
        __smtx_typeof_seq_op_3
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y))
          (__smtx_typeof (__eo_to_smt z)))
    (hNN :
      term_has_non_none_type
        (op (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z))) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  rcases seq_triop_args_of_non_none (op := op) hTy hNN with
    ⟨T, hXTy, hYTy, hZTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hZTy (by simp)⟩

theorem seq_nth_args_have_smt_translation_of_non_none
    {x y : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.seq_nth (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases seq_nth_args_of_non_none hNN with ⟨T, hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem str_substr_args_have_smt_translation_of_non_none
    {x y z : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.str_substr (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt z))) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  rcases str_substr_args_of_non_none hNN with ⟨T, hXTy, hYTy, hZTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hZTy (by simp)⟩

theorem str_indexof_args_have_smt_translation_of_non_none
    {x y z : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.str_indexof (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt z))) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  rcases str_indexof_args_of_non_none hNN with
    ⟨T, hXTy, hYTy, hZTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hZTy (by simp)⟩

theorem str_at_args_have_smt_translation_of_non_none
    {x y : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.str_at (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases str_at_args_of_non_none hNN with ⟨T, hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem str_update_args_have_smt_translation_of_non_none
    {x y z : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.str_update (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt z))) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  rcases str_update_args_of_non_none hNN with ⟨T, hXTy, hYTy, hZTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hZTy (by simp)⟩

theorem reglan_binop_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.RegLan)
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.RegLan)
            SmtType.RegLan SmtType.None)
          SmtType.None)
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases reglan_binop_args_of_non_none (op := op) hTy hNN with
    ⟨hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem seq_char_binop_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {ret : SmtType}
    {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x))
            (SmtType.Seq SmtType.Char))
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y))
              (SmtType.Seq SmtType.Char))
            ret SmtType.None)
          SmtType.None)
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases seq_char_binop_args_of_non_none (op := op) (ret := ret) hTy hNN with
    ⟨hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem seq_char_reglan_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {ret : SmtType}
    {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x))
            (SmtType.Seq SmtType.Char))
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.RegLan)
            ret SmtType.None)
          SmtType.None)
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases seq_char_reglan_args_of_non_none (op := op) (ret := ret) hTy hNN with
    ⟨hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem str_replace_re_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm} {x y z : Term}
    (hTy :
      __smtx_typeof
          (op (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x))
            (SmtType.Seq SmtType.Char))
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.RegLan)
            (native_ite
              (native_Teq (__smtx_typeof (__eo_to_smt z))
                (SmtType.Seq SmtType.Char))
              (SmtType.Seq SmtType.Char) SmtType.None)
            SmtType.None)
          SmtType.None)
    (hNN :
      term_has_non_none_type
        (op (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z))) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  rcases str_replace_re_args_of_non_none (op := op) hTy hNN with
    ⟨hXTy, hYTy, hZTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hZTy (by simp)⟩

theorem str_indexof_re_args_have_smt_translation_of_non_none
    {x y z : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.str_indexof_re (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt z))) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  rcases str_indexof_re_args_of_non_none hNN with
    ⟨hXTy, hYTy, hZTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hZTy (by simp)⟩

theorem str_indexof_re_split_args_have_smt_translation_of_non_none
    {x y z : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.str_indexof_re_split (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt z))) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  rcases str_indexof_re_split_args_of_non_none hNN with
    ⟨hXTy, hYTy, hZTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hZTy (by simp)⟩

theorem set_binop_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_sets_op_2
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)))
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases set_binop_args_of_non_none (op := op) hTy hNN with
    ⟨A, hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem set_binop_ret_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {ret : SmtType}
    {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_sets_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) ret)
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases set_binop_ret_args_of_non_none (op := op) (T := ret) hTy hNN with
    ⟨A, hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem set_member_args_have_smt_translation_of_non_none
    {x y : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.set_member (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases set_member_args_of_non_none hNN with ⟨A, hXTy, hYTy⟩
  have hANe : A ≠ SmtType.None :=
    set_type_component_non_none_of_eo_type_eq hYTy
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy hANe,
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem plus_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.plus) (smtOp := SmtTerm.plus) (by rfl)
      (fun hNN =>
        arith_binop_args_have_smt_translation_of_non_none
          (typeof_plus_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem neg_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.neg) (smtOp := SmtTerm.neg) (by rfl)
      (fun hNN =>
        arith_binop_args_have_smt_translation_of_non_none
          (typeof_neg_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem mult_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.mult) (smtOp := SmtTerm.mult) (by rfl)
      (fun hNN =>
        arith_binop_args_have_smt_translation_of_non_none
          (typeof_mult_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem lt_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.lt) (smtOp := SmtTerm.lt) (by rfl)
      (fun hNN =>
        arith_binop_ret_bool_args_have_smt_translation_of_non_none
          (typeof_lt_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem leq_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.leq) (smtOp := SmtTerm.leq) (by rfl)
      (fun hNN =>
        arith_binop_ret_bool_args_have_smt_translation_of_non_none
          (typeof_leq_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem gt_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.gt) (smtOp := SmtTerm.gt) (by rfl)
      (fun hNN =>
        arith_binop_ret_bool_args_have_smt_translation_of_non_none
          (typeof_gt_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem geq_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.geq) (smtOp := SmtTerm.geq) (by rfl)
      (fun hNN =>
        arith_binop_ret_bool_args_have_smt_translation_of_non_none
          (typeof_geq_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem div_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.div) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.div) (smtOp := SmtTerm.div) (by rfl)
      (fun hNN =>
        int_binop_args_have_smt_translation_of_non_none
          (typeof_div_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem mod_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.mod) (smtOp := SmtTerm.mod) (by rfl)
      (fun hNN =>
        int_binop_args_have_smt_translation_of_non_none
          (typeof_mod_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem div_total_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.div_total) (smtOp := SmtTerm.div_total) (by rfl)
      (fun hNN =>
        int_binop_args_have_smt_translation_of_non_none
          (typeof_div_total_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem mod_total_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.mod_total) (smtOp := SmtTerm.mod_total) (by rfl)
      (fun hNN =>
        int_binop_args_have_smt_translation_of_non_none
          (typeof_mod_total_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem divisible_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.divisible) (smtOp := SmtTerm.divisible) (by rfl)
      (fun hNN =>
        int_binop_args_have_smt_translation_of_non_none
          (typeof_divisible_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem qdiv_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.qdiv) (smtOp := SmtTerm.qdiv) (by rfl)
      (fun hNN =>
        arith_binop_ret_args_have_smt_translation_of_non_none
          (typeof_qdiv_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem qdiv_total_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.qdiv_total) (smtOp := SmtTerm.qdiv_total) (by rfl)
      (fun hNN =>
        arith_binop_ret_args_have_smt_translation_of_non_none
          (typeof_qdiv_total_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem array_deq_diff_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_array_deq_diff) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (__eo_to_smt_array_deq_diff (__eo_to_smt x)
            (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
            (__smtx_typeof (__eo_to_smt y))) ≠
        SmtType.None at hTrans
  cases hx : __smtx_typeof (__eo_to_smt x) with
  | Map A B =>
      cases hy : __smtx_typeof (__eo_to_smt y) with
      | Map C D =>
          exact
            ⟨eo_has_smt_translation_of_smt_type_eq hx (by simp),
              eo_has_smt_translation_of_smt_type_eq hy (by simp)⟩
      | _ =>
          exfalso
          exact hTrans (by
            simp [__eo_to_smt_array_deq_diff, hx, hy,
              TranslationProofs.smtx_typeof_none])
  | _ =>
      exfalso
      exact hTrans (by
        simp [__eo_to_smt_array_deq_diff, hx,
          TranslationProofs.smtx_typeof_none])

theorem sets_deq_diff_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_sets_deq_diff) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (__eo_to_smt_sets_deq_diff (__eo_to_smt x)
            (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
            (__smtx_typeof (__eo_to_smt y))) ≠
        SmtType.None at hTrans
  cases hx : __smtx_typeof (__eo_to_smt x) with
  | Set A =>
      cases hy : __smtx_typeof (__eo_to_smt y) with
      | Set B =>
          exact
            ⟨eo_has_smt_translation_of_smt_type_eq hx (by simp),
              eo_has_smt_translation_of_smt_type_eq hy (by simp)⟩
      | _ =>
          exfalso
          exact hTrans (by
            simp [__eo_to_smt_sets_deq_diff, hx, hy,
              TranslationProofs.smtx_typeof_none])
  | _ =>
      exfalso
      exact hTrans (by
        simp [__eo_to_smt_sets_deq_diff, hx,
          TranslationProofs.smtx_typeof_none])

theorem strings_deq_diff_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change
      term_has_non_none_type
        (SmtTerm.seq_diff (__eo_to_smt x) (__eo_to_smt y)) at hNN
  rcases seq_binop_args_of_non_none_ret (op := SmtTerm.seq_diff)
      (typeof_seq_diff_eq (__eo_to_smt x) (__eo_to_smt y)) hNN with ⟨A, hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem strings_stoi_result_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_strings_stoi_result) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  let zero := SmtTerm.Numeral 0
  let prefixTerm := SmtTerm.str_substr (__eo_to_smt x) zero (__eo_to_smt y)
  let parsed := SmtTerm.str_to_int prefixTerm
  let result :=
    SmtTerm.ite (SmtTerm.eq (__eo_to_smt y) zero) zero parsed
  change term_has_non_none_type result at hNN
  rcases ite_args_of_non_none hNN with
    ⟨T, _hCondTy, _hZeroTy, hParsedTy, hTNN⟩
  have hParsedNN : term_has_non_none_type parsed := by
    unfold term_has_non_none_type
    rw [hParsedTy]
    exact hTNN
  have hPrefixTy : __smtx_typeof prefixTerm = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_int)
      (typeof_str_to_int_eq prefixTerm) hParsedNN
  have hPrefixNN : term_has_non_none_type prefixTerm := by
    unfold term_has_non_none_type
    rw [hPrefixTy]
    simp
  rcases str_substr_args_of_non_none hPrefixNN with
    ⟨A, hXTy, _hZeroTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem strings_itos_result_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_strings_itos_result) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  let zero := SmtTerm.Numeral 0
  let fromInt := SmtTerm.str_from_int (__eo_to_smt x)
  let prefixTerm := SmtTerm.str_substr fromInt zero (__eo_to_smt y)
  let parsed := SmtTerm.str_to_int prefixTerm
  let result :=
    SmtTerm.ite (SmtTerm.eq (__eo_to_smt y) zero) zero parsed
  change term_has_non_none_type result at hNN
  rcases ite_args_of_non_none hNN with
    ⟨T, _hCondTy, _hZeroTy, hParsedTy, hTNN⟩
  have hParsedNN : term_has_non_none_type parsed := by
    unfold term_has_non_none_type
    rw [hParsedTy]
    exact hTNN
  have hPrefixTy : __smtx_typeof prefixTerm = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_int)
      (typeof_str_to_int_eq prefixTerm) hParsedNN
  have hPrefixNN : term_has_non_none_type prefixTerm := by
    unfold term_has_non_none_type
    rw [hPrefixTy]
    simp
  rcases str_substr_args_of_non_none hPrefixNN with
    ⟨A, hFromIntTy, _hZeroInt, hYTy⟩
  have hFromIntNN : term_has_non_none_type fromInt := by
    unfold term_has_non_none_type
    rw [hFromIntTy]
    simp
  have hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
    int_arg_of_non_none_ret (op := SmtTerm.str_from_int)
      (ret := SmtType.Seq SmtType.Char)
      (typeof_str_from_int_eq (__eo_to_smt x)) hFromIntNN
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem strings_num_occur_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  rw [TranslationProofs.eo_to_smt_strings_num_occur_eq] at hNN
  rcases
      TranslationProofs.smt_strings_num_occur_args_of_non_none
        (__eo_to_smt x) (__eo_to_smt y) hNN with
    ⟨T, hXTy, hYTy, _hResultTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem strings_num_occur_re_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_strings_num_occur_re) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  rw [TranslationProofs.eo_to_smt_strings_num_occur_re_eq] at hNN
  rcases
      TranslationProofs.smt_strings_num_occur_re_args_of_non_none
        (__eo_to_smt x) (__eo_to_smt y) hNN with
    ⟨hXTy, hYTy, _hResultTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem strings_occur_index_args_have_smt_translation_of_has_smt_translation
    {x y z : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_strings_occur_index) x) y)
          z)) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  rw [TranslationProofs.eo_to_smt_strings_occur_index_eq] at hNN
  rcases
      TranslationProofs.smt_strings_occur_index_args_of_non_none
        (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z) hNN with
    ⟨T, hXTy, hYTy, hZTy, _hResultTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hZTy (by simp)⟩

theorem strings_occur_index_re_args_have_smt_translation_of_has_smt_translation
    {x y z : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_strings_occur_index_re) x) y)
          z)) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  rw [TranslationProofs.eo_to_smt_strings_occur_index_re_eq] at hNN
  rcases
      TranslationProofs.smt_strings_occur_index_re_args_of_non_none
        (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z) hNN with
    ⟨hXTy, hYTy, hZTy, _hResultTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hZTy (by simp)⟩

theorem strings_replace_all_result_args_have_smt_translation_of_has_smt_translation
    {w z y x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.UOp UserOp._at_strings_replace_all_result) w)
              z)
            y)
          x)) :
  eoHasSmtTranslation w ∧
    eoHasSmtTranslation z ∧
      eoHasSmtTranslation y ∧
        eoHasSmtTranslation x :=
by
  let start :=
    SmtTerm._at_strings_occur_index
      (__eo_to_smt w) (__eo_to_smt z) (__eo_to_smt x)
  let suffix :=
    SmtTerm.str_substr (__eo_to_smt w) start
      (SmtTerm.str_len (__eo_to_smt w))
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  rw [TranslationProofs.eo_to_smt_strings_replace_all_result_eq] at hNN
  rcases
      seq_triop_args_of_non_none (op := SmtTerm.str_replace_all)
        (typeof_str_replace_all_eq suffix (__eo_to_smt z) (__eo_to_smt y))
        (by simpa [suffix] using hNN) with
    ⟨T, hSuffixTy, hZTy, hYTy⟩
  have hSuffixNN : term_has_non_none_type suffix := by
    unfold term_has_non_none_type
    rw [hSuffixTy]
    simp
  rcases str_substr_args_of_non_none (by simpa [suffix] using hSuffixNN) with
    ⟨U, hWTy, hStartTy, _hLengthTy⟩
  have hStartNN : term_has_non_none_type start := by
    unfold term_has_non_none_type
    rw [hStartTy]
    simp
  rcases
      TranslationProofs.smt_strings_occur_index_args_of_non_none
        (__eo_to_smt w) (__eo_to_smt z) (__eo_to_smt x)
        (by simpa [start] using hStartNN) with
    ⟨V, _hWFromStart, _hZFromStart, hXTy, _hStartResultTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hWTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hZTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hXTy (by simp)⟩

theorem strings_replace_re_all_result_args_have_smt_translation_of_has_smt_translation
    {w z y x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.UOp UserOp._at_strings_replace_re_all_result) w)
              z)
            y)
          x)) :
  eoHasSmtTranslation w ∧
    eoHasSmtTranslation z ∧
      eoHasSmtTranslation y ∧
        eoHasSmtTranslation x :=
by
  let start :=
    SmtTerm._at_strings_occur_index_re
      (__eo_to_smt w) (__eo_to_smt z) (__eo_to_smt x)
  let suffix :=
    SmtTerm.str_substr (__eo_to_smt w) start
      (SmtTerm.str_len (__eo_to_smt w))
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  rw [TranslationProofs.eo_to_smt_strings_replace_re_all_result_eq] at hNN
  have hArgs :=
    str_replace_re_args_of_non_none (op := SmtTerm.str_replace_re_all)
      (typeof_str_replace_re_all_eq suffix (__eo_to_smt z) (__eo_to_smt y))
      (by simpa [suffix] using hNN)
  have hSuffixNN : term_has_non_none_type suffix := by
    unfold term_has_non_none_type
    rw [hArgs.1]
    simp
  rcases str_substr_args_of_non_none (by simpa [suffix] using hSuffixNN) with
    ⟨T, hWTy, hStartTy, _hLengthTy⟩
  have hStartNN : term_has_non_none_type start := by
    unfold term_has_non_none_type
    rw [hStartTy]
    simp
  have hOccurArgs :=
    TranslationProofs.smt_strings_occur_index_re_args_of_non_none
      (__eo_to_smt w) (__eo_to_smt z) (__eo_to_smt x)
      (by simpa [start] using hStartNN)
  exact ⟨eo_has_smt_translation_of_smt_type_eq hWTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hArgs.2.1 (by simp),
    eo_has_smt_translation_of_smt_type_eq hArgs.2.2 (by simp),
    eo_has_smt_translation_of_smt_type_eq hOccurArgs.2.2.1 (by simp)⟩

theorem tuple_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  have hTop := hTrans
  unfold eoHasSmtTranslation at hTop
  rcases
      TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
        y x hTop with
    ⟨c, hTailTy⟩
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (__eo_to_smt_tuple_prepend (__eo_to_smt x)
            (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)) ≠
        SmtType.None at hTrans
  constructor
  · unfold eoHasSmtTranslation
    exact
      TranslationProofs.smtx_tuple_prepend_head_non_none_of_tail_tuple_type
        (__eo_to_smt y) (__eo_to_smt x)
        (__smtx_typeof (__eo_to_smt x)) c hTailTy hTrans
  · exact eo_has_smt_translation_of_smt_type_eq hTailTy (by simp)

theorem select_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.select) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.select) (smtOp := SmtTerm.select) (by rfl)
      select_args_have_smt_translation_of_non_none hTrans

theorem store_args_have_smt_translation_of_has_smt_translation
    {x y z : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) x) y)
          z)) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.store (__eo_to_smt x) (__eo_to_smt y)
            (__eo_to_smt z)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.store (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt z)) := by
    unfold term_has_non_none_type
    exact hTrans
  exact store_args_have_smt_translation_of_non_none hNN

theorem is_closed_rec_apply_apply_plus_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x) y) env =
        Term.Boolean b :=
by
  rcases plus_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_neg_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x) y) env =
        Term.Boolean b :=
by
  rcases neg_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_mult_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y) env =
        Term.Boolean b :=
by
  rcases mult_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_lt_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x) y) env =
        Term.Boolean b :=
by
  rcases lt_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_leq_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x) y) env =
        Term.Boolean b :=
by
  rcases leq_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_gt_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x) y) env =
        Term.Boolean b :=
by
  rcases gt_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_geq_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) y) env =
        Term.Boolean b :=
by
  rcases geq_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_div_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.div) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.div) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.div) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.div) x) y) env =
        Term.Boolean b :=
by
  rcases div_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_mod_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x) y) env =
        Term.Boolean b :=
by
  rcases mod_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_div_total_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x) y) env =
        Term.Boolean b :=
by
  rcases div_total_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_mod_total_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x) y) env =
        Term.Boolean b :=
by
  rcases mod_total_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_divisible_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x) y) env =
        Term.Boolean b :=
by
  rcases divisible_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_qdiv_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x) y) env =
        Term.Boolean b :=
by
  rcases qdiv_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_qdiv_total_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x) y) env =
        Term.Boolean b :=
by
  rcases qdiv_total_args_have_smt_translation_of_has_smt_translation
      hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_select_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.select) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.select) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.select) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.select) x) y) env =
        Term.Boolean b :=
by
  rcases select_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_array_deq_diff_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_array_deq_diff) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_array_deq_diff) x) y) env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_array_deq_diff) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_array_deq_diff) x) y) env =
        Term.Boolean b :=
by
  rcases array_deq_diff_args_have_smt_translation_of_has_smt_translation
      hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_apply_store_eq_and_bool_of_has_smt_translation
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) x) y)
          z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) x) y)
        z) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) x) y)
        z) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) x) y)
          z) env =
        Term.Boolean b :=
by
  rcases store_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans, hZTrans⟩
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hXTrans hYTrans hZTrans ihX ihY ihZ

theorem is_closed_rec_apply_apply_uop_seq_binop_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_seq_op_2
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)))
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        seq_binop_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem is_closed_rec_apply_apply_uop_seq_binop_ret_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {ret : SmtType} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_seq_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) ret)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        seq_binop_ret_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem is_closed_rec_apply_apply_seq_nth_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv (by decide) (by decide) hTrans (by rfl)
      seq_nth_args_have_smt_translation_of_non_none ihX ihY

theorem is_closed_rec_apply_apply_str_at_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv (by decide) (by decide) hTrans (by rfl)
      str_at_args_have_smt_translation_of_non_none ihX ihY

theorem is_closed_rec_apply_apply_uop_reglan_binop_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.RegLan)
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.RegLan)
            SmtType.RegLan SmtType.None)
          SmtType.None)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        reglan_binop_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem is_closed_rec_apply_apply_uop_seq_char_binop_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {ret : SmtType} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x))
            (SmtType.Seq SmtType.Char))
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y))
              (SmtType.Seq SmtType.Char))
            ret SmtType.None)
          SmtType.None)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        seq_char_binop_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem is_closed_rec_apply_apply_uop_seq_char_reglan_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {ret : SmtType} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x))
            (SmtType.Seq SmtType.Char))
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.RegLan)
            ret SmtType.None)
          SmtType.None)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        seq_char_reglan_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem is_closed_rec_apply_apply_uop_set_binop_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_sets_op_2
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)))
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        set_binop_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem is_closed_rec_apply_apply_uop_set_binop_ret_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {ret : SmtType} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_sets_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) ret)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        set_binop_ret_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem is_closed_rec_apply_apply_set_member_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv (by decide) (by decide) hTrans (by rfl)
      set_member_args_have_smt_translation_of_non_none ihX ihY

theorem is_closed_rec_apply_apply_str_concat_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_seq_binop_eq_and_bool_of_has_smt_translation
      hEnv (by decide) (by decide) (by rfl)
      (typeof_str_concat_eq (__eo_to_smt x) (__eo_to_smt y))
      hTrans ihX ihY

theorem is_closed_rec_apply_apply_str_contains_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_seq_binop_ret_eq_and_bool_of_has_smt_translation
      hEnv (by decide) (by decide) (by rfl)
      (typeof_str_contains_eq (__eo_to_smt x) (__eo_to_smt y))
      hTrans ihX ihY

theorem is_closed_rec_apply_apply_uop_seq_char_bool_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x))
            (SmtType.Seq SmtType.Char))
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y))
              (SmtType.Seq SmtType.Char))
            SmtType.Bool SmtType.None)
          SmtType.None)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_seq_char_binop_eq_and_bool_of_has_smt_translation
      hEnv hNotForall hNotExists hTranslate hTy hTrans ihX ihY

theorem is_closed_rec_apply_apply_str_prefixof_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_seq_binop_ret_eq_and_bool_of_has_smt_translation
      hEnv (by decide) (by decide) (by rfl)
      (typeof_str_prefixof_eq (__eo_to_smt x) (__eo_to_smt y))
      hTrans ihX ihY

theorem is_closed_rec_apply_apply_str_suffixof_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_seq_binop_ret_eq_and_bool_of_has_smt_translation
      hEnv (by decide) (by decide) (by rfl)
      (typeof_str_suffixof_eq (__eo_to_smt x) (__eo_to_smt y))
      hTrans ihX ihY

theorem is_closed_rec_apply_apply_str_lt_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_lt) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_lt) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_lt) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_lt) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_seq_char_bool_eq_and_bool_of_has_smt_translation
      hEnv (by decide) (by decide) (by rfl)
      (typeof_str_lt_eq (__eo_to_smt x) (__eo_to_smt y))
      hTrans ihX ihY

theorem is_closed_rec_apply_apply_str_leq_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_seq_char_bool_eq_and_bool_of_has_smt_translation
      hEnv (by decide) (by decide) (by rfl)
      (typeof_str_leq_eq (__eo_to_smt x) (__eo_to_smt y))
      hTrans ihX ihY

theorem is_closed_rec_apply_apply_re_range_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_seq_char_binop_eq_and_bool_of_has_smt_translation
      hEnv (by decide) (by decide) (by rfl)
      (typeof_re_range_eq (__eo_to_smt x) (__eo_to_smt y))
      hTrans ihX ihY

theorem is_closed_rec_apply_apply_re_concat_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_reglan_binop_eq_and_bool_of_has_smt_translation
      hEnv (by decide) (by decide) (by rfl)
      (typeof_re_concat_eq (__eo_to_smt x) (__eo_to_smt y))
      hTrans ihX ihY

theorem is_closed_rec_apply_apply_re_inter_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_reglan_binop_eq_and_bool_of_has_smt_translation
      hEnv (by decide) (by decide) (by rfl)
      (typeof_re_inter_eq (__eo_to_smt x) (__eo_to_smt y))
      hTrans ihX ihY

theorem is_closed_rec_apply_apply_re_union_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_reglan_binop_eq_and_bool_of_has_smt_translation
      hEnv (by decide) (by decide) (by rfl)
      (typeof_re_union_eq (__eo_to_smt x) (__eo_to_smt y))
      hTrans ihX ihY

theorem is_closed_rec_apply_apply_re_diff_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_reglan_binop_eq_and_bool_of_has_smt_translation
      hEnv (by decide) (by decide) (by rfl)
      (typeof_re_diff_eq (__eo_to_smt x) (__eo_to_smt y))
      hTrans ihX ihY

theorem is_closed_rec_apply_apply_str_in_re_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_seq_char_reglan_eq_and_bool_of_has_smt_translation
      hEnv (by decide) (by decide) (by rfl)
      (typeof_str_in_re_eq (__eo_to_smt x) (__eo_to_smt y))
      hTrans ihX ihY

theorem is_closed_rec_apply_apply_set_union_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_set_binop_eq_and_bool_of_has_smt_translation
      hEnv (by decide) (by decide) (by rfl)
      (typeof_set_union_eq (__eo_to_smt x) (__eo_to_smt y))
      hTrans ihX ihY

theorem is_closed_rec_apply_apply_set_inter_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_set_binop_eq_and_bool_of_has_smt_translation
      hEnv (by decide) (by decide) (by rfl)
      (typeof_set_inter_eq (__eo_to_smt x) (__eo_to_smt y))
      hTrans ihX ihY

theorem is_closed_rec_apply_apply_set_minus_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_set_binop_eq_and_bool_of_has_smt_translation
      hEnv (by decide) (by decide) (by rfl)
      (typeof_set_minus_eq (__eo_to_smt x) (__eo_to_smt y))
      hTrans ihX ihY

theorem is_closed_rec_apply_apply_set_subset_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_subset) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_subset) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_subset) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_subset) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_set_binop_ret_eq_and_bool_of_has_smt_translation
      hEnv (by decide) (by decide) (by rfl)
      (typeof_set_subset_eq (__eo_to_smt x) (__eo_to_smt y))
      hTrans ihX ihY

theorem is_closed_rec_apply_apply_sets_deq_diff_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_sets_deq_diff) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp._at_sets_deq_diff) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp._at_sets_deq_diff) x) y)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_sets_deq_diff) x) y) env =
        Term.Boolean b :=
by
  rcases sets_deq_diff_args_have_smt_translation_of_has_smt_translation
      hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_tuple_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y) env =
        Term.Boolean b :=
by
  rcases tuple_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_apply_uop_seq_triop_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp}
    {smtOp : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm}
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z) =
        smtOp (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z))
    (hTy :
      __smtx_typeof
          (smtOp (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z)) =
        __smtx_typeof_seq_op_3
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y))
          (__smtx_typeof (__eo_to_smt z)))
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
        env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_triop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        seq_triop_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY ihZ

theorem is_closed_rec_apply_apply_apply_str_replace_eq_and_bool_of_has_smt_translation
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) x) y) z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) x) y) z)
        env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_seq_triop_eq_and_bool_of_has_smt_translation
      hEnv (by decide) (by decide) (by rfl)
      (typeof_str_replace_eq (__eo_to_smt x) (__eo_to_smt y)
        (__eo_to_smt z))
      hTrans ihX ihY ihZ

theorem is_closed_rec_apply_apply_apply_str_substr_eq_and_bool_of_has_smt_translation
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) x) y) z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) x) y) z)
        env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_triop_non_none
      hEnv (by decide) (by decide) hTrans (by rfl)
      str_substr_args_have_smt_translation_of_non_none ihX ihY ihZ

theorem is_closed_rec_apply_apply_apply_str_indexof_eq_and_bool_of_has_smt_translation
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) x) y) z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) x) y) z)
        env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_triop_non_none
      hEnv (by decide) (by decide) hTrans (by rfl)
      str_indexof_args_have_smt_translation_of_non_none ihX ihY ihZ

theorem is_closed_rec_apply_apply_apply_str_update_eq_and_bool_of_has_smt_translation
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) x) y) z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) x) y) z)
        env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_triop_non_none
      hEnv (by decide) (by decide) hTrans (by rfl)
      str_update_args_have_smt_translation_of_non_none ihX ihY ihZ

theorem is_closed_rec_apply_apply_apply_str_replace_all_eq_and_bool_of_has_smt_translation
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) x) y)
          z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) x) y)
        z) env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) x) y)
        z) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) x) y)
          z) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_seq_triop_eq_and_bool_of_has_smt_translation
      hEnv (by decide) (by decide) (by rfl)
      (typeof_str_replace_all_eq (__eo_to_smt x) (__eo_to_smt y)
        (__eo_to_smt z))
      hTrans ihX ihY ihZ

theorem is_closed_rec_apply_apply_apply_uop_str_replace_re_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp}
    {smtOp : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm}
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z) =
        smtOp (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z))
    (hTy :
      __smtx_typeof
          (smtOp (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x))
            (SmtType.Seq SmtType.Char))
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.RegLan)
            (native_ite
              (native_Teq (__smtx_typeof (__eo_to_smt z))
                (SmtType.Seq SmtType.Char))
              (SmtType.Seq SmtType.Char) SmtType.None)
            SmtType.None)
          SmtType.None)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
        env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_triop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        str_replace_re_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY ihZ

theorem is_closed_rec_apply_apply_apply_str_replace_re_eq_and_bool_of_has_smt_translation
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) x) y)
          z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) x) y)
        z) env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) x) y)
        z) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) x) y)
          z) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_str_replace_re_eq_and_bool_of_has_smt_translation
      hEnv (by decide) (by decide) (by rfl)
      (typeof_str_replace_re_eq (__eo_to_smt x) (__eo_to_smt y)
        (__eo_to_smt z))
      hTrans ihX ihY ihZ

theorem is_closed_rec_apply_apply_apply_str_replace_re_all_eq_and_bool_of_has_smt_translation
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_replace_re_all) x) y) z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_replace_re_all) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_replace_re_all) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_replace_re_all) x) y) z)
        env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_str_replace_re_eq_and_bool_of_has_smt_translation
      hEnv (by decide) (by decide) (by rfl)
      (typeof_str_replace_re_all_eq (__eo_to_smt x) (__eo_to_smt y)
        (__eo_to_smt z))
      hTrans ihX ihY ihZ

theorem is_closed_rec_apply_apply_apply_str_indexof_re_eq_and_bool_of_has_smt_translation
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x) y)
          z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x) y)
        z) env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x) y)
        z) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x) y)
          z) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_triop_non_none
      hEnv (by decide) (by decide) hTrans (by rfl)
      str_indexof_re_args_have_smt_translation_of_non_none ihX ihY ihZ

theorem is_closed_rec_apply_apply_strings_deq_diff_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) x) y) env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) x) y) env =
        Term.Boolean b :=
by
  rcases strings_deq_diff_args_have_smt_translation_of_has_smt_translation
      hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_strings_stoi_result_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_strings_stoi_result) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_stoi_result) x) y) env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_stoi_result) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_strings_stoi_result) x) y) env =
        Term.Boolean b :=
by
  rcases strings_stoi_result_args_have_smt_translation_of_has_smt_translation
      hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_strings_stoi_non_digit_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp UserOp._at_strings_stoi_non_digit) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.UOp UserOp._at_strings_stoi_non_digit) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp UserOp._at_strings_stoi_non_digit) x) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.UOp UserOp._at_strings_stoi_non_digit) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (strings_stoi_non_digit_arg_has_smt_translation_of_has_smt_translation
        hTrans)
      ihX

theorem is_closed_rec_apply_apply_strings_itos_result_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_strings_itos_result) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_itos_result) x) y) env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_itos_result) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_strings_itos_result) x) y) env =
        Term.Boolean b :=
by
  rcases strings_itos_result_args_have_smt_translation_of_has_smt_translation
      hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_strings_num_occur_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x) y) env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x) y) env =
        Term.Boolean b :=
by
  rcases strings_num_occur_args_have_smt_translation_of_has_smt_translation
      hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_uop_arith_binop_ret_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {ret : SmtType} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_arith_overload_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) ret)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        arith_binop_ret_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem is_closed_rec_apply_apply_uop_int_binop_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {ret : SmtType} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Int)
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.Int)
            ret SmtType.None)
          SmtType.None)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        int_binop_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem bv_concat_args_have_smt_translation_of_non_none
    {x y : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases bv_concat_args_of_non_none hNN with ⟨w1, w2, hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem bv_binop_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_bv_op_2
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)))
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases bv_binop_args_of_non_none (op := op) hTy hNN with
    ⟨w, hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem bv_binop_ret_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {ret : SmtType} {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_bv_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) ret)
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases bv_binop_ret_args_of_non_none (op := op) (ret := ret) hTy hNN with
    ⟨w, hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem is_closed_rec_apply_apply_concat_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv (by decide) (by decide) hTrans (by rfl)
      bv_concat_args_have_smt_translation_of_non_none ihX ihY

theorem is_closed_rec_apply_apply_uop_bv_binop_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_bv_op_2
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)))
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        bv_binop_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem is_closed_rec_apply_apply_uop_bv_binop_ret_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {ret : SmtType} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_bv_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) ret)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        bv_binop_ret_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem eo_list_concat_nil_left_eq_of_env
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars) :
  __eo_list_concat Term.__eo_List_cons Term.__eo_List_nil env = env :=
by
  have hNilList :
      __eo_is_list Term.__eo_List_cons Term.__eo_List_nil =
        Term.Boolean true := by
    simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
      __eo_requires, __eo_is_ok, native_ite, native_teq, native_not]
  have hEnvList := hEnv.is_list
  cases hEnv <;>
    simp [__eo_list_concat, __eo_list_concat_rec, __eo_requires,
      hNilList, hEnvList, native_ite, native_teq, native_not]

/--
For quantifiers with an empty binder list, `__is_closed_rec` reaches the
generic application branch while `__eo_is_closed_rec` reaches its quantifier
branch. The extra head check is `true`, and concatenating the empty binder
list leaves the environment unchanged.
-/
theorem is_closed_rec_quantifier_nil_branch_eq_and_bool_of_body
    {op : UserOp} {env : Term} {vars : List SmtVarKey}
    (hOp : op = UserOp.forall ∨ op = UserOp.exists)
    (hEnv : EoSmtVarEnv env vars)
    (body : Term)
    (hBody :
      __is_closed_rec body env = __eo_is_closed_rec body env ∧
        ∃ b, __eo_is_closed_rec body env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp op) Term.__eo_List_nil) body)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp op) Term.__eo_List_nil) body)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp op) Term.__eo_List_nil) body)
        env =
      Term.Boolean b :=
by
  rcases hBody with ⟨hBodyEq, hBodyBool⟩
  rcases hBodyBool with ⟨b, hBodyBool⟩
  have hConcat := eo_list_concat_nil_left_eq_of_env hEnv
  rcases hOp with hForall | hExists
  · subst op
    refine ⟨?_, ?_⟩
    · cases hEnv <;>
        simp [__is_closed_rec, __eo_is_closed_rec, hBodyEq, hConcat,
          hBodyBool, __eo_and, native_and]
    · exact ⟨b, by
        cases hEnv <;> simpa [__eo_is_closed_rec, hConcat] using hBodyBool⟩
  · subst op
    refine ⟨?_, ?_⟩
    · cases hEnv <;>
        simp [__is_closed_rec, __eo_is_closed_rec, hBodyEq, hConcat,
          hBodyBool, __eo_and, native_and]
    · exact ⟨b, by
        cases hEnv <;> simpa [__eo_is_closed_rec, hConcat] using hBodyBool⟩

/--
The broad binder-list branch of `__is_closed_rec` agrees with
`__eo_is_closed_rec` for actual quantifier heads, once the recursive body result
is known to agree and to be boolean.
-/
theorem is_closed_rec_quantifier_list_branch_eq_of_body
    {op : UserOp} {env : Term} {vars : List SmtVarKey}
    (hOp : op = UserOp.forall ∨ op = UserOp.exists)
    (hEnv : EoSmtVarEnv env vars)
    (v vs body : Term)
    (hBodyEq :
      __is_closed_rec body
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env) =
        __eo_is_closed_rec body
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env))
    (hBodyBool :
      ∃ b,
        __eo_is_closed_rec body
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env) =
          Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp op)
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
        body)
      env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp op)
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
        body)
      env :=
by
  rcases hBodyBool with ⟨b, hBodyBool⟩
  rcases hOp with hForall | hExists
  · subst op
    cases hEnv with
    | nil =>
        simpa [__is_closed_rec, __eo_is_closed_rec, hBodyEq]
          using eo_and_true_left_eq_of_boolean hBodyBool
    | cons hTail =>
        rename_i s' T' env' vars'
        simpa [__is_closed_rec, __eo_is_closed_rec, hBodyEq]
          using eo_and_true_left_eq_of_boolean hBodyBool
  · subst op
    cases hEnv with
    | nil =>
        simpa [__is_closed_rec, __eo_is_closed_rec, hBodyEq]
          using eo_and_true_left_eq_of_boolean hBodyBool
    | cons hTail =>
        rename_i s' T' env' vars'
        simpa [__is_closed_rec, __eo_is_closed_rec, hBodyEq]
          using eo_and_true_left_eq_of_boolean hBodyBool

/--
SMT-translatability supplies the quantifier-head fact for the `UOp` binder-list
case; the remaining obligations are exactly the recursive body comparison in
the concatenated environment.
-/
theorem is_closed_rec_uop_list_branch_eq_of_has_smt_translation_and_body
    {op : UserOp} {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (hBodyEq :
      __is_closed_rec body
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env) =
        __eo_is_closed_rec body
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env))
    (hBodyBool :
      ∃ b,
        __eo_is_closed_rec body
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env) =
          Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp op)
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
        body)
      env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp op)
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
        body)
      env :=
by
  exact
    is_closed_rec_quantifier_list_branch_eq_of_body
      (is_closed_rec_uop_list_branch_head_quantifier_of_has_smt_translation
        hTrans)
      hEnv v vs body hBodyEq hBodyBool

theorem is_closed_rec_uop_list_branch_eq_and_bool_of_has_smt_translation_and_body
    {op : UserOp} {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (hBody :
      __is_closed_rec body
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env) =
        __eo_is_closed_rec body
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env) ∧
        ∃ b,
          __eo_is_closed_rec body
            (__eo_list_concat Term.__eo_List_cons
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env) =
            Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp op)
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
        body)
      env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp op)
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
        body)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)
        env =
      Term.Boolean b :=
by
  rcases hBody with ⟨hBodyEq, hBodyBool⟩
  refine ⟨
    is_closed_rec_uop_list_branch_eq_of_has_smt_translation_and_body
      hEnv hTrans hBodyEq hBodyBool,
    ?_⟩
  rcases hBodyBool with ⟨b, hBodyBool⟩
  rcases
    is_closed_rec_uop_list_branch_head_quantifier_of_has_smt_translation
      hTrans with hForall | hExists
  · subst op
    cases hEnv with
    | nil =>
        exact ⟨b, by simpa [__eo_is_closed_rec] using hBodyBool⟩
    | cons hTail =>
        exact ⟨b, by simpa [__eo_is_closed_rec] using hBodyBool⟩
  · subst op
    cases hEnv with
    | nil =>
        exact ⟨b, by simpa [__eo_is_closed_rec] using hBodyBool⟩
    | cons hTail =>
        exact ⟨b, by simpa [__eo_is_closed_rec] using hBodyBool⟩

theorem is_closed_rec_uop_list_branch_eq_and_bool_of_has_smt_translation
    {op : UserOp} {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (ihBody :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnv env' vars' ->
          eoHasSmtTranslation body ->
            __is_closed_rec body env' = __eo_is_closed_rec body env' ∧
              ∃ b, __eo_is_closed_rec body env' = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp op)
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
        body)
      env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp op)
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
        body)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)
        env =
      Term.Boolean b :=
by
  rcases body_obligations_of_uop_list_branch_has_smt_translation
      hEnv hTrans with
    ⟨hBodyTrans, ⟨vars', hBodyEnv⟩⟩
  exact
    is_closed_rec_uop_list_branch_eq_and_bool_of_has_smt_translation_and_body
      hEnv hTrans (ihBody hBodyEnv hBodyTrans)

theorem false_of_forall_non_list_has_smt_translation {P : Prop}
    {x body : Term}
    (hNotCons :
      ∀ v vs, x ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) x) body)) :
  P :=
by
  exfalso
  unfold eoHasSmtTranslation at hTrans
  cases x with
  | __eo_List_nil =>
      change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
      exact hTrans (by simp [__smtx_typeof, native_Teq, native_ite])
  | Apply f a =>
      cases f with
      | Apply g v =>
          cases g with
          | __eo_List_cons =>
              exact False.elim (hNotCons v a rfl)
          | _ =>
              change __smtx_typeof (SmtTerm.not SmtTerm.None) ≠
                SmtType.None at hTrans
              exact hTrans (by simp [__smtx_typeof, native_Teq, native_ite])
      | _ =>
          change __smtx_typeof (SmtTerm.not SmtTerm.None) ≠ SmtType.None
            at hTrans
          exact hTrans (by simp [__smtx_typeof, native_Teq, native_ite])
  | _ =>
      change __smtx_typeof (SmtTerm.not SmtTerm.None) ≠ SmtType.None at hTrans
      exact hTrans (by simp [__smtx_typeof, native_Teq, native_ite])

theorem false_of_exists_non_list_has_smt_translation {P : Prop}
    {x body : Term}
    (hNotCons :
      ∀ v vs, x ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.exists) x) body)) :
  P :=
by
  exfalso
  unfold eoHasSmtTranslation at hTrans
  cases x with
  | __eo_List_nil =>
      change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
      exact hTrans (by simp [__smtx_typeof, native_Teq, native_ite])
  | Apply f a =>
      cases f with
      | Apply g v =>
          cases g with
          | __eo_List_cons =>
              exact False.elim (hNotCons v a rfl)
          | _ =>
              change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
              exact hTrans (by simp [__smtx_typeof, native_Teq, native_ite])
      | _ =>
          change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
          exact hTrans (by simp [__smtx_typeof, native_Teq, native_ite])
  | _ =>
      change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
      exact hTrans (by simp [__smtx_typeof, native_Teq, native_ite])

theorem smtx_typeof_generic_apply_bool_or_none_head_eq_none
    (f x : SmtTerm)
    (hGeneric : generic_apply_type f x)
    (hHead :
      __smtx_typeof f = SmtType.Bool ∨
        __smtx_typeof f = SmtType.None) :
  __smtx_typeof (SmtTerm.Apply f x) = SmtType.None :=
by
  rw [hGeneric]
  rcases hHead with hBool | hNone
  · rw [hBool]
    simp [__smtx_typeof_apply]
  · rw [hNone]
    simp [__smtx_typeof_apply]

theorem smtx_typeof_not_bool_or_none_closed (t : SmtTerm) :
  __smtx_typeof (SmtTerm.not t) = SmtType.Bool ∨
    __smtx_typeof (SmtTerm.not t) = SmtType.None :=
by
  by_cases hNone : __smtx_typeof (SmtTerm.not t) = SmtType.None
  · exact Or.inr hNone
  · exact Or.inl (smtx_typeof_not_eq_bool_of_non_none t hNone)

theorem smtx_typeof_exists_bool_or_none_closed
    (s : native_String) (T : SmtType) (body : SmtTerm) :
  __smtx_typeof (SmtTerm.exists s T body) = SmtType.Bool ∨
    __smtx_typeof (SmtTerm.exists s T body) = SmtType.None :=
by
  by_cases hNone :
      __smtx_typeof (SmtTerm.exists s T body) = SmtType.None
  · exact Or.inr hNone
  · exact Or.inl (smtx_typeof_exists_eq_bool_of_non_none hNone)

theorem smtx_typeof_eo_to_smt_exists_top_bool_or_none_closed
    (body xs : Term) :
  __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body)) =
      SmtType.Bool ∨
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body)) =
      SmtType.None :=
by
  cases xs
  case __eo_List_nil =>
    right
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
  case Apply f tail =>
    cases f
    case Apply g head =>
      cases g
      case __eo_List_cons =>
        cases head
        case Var name T =>
          cases name
          case String s =>
            change
              __smtx_typeof
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists tail (__eo_to_smt body))) =
                  SmtType.Bool ∨
                __smtx_typeof
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists tail (__eo_to_smt body))) =
                  SmtType.None
            exact
              smtx_typeof_exists_bool_or_none_closed s
                (__eo_to_smt_type T)
                (__eo_to_smt_exists tail (__eo_to_smt body))
          all_goals
            right
            change __smtx_typeof SmtTerm.None = SmtType.None
            exact TranslationProofs.smtx_typeof_none
        all_goals
          right
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none
      all_goals
        right
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none
    all_goals
      right
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  all_goals
    right
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none

theorem smtx_typeof_eo_to_smt_forall_top_bool_or_none_closed
    (body xs : Term) :
  __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)) =
      SmtType.Bool ∨
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)) =
      SmtType.None :=
by
  cases xs
  case __eo_List_nil =>
    right
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
  all_goals
    change
      __smtx_typeof
          (SmtTerm.not
            (__eo_to_smt_exists _ (SmtTerm.not (__eo_to_smt body)))) =
          SmtType.Bool ∨
        __smtx_typeof
          (SmtTerm.not
            (__eo_to_smt_exists _ (SmtTerm.not (__eo_to_smt body)))) =
          SmtType.None
    exact
      smtx_typeof_not_bool_or_none_closed
        (__eo_to_smt_exists _ (SmtTerm.not (__eo_to_smt body)))

theorem false_of_apply_apply_apply_forall_has_smt_translation {P : Prop}
    {xs body z : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) z)) :
  P :=
by
  exfalso
  unfold eoHasSmtTranslation at hTrans
  apply hTrans
  change
    __smtx_typeof
        (SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body))
          (__eo_to_smt z)) =
      SmtType.None
  exact
    smtx_typeof_generic_apply_bool_or_none_head_eq_none _ _
      (generic_apply_type_of_non_special_head_closed _ _
        (by
          intro s d i j h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_sel
              _ _ s d i j h)
        (by
          intro s d i h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_tester
              _ _ s d i h))
      (smtx_typeof_eo_to_smt_forall_top_bool_or_none_closed body xs)

theorem false_of_apply_apply_apply_exists_has_smt_translation {P : Prop}
    {xs body z : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body) z)) :
  P :=
by
  exfalso
  unfold eoHasSmtTranslation at hTrans
  apply hTrans
  change
    __smtx_typeof
        (SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body))
          (__eo_to_smt z)) =
      SmtType.None
  exact
    smtx_typeof_generic_apply_bool_or_none_head_eq_none _ _
      (generic_apply_type_of_non_special_head_closed _ _
        (by
          intro s d i j h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_sel
              _ _ s d i j h)
        (by
          intro s d i h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_tester
              _ _ s d i h))
      (smtx_typeof_eo_to_smt_exists_top_bool_or_none_closed body xs)

theorem false_of_apply_apply_apply_uop_over_binary_middle_raw_list
    {P : Prop} {op : UserOp} {x v vs z : Term}
    (hRawTransOfHead :
      eoHasSmtTranslation
          (Term.Apply (Term.Apply (Term.UOp op) x)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) ->
        eoHasSmtTranslation
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hOuterTranslate :
      __eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp op) x)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            z) =
        SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp op) x)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
          (__eo_to_smt z))
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp op) x)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          z)) :
  P :=
by
  exfalso
  have hTy :
      __smtx_typeof
          (SmtTerm.Apply
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp op) x)
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            (__eo_to_smt z)) =
        __smtx_typeof_apply
          (__smtx_typeof
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp op) x)
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))))
          (__smtx_typeof (__eo_to_smt z)) := by
    exact
      generic_apply_type_of_non_special_head_closed _ _
        (by
          intro s d i j h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_sel
              _ _ s d i j h)
        (by
          intro s d i h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_tester
              _ _ s d i h)
  have hNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp op) x)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
          (__eo_to_smt z)) := by
    unfold term_has_non_none_type
    rw [← hOuterTranslate]
    exact hTrans
  rcases apply_args_have_smt_translation_of_non_none hTy hNN with
    ⟨hHeadTrans, _hZTrans⟩
  have hRawTrans :=
    hRawTransOfHead hHeadTrans
  exact term_not_eo_list_cons_of_has_smt_translation hRawTrans v vs rfl

theorem false_of_apply_apply_apply_uop_smt_triop_middle_raw_list
    {P : Prop} {eoOp : UserOp}
    {smtOp : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm}
    {x v vs z : Term}
    (hTranslate :
      __eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp eoOp) x)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            z) =
        smtOp (__eo_to_smt x)
          (__eo_to_smt (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          (__eo_to_smt z))
    (hArgs :
      term_has_non_none_type
          (smtOp (__eo_to_smt x)
            (__eo_to_smt (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            (__eo_to_smt z)) ->
        eoHasSmtTranslation x ∧
          eoHasSmtTranslation
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) ∧
            eoHasSmtTranslation z)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp eoOp) x)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          z)) :
  P :=
by
  exfalso
  unfold eoHasSmtTranslation at hTrans
  have hNN :
      term_has_non_none_type
        (smtOp (__eo_to_smt x)
          (__eo_to_smt (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          (__eo_to_smt z)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans
  have hRawTrans := (hArgs hNN).2.1
  exact term_not_eo_list_cons_of_has_smt_translation hRawTrans v vs rfl

theorem false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
    {P : Prop} {op : UserOp} {x v vs z : Term}
    (hArgsOfHead :
      eoHasSmtTranslation
          (Term.Apply (Term.Apply (Term.UOp op) x)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) ->
        eoHasSmtTranslation x ∧
          eoHasSmtTranslation
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hOuterTranslate :
      __eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp op) x)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            z) =
        SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp op) x)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
          (__eo_to_smt z))
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp op) x)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          z)) :
  P :=
by
  exact
    false_of_apply_apply_apply_uop_over_binary_middle_raw_list
      (fun hHeadTrans => (hArgsOfHead hHeadTrans).2)
      hOuterTranslate hTrans

theorem false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
    {P : Prop} {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {x v vs z : Term}
    (hHeadTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp eoOp) x)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) =
        smtOp (__eo_to_smt x)
          (__eo_to_smt (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
    (hArgs :
      term_has_non_none_type
          (smtOp (__eo_to_smt x)
            (__eo_to_smt
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))) ->
        eoHasSmtTranslation x ∧
          eoHasSmtTranslation
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hOuterTranslate :
      __eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp eoOp) x)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            z) =
        SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp eoOp) x)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
          (__eo_to_smt z))
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp eoOp) x)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          z)) :
  P :=
by
  exact
    false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
      (fun hHeadTrans =>
        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
          hHeadTranslate hArgs hHeadTrans)
      hOuterTranslate hTrans

theorem false_of_apply_apply_apply_generic_middle_list_has_smt_translation
    {P : Prop} {op : UserOp} {x v vs z : Term}
    (hInnerTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp op) x)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) =
        SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.UOp op) x))
          (__eo_to_smt (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
    (hOuterTranslate :
      __eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp op) x)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            z) =
        SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp op) x)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
          (__eo_to_smt z))
    (hInnerGeneric :
      generic_apply_type
        (__eo_to_smt (Term.Apply (Term.UOp op) x))
        (__eo_to_smt (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
    (hOuterGeneric :
      generic_apply_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp op) x)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
        (__eo_to_smt z))
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp op) x)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          z)) :
  P :=
by
  exfalso
  unfold eoHasSmtTranslation at hTrans
  apply hTrans
  rw [hOuterTranslate, hOuterGeneric]
  have hInnerNone :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp op) x)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))) =
        SmtType.None := by
    rw [hInnerTranslate]
    exact
      smtx_typeof_generic_apply_eo_list_cons_arg_eq_none_closed
        (__eo_to_smt (Term.Apply (Term.UOp op) x)) v vs hInnerGeneric
  rw [hInnerNone]
  rfl

theorem false_of_apply_apply_apply_uop_middle_raw_list_has_smt_translation
    {P : Prop} {op : UserOp} {x v vs z : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp op) x)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          z)) :
  P :=
by
  cases op
  case ite =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_middle_raw_list
        (eoOp := UserOp.ite) (smtOp := SmtTerm.ite)
        (by rfl) ite_args_have_smt_translation_of_non_none hTrans
  case or =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        or_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case and =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        and_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case imp =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        imp_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case xor =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        xor_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case eq =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        eq_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case plus =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        plus_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case neg =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        neg_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case mult =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        mult_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case lt =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        lt_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case leq =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        leq_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case gt =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        gt_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case geq =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        geq_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case div =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        div_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case mod =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        mod_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case divisible =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        divisible_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case div_total =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        div_total_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case mod_total =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        mod_total_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case select =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        select_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case store =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_middle_raw_list
        (eoOp := UserOp.store) (smtOp := SmtTerm.store)
        (by rfl) store_args_have_smt_translation_of_non_none hTrans
  case _at_array_deq_diff =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        array_deq_diff_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case concat =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.concat) (smtOp := SmtTerm.concat)
        (by rfl) bv_concat_args_have_smt_translation_of_non_none
        (by rfl) hTrans
  case bvand =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvand) (smtOp := SmtTerm.bvand)
        (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvor =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvor) (smtOp := SmtTerm.bvor)
        (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvnand =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvnand) (smtOp := SmtTerm.bvnand)
        (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvnor =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvnor) (smtOp := SmtTerm.bvnor)
        (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvxor =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvxor) (smtOp := SmtTerm.bvxor)
        (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvxnor =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvxnor) (smtOp := SmtTerm.bvxnor)
        (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvcomp =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvcomp) (smtOp := SmtTerm.bvcomp)
        (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvadd =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvadd) (smtOp := SmtTerm.bvadd)
        (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvmul =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvmul) (smtOp := SmtTerm.bvmul)
        (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvudiv =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvudiv) (smtOp := SmtTerm.bvudiv)
        (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvurem =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvurem) (smtOp := SmtTerm.bvurem)
        (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvsub =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvsub) (smtOp := SmtTerm.bvsub)
        (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvsdiv =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvsdiv) (smtOp := SmtTerm.bvsdiv)
        (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvsrem =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvsrem) (smtOp := SmtTerm.bvsrem)
        (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvsmod =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvsmod) (smtOp := SmtTerm.bvsmod)
        (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvult =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvult) (smtOp := SmtTerm.bvult)
        (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvule =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvule) (smtOp := SmtTerm.bvule)
        (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvugt =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvugt) (smtOp := SmtTerm.bvugt)
        (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvuge =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvuge) (smtOp := SmtTerm.bvuge)
        (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvslt =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvslt) (smtOp := SmtTerm.bvslt)
        (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvsle =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvsle) (smtOp := SmtTerm.bvsle)
        (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvsgt =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvsgt) (smtOp := SmtTerm.bvsgt)
        (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvsge =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvsge) (smtOp := SmtTerm.bvsge)
        (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvshl =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvshl) (smtOp := SmtTerm.bvshl)
        (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvlshr =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvlshr) (smtOp := SmtTerm.bvlshr)
        (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvashr =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvashr) (smtOp := SmtTerm.bvashr)
        (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvite =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_middle_raw_list
        (eoOp := UserOp.bvite)
        (smtOp := fun c y z =>
          SmtTerm.ite (SmtTerm.eq c (SmtTerm.Binary 1 1)) y z)
        (by rfl) bvite_args_have_smt_translation_of_non_none hTrans
  case bvuaddo =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvuaddo) (smtOp := SmtTerm.bvuaddo)
        (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvsaddo =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvsaddo) (smtOp := SmtTerm.bvsaddo)
        (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvumulo =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvumulo) (smtOp := SmtTerm.bvumulo)
        (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvsmulo =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvsmulo) (smtOp := SmtTerm.bvsmulo)
        (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvusubo =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvusubo) (smtOp := SmtTerm.bvusubo)
        (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvssubo =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvssubo) (smtOp := SmtTerm.bvssubo)
        (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvsdivo =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.bvsdivo) (smtOp := SmtTerm.bvsdivo)
        (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans
  case bvultbv =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        bvultbv_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case bvsltbv =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        bvsltbv_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case _at_from_bools =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        from_bools_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case str_concat =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.str_concat) (smtOp := SmtTerm.str_concat)
        (by rfl)
        (fun hNN =>
          seq_binop_args_have_smt_translation_of_non_none
            (typeof_str_concat_eq (__eo_to_smt x)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            hNN)
        (by rfl) hTrans
  case str_substr =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_middle_raw_list
        (eoOp := UserOp.str_substr) (smtOp := SmtTerm.str_substr)
        (by rfl) str_substr_args_have_smt_translation_of_non_none hTrans
  case str_contains =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.str_contains) (smtOp := SmtTerm.str_contains)
        (by rfl)
        (fun hNN =>
          seq_binop_ret_args_have_smt_translation_of_non_none
            (typeof_str_contains_eq (__eo_to_smt x)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            hNN)
        (by rfl) hTrans
  case str_replace =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_middle_raw_list
        (eoOp := UserOp.str_replace) (smtOp := SmtTerm.str_replace)
        (by rfl)
        (fun hNN =>
          seq_triop_args_have_smt_translation_of_non_none
            (typeof_str_replace_eq (__eo_to_smt x)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
              (__eo_to_smt z))
            hNN)
        hTrans
  case str_indexof =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_middle_raw_list
        (eoOp := UserOp.str_indexof) (smtOp := SmtTerm.str_indexof)
        (by rfl) str_indexof_args_have_smt_translation_of_non_none hTrans
  case str_at =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.str_at) (smtOp := SmtTerm.str_at)
        (by rfl) str_at_args_have_smt_translation_of_non_none
        (by rfl) hTrans
  case str_prefixof =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.str_prefixof) (smtOp := SmtTerm.str_prefixof)
        (by rfl)
        (fun hNN =>
          seq_binop_ret_args_have_smt_translation_of_non_none
            (typeof_str_prefixof_eq (__eo_to_smt x)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            hNN)
        (by rfl) hTrans
  case str_suffixof =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.str_suffixof) (smtOp := SmtTerm.str_suffixof)
        (by rfl)
        (fun hNN =>
          seq_binop_ret_args_have_smt_translation_of_non_none
            (typeof_str_suffixof_eq (__eo_to_smt x)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            hNN)
        (by rfl) hTrans
  case str_update =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_middle_raw_list
        (eoOp := UserOp.str_update) (smtOp := SmtTerm.str_update)
        (by rfl) str_update_args_have_smt_translation_of_non_none hTrans
  case str_lt =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.str_lt) (smtOp := SmtTerm.str_lt)
        (by rfl)
        (fun hNN =>
          seq_char_binop_args_have_smt_translation_of_non_none
            (ret := SmtType.Bool)
            (typeof_str_lt_eq (__eo_to_smt x)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            hNN)
        (by rfl) hTrans
  case str_leq =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.str_leq) (smtOp := SmtTerm.str_leq)
        (by rfl)
        (fun hNN =>
          seq_char_binop_args_have_smt_translation_of_non_none
            (ret := SmtType.Bool)
            (typeof_str_leq_eq (__eo_to_smt x)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            hNN)
        (by rfl) hTrans
  case str_replace_all =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_middle_raw_list
        (eoOp := UserOp.str_replace_all)
        (smtOp := SmtTerm.str_replace_all)
        (by rfl)
        (fun hNN =>
          seq_triop_args_have_smt_translation_of_non_none
            (typeof_str_replace_all_eq (__eo_to_smt x)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
              (__eo_to_smt z))
            hNN)
        hTrans
  case str_replace_re =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_middle_raw_list
        (eoOp := UserOp.str_replace_re)
        (smtOp := SmtTerm.str_replace_re)
        (by rfl)
        (fun hNN =>
          str_replace_re_args_have_smt_translation_of_non_none
            (typeof_str_replace_re_eq (__eo_to_smt x)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
              (__eo_to_smt z))
            hNN)
        hTrans
  case str_replace_re_all =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_middle_raw_list
        (eoOp := UserOp.str_replace_re_all)
        (smtOp := SmtTerm.str_replace_re_all)
        (by rfl)
        (fun hNN =>
          str_replace_re_args_have_smt_translation_of_non_none
            (typeof_str_replace_re_all_eq (__eo_to_smt x)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
              (__eo_to_smt z))
            hNN)
        hTrans
  case str_indexof_re =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_middle_raw_list
        (eoOp := UserOp.str_indexof_re)
        (smtOp := SmtTerm.str_indexof_re)
        (by rfl) str_indexof_re_args_have_smt_translation_of_non_none hTrans
  case re_range =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.re_range) (smtOp := SmtTerm.re_range)
        (by rfl)
        (fun hNN =>
          seq_char_binop_args_have_smt_translation_of_non_none
            (ret := SmtType.RegLan)
            (typeof_re_range_eq (__eo_to_smt x)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            hNN)
        (by rfl) hTrans
  case re_concat =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.re_concat) (smtOp := SmtTerm.re_concat)
        (by rfl)
        (fun hNN =>
          reglan_binop_args_have_smt_translation_of_non_none
            (typeof_re_concat_eq (__eo_to_smt x)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            hNN)
        (by rfl) hTrans
  case re_inter =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.re_inter) (smtOp := SmtTerm.re_inter)
        (by rfl)
        (fun hNN =>
          reglan_binop_args_have_smt_translation_of_non_none
            (typeof_re_inter_eq (__eo_to_smt x)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            hNN)
        (by rfl) hTrans
  case re_union =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.re_union) (smtOp := SmtTerm.re_union)
        (by rfl)
        (fun hNN =>
          reglan_binop_args_have_smt_translation_of_non_none
            (typeof_re_union_eq (__eo_to_smt x)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            hNN)
        (by rfl) hTrans
  case re_diff =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.re_diff) (smtOp := SmtTerm.re_diff)
        (by rfl)
        (fun hNN =>
          reglan_binop_args_have_smt_translation_of_non_none
            (typeof_re_diff_eq (__eo_to_smt x)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            hNN)
        (by rfl) hTrans
  case str_in_re =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.str_in_re) (smtOp := SmtTerm.str_in_re)
        (by rfl)
        (fun hNN =>
          seq_char_reglan_args_have_smt_translation_of_non_none
            (ret := SmtType.Bool)
            (typeof_str_in_re_eq (__eo_to_smt x)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            hNN)
        (by rfl) hTrans
  case seq_nth =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.seq_nth) (smtOp := SmtTerm.seq_nth)
        (by rfl) seq_nth_args_have_smt_translation_of_non_none
        (by rfl) hTrans
  case _at_strings_deq_diff =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        strings_deq_diff_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case _at_strings_stoi_result =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        strings_stoi_result_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case _at_strings_itos_result =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        strings_itos_result_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case _at_strings_num_occur =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        strings_num_occur_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case _at_strings_num_occur_re =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        strings_num_occur_re_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case _at_strings_occur_index =>
    exact False.elim
      (term_not_eo_list_cons_of_has_smt_translation
        (strings_occur_index_args_have_smt_translation_of_has_smt_translation
          hTrans).2.1 v vs rfl)
  case _at_strings_occur_index_re =>
    exact False.elim
      (term_not_eo_list_cons_of_has_smt_translation
        (strings_occur_index_re_args_have_smt_translation_of_has_smt_translation
          hTrans).2.1 v vs rfl)
  case tuple =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        tuple_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case set_union =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.set_union) (smtOp := SmtTerm.set_union)
        (by rfl)
        (fun hNN =>
          set_binop_args_have_smt_translation_of_non_none
            (typeof_set_union_eq (__eo_to_smt x)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            hNN)
        (by rfl) hTrans
  case set_inter =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.set_inter) (smtOp := SmtTerm.set_inter)
        (by rfl)
        (fun hNN =>
          set_binop_args_have_smt_translation_of_non_none
            (typeof_set_inter_eq (__eo_to_smt x)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            hNN)
        (by rfl) hTrans
  case set_minus =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.set_minus) (smtOp := SmtTerm.set_minus)
        (by rfl)
        (fun hNN =>
          set_binop_args_have_smt_translation_of_non_none
            (typeof_set_minus_eq (__eo_to_smt x)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            hNN)
        (by rfl) hTrans
  case set_member =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.set_member) (smtOp := SmtTerm.set_member)
        (by rfl) set_member_args_have_smt_translation_of_non_none
        (by rfl) hTrans
  case set_subset =>
    exact
      false_of_apply_apply_apply_uop_over_binary_smt_binop_middle_raw_list
        (eoOp := UserOp.set_subset) (smtOp := SmtTerm.set_subset)
        (by rfl)
        (fun hNN =>
          set_binop_ret_args_have_smt_translation_of_non_none
            (ret := SmtType.Bool)
            (typeof_set_subset_eq (__eo_to_smt x)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            hNN)
        (by rfl) hTrans
  case set_insert =>
    exact
      false_of_apply_apply_apply_set_insert_middle_list_has_smt_translation
        hTrans
  case _at_sets_deq_diff =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        sets_deq_diff_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case qdiv =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        qdiv_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case qdiv_total =>
    exact
      false_of_apply_apply_apply_uop_over_binary_of_args_middle_raw_list
        qdiv_total_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans
  case «forall» =>
    exact false_of_apply_apply_apply_forall_has_smt_translation hTrans
  case «exists» =>
    exact false_of_apply_apply_apply_exists_has_smt_translation hTrans
  all_goals
    exact
      false_of_apply_apply_apply_generic_middle_list_has_smt_translation
        (by rfl) (by rfl)
        (generic_apply_type_of_non_special_head_closed _ _
          (by
            intro s d i j h
            exact
              TranslationProofs.eo_to_smt_apply_ne_dt_sel
                _ _ s d i j h)
          (by
            intro s d i h
            exact
              TranslationProofs.eo_to_smt_apply_ne_dt_tester
                _ _ s d i h))
        (generic_apply_type_of_non_special_head_closed _ _
          (by
            intro s d i j h
            exact
              TranslationProofs.eo_to_smt_apply_ne_dt_sel
                _ _ s d i j h)
          (by
            intro s d i h
            exact
              TranslationProofs.eo_to_smt_apply_ne_dt_tester
                _ _ s d i h))
        hTrans

theorem false_of_apply_generic_raw_arg_has_smt_translation
    {P : Prop} {q v vs : Term}
    (hTranslate :
      __eo_to_smt
          (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) =
        SmtTerm.Apply (__eo_to_smt q)
          (__eo_to_smt (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
    (hGeneric :
      generic_apply_type (__eo_to_smt q)
        (__eo_to_smt (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))) :
  P :=
by
  exfalso
  unfold eoHasSmtTranslation at hTrans
  apply hTrans
  rw [hTranslate, hGeneric, smtx_typeof_eo_list_cons_eq_none]
  exact smtx_typeof_apply_arg_none_eq_none_closed
    (__smtx_typeof (__eo_to_smt q))

theorem false_of_apply_apply_apply_uop_smt_triop_last_raw_list
    {P : Prop} {eoOp : UserOp}
    {smtOp : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm}
    {x y v vs : Term}
    (hTranslate :
      __eo_to_smt
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp eoOp) x) y)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) =
        smtOp (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
    (hArgs :
      term_has_non_none_type
          (smtOp (__eo_to_smt x) (__eo_to_smt y)
            (__eo_to_smt (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))) ->
        eoHasSmtTranslation x ∧
          eoHasSmtTranslation y ∧
            eoHasSmtTranslation
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp eoOp) x) y)
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))) :
  P :=
by
  exfalso
  unfold eoHasSmtTranslation at hTrans
  have hNN :
      term_has_non_none_type
        (smtOp (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans
  have hRawTrans := (hArgs hNN).2.2
  exact term_not_eo_list_cons_of_has_smt_translation hRawTrans v vs rfl

theorem false_of_apply_apply_apply_uop_last_raw_list_has_smt_translation
    {P : Prop} {op : UserOp} {x y v vs : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp op) x) y)
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))) :
  P :=
by
  cases op
  case ite =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_last_raw_list
        (eoOp := UserOp.ite) (smtOp := SmtTerm.ite)
        (by rfl) ite_args_have_smt_translation_of_non_none hTrans
  case store =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_last_raw_list
        (eoOp := UserOp.store) (smtOp := SmtTerm.store)
        (by rfl) store_args_have_smt_translation_of_non_none hTrans
  case bvite =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_last_raw_list
        (eoOp := UserOp.bvite)
        (smtOp := fun c y z =>
          SmtTerm.ite (SmtTerm.eq c (SmtTerm.Binary 1 1)) y z)
        (by rfl) bvite_args_have_smt_translation_of_non_none hTrans
  case str_substr =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_last_raw_list
        (eoOp := UserOp.str_substr) (smtOp := SmtTerm.str_substr)
        (by rfl) str_substr_args_have_smt_translation_of_non_none hTrans
  case str_replace =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_last_raw_list
        (eoOp := UserOp.str_replace) (smtOp := SmtTerm.str_replace)
        (by rfl)
        (fun hNN =>
          seq_triop_args_have_smt_translation_of_non_none
            (typeof_str_replace_eq (__eo_to_smt x) (__eo_to_smt y)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            hNN)
        hTrans
  case str_indexof =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_last_raw_list
        (eoOp := UserOp.str_indexof) (smtOp := SmtTerm.str_indexof)
        (by rfl) str_indexof_args_have_smt_translation_of_non_none hTrans
  case str_update =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_last_raw_list
        (eoOp := UserOp.str_update) (smtOp := SmtTerm.str_update)
        (by rfl) str_update_args_have_smt_translation_of_non_none hTrans
  case str_replace_all =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_last_raw_list
        (eoOp := UserOp.str_replace_all)
        (smtOp := SmtTerm.str_replace_all)
        (by rfl)
        (fun hNN =>
          seq_triop_args_have_smt_translation_of_non_none
            (typeof_str_replace_all_eq (__eo_to_smt x) (__eo_to_smt y)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            hNN)
        hTrans
  case str_replace_re =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_last_raw_list
        (eoOp := UserOp.str_replace_re)
        (smtOp := SmtTerm.str_replace_re)
        (by rfl)
        (fun hNN =>
          str_replace_re_args_have_smt_translation_of_non_none
            (typeof_str_replace_re_eq (__eo_to_smt x) (__eo_to_smt y)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            hNN)
        hTrans
  case str_replace_re_all =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_last_raw_list
        (eoOp := UserOp.str_replace_re_all)
        (smtOp := SmtTerm.str_replace_re_all)
        (by rfl)
        (fun hNN =>
          str_replace_re_args_have_smt_translation_of_non_none
            (typeof_str_replace_re_all_eq (__eo_to_smt x) (__eo_to_smt y)
              (__eo_to_smt
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            hNN)
        hTrans
  case str_indexof_re =>
    exact
      false_of_apply_apply_apply_uop_smt_triop_last_raw_list
        (eoOp := UserOp.str_indexof_re)
        (smtOp := SmtTerm.str_indexof_re)
        (by rfl) str_indexof_re_args_have_smt_translation_of_non_none hTrans
  case _at_strings_occur_index =>
    exact False.elim
      (term_not_eo_list_cons_of_has_smt_translation
        (strings_occur_index_args_have_smt_translation_of_has_smt_translation
          hTrans).2.2 v vs rfl)
  case _at_strings_occur_index_re =>
    exact False.elim
      (term_not_eo_list_cons_of_has_smt_translation
        (strings_occur_index_re_args_have_smt_translation_of_has_smt_translation
          hTrans).2.2 v vs rfl)
  all_goals
    exact
      false_of_apply_generic_raw_arg_has_smt_translation
        (by rfl)
        (generic_apply_type_of_non_special_head_closed _ _
          (by
            intro s d i j h
            exact
              TranslationProofs.eo_to_smt_apply_ne_dt_sel
                _ _ s d i j h)
          (by
            intro s d i h
            exact
              TranslationProofs.eo_to_smt_apply_ne_dt_tester
                _ _ s d i h))
        hTrans

theorem false_of_apply_apply_apply_uop1_last_raw_list_has_smt_translation
    {P : Prop} {op : UserOp1} {idx x y v vs : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))) :
  P :=
by
  exact
    false_of_apply_generic_raw_arg_has_smt_translation
      (q := Term.Apply (Term.Apply (Term.UOp1 op idx) x) y)
      (by rfl)
      (generic_apply_type_of_non_special_head_closed _ _
        (by
          intro s d i j h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_sel
              _ _ s d i j h)
        (by
          intro s d i h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_tester
              _ _ s d i h))
      hTrans

theorem false_of_apply_apply_apply_apply_uop_last_raw_list_has_smt_translation
    {P : Prop} {op : UserOp} {w z y v vs : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp op) w) z)
            y)
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))) :
  P :=
by
  cases op
  case _at_strings_replace_all_result =>
    exact False.elim
      (term_not_eo_list_cons_of_has_smt_translation
        (strings_replace_all_result_args_have_smt_translation_of_has_smt_translation
          hTrans).2.2.2 v vs rfl)
  case _at_strings_replace_re_all_result =>
    exact False.elim
      (term_not_eo_list_cons_of_has_smt_translation
        (strings_replace_re_all_result_args_have_smt_translation_of_has_smt_translation
          hTrans).2.2.2 v vs rfl)
  all_goals
    exact
      false_of_apply_generic_raw_arg_has_smt_translation
        (q := Term.Apply
          (Term.Apply (Term.Apply (Term.UOp _) w) z) y)
        (by rfl)
        (generic_apply_type_of_non_special_head_closed _ _
          (by
            intro s d i j h
            exact
              TranslationProofs.eo_to_smt_apply_ne_dt_sel
                _ _ s d i j h)
          (by
            intro s d i h
            exact
              TranslationProofs.eo_to_smt_apply_ne_dt_tester
                _ _ s d i h))
        hTrans

theorem false_of_apply_apply_apply_apply_uop_third_raw_list_has_smt_translation
    {P : Prop} {op : UserOp} {w z v vs x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp op) w)
              z)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          x)) :
  P :=
by
  by_cases hReplaceAll :
      op = UserOp._at_strings_replace_all_result
  · subst op
    exact False.elim
      (term_not_eo_list_cons_of_has_smt_translation
        (strings_replace_all_result_args_have_smt_translation_of_has_smt_translation
          hTrans).2.2.1 v vs rfl)
  by_cases hReplaceReAll :
      op = UserOp._at_strings_replace_re_all_result
  · subst op
    exact False.elim
      (term_not_eo_list_cons_of_has_smt_translation
        (strings_replace_re_all_result_args_have_smt_translation_of_has_smt_translation
          hTrans).2.2.1 v vs rfl)
  ·
    exfalso
    have hTranslate :
        __eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.UOp op) w)
                  z)
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
              x) =
          SmtTerm.Apply
            (__eo_to_smt
              (Term.Apply
                (Term.Apply (Term.Apply (Term.UOp op) w) z)
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            (__eo_to_smt x) :=
      TranslationProofs.eo_to_smt_apply_apply_apply_apply_uop_generic_eq
        op w z (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) x
        hReplaceAll hReplaceReAll
    have hTy :
        __smtx_typeof
            (SmtTerm.Apply
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.Apply (Term.UOp op) w) z)
                  (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
              (__eo_to_smt x)) =
          __smtx_typeof_apply
            (__smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.Apply (Term.UOp op) w) z)
                  (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))))
            (__smtx_typeof (__eo_to_smt x)) :=
      generic_apply_type_of_non_special_head_closed _ _
        (by
          intro s d i j h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_sel
              _ _ s d i j h)
        (by
          intro s d i h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_tester
              _ _ s d i h)
    have hNN :
        term_has_non_none_type
          (SmtTerm.Apply
            (__eo_to_smt
              (Term.Apply
                (Term.Apply (Term.Apply (Term.UOp op) w) z)
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hTrans
    have hHeadTrans :=
      (apply_args_have_smt_translation_of_non_none hTy hNN).1
    exact false_of_apply_apply_apply_uop_last_raw_list_has_smt_translation
      hHeadTrans

theorem false_of_apply_apply_apply_raw_list_has_smt_translation
    {P : Prop} {f x y v vs : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.Apply f x) y)
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))) :
  P :=
by
  cases f
  case UOp op =>
    exact false_of_apply_apply_apply_uop_last_raw_list_has_smt_translation
      hTrans
  case UOp1 op idx =>
    exact false_of_apply_apply_apply_uop1_last_raw_list_has_smt_translation
      hTrans
  case Apply g w =>
    cases g
    case UOp op =>
      exact
        false_of_apply_apply_apply_apply_uop_last_raw_list_has_smt_translation
          hTrans
    all_goals
      exact
        false_of_apply_generic_raw_arg_has_smt_translation
          (by rfl)
          (generic_apply_type_of_non_special_head_closed _ _
            (by
              intro s d i j h
              exact
                TranslationProofs.eo_to_smt_apply_ne_dt_sel
                  _ _ s d i j h)
            (by
              intro s d i h
              exact
                TranslationProofs.eo_to_smt_apply_ne_dt_tester
                  _ _ s d i h))
          hTrans
  all_goals
    exact
      false_of_apply_generic_raw_arg_has_smt_translation
        (by rfl)
        (generic_apply_type_of_non_special_head_closed _ _
          (by
            intro s d i j h
            exact
              TranslationProofs.eo_to_smt_apply_ne_dt_sel
                _ _ s d i j h)
          (by
            intro s d i h
            exact
              TranslationProofs.eo_to_smt_apply_ne_dt_tester
                _ _ s d i h))
        hTrans

theorem false_of_apply_apply_apply_apply_middle_raw_list_has_smt_translation
    {P : Prop} {g y x v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply g y) x)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  P :=
by
  by_cases hUOp : ∃ op, g = Term.UOp op
  · rcases hUOp with ⟨op, rfl⟩
    exact
      false_of_apply_apply_apply_apply_uop_third_raw_list_has_smt_translation
        hTrans
  ·
    exfalso
    unfold eoHasSmtTranslation at hTrans
    rw [TranslationProofs.eo_to_smt_apply_apply_apply_apply_eq_of_head_not_uop
      g y x (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) body
      (by intro op h; exact hUOp ⟨op, h⟩)] at hTrans
    have hNN :
        term_has_non_none_type
          (SmtTerm.Apply
            (__eo_to_smt
              (Term.Apply
                (Term.Apply (Term.Apply g y) x)
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
            (__eo_to_smt body)) := by
      exact hTrans
    have hTy :
        __smtx_typeof
            (SmtTerm.Apply
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.Apply g y) x)
                  (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
              (__eo_to_smt body)) =
          __smtx_typeof_apply
            (__smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.Apply g y) x)
                  (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))))
            (__smtx_typeof (__eo_to_smt body)) :=
      generic_apply_type_of_non_special_head_closed
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.Apply g y) x)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)))
        (__eo_to_smt body)
        (by
          intro s d i j h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_sel
              (Term.Apply (Term.Apply g y) x)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
              s d i j h)
        (by
          intro s d i h
          exact
            TranslationProofs.eo_to_smt_apply_ne_dt_tester
              (Term.Apply (Term.Apply g y) x)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
              s d i h)
    have hHeadTrans :=
      (apply_args_have_smt_translation_of_non_none hTy hNN).1
    exact false_of_apply_apply_apply_raw_list_has_smt_translation
      hHeadTrans

theorem is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
    {q v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  q = Term.UOp UserOp.forall ∨ q = Term.UOp UserOp.exists :=
by
  cases q
  case UOp op =>
    exact
      is_closed_rec_uop_list_branch_head_term_quantifier_of_has_smt_translation
        hTrans
  case UOp1 op i =>
    exact false_of_apply_apply_uop1_raw_list_has_smt_translation hTrans
  case UOp2 op i j =>
    exact false_of_apply_apply_uop2_raw_list_has_smt_translation hTrans
  case UOp3 op a b c =>
    exact false_of_apply_apply_uop3_raw_list_has_smt_translation hTrans
  case Apply f x =>
    cases f
    case UOp op =>
      exact false_of_apply_apply_apply_uop_middle_raw_list_has_smt_translation hTrans
    case UOp1 op idx =>
      exact false_of_apply_apply_apply_uop1_middle_raw_list_has_smt_translation hTrans
    case Apply g y =>
      exact
        false_of_apply_apply_apply_apply_middle_raw_list_has_smt_translation
          hTrans
    all_goals
      exact
        false_of_apply_apply_generic_raw_list_has_smt_translation
          (by rfl) (by rfl)
          (generic_apply_type_of_non_special_head_closed _ _
            (by
              intro s d i j h
              exact
                TranslationProofs.eo_to_smt_apply_ne_dt_sel
                  _ _ s d i j h)
            (by
              intro s d i h
              exact
                TranslationProofs.eo_to_smt_apply_ne_dt_tester
                  _ _ s d i h))
          hTrans
  all_goals
    exact
      false_of_apply_apply_generic_raw_list_has_smt_translation
        (by rfl) (by rfl)
        (generic_apply_type_of_non_special_head_closed _ _
          (by
            intro s d i j h
            exact
              TranslationProofs.eo_to_smt_apply_ne_dt_sel
                _ _ s d i j h)
          (by
            intro s d i h
            exact
              TranslationProofs.eo_to_smt_apply_ne_dt_tester
                _ _ s d i h))
        hTrans

theorem is_closed_rec_apply_apply_uop_any_eq_and_bool_of_has_smt_translation
    (root : Term)
    {op : UserOp} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x) y))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
    __eo_is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
        Term.Boolean b :=
by
  cases op
  case or =>
    exact
      is_closed_rec_apply_apply_or_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case and =>
    exact
      is_closed_rec_apply_apply_and_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case imp =>
    exact
      is_closed_rec_apply_apply_imp_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case xor =>
    exact
      is_closed_rec_apply_apply_xor_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case eq =>
    exact
      is_closed_rec_apply_apply_eq_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case plus =>
    exact
      is_closed_rec_apply_apply_plus_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case neg =>
    exact
      is_closed_rec_apply_apply_neg_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case mult =>
    exact
      is_closed_rec_apply_apply_mult_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case lt =>
    exact
      is_closed_rec_apply_apply_lt_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case leq =>
    exact
      is_closed_rec_apply_apply_leq_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case gt =>
    exact
      is_closed_rec_apply_apply_gt_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case geq =>
    exact
      is_closed_rec_apply_apply_geq_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case div =>
    exact
      is_closed_rec_apply_apply_div_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case mod =>
    exact
      is_closed_rec_apply_apply_mod_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case divisible =>
    exact
      is_closed_rec_apply_apply_divisible_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case div_total =>
    exact
      is_closed_rec_apply_apply_div_total_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case mod_total =>
    exact
      is_closed_rec_apply_apply_mod_total_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case select =>
    exact
      is_closed_rec_apply_apply_select_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case _at_array_deq_diff =>
    exact
      is_closed_rec_apply_apply_array_deq_diff_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case concat =>
    exact
      is_closed_rec_apply_apply_concat_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case bvand =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvor =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvnand =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvnor =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvxor =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvxnor =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvcomp =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_ret_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvadd =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvmul =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvudiv =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvurem =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvsub =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvsdiv =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvsrem =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvsmod =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvult =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_ret_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvule =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_ret_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvugt =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_ret_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvuge =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_ret_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvslt =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_ret_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvsle =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_ret_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvsgt =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_ret_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvsge =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_ret_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvshl =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvlshr =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvashr =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvuaddo =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_ret_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvsaddo =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_ret_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvumulo =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_ret_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvsmulo =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_ret_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvusubo =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_ret_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvssubo =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_ret_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvsdivo =>
    exact
      is_closed_rec_apply_apply_uop_bv_binop_ret_eq_and_bool_of_has_smt_translation
        hEnv (by decide) (by decide) (by rfl)
        (by rw [__smtx_typeof.eq_def]) hTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case bvultbv =>
    exact
      is_closed_rec_apply_apply_bvultbv_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case bvsltbv =>
    exact
      is_closed_rec_apply_apply_bvsltbv_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case _at_from_bools =>
    exact
      is_closed_rec_apply_apply_from_bools_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case str_concat =>
    exact
      is_closed_rec_apply_apply_str_concat_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case str_contains =>
    exact
      is_closed_rec_apply_apply_str_contains_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case str_at =>
    exact
      is_closed_rec_apply_apply_str_at_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case str_prefixof =>
    exact
      is_closed_rec_apply_apply_str_prefixof_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case str_suffixof =>
    exact
      is_closed_rec_apply_apply_str_suffixof_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case str_lt =>
    exact
      is_closed_rec_apply_apply_str_lt_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case str_leq =>
    exact
      is_closed_rec_apply_apply_str_leq_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case re_range =>
    exact
      is_closed_rec_apply_apply_re_range_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case re_concat =>
    exact
      is_closed_rec_apply_apply_re_concat_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case re_inter =>
    exact
      is_closed_rec_apply_apply_re_inter_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case re_union =>
    exact
      is_closed_rec_apply_apply_re_union_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case re_diff =>
    exact
      is_closed_rec_apply_apply_re_diff_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case str_in_re =>
    exact
      is_closed_rec_apply_apply_str_in_re_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case seq_nth =>
    exact
      is_closed_rec_apply_apply_seq_nth_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case _at_strings_deq_diff =>
    exact
      is_closed_rec_apply_apply_strings_deq_diff_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case _at_strings_stoi_result =>
    exact
      is_closed_rec_apply_apply_strings_stoi_result_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case _at_strings_itos_result =>
    exact
      is_closed_rec_apply_apply_strings_itos_result_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case _at_strings_num_occur =>
    exact
      is_closed_rec_apply_apply_strings_num_occur_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case _at_strings_num_occur_re =>
    rcases
        strings_num_occur_re_args_have_smt_translation_of_has_smt_translation
          hTrans with
      ⟨hXTrans, hYTrans⟩
    exact
      is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
        hEnv (by decide) (by decide) hTrans hXTrans hYTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
  case tuple =>
    exact
      is_closed_rec_apply_apply_tuple_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case set_union =>
    exact
      is_closed_rec_apply_apply_set_union_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case set_inter =>
    exact
      is_closed_rec_apply_apply_set_inter_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case set_minus =>
    exact
      is_closed_rec_apply_apply_set_minus_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case set_member =>
    exact
      is_closed_rec_apply_apply_set_member_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case set_subset =>
    exact
      is_closed_rec_apply_apply_set_subset_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case set_insert =>
    exact
      is_closed_rec_apply_apply_set_insert_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hTrans ih
  case _at_sets_deq_diff =>
    exact
      is_closed_rec_apply_apply_sets_deq_diff_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case qdiv =>
    exact
      is_closed_rec_apply_apply_qdiv_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case qdiv_total =>
    exact
      is_closed_rec_apply_apply_qdiv_total_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy)
  case «forall» =>
    by_cases hCons :
        ∃ v vs, x = Term.Apply (Term.Apply Term.__eo_List_cons v) vs
    · rcases hCons with ⟨v, vs, hX⟩
      subst x
      exact
        is_closed_rec_uop_list_branch_eq_and_bool_of_has_smt_translation
          hEnv hTrans (fun hEnv' hBodyTrans => ih hYLt hEnv' hBodyTrans)
    · exact
        false_of_forall_non_list_has_smt_translation
          (by intro v vs hX; exact hCons ⟨v, vs, hX⟩) hTrans
  case «exists» =>
    by_cases hCons :
        ∃ v vs, x = Term.Apply (Term.Apply Term.__eo_List_cons v) vs
    · rcases hCons with ⟨v, vs, hX⟩
      subst x
      exact
        is_closed_rec_uop_list_branch_eq_and_bool_of_has_smt_translation
          hEnv hTrans (fun hEnv' hBodyTrans => ih hYLt hEnv' hBodyTrans)
    · exact
        false_of_exists_non_list_has_smt_translation
          (by intro v vs hX; exact hCons ⟨v, vs, hX⟩) hTrans
  all_goals
    exact
      is_closed_rec_apply_generic_eq_and_bool_of_has_smt_translation
        hEnv
        (by
          intro q v vs hEq
          cases hEq
          exact
            apply_apply_uop_arg_not_list_of_nonquantifier_has_smt_translation
              (by decide) (by decide) hTrans v vs rfl)
        (by
          intro vs hEq
          cases hEq)
        (by
          intro vs hEq
          cases hEq)
        (by rfl)
        (by
          exact
            generic_apply_type_of_non_special_head_closed _ _
              (by
                intro s d i j h
                exact
                  TranslationProofs.eo_to_smt_apply_ne_dt_sel
                    _ _ s d i j h)
              (by
                intro s d i h
                exact
                  TranslationProofs.eo_to_smt_apply_ne_dt_tester
                    _ _ s d i h))
        hTrans
        (fun hHeadTrans =>
          is_closed_rec_apply_uop_any_eq_and_bool_of_has_smt_translation
            root hEnv hXLt hHeadTrans ih)
        (fun hYTrans => ih hYLt hEnv hYTrans)

theorem is_closed_rec_apply_apply_apply_uop_generic_eq_and_bool_of_has_smt_translation
    (root : Term)
    {op : UserOp} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hZLt : sizeOf z < sizeOf root)
    (hInnerTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.UOp op) x))
          (__eo_to_smt y))
    (hOuterTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) =
        SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y))
          (__eo_to_smt z))
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
        env =
        Term.Boolean b :=
by
  have hTy :
      __smtx_typeof
          (SmtTerm.Apply
            (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y))
            (__eo_to_smt z)) =
        __smtx_typeof_apply
          (__smtx_typeof
            (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)))
          (__smtx_typeof (__eo_to_smt z)) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j h
        exact
          TranslationProofs.eo_to_smt_apply_ne_dt_sel
            _ _ s d i j h)
      (by
        intro s d i h
        exact
          TranslationProofs.eo_to_smt_apply_ne_dt_tester
            _ _ s d i h)
  have hNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y))
          (__eo_to_smt z)) := by
    unfold term_has_non_none_type
    rw [← hOuterTranslate]
    exact hTrans
  rcases apply_args_have_smt_translation_of_non_none hTy hNN with
    ⟨hHeadTrans, hZTrans⟩
  have hHeadClosed :
      __is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
        __eo_is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y)
          env ∧
        ∃ b,
          __eo_is_closed_rec
              (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
            Term.Boolean b :=
    is_closed_rec_apply_apply_uop_any_eq_and_bool_of_has_smt_translation
      root hEnv hXLt hYLt hHeadTrans ih
  exact
    is_closed_rec_apply_generic_eq_and_bool_of_parts
      hEnv
      (by
        intro q v vs hEq
        cases hEq
        exact
          false_of_apply_apply_apply_generic_middle_list_has_smt_translation
            hInnerTranslate hOuterTranslate
            (generic_apply_type_of_non_special_head_closed _ _
              (by
                intro s d i j h
                exact
                  TranslationProofs.eo_to_smt_apply_ne_dt_sel
                    _ _ s d i j h)
              (by
                intro s d i h
                exact
                  TranslationProofs.eo_to_smt_apply_ne_dt_tester
                    _ _ s d i h))
            (generic_apply_type_of_non_special_head_closed _ _
              (by
                intro s d i j h
                exact
                  TranslationProofs.eo_to_smt_apply_ne_dt_sel
                    _ _ s d i j h)
              (by
                intro s d i h
                exact
                  TranslationProofs.eo_to_smt_apply_ne_dt_tester
                    _ _ s d i h))
            hTrans)
      (by
        intro vs hEq
        cases hEq)
      (by
        intro vs hEq
        cases hEq)
      hHeadClosed
      (ih hZLt hEnv hZTrans)

theorem is_closed_rec_apply_apply_apply_uop_over_binary_eq_and_bool_of_has_smt_translation
    (root : Term)
    {op : UserOp} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hZLt : sizeOf z < sizeOf root)
    (hYTransOfHead :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x) y) ->
        eoHasSmtTranslation y)
    (hOuterTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) =
        SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y))
          (__eo_to_smt z))
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
        env =
        Term.Boolean b :=
by
  have hTy :
      __smtx_typeof
          (SmtTerm.Apply
            (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y))
            (__eo_to_smt z)) =
        __smtx_typeof_apply
          (__smtx_typeof
            (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y)))
          (__smtx_typeof (__eo_to_smt z)) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j h
        exact
          TranslationProofs.eo_to_smt_apply_ne_dt_sel
            _ _ s d i j h)
      (by
        intro s d i h
        exact
          TranslationProofs.eo_to_smt_apply_ne_dt_tester
            _ _ s d i h)
  have hNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y))
          (__eo_to_smt z)) := by
    unfold term_has_non_none_type
    rw [← hOuterTranslate]
    exact hTrans
  rcases apply_args_have_smt_translation_of_non_none hTy hNN with
    ⟨hHeadTrans, hZTrans⟩
  have hYTrans : eoHasSmtTranslation y :=
    hYTransOfHead hHeadTrans
  have hHeadClosed :
      __is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
        __eo_is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y)
          env ∧
        ∃ b,
          __eo_is_closed_rec
              (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
            Term.Boolean b :=
    is_closed_rec_apply_apply_uop_any_eq_and_bool_of_has_smt_translation
      root hEnv hXLt hYLt hHeadTrans ih
  exact
    is_closed_rec_apply_generic_eq_and_bool_of_parts
      hEnv
      (by
        intro q v vs hEq
        cases hEq
        exact term_not_eo_list_cons_of_has_smt_translation hYTrans v vs rfl)
      (by
        intro vs hEq
        cases hEq)
      (by
        intro vs hEq
        cases hEq)
      hHeadClosed
      (ih hZLt hEnv hZTrans)

theorem is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
    (root : Term)
    {op : UserOp} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hZLt : sizeOf z < sizeOf root)
    (hArgsOfHead :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x) y) ->
        eoHasSmtTranslation x ∧ eoHasSmtTranslation y)
    (hOuterTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) =
        SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y))
          (__eo_to_smt z))
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
        env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_over_binary_eq_and_bool_of_has_smt_translation
      root hEnv hXLt hYLt hZLt
      (fun hHeadTrans => (hArgsOfHead hHeadTrans).2)
      hOuterTranslate hTrans ih

theorem is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
    (root : Term)
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hZLt : sizeOf z < sizeOf root)
    (hHeadTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hArgs :
      term_has_non_none_type (smtOp (__eo_to_smt x) (__eo_to_smt y)) ->
        eoHasSmtTranslation x ∧ eoHasSmtTranslation y)
    (hOuterTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z) =
        SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
          (__eo_to_smt z))
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
        env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
      root hEnv hXLt hYLt hZLt
      (fun hHeadTrans =>
        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
          hHeadTranslate hArgs hHeadTrans)
      hOuterTranslate hTrans ih

theorem is_closed_rec_apply_apply_apply_or_eq_and_bool_of_has_smt_translation
    (root : Term)
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hZLt : sizeOf z < sizeOf root)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y) z))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y)
          z) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_over_binary_eq_and_bool_of_has_smt_translation
      root hEnv hXLt hYLt hZLt
      (fun hHeadTrans =>
        (or_args_have_smt_translation_of_has_smt_translation
          hHeadTrans).2)
      (by rfl) hTrans ih

theorem is_closed_rec_apply_apply_apply_and_eq_and_bool_of_has_smt_translation
    (root : Term)
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hZLt : sizeOf z < sizeOf root)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y) z))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y)
        z) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y)
        z) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y)
          z) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_over_binary_eq_and_bool_of_has_smt_translation
      root hEnv hXLt hYLt hZLt
      (fun hHeadTrans =>
        (and_args_have_smt_translation_of_has_smt_translation
          hHeadTrans).2)
      (by rfl) hTrans ih

theorem is_closed_rec_apply_apply_apply_imp_eq_and_bool_of_has_smt_translation
    (root : Term)
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hZLt : sizeOf z < sizeOf root)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y) z))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y)
        z) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y)
        z) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y)
          z) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_over_binary_eq_and_bool_of_has_smt_translation
      root hEnv hXLt hYLt hZLt
      (fun hHeadTrans =>
        (imp_args_have_smt_translation_of_has_smt_translation
          hHeadTrans).2)
      (by rfl) hTrans ih

theorem is_closed_rec_apply_apply_apply_xor_eq_and_bool_of_has_smt_translation
    (root : Term)
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hZLt : sizeOf z < sizeOf root)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y) z))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y)
        z) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y)
        z) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y)
          z) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_over_binary_eq_and_bool_of_has_smt_translation
      root hEnv hXLt hYLt hZLt
      (fun hHeadTrans =>
        (xor_args_have_smt_translation_of_has_smt_translation
          hHeadTrans).2)
      (by rfl) hTrans ih

theorem is_closed_rec_apply_apply_apply_eq_eq_and_bool_of_has_smt_translation
    (root : Term)
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hZLt : sizeOf z < sizeOf root)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) z))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)
          z) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_over_binary_eq_and_bool_of_has_smt_translation
      root hEnv hXLt hYLt hZLt
      (fun hHeadTrans =>
        (eq_args_have_smt_translation_of_has_smt_translation
          hHeadTrans).2)
      (by rfl) hTrans ih

theorem is_closed_rec_apply_apply_apply_uop_any_eq_and_bool_of_has_smt_translation
    (root : Term)
    {op : UserOp} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hXLt : sizeOf x < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hZLt : sizeOf z < sizeOf root)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
        env =
        Term.Boolean b :=
by
  cases op
  case ite =>
    exact
      is_closed_rec_apply_apply_apply_ite_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy) (fun hz => ih hZLt hEnv hz)
  case or =>
    exact
      is_closed_rec_apply_apply_apply_or_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt hTrans ih
  case and =>
    exact
      is_closed_rec_apply_apply_apply_and_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt hTrans ih
  case imp =>
    exact
      is_closed_rec_apply_apply_apply_imp_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt hTrans ih
  case xor =>
    exact
      is_closed_rec_apply_apply_apply_xor_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt hTrans ih
  case eq =>
    exact
      is_closed_rec_apply_apply_apply_eq_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt hTrans ih
  case plus =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        plus_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case neg =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        neg_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case mult =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        mult_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case lt =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        lt_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case leq =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        leq_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case gt =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        gt_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case geq =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        geq_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case div =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        div_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case mod =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        mod_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case divisible =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        divisible_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case div_total =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        div_total_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case mod_total =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        mod_total_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case select =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        select_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case store =>
    exact
      is_closed_rec_apply_apply_apply_store_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy) (fun hz => ih hZLt hEnv hz)
  case _at_array_deq_diff =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        array_deq_diff_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case concat =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.concat) (smtOp := SmtTerm.concat)
        root hEnv hXLt hYLt hZLt (by rfl)
        bv_concat_args_have_smt_translation_of_non_none (by rfl) hTrans ih
  case bvand =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvand) (smtOp := SmtTerm.bvand)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvor =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvor) (smtOp := SmtTerm.bvor)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvnand =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvnand) (smtOp := SmtTerm.bvnand)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvnor =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvnor) (smtOp := SmtTerm.bvnor)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvxor =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvxor) (smtOp := SmtTerm.bvxor)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvxnor =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvxnor) (smtOp := SmtTerm.bvxnor)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvcomp =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvcomp) (smtOp := SmtTerm.bvcomp)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvadd =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvadd) (smtOp := SmtTerm.bvadd)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvmul =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvmul) (smtOp := SmtTerm.bvmul)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvudiv =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvudiv) (smtOp := SmtTerm.bvudiv)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvurem =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvurem) (smtOp := SmtTerm.bvurem)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvsub =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvsub) (smtOp := SmtTerm.bvsub)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvsdiv =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvsdiv) (smtOp := SmtTerm.bvsdiv)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvsrem =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvsrem) (smtOp := SmtTerm.bvsrem)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvsmod =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvsmod) (smtOp := SmtTerm.bvsmod)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvult =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvult) (smtOp := SmtTerm.bvult)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvule =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvule) (smtOp := SmtTerm.bvule)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvugt =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvugt) (smtOp := SmtTerm.bvugt)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvuge =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvuge) (smtOp := SmtTerm.bvuge)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvslt =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvslt) (smtOp := SmtTerm.bvslt)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvsle =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvsle) (smtOp := SmtTerm.bvsle)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvsgt =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvsgt) (smtOp := SmtTerm.bvsgt)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvsge =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvsge) (smtOp := SmtTerm.bvsge)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvshl =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvshl) (smtOp := SmtTerm.bvshl)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvlshr =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvlshr) (smtOp := SmtTerm.bvlshr)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvashr =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvashr) (smtOp := SmtTerm.bvashr)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvite =>
    exact
      is_closed_rec_apply_apply_apply_bvite_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy) (fun hz => ih hZLt hEnv hz)
  case bvuaddo =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvuaddo) (smtOp := SmtTerm.bvuaddo)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvsaddo =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvsaddo) (smtOp := SmtTerm.bvsaddo)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvumulo =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvumulo) (smtOp := SmtTerm.bvumulo)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvsmulo =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvsmulo) (smtOp := SmtTerm.bvsmulo)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvusubo =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvusubo) (smtOp := SmtTerm.bvusubo)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvssubo =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvssubo) (smtOp := SmtTerm.bvssubo)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvsdivo =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.bvsdivo) (smtOp := SmtTerm.bvsdivo)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          bv_binop_ret_args_have_smt_translation_of_non_none
            (by rw [__smtx_typeof.eq_def]) hNN)
        (by rfl) hTrans ih
  case bvultbv =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        bvultbv_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case bvsltbv =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        bvsltbv_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case _at_from_bools =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        from_bools_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case str_concat =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.str_concat) (smtOp := SmtTerm.str_concat)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          seq_binop_args_have_smt_translation_of_non_none
            (typeof_str_concat_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
        (by rfl) hTrans ih
  case str_substr =>
    exact
      is_closed_rec_apply_apply_apply_str_substr_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy) (fun hz => ih hZLt hEnv hz)
  case str_contains =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.str_contains) (smtOp := SmtTerm.str_contains)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          seq_binop_ret_args_have_smt_translation_of_non_none
            (typeof_str_contains_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
        (by rfl) hTrans ih
  case str_replace =>
    exact
      is_closed_rec_apply_apply_apply_str_replace_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy) (fun hz => ih hZLt hEnv hz)
  case str_indexof =>
    exact
      is_closed_rec_apply_apply_apply_str_indexof_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy) (fun hz => ih hZLt hEnv hz)
  case str_at =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.str_at) (smtOp := SmtTerm.str_at)
        root hEnv hXLt hYLt hZLt (by rfl)
        str_at_args_have_smt_translation_of_non_none (by rfl) hTrans ih
  case str_prefixof =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.str_prefixof) (smtOp := SmtTerm.str_prefixof)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          seq_binop_ret_args_have_smt_translation_of_non_none
            (typeof_str_prefixof_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
        (by rfl) hTrans ih
  case str_suffixof =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.str_suffixof) (smtOp := SmtTerm.str_suffixof)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          seq_binop_ret_args_have_smt_translation_of_non_none
            (typeof_str_suffixof_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
        (by rfl) hTrans ih
  case str_update =>
    exact
      is_closed_rec_apply_apply_apply_str_update_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy) (fun hz => ih hZLt hEnv hz)
  case str_lt =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.str_lt) (smtOp := SmtTerm.str_lt)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          seq_char_binop_args_have_smt_translation_of_non_none
            (ret := SmtType.Bool)
            (typeof_str_lt_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
        (by rfl) hTrans ih
  case str_leq =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.str_leq) (smtOp := SmtTerm.str_leq)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          seq_char_binop_args_have_smt_translation_of_non_none
            (ret := SmtType.Bool)
            (typeof_str_leq_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
        (by rfl) hTrans ih
  case str_replace_all =>
    exact
      is_closed_rec_apply_apply_apply_str_replace_all_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy) (fun hz => ih hZLt hEnv hz)
  case str_replace_re =>
    exact
      is_closed_rec_apply_apply_apply_str_replace_re_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy) (fun hz => ih hZLt hEnv hz)
  case str_replace_re_all =>
    exact
      is_closed_rec_apply_apply_apply_str_replace_re_all_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy) (fun hz => ih hZLt hEnv hz)
  case str_indexof_re =>
    exact
      is_closed_rec_apply_apply_apply_str_indexof_re_eq_and_bool_of_has_smt_translation
        hEnv hTrans (fun hx => ih hXLt hEnv hx)
        (fun hy => ih hYLt hEnv hy) (fun hz => ih hZLt hEnv hz)
  case re_range =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.re_range) (smtOp := SmtTerm.re_range)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          seq_char_binop_args_have_smt_translation_of_non_none
            (ret := SmtType.RegLan)
            (typeof_re_range_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
        (by rfl) hTrans ih
  case re_concat =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.re_concat) (smtOp := SmtTerm.re_concat)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          reglan_binop_args_have_smt_translation_of_non_none
            (typeof_re_concat_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
        (by rfl) hTrans ih
  case re_inter =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.re_inter) (smtOp := SmtTerm.re_inter)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          reglan_binop_args_have_smt_translation_of_non_none
            (typeof_re_inter_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
        (by rfl) hTrans ih
  case re_union =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.re_union) (smtOp := SmtTerm.re_union)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          reglan_binop_args_have_smt_translation_of_non_none
            (typeof_re_union_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
        (by rfl) hTrans ih
  case re_diff =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.re_diff) (smtOp := SmtTerm.re_diff)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          reglan_binop_args_have_smt_translation_of_non_none
            (typeof_re_diff_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
        (by rfl) hTrans ih
  case str_in_re =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.str_in_re) (smtOp := SmtTerm.str_in_re)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          seq_char_reglan_args_have_smt_translation_of_non_none
            (ret := SmtType.Bool)
            (typeof_str_in_re_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
        (by rfl) hTrans ih
  case seq_nth =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.seq_nth) (smtOp := SmtTerm.seq_nth)
        root hEnv hXLt hYLt hZLt (by rfl)
        seq_nth_args_have_smt_translation_of_non_none (by rfl) hTrans ih
  case _at_strings_deq_diff =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        strings_deq_diff_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case _at_strings_stoi_result =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        strings_stoi_result_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case _at_strings_itos_result =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        strings_itos_result_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case _at_strings_num_occur =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        strings_num_occur_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case _at_strings_num_occur_re =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        strings_num_occur_re_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case _at_strings_occur_index =>
    rcases
        strings_occur_index_args_have_smt_translation_of_has_smt_translation
          hTrans with
      ⟨hXTrans, hYTrans, hZTrans⟩
    exact
      is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
        hEnv (by decide) (by decide) hXTrans hYTrans hZTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
        (fun hz => ih hZLt hEnv hz)
  case _at_strings_occur_index_re =>
    rcases
        strings_occur_index_re_args_have_smt_translation_of_has_smt_translation
          hTrans with
      ⟨hXTrans, hYTrans, hZTrans⟩
    exact
      is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
        hEnv (by decide) (by decide) hXTrans hYTrans hZTrans
        (fun hx => ih hXLt hEnv hx) (fun hy => ih hYLt hEnv hy)
        (fun hz => ih hZLt hEnv hz)
  case tuple =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        tuple_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case set_union =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.set_union) (smtOp := SmtTerm.set_union)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          set_binop_args_have_smt_translation_of_non_none
            (typeof_set_union_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
        (by rfl) hTrans ih
  case set_inter =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.set_inter) (smtOp := SmtTerm.set_inter)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          set_binop_args_have_smt_translation_of_non_none
            (typeof_set_inter_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
        (by rfl) hTrans ih
  case set_minus =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.set_minus) (smtOp := SmtTerm.set_minus)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          set_binop_args_have_smt_translation_of_non_none
            (typeof_set_minus_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
        (by rfl) hTrans ih
  case set_member =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.set_member) (smtOp := SmtTerm.set_member)
        root hEnv hXLt hYLt hZLt (by rfl)
        set_member_args_have_smt_translation_of_non_none
        (by rfl) hTrans ih
  case set_subset =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_smt_binop_eq_and_bool_of_has_smt_translation
        (eoOp := UserOp.set_subset) (smtOp := SmtTerm.set_subset)
        root hEnv hXLt hYLt hZLt (by rfl)
        (fun hNN =>
          set_binop_ret_args_have_smt_translation_of_non_none
            (ret := SmtType.Bool)
            (typeof_set_subset_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
        (by rfl) hTrans ih
  case set_insert =>
    exact
      is_closed_rec_apply_apply_apply_set_insert_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt hTrans ih
  case _at_sets_deq_diff =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        sets_deq_diff_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case qdiv =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        qdiv_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case qdiv_total =>
    exact
      is_closed_rec_apply_apply_apply_uop_over_binary_of_args_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt
        qdiv_total_args_have_smt_translation_of_has_smt_translation
        (by rfl) hTrans ih
  case «forall» =>
    exact false_of_apply_apply_apply_forall_has_smt_translation hTrans
  case «exists» =>
    exact false_of_apply_apply_apply_exists_has_smt_translation hTrans
  all_goals
    exact
      is_closed_rec_apply_apply_apply_uop_generic_eq_and_bool_of_has_smt_translation
        root hEnv hXLt hYLt hZLt (by rfl) (by rfl) hTrans ih

theorem is_closed_rec_apply_apply_apply_apply_uop_any_eq_and_bool_of_has_smt_translation
    (root : Term)
    {op : UserOp} {w z y x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hWLt : sizeOf w < sizeOf root)
    (hZLt : sizeOf z < sizeOf root)
    (hYLt : sizeOf y < sizeOf root)
    (hXLt : sizeOf x < sizeOf root)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp op) w) z)
            y)
          x))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp op) w) z)
          y)
        x)
      env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp op) w) z)
          y)
        x)
      env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp op) w) z)
              y)
            x)
          env =
        Term.Boolean b :=
by
  cases op
  case _at_strings_replace_all_result =>
    rcases
        strings_replace_all_result_args_have_smt_translation_of_has_smt_translation
          hTrans with
      ⟨hWTrans, hZTrans, hYTrans, hXTrans⟩
    exact
      is_closed_rec_apply_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_arg_trans
        hEnv (by decide) (by decide)
        hWTrans hZTrans hYTrans hXTrans
        (fun hw => ih hWLt hEnv hw) (fun hz => ih hZLt hEnv hz)
        (fun hy => ih hYLt hEnv hy) (fun hx => ih hXLt hEnv hx)
  case _at_strings_replace_re_all_result =>
    rcases
        strings_replace_re_all_result_args_have_smt_translation_of_has_smt_translation
          hTrans with
      ⟨hWTrans, hZTrans, hYTrans, hXTrans⟩
    exact
      is_closed_rec_apply_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_arg_trans
        hEnv (by decide) (by decide)
        hWTrans hZTrans hYTrans hXTrans
        (fun hw => ih hWLt hEnv hw) (fun hz => ih hZLt hEnv hz)
        (fun hy => ih hYLt hEnv hy) (fun hx => ih hXLt hEnv hx)
  all_goals
    exact
      is_closed_rec_apply_generic_eq_and_bool_of_has_smt_translation
        hEnv
        (by
          intro q v vs hEq
          cases hEq
          rcases
              is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
                hTrans with hForall | hExists
          · cases hForall
          · cases hExists)
        (by intro vs hEq; cases hEq)
        (by intro vs hEq; cases hEq)
        (by rfl)
        (generic_apply_type_of_non_special_head_closed _ _
          (by
            intro s d i j hSel
            exact
              TranslationProofs.eo_to_smt_apply_ne_dt_sel
                _ _ s d i j hSel)
          (by
            intro s d i hTester
            exact
              TranslationProofs.eo_to_smt_apply_ne_dt_tester
                _ _ s d i hTester))
        hTrans
        (fun hFTrans =>
          is_closed_rec_apply_apply_apply_uop_any_eq_and_bool_of_has_smt_translation
            root hEnv hWLt hZLt hYLt hFTrans ih)
        (fun hXTrans => ih hXLt hEnv hXTrans)

theorem apply_dt_sel_arg_has_smt_translation_of_has_smt_translation
    {s : native_String} {d : DatatypeDecl} {i j : native_Nat} {x : Term}
    (hTrans : eoHasSmtTranslation (Term.Apply (Term.DtSel s d i j) x)) :
  eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans ⊢
  cases hReserved : __eo_to_smt_reserved_datatype_name s
  · have hTrans' :
        __smtx_typeof
            (SmtTerm.Apply
              (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j)
              (__eo_to_smt x)) ≠
          SmtType.None := by
      change
          __smtx_typeof
              (SmtTerm.Apply
                (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
                  (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j))
                (__eo_to_smt x)) ≠
            SmtType.None at hTrans
      rw [hReserved] at hTrans
      simpa [native_ite] using hTrans
    have hNN :
        term_has_non_none_type
          (SmtTerm.Apply
            (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j)
            (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      exact hTrans'
    have hXTy :
        __smtx_typeof (__eo_to_smt x) =
          SmtType.Datatype s (__eo_to_smt_datatype_decl d) :=
      dt_sel_arg_datatype_of_non_none hNN
    rw [hXTy]
    simp
  · exfalso
    change
        __smtx_typeof
            (SmtTerm.Apply
              (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
                (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j))
              (__eo_to_smt x)) ≠
          SmtType.None at hTrans
    rw [hReserved] at hTrans
    exact hTrans (by
      simpa [native_ite] using
        TranslationProofs.typeof_apply_none_eq (__eo_to_smt x))

theorem is_closed_rec_apply_dt_sel_eq_and_bool_of_has_smt_translation
    (root : Term)
    {s : native_String} {d : DatatypeDecl} {i j : native_Nat}
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hXLt : sizeOf x < sizeOf root)
    (hTrans : eoHasSmtTranslation (Term.Apply (Term.DtSel s d i j) x))
    (ih :
      ∀ {t env : Term} {vars : List SmtVarKey},
        sizeOf t < sizeOf root ->
          EoSmtVarEnv env vars ->
            eoHasSmtTranslation t ->
              __is_closed_rec t env = __eo_is_closed_rec t env ∧
                ∃ b, __eo_is_closed_rec t env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.DtSel s d i j) x) env =
    __eo_is_closed_rec (Term.Apply (Term.DtSel s d i j) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.DtSel s d i j) x) env =
        Term.Boolean b :=
by
  have hHead :
      __is_closed_rec (Term.DtSel s d i j) env =
        __eo_is_closed_rec (Term.DtSel s d i j) env ∧
        ∃ b, __eo_is_closed_rec (Term.DtSel s d i j) env = Term.Boolean b := by
    refine ⟨?_, ?_⟩
    · cases hEnv <;> simp [__is_closed_rec, __eo_is_closed_rec]
    · exact ⟨true, by cases hEnv <;> simp [__eo_is_closed_rec]⟩
  have hXTrans :
      eoHasSmtTranslation x :=
    apply_dt_sel_arg_has_smt_translation_of_has_smt_translation hTrans
  exact
    is_closed_rec_apply_generic_eq_and_bool_of_parts
      hEnv
      (by intro q v vs hEq; cases hEq)
      (by intro vs hEq; cases hEq)
      (by intro vs hEq; cases hEq)
      hHead
      (ih hXLt hEnv hXTrans)

theorem is_closed_rec_eq_and_bool_of_has_smt_translation_lt
    (n : Nat) {t env : Term} {vars : List SmtVarKey}
    (hLt : sizeOf t < n)
    (hEnv : EoSmtVarEnv env vars)
    (hTrans : eoHasSmtTranslation t) :
  __is_closed_rec t env = __eo_is_closed_rec t env ∧
    ∃ b, __eo_is_closed_rec t env = Term.Boolean b :=
by
  cases n with
  | zero =>
      omega
  | succ n =>
      let hRec :
          ∀ {u env' : Term} {vars' : List SmtVarKey},
            sizeOf u < sizeOf t ->
              EoSmtVarEnv env' vars' ->
                eoHasSmtTranslation u ->
                  __is_closed_rec u env' = __eo_is_closed_rec u env' ∧
                    ∃ b, __eo_is_closed_rec u env' = Term.Boolean b :=
        fun {u env'} {vars'} hULt hEnv' hTrans' =>
          is_closed_rec_eq_and_bool_of_has_smt_translation_lt
            n (t := u) (env := env') (vars := vars')
            (by omega) hEnv' hTrans'
      cases t
      case Stuck =>
        exfalso
        unfold eoHasSmtTranslation at hTrans
        change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
        exact hTrans TranslationProofs.smtx_typeof_none
      case UOp1 op x =>
        exact is_closed_rec_uop1_eq_and_bool_of_has_smt_translation
          hEnv hTrans
      case UOp2 op x y =>
        exact
          is_closed_rec_uop2_eq_and_bool_of_has_smt_translation
            hEnv hTrans
            (fun hXTrans => hRec (by simp; omega) hEnv hXTrans)
      case UOp3 op x y z =>
        exact
          is_closed_rec_uop3_eq_and_bool_of_has_smt_translation
            hEnv hTrans
            (fun hXTrans => hRec (by simp; omega) hEnv hXTrans)
            (fun hYTrans => hRec (by simp; omega) hEnv hYTrans)
      case Apply f x =>
        cases f
        case UOp op =>
          exact
            is_closed_rec_apply_uop_any_eq_and_bool_of_has_smt_translation
              (Term.Apply (Term.UOp op) x) hEnv (by simp; omega)
              hTrans hRec
        case UOp1 op idx =>
          exact
            is_closed_rec_apply_uop1_any_eq_and_bool_of_has_smt_translation
              (Term.Apply (Term.UOp1 op idx) x) hEnv (by simp; omega)
              hTrans hRec
        case UOp2 op i j =>
          exact
            is_closed_rec_apply_uop2_any_eq_and_bool_of_has_smt_translation
              (Term.Apply (Term.UOp2 op i j) x) hEnv (by simp; omega)
              (by simp; omega) hTrans hRec
        case UOp3 op a b c =>
          exact
            is_closed_rec_apply_uop3_any_eq_and_bool_of_has_smt_translation
              (Term.Apply (Term.UOp3 op a b c) x) hEnv
              (by simp; omega) (by simp; omega) hTrans hRec
        case DtSel s d i j =>
          exact
            is_closed_rec_apply_dt_sel_eq_and_bool_of_has_smt_translation
              (Term.Apply (Term.DtSel s d i j) x) hEnv
              (by simp; omega) hTrans hRec
        case Apply g y =>
          cases g
          case UOp op =>
            exact
              is_closed_rec_apply_apply_uop_any_eq_and_bool_of_has_smt_translation
                (Term.Apply (Term.Apply (Term.UOp op) y) x) hEnv
                (by simp; omega) (by simp; omega) hTrans hRec
          case UOp1 op idx =>
            exact
              is_closed_rec_apply_apply_uop1_any_eq_and_bool_of_has_smt_translation
                (Term.Apply (Term.Apply (Term.UOp1 op idx) y) x) hEnv
                (by simp; omega) (by simp; omega) hTrans hRec
          case Apply h z =>
            cases h
            case UOp op =>
              exact
                is_closed_rec_apply_apply_apply_uop_any_eq_and_bool_of_has_smt_translation
                  (Term.Apply
                    (Term.Apply (Term.Apply (Term.UOp op) z) y) x)
                  hEnv (by simp; omega) (by simp; omega)
                  (by simp; omega) hTrans hRec
            case Apply k w =>
              cases k
              case UOp op =>
                exact
                  is_closed_rec_apply_apply_apply_apply_uop_any_eq_and_bool_of_has_smt_translation
                    (Term.Apply
                      (Term.Apply
                        (Term.Apply (Term.Apply (Term.UOp op) w) z)
                        y)
                      x)
                    hEnv (by simp; omega) (by simp; omega)
                    (by simp; omega) (by simp; omega) hTrans hRec
              all_goals
                exact
                  is_closed_rec_apply_generic_eq_and_bool_of_has_smt_translation
                    hEnv
                    (by
                      intro q v vs hEq
                      cases hEq
                      rcases
                        is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
                          hTrans with hForall | hExists
                      · cases hForall
                      · cases hExists)
                    (by intro vs hEq; cases hEq)
                    (by intro vs hEq; cases hEq)
                    (TranslationProofs.eo_to_smt_apply_apply_apply_apply_eq_of_head_not_uop
                      _ w z y x (by intro op h; cases h))
                    (generic_apply_type_of_non_special_head_closed _ _
                      (by
                        intro s d i j hSel
                        exact
                          TranslationProofs.eo_to_smt_apply_ne_dt_sel
                            _ _ s d i j hSel)
                      (by
                        intro s d i hTester
                        exact
                          TranslationProofs.eo_to_smt_apply_ne_dt_tester
                            _ _ s d i hTester))
                    hTrans
                    (fun hFTrans => hRec (by simp; omega) hEnv hFTrans)
                    (fun hXTrans => hRec (by simp; omega) hEnv hXTrans)
            all_goals
              exact
                is_closed_rec_apply_generic_eq_and_bool_of_has_smt_translation
                  hEnv
                  (by
                    intro q v vs hEq
                    cases hEq
                    rcases
                      is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
                        hTrans with hForall | hExists
                    · cases hForall
                    · cases hExists)
                  (by intro vs hEq; cases hEq)
                  (by intro vs hEq; cases hEq)
                  (by rfl)
                  (generic_apply_type_of_non_special_head_closed _ _
                    (by
                      intro s d i j hSel
                      exact
                        TranslationProofs.eo_to_smt_apply_ne_dt_sel
                          _ _ s d i j hSel)
                    (by
                      intro s d i hTester
                      exact
                        TranslationProofs.eo_to_smt_apply_ne_dt_tester
                          _ _ s d i hTester))
                  hTrans
                  (fun hFTrans => hRec (by simp; omega) hEnv hFTrans)
                  (fun hXTrans => hRec (by simp; omega) hEnv hXTrans)
          all_goals
            exact
              is_closed_rec_apply_generic_eq_and_bool_of_has_smt_translation
                hEnv
                (by
                  intro q v vs hEq
                  cases hEq
                  rcases
                    is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
                      hTrans with hForall | hExists
                  · cases hForall
                  · cases hExists)
                (by intro vs hEq; cases hEq)
                (by intro vs hEq; cases hEq)
                (by rfl)
                (generic_apply_type_of_non_special_head_closed _ _
                  (by
                    intro s d i j hSel
                    exact
                      TranslationProofs.eo_to_smt_apply_ne_dt_sel
                        _ _ s d i j hSel)
                  (by
                    intro s d i hTester
                    exact
                      TranslationProofs.eo_to_smt_apply_ne_dt_tester
                        _ _ s d i hTester))
                hTrans
                (fun hFTrans => hRec (by simp; omega) hEnv hFTrans)
                (fun hXTrans => hRec (by simp; omega) hEnv hXTrans)
        all_goals
          exact
            is_closed_rec_apply_generic_eq_and_bool_of_has_smt_translation
              hEnv
              (by intro q v vs hEq; cases hEq)
              (by intro vs hEq; cases hEq)
              (by intro vs hEq; cases hEq)
              (by rfl)
              (generic_apply_type_of_non_special_head_closed _ _
                (by
                  intro s d i j hSel
                  rcases
                    TranslationProofs.eo_to_smt_eq_dt_sel_cases
                      _ s d i j hSel with hSelTerm | hPurify
                  · rcases hSelTerm with ⟨d0, hd, hTerm, hReserved⟩
                    cases hTerm
                  · rcases hPurify with ⟨z, hTerm, hz⟩
                    cases hTerm)
                (by
                  intro s d i hTester
                  exact
                    TranslationProofs.eo_to_smt_ne_dt_tester
                      _ s d i hTester))
              hTrans
              (fun hFTrans => hRec (by simp; omega) hEnv hFTrans)
              (fun hXTrans => hRec (by simp <;> omega) hEnv hXTrans)
      case Var name T =>
        exact is_closed_rec_var_eq_and_bool_any hEnv name T
      all_goals
        refine ⟨?_, ?_⟩
        · cases hEnv <;> simp [__is_closed_rec, __eo_is_closed_rec]
        · exact ⟨true, by cases hEnv <;> simp [__eo_is_closed_rec]⟩
termination_by n
decreasing_by
  all_goals omega

theorem is_closed_rec_eq_and_bool_of_has_smt_translation
    {t env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans : eoHasSmtTranslation t) :
  __is_closed_rec t env = __eo_is_closed_rec t env ∧
    ∃ b, __eo_is_closed_rec t env = Term.Boolean b :=
by
  exact
    is_closed_rec_eq_and_bool_of_has_smt_translation_lt
      (sizeOf t + 1) (by omega) hEnv hTrans

theorem is_closed_rec_eq_eo_is_closed_rec_of_has_smt_translation
    {t env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans : eoHasSmtTranslation t) :
  __is_closed_rec t env = __eo_is_closed_rec t env :=
by
  exact (is_closed_rec_eq_and_bool_of_has_smt_translation hEnv hTrans).1

theorem is_closed_rec_eq_eo_is_closed_of_has_smt_translation
    {t : Term} (hTrans : eoHasSmtTranslation t) :
  __is_closed_rec t Term.__eo_List_nil = __eo_is_closed t :=
by
  cases t
  case Stuck =>
    exfalso
    unfold eoHasSmtTranslation at hTrans
    change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
    exact hTrans TranslationProofs.smtx_typeof_none
  all_goals
    simpa [__eo_is_closed] using
      is_closed_rec_eq_eo_is_closed_rec_of_has_smt_translation
        EoSmtVarEnv.nil hTrans

theorem is_closed_rec_var_eq_eo_is_closed
    (s : native_String) (T : Term) :
  __is_closed_rec (Term.Var (Term.String s) T) Term.__eo_List_nil =
    __eo_is_closed (Term.Var (Term.String s) T) :=
by
  simpa [__eo_is_closed] using
    is_closed_rec_var_eq_eo_is_closed_rec_var
      EoSmtVarEnv.nil s T
