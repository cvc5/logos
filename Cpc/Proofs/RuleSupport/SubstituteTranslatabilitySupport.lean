module

public import Cpc.Proofs.RuleSupport.SubstituteTypeSupport
import all Cpc.Proofs.RuleSupport.SubstituteTypeSupport
public import Cpc.Proofs.Canonical
import all Cpc.Proofs.Canonical
public import Cpc.Proofs.Closed.ContainsAtomicTermListFree
import all Cpc.Proofs.Closed.ContainsAtomicTermListFree

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

/-!
# Substitution translatability support

Reusable SMT-translatability facts for `__substitute_simul_rec` in substitution
mode (`isr = false`). These are independent of the CPC `instantiate` rule; rule
files only need to provide the checker-side proof that actual terms match the
binder list.
-/

namespace SubstituteTranslatabilitySupport

/-- A translatable universal quantifier has a Boolean-translatable body. -/
theorem forall_body_has_bool_type_of_has_smt_translation
    (xs F : Term)
    (hForall : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)) :
    RuleProofs.eo_has_bool_type F := by
  unfold RuleProofs.eo_has_smt_translation at hForall
  unfold RuleProofs.eo_has_bool_type
  by_cases hNil : xs = Term.__eo_List_nil
  · subst xs
    exact False.elim (by
      apply hForall
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none)
  · have hForallNN :
        __smtx_typeof
            (SmtTerm.not
              (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F)))) ≠
          SmtType.None := by
      cases xs with
      | __eo_List_nil =>
          exact False.elim (hNil rfl)
      | _ =>
          change
            __smtx_typeof
                (SmtTerm.not
                  (__eo_to_smt_exists _ (SmtTerm.not (__eo_to_smt F)))) ≠
              SmtType.None at hForall
          exact hForall
    have hNotBool :
        __smtx_typeof
            (SmtTerm.not
              (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F)))) =
          SmtType.Bool :=
      smtx_typeof_not_eq_bool_of_non_none
        (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F))) hForallNN
    have hExistsBool :
        __smtx_typeof
            (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F))) =
          SmtType.Bool :=
      smtx_typeof_not_arg_eq_bool
        (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F))) hNotBool
    have hBodyNotBool :
        __smtx_typeof (SmtTerm.not (__eo_to_smt F)) = SmtType.Bool :=
      TranslationProofs.eo_to_smt_exists_body_bool_of_bool xs
        (SmtTerm.not (__eo_to_smt F)) hExistsBool
    exact smtx_typeof_not_arg_eq_bool (__eo_to_smt F) hBodyNotBool

/-- A translatable universal quantifier carries a reflected EO binder environment. -/
theorem forall_binders_env_of_has_smt_translation
    (xs F : Term)
    (hForall : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)) :
    ∃ vars, EoVarEnv xs vars := by
  exact eo_var_env_of_forall_has_smt_translation
    (by
      simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
        using hForall)

/-- Peels one binder from a Boolean-typed encoded existential. -/
theorem smtx_typeof_exists_tail_bool_of_cons_bool
    (s : native_String) (T xs : Term) (body : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) xs)
          body) = SmtType.Bool ->
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool := by
  intro hTy
  have hExists :
      __smtx_typeof
          (SmtTerm.exists s (__eo_to_smt_type T)
            (__eo_to_smt_exists xs body)) = SmtType.Bool := by
    simpa [__eo_to_smt_exists] using hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.exists s (__eo_to_smt_type T)
          (__eo_to_smt_exists xs body)) := by
    unfold term_has_non_none_type
    rw [hExists]
    simp
  exact exists_body_bool_of_non_none hNN

/-- The head type of a Boolean-typed encoded existential is well-formed. -/
theorem smtx_type_wf_of_exists_cons_bool
    (s : native_String) (T xs : Term) (body : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) xs)
          body) = SmtType.Bool ->
    __smtx_type_wf (__eo_to_smt_type T) = true := by
  intro hTy
  have hTail :
      __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool :=
    smtx_typeof_exists_tail_bool_of_cons_bool s T xs body hTy
  have hGuardNN :
      __smtx_typeof_guard_wf (__eo_to_smt_type T) SmtType.Bool ≠
        SmtType.None := by
    intro hNone
    have hExists :
        __smtx_typeof
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists xs body)) = SmtType.Bool := by
      simpa [__eo_to_smt_exists] using hTy
    rw [smtx_typeof_exists_term_eq, hTail] at hExists
    simp [native_ite, native_Teq, hNone] at hExists
  exact smtx_typeof_guard_wf_wf_of_non_none
    (__eo_to_smt_type T) SmtType.Bool hGuardNN

/-- Every binder in a Boolean-typed encoded existential has a well-formed type. -/
theorem smtx_type_wf_of_eo_var_env_exists_bool
    {xs : Term} {vars : List EoVarKey} {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hTy : __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool) :
    ∀ s T, (s, T) ∈ vars ->
      __smtx_type_wf (__eo_to_smt_type T) = true := by
  induction hEnv generalizing body with
  | nil =>
      intro s T hMem
      cases hMem
  | cons hTail ih =>
      rename_i s T xs tailVars
      intro s' T' hMem
      cases hMem with
      | head =>
          exact smtx_type_wf_of_exists_cons_bool s T xs body hTy
      | tail _ hTailMem =>
          have hTailTy :
              __smtx_typeof (__eo_to_smt_exists xs body) =
                SmtType.Bool :=
            smtx_typeof_exists_tail_bool_of_cons_bool s T xs body hTy
          exact ih hTailTy s' T' hTailMem

/-- A translatable universal quantifier has well-formed SMT binder types. -/
theorem forall_binder_types_wf_of_has_smt_translation
    {xs F : Term} {vars : List EoVarKey}
    (hForall : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hEnv : EoVarEnv xs vars) :
    ∀ s T, (s, T) ∈ vars ->
      __smtx_type_wf (__eo_to_smt_type T) = true := by
  cases hEnv with
  | nil =>
      intro s T hMem
      cases hMem
  | cons hTail =>
      rename_i s T env tailVars
      have hNotTy :
          __smtx_typeof
              (SmtTerm.not
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) env)
                  (SmtTerm.not (__eo_to_smt F)))) =
            SmtType.Bool :=
        smtx_typeof_not_eq_bool_of_non_none
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) env)
            (SmtTerm.not (__eo_to_smt F)))
          (by
            change
              __smtx_typeof
                  (SmtTerm.not
                    (__eo_to_smt_exists
                      (Term.Apply (Term.Apply Term.__eo_List_cons
                        (Term.Var (Term.String s) T)) env)
                      (SmtTerm.not (__eo_to_smt F)))) ≠
                SmtType.None
            simpa [RuleProofs.eo_has_smt_translation, __eo_to_smt, __eo_to_smt_exists, __eo_to_smt_type] using hForall)
      have hExistsTy :
          __smtx_typeof
              (__eo_to_smt_exists
                (Term.Apply (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s) T)) env)
                (SmtTerm.not (__eo_to_smt F))) =
            SmtType.Bool :=
        smtx_typeof_not_arg_eq_bool
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) env)
            (SmtTerm.not (__eo_to_smt F)))
          hNotTy
      exact
        smtx_type_wf_of_eo_var_env_exists_bool
          (EoVarEnv.cons (s := s) (T := T) hTail) hExistsTy

theorem smtx_typeof_eo_to_smt_exists_eq_bool_of_eo_var_env
    {xs : Term} {vars : List EoVarKey} {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool := by
  induction hEnv generalizing body with
  | nil =>
      simpa [__eo_to_smt_exists] using hBodyTy
  | cons hTail ih =>
      rename_i s T env tailVars
      exact
        closed_smtx_typeof_eo_to_smt_exists_cons_bool_of_tail_bool
          s T env body
          (hWf s T (List.Mem.head _))
          (ih
            (by
              intro s' T' hMem
              exact hWf s' T' (List.Mem.tail _ hMem))
            hBodyTy)

theorem smtx_typeof_not_of_arg_bool (t : SmtTerm)
    (hTy : __smtx_typeof t = SmtType.Bool) :
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool := by
  rw [__smtx_typeof.eq_def]
  change
    native_ite (native_Teq (__smtx_typeof t) SmtType.Bool)
      SmtType.Bool SmtType.None = SmtType.Bool
  rw [hTy]
  simp [native_Teq, native_ite]

/-- A translatable universal quantifier has a translatable body. -/
theorem forall_body_has_smt_translation_of_has_smt_translation
    (xs F : Term)
    (hForall : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)) :
    RuleProofs.eo_has_smt_translation F :=
  RuleProofs.eo_has_smt_translation_of_has_bool_type F
    (forall_body_has_bool_type_of_has_smt_translation xs F hForall)

/-- A translatable universal quantifier has a nonempty binder list. -/
theorem forall_binders_non_nil_of_has_smt_translation
    (xs F : Term)
    (hForall : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)) :
    xs ≠ Term.__eo_List_nil := by
  intro hNil
  subst xs
  unfold RuleProofs.eo_has_smt_translation at hForall
  exact hForall (by
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none)

/-- Unfolds the EO-to-SMT encoding of a nonempty universal quantifier. -/
theorem eo_to_smt_forall_eq_of_non_nil
    (xs F : Term) (hXs : xs ≠ Term.__eo_List_nil) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) =
      SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F))) := by
  cases xs with
  | __eo_List_nil => exact False.elim (hXs rfl)
  | _ => rfl

/-- A translated EO term evaluates to a canonical value of its SMT type. -/
theorem eo_to_smt_eval_typed_canonical
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t) :
    __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) ∧
      value_canonical (__smtx_model_eval M (__eo_to_smt t)) := by
  have hNN : term_has_non_none_type (__eo_to_smt t) := by
    simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hTrans
  exact ⟨smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) hNN,
    Smtm.model_eval_canonical M hM (__eo_to_smt t) hNN⟩

/-- Actuals are well-typed for the binders they instantiate in the ambient model. -/
inductive SubstActualsTyped (M : SmtModel) : Term -> Term -> Prop where
  | nil (ts : Term) :
      SubstActualsTyped M Term.__eo_List_nil ts
  | cons {s : native_String} {T env t ts : Term} :
      __smtx_type_wf (__eo_to_smt_type T) = true ->
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __eo_to_smt_type T ->
      __smtx_value_canonical (__smtx_model_eval M (__eo_to_smt t)) = true ->
      SubstActualsTyped M env ts ->
      SubstActualsTyped M
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) env)
        (Term.Apply (Term.Apply Term.__eo_List_cons t) ts)

/-- Syntactic actual-list typing against a binder list. -/
inductive SubstActualsHaveSmtTypes : Term -> Term -> Prop where
  | nil (ts : Term) :
      SubstActualsHaveSmtTypes Term.__eo_List_nil ts
  | cons {s : native_String} {T env t ts : Term} :
      __smtx_type_wf (__eo_to_smt_type T) = true ->
      RuleProofs.eo_has_smt_translation t ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type T ->
      SubstActualsHaveSmtTypes env ts ->
      SubstActualsHaveSmtTypes
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) env)
        (Term.Apply (Term.Apply Term.__eo_List_cons t) ts)

theorem SubstActualsHaveSmtTypes.env :
    ∀ {xs ts : Term},
      SubstActualsHaveSmtTypes xs ts ->
        ∃ vars, EoVarEnv xs vars
  | _, _, SubstActualsHaveSmtTypes.nil ts =>
      ⟨[], EoVarEnv.nil⟩
  | _, _, SubstActualsHaveSmtTypes.cons _hWf _hTrans _hTy hTail =>
      by
        rename_i s T env t ts
        rcases SubstActualsHaveSmtTypes.env hTail with ⟨vars, hEnv⟩
        exact ⟨(s, T) :: vars, EoVarEnv.cons hEnv⟩

theorem SubstActualsHaveSmtTypes.to_typed
    (M : SmtModel) (hM : model_wf M) :
    ∀ {xs ts : Term},
      SubstActualsHaveSmtTypes xs ts ->
        SubstActualsTyped M xs ts
  | _, _, SubstActualsHaveSmtTypes.nil ts =>
      SubstActualsTyped.nil ts
  | _, _, SubstActualsHaveSmtTypes.cons hWf hTrans hTy hTail =>
      by
        rename_i s T env t ts
        rcases eo_to_smt_eval_typed_canonical M hM t hTrans with
          ⟨hEvalTy, hEvalCan⟩
        exact SubstActualsTyped.cons hWf
          (by simpa [hTy] using hEvalTy)
          (by simpa [value_canonical] using hEvalCan)
          (SubstActualsHaveSmtTypes.to_typed M hM hTail)

theorem SubstActualsHaveSmtTypes.env_wf :
    ∀ {xs ts : Term},
      SubstActualsHaveSmtTypes xs ts ->
        ∃ vars, EoVarEnv xs vars ∧
          ∀ s T, (s, T) ∈ vars ->
            __smtx_type_wf (__eo_to_smt_type T) = true
  | _, _, SubstActualsHaveSmtTypes.nil ts =>
      ⟨[], EoVarEnv.nil, by
        intro s T hMem
        cases hMem⟩
  | _, _, SubstActualsHaveSmtTypes.cons hWf _hTrans _hTy hTail =>
      by
        rename_i s T env t ts
        rcases SubstActualsHaveSmtTypes.env_wf hTail with
          ⟨vars, hEnv, hVarsWf⟩
        refine ⟨(s, T) :: vars, EoVarEnv.cons hEnv, ?_⟩
        intro s' T' hMem
        cases hMem with
        | head =>
          exact hWf
        | tail _ hTailMem =>
          exact hVarsWf s' T' hTailMem

theorem SubstActualsHaveSmtTypes.wf_of_find_neg_false
    {xs ts : Term}
    (hActuals : SubstActualsHaveSmtTypes xs ts) :
    ∀ (s : native_String) (T : Term),
      __eo_is_neg (__eo_list_find Term.__eo_List_cons xs
        (Term.Var (Term.String s) T)) = Term.Boolean false ->
      __smtx_type_wf (__eo_to_smt_type T) = true := by
  intro s T hFind
  rcases SubstActualsHaveSmtTypes.env_wf hActuals with
    ⟨vars, hEnv, hVarsWf⟩
  have hMem : (s, T) ∈ vars :=
    EoVarEnvPerm.mem_of_find_neg_false (EoVarEnvPerm.of_exact hEnv) hFind
  exact hVarsWf s T hMem

theorem EoVarEnv.find_rec_succ_pred_of_mem
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
    ∀ {s : native_String} {T : Term},
      (s, T) ∈ vars ->
      ∀ n : native_Int,
        __eo_add
            (__eo_list_find_rec env (Term.Var (Term.String s) T)
              (Term.Numeral (native_zplus n 1)))
            (Term.Numeral (-1 : native_Int)) =
          __eo_list_find_rec env (Term.Var (Term.String s) T)
            (Term.Numeral n) := by
  induction hEnv with
  | nil =>
      intro s T hMem n
      cases hMem
  | cons hTail ih =>
      rename_i s0 T0 env vars
      intro s T hMem n
      by_cases hVarEq :
          Term.Var (Term.String s0) T0 =
            Term.Var (Term.String s) T
      · have hFindEq :
            __eo_eq (Term.Var (Term.String s0) T0)
                (Term.Var (Term.String s) T) =
              Term.Boolean true := by
          simp [__eo_eq, native_teq, hVarEq.symm]
        simp [__eo_list_find_rec, hFindEq, __eo_ite, __eo_add,
          native_ite, native_teq, native_zplus, Int.add_assoc]
      · have hVarEqSymm :
            Term.Var (Term.String s) T ≠
              Term.Var (Term.String s0) T0 := by
          intro h
          exact hVarEq h.symm
        have hFindEq :
            __eo_eq (Term.Var (Term.String s0) T0)
                (Term.Var (Term.String s) T) =
              Term.Boolean false := by
          simp [__eo_eq, native_teq, hVarEqSymm]
        have hTailMem : (s, T) ∈ vars := by
          cases hMem with
          | head =>
              exfalso
              exact hVarEq rfl
          | tail _ hTailMem =>
              exact hTailMem
        have hTailStep := ih hTailMem (native_zplus n 1)
        simpa [__eo_list_find_rec, hFindEq, __eo_ite, __eo_add,
          native_ite, native_teq, native_zplus, Int.add_assoc,
          Int.add_comm, Int.add_left_comm] using hTailStep

theorem EoVarEnv.find_rec_numeral_ne_zero_of_mem_pos
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
    ∀ {s : native_String} {T : Term},
      (s, T) ∈ vars ->
      ∀ n : native_Int,
        0 < n ->
          ∃ k : native_Int,
            __eo_list_find_rec env (Term.Var (Term.String s) T)
              (Term.Numeral n) = Term.Numeral k ∧
            k ≠ 0 := by
  induction hEnv with
  | nil =>
      intro s T hMem n hPos
      cases hMem
  | cons hTail ih =>
      rename_i s0 T0 env vars
      intro s T hMem n hPos
      by_cases hVarEq :
          Term.Var (Term.String s0) T0 =
            Term.Var (Term.String s) T
      · have hFindEq :
            __eo_eq (Term.Var (Term.String s0) T0)
                (Term.Var (Term.String s) T) =
              Term.Boolean true := by
          simp [__eo_eq, native_teq, hVarEq.symm]
        refine ⟨n, ?_, ?_⟩
        · simp [__eo_list_find_rec, hFindEq, __eo_ite, native_ite, native_teq]
        · intro hZero
          rw [hZero] at hPos
          exact (by decide : ¬ (0 : native_Int) < 0) hPos
      · have hVarEqSymm :
            Term.Var (Term.String s) T ≠
              Term.Var (Term.String s0) T0 := by
          intro h
          exact hVarEq h.symm
        have hFindEq :
            __eo_eq (Term.Var (Term.String s0) T0)
                (Term.Var (Term.String s) T) =
              Term.Boolean false := by
          simp [__eo_eq, native_teq, hVarEqSymm]
        have hTailMem : (s, T) ∈ vars := by
          cases hMem with
          | head =>
              exfalso
              exact hVarEq rfl
          | tail _ hTailMem =>
              exact hTailMem
        have hSuccPos : 0 < native_zplus n 1 := by
          have hLe : n ≤ native_zplus n 1 := by
            simpa [native_zplus] using
              (Int.le_add_of_nonneg_right
                (a := n) (by decide : (0 : native_Int) ≤ 1))
          exact Int.lt_of_lt_of_le hPos hLe
        rcases ih hTailMem (native_zplus n 1) hSuccPos with
          ⟨k, hFind, hNeZero⟩
        refine ⟨k, ?_, hNeZero⟩
        simpa [__eo_list_find_rec, hFindEq, __eo_ite, __eo_add,
          native_ite, native_teq] using hFind

theorem assoc_nil_nth_cons_find_tail_eq
    {env ts : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars)
    (s0 : native_String) (T0 t : Term)
    {s : native_String} {T : Term}
    (hHeadNe :
      Term.Var (Term.String s0) T0 ≠ Term.Var (Term.String s) T)
    (hTailMem : (s, T) ∈ vars) :
    __assoc_nil_nth Term.__eo_List_cons
        (Term.Apply (Term.Apply Term.__eo_List_cons t) ts)
        (__eo_list_find Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s0) T0)) env)
          (Term.Var (Term.String s) T)) =
      __assoc_nil_nth Term.__eo_List_cons ts
        (__eo_list_find Term.__eo_List_cons env
          (Term.Var (Term.String s) T)) := by
  have hTailList := hEnv.is_list
  have hConsList :
      __eo_is_list Term.__eo_List_cons
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s0) T0)) env) =
        Term.Boolean true := by
    simpa using (EoVarEnv.cons (s := s0) (T := T0) hEnv).is_list
  have hFindEq :
      __eo_eq (Term.Var (Term.String s0) T0)
          (Term.Var (Term.String s) T) =
        Term.Boolean false := by
    have hSym :
        Term.Var (Term.String s) T ≠
          Term.Var (Term.String s0) T0 := by
      intro h
      exact hHeadNe h.symm
    simp [__eo_eq, native_teq, hSym]
  rcases
      EoVarEnv.find_rec_numeral_ne_zero_of_mem_pos hEnv
        hTailMem 1 (by decide : (0 : native_Int) < 1) with
    ⟨k, hFindOne, hKNeZero⟩
  have hPred :=
    EoVarEnv.find_rec_succ_pred_of_mem hEnv hTailMem 0
  have hPred' :
      __eo_add (Term.Numeral k) (Term.Numeral (-1 : native_Int)) =
        __eo_list_find_rec env (Term.Var (Term.String s) T)
          (Term.Numeral 0) := by
    simpa [native_zplus, hFindOne] using hPred
  simp [__eo_list_find, __eo_requires, hTailList, hConsList,
    __eo_list_find_rec, hFindEq, __eo_ite, __eo_add, native_ite,
    native_teq, native_zplus, native_not, SmtEval.native_not]
  rw [hFindOne, ← hPred']
  by_cases hKZero : k = 0
  · exact False.elim (hKNeZero hKZero)
  · simp [__assoc_nil_nth, __eo_l_1___assoc_nil_nth, __eo_requires,
      __eo_eq, __eo_add, native_ite, native_teq,
      native_not, SmtEval.native_not, native_zplus, hKZero]

theorem SubstActualsHaveSmtTypes.entry_has_smt_translation :
    ∀ {xs ts : Term},
      SubstActualsHaveSmtTypes xs ts ->
        ∀ (s : native_String) (T : Term),
          __eo_is_neg (__eo_list_find Term.__eo_List_cons xs
            (Term.Var (Term.String s) T)) = Term.Boolean false ->
          eoHasSmtTranslation
            (__assoc_nil_nth Term.__eo_List_cons ts
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) T)))
  | _, _, SubstActualsHaveSmtTypes.nil ts =>
      by
        intro s T hFind
        have hFindTrue :
            __eo_is_neg
                (__eo_list_find Term.__eo_List_cons Term.__eo_List_nil
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true :=
          EoVarEnv.nil.find_neg_true_of_not_mem (by simp)
        rw [hFindTrue] at hFind
        cases hFind
  | _, _, SubstActualsHaveSmtTypes.cons _hWf hTrans _hTy hTail =>
      by
        rename_i s0 T0 env t ts
        intro s T hFind
        rcases SubstActualsHaveSmtTypes.env hTail with ⟨vars, hEnv⟩
        by_cases hHead :
            Term.Var (Term.String s0) T0 =
              Term.Var (Term.String s) T
        · have hAssoc :
              __assoc_nil_nth Term.__eo_List_cons
                  (Term.Apply (Term.Apply Term.__eo_List_cons t) ts)
                  (__eo_list_find Term.__eo_List_cons
                    (Term.Apply (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String s0) T0)) env)
                    (Term.Var (Term.String s) T)) =
                t := by
            cases hHead
            have hConsList :
                __eo_is_list Term.__eo_List_cons
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s0) T0)) env) =
                  Term.Boolean true := by
              simpa using (EoVarEnv.cons (s := s0) (T := T0) hEnv).is_list
            simp [__eo_list_find, __eo_requires, hConsList,
              __eo_list_find_rec, __eo_ite, __assoc_nil_nth, __eo_eq,
              native_ite, native_teq, native_not, SmtEval.native_not]
          simpa [hAssoc] using hTrans
        · have hConsEnv :
              EoVarEnv
                (Term.Apply (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s0) T0)) env)
                ((s0, T0) :: vars) :=
            EoVarEnv.cons hEnv
          have hMemCons : (s, T) ∈ (s0, T0) :: vars :=
            EoVarEnvPerm.mem_of_find_neg_false
              (EoVarEnvPerm.of_exact hConsEnv) hFind
          have hHeadKeyNe : (s, T) ≠ (s0, T0) := by
            intro hEq
            cases hEq
            exact hHead rfl
          have hTailMem : (s, T) ∈ vars := by
            cases hMemCons with
            | head =>
                exfalso
                exact hHeadKeyNe rfl
            | tail _ hTailMem =>
                exact hTailMem
          have hTailFind :
              __eo_is_neg (__eo_list_find Term.__eo_List_cons env
                (Term.Var (Term.String s) T)) = Term.Boolean false :=
            hEnv.find_neg_false_of_mem hTailMem
          have hAssoc :=
            assoc_nil_nth_cons_find_tail_eq (ts := ts)
              hEnv s0 T0 t hHead hTailMem
          rw [hAssoc]
          exact
            SubstActualsHaveSmtTypes.entry_has_smt_translation hTail
              s T hTailFind

theorem SubstActualsHaveSmtTypes.entry_smt_type_eq :
    ∀ {xs ts : Term},
      SubstActualsHaveSmtTypes xs ts ->
        ∀ (s : native_String) (T : Term),
          __eo_is_neg (__eo_list_find Term.__eo_List_cons xs
            (Term.Var (Term.String s) T)) = Term.Boolean false ->
          __smtx_typeof
              (__eo_to_smt
                (__assoc_nil_nth Term.__eo_List_cons ts
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)))) =
            __eo_to_smt_type T
  | _, _, SubstActualsHaveSmtTypes.nil ts =>
      by
        intro s T hFind
        have hFindTrue :
            __eo_is_neg
                (__eo_list_find Term.__eo_List_cons Term.__eo_List_nil
                  (Term.Var (Term.String s) T)) =
              Term.Boolean true :=
          EoVarEnv.nil.find_neg_true_of_not_mem (by simp)
        rw [hFindTrue] at hFind
        cases hFind
  | _, _, SubstActualsHaveSmtTypes.cons _hWf _hTrans hTy hTail =>
      by
        rename_i s0 T0 env t ts
        intro s T hFind
        rcases SubstActualsHaveSmtTypes.env hTail with ⟨vars, hEnv⟩
        by_cases hHead :
            Term.Var (Term.String s0) T0 =
              Term.Var (Term.String s) T
        · have hAssoc :
              __assoc_nil_nth Term.__eo_List_cons
                  (Term.Apply (Term.Apply Term.__eo_List_cons t) ts)
                  (__eo_list_find Term.__eo_List_cons
                    (Term.Apply (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String s0) T0)) env)
                    (Term.Var (Term.String s) T)) =
                t := by
            cases hHead
            have hConsList :
                __eo_is_list Term.__eo_List_cons
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s0) T0)) env) =
                  Term.Boolean true := by
              simpa using (EoVarEnv.cons (s := s0) (T := T0) hEnv).is_list
            simp [__eo_list_find, __eo_requires, hConsList,
              __eo_list_find_rec, __eo_ite, __assoc_nil_nth, __eo_eq,
              native_ite, native_teq, native_not, SmtEval.native_not]
          cases hHead
          simpa [hAssoc] using hTy
        · have hConsEnv :
              EoVarEnv
                (Term.Apply (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s0) T0)) env)
                ((s0, T0) :: vars) :=
            EoVarEnv.cons hEnv
          have hMemCons : (s, T) ∈ (s0, T0) :: vars :=
            EoVarEnvPerm.mem_of_find_neg_false
              (EoVarEnvPerm.of_exact hConsEnv) hFind
          have hHeadKeyNe : (s, T) ≠ (s0, T0) := by
            intro hEq
            cases hEq
            exact hHead rfl
          have hTailMem : (s, T) ∈ vars := by
            cases hMemCons with
            | head =>
                exfalso
                exact hHeadKeyNe rfl
            | tail _ hTailMem =>
                exact hTailMem
          have hTailFind :
              __eo_is_neg (__eo_list_find Term.__eo_List_cons env
                (Term.Var (Term.String s) T)) = Term.Boolean false :=
            hEnv.find_neg_false_of_mem hTailMem
          have hAssoc :=
            assoc_nil_nth_cons_find_tail_eq (ts := ts)
              hEnv s0 T0 t hHead hTailMem
          rw [hAssoc]
          exact
            SubstActualsHaveSmtTypes.entry_smt_type_eq hTail
              s T hTailFind

theorem SubstActualsHaveSmtTypes.entry_eo_type_eq
    {xs ts : Term}
    (hActuals : SubstActualsHaveSmtTypes xs ts) :
    ∀ (s : native_String) (T : Term),
      __eo_is_neg (__eo_list_find Term.__eo_List_cons xs
        (Term.Var (Term.String s) T)) = Term.Boolean false ->
      __eo_typeof
          (__assoc_nil_nth Term.__eo_List_cons ts
            (__eo_list_find Term.__eo_List_cons xs
              (Term.Var (Term.String s) T))) = T := by
  intro s T hFind
  let actual :=
    __assoc_nil_nth Term.__eo_List_cons ts
      (__eo_list_find Term.__eo_List_cons xs
        (Term.Var (Term.String s) T))
  have hActualTrans : RuleProofs.eo_has_smt_translation actual := by
    simpa [actual, RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using SubstActualsHaveSmtTypes.entry_has_smt_translation
        hActuals s T hFind
  exact SubstituteSupport.eo_typeof_eq_of_smt_type_eq actual T
    hActualTrans
    (SubstActualsHaveSmtTypes.wf_of_find_neg_false hActuals s T hFind)
    (by
      simpa [actual] using
        SubstActualsHaveSmtTypes.entry_smt_type_eq hActuals s T hFind)

/-- A translated EO term list is never `Stuck`. -/
theorem eoListAllHaveSmtTranslation_ne_stuck {ts : Term}
    (hTs : EoListAllHaveSmtTranslation ts) : ts ≠ Term.Stuck := by
  intro h
  subst ts
  cases hTs

theorem substitute_simul_rec_uop_eq_self
    {isRename : Bool} (op : UserOp) (xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts) :
    __substitute_simul_rec (Term.Boolean isRename) (Term.UOp op) xs ts bvs =
      Term.UOp op := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by
    cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadEq :
      __substitute_simul_rec (Term.Boolean isRename) (Term.UOp op) xs ts bvs =
        __eo_requires
          (__is_closed_rec (Term.UOp op) Term.__eo_List_nil)
          (Term.Boolean true) (Term.UOp op) :=
    SubstituteSupport.substitute_simul_rec_atom
      (Term.Boolean isRename) (Term.UOp op) xs ts bvs
      hisr hxs hts hbvs
      (by intro f a h; cases h)
      (by intro s S h; cases h)
      (by intro h; cases h)
  rw [hHeadEq]
  simp [__is_closed_rec, __eo_requires, native_ite, native_teq,
    native_not, SmtEval.native_not]

theorem substitute_simul_rec_uop1_eq_self
    {isRename : Bool} (op : UserOp1) (idx xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts) :
    __substitute_simul_rec (Term.Boolean isRename) (Term.UOp1 op idx) xs ts bvs =
      Term.UOp1 op idx := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by
    cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadEq :
      __substitute_simul_rec (Term.Boolean isRename) (Term.UOp1 op idx) xs ts bvs =
        __eo_requires
          (__is_closed_rec (Term.UOp1 op idx) Term.__eo_List_nil)
          (Term.Boolean true) (Term.UOp1 op idx) :=
    SubstituteSupport.substitute_simul_rec_atom
      (Term.Boolean isRename) (Term.UOp1 op idx) xs ts bvs
      hisr hxs hts hbvs
      (by intro f a h; cases h)
      (by intro s S h; cases h)
      (by intro h; cases h)
  rw [hHeadEq]
  simp [__is_closed_rec, __eo_requires, native_ite, native_teq,
    native_not, SmtEval.native_not]

theorem substitute_simul_rec_atom_eq_self_of_ne_stuck
    {isRename : Bool} (F xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotApply : ∀ f a, F ≠ Term.Apply f a)
    (hNotVar : ∀ s S, F ≠ Term.Var s S)
    (hNotStuck : F ≠ Term.Stuck)
    (hSubstNe :
      __substitute_simul_rec (Term.Boolean isRename) F xs ts bvs ≠ Term.Stuck) :
    __substitute_simul_rec (Term.Boolean isRename) F xs ts bvs = F := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by
    cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadEq :
      __substitute_simul_rec (Term.Boolean isRename) F xs ts bvs =
        __eo_requires (__is_closed_rec F Term.__eo_List_nil)
          (Term.Boolean true) F :=
    SubstituteSupport.substitute_simul_rec_atom
      (Term.Boolean isRename) F xs ts bvs
      hisr hxs hts hbvs hNotApply hNotVar hNotStuck
  rw [hHeadEq] at hSubstNe ⊢
  by_cases hck :
      native_teq (__is_closed_rec F Term.__eo_List_nil)
        (Term.Boolean true) = true
  · have hcTrue :
        __is_closed_rec F Term.__eo_List_nil = Term.Boolean true := by
      simpa only [native_teq, decide_eq_true_eq] using hck
    simp [__eo_requires, hcTrue, native_ite, native_teq, native_not,
      SmtEval.native_not]
  · have hReq :
        __eo_requires (__is_closed_rec F Term.__eo_List_nil)
            (Term.Boolean true) F =
          Term.Stuck := by
      simp [__eo_requires, native_ite, hck]
    exact False.elim (hSubstNe hReq)

theorem substitute_simul_rec_atom_head_eq_self_of_apply_subst_trans
    {isRename : Bool} (F a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        F ≠ Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hNotApply : ∀ f a, F ≠ Term.Apply f a)
    (hNotVar : ∀ s S, F ≠ Term.Var s S)
    (hNotStuck : F ≠ Term.Stuck)
    (hSubstTrans :
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename) (Term.Apply F a)
          xs ts bvs)) :
    __substitute_simul_rec (Term.Boolean isRename) F xs ts bvs = F := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by
    cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hApplyEq :
      __substitute_simul_rec (Term.Boolean isRename) (Term.Apply F a) xs ts bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename) F xs ts bvs)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) :=
    SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
      F a xs ts bvs hisr hxs hts hbvs hNotBinder
  have hApplyNe :
      __substitute_simul_rec (Term.Boolean isRename) (Term.Apply F a) xs ts bvs ≠
        Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hMkNe :
      __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename) F xs ts bvs)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) ≠
        Term.Stuck := by
    rw [← hApplyEq]
    exact hApplyNe
  have hHeadNe :
      __substitute_simul_rec (Term.Boolean isRename) F xs ts bvs ≠ Term.Stuck :=
    by
      intro h
      rw [h] at hMkNe
      exact hMkNe rfl
  exact
    substitute_simul_rec_atom_eq_self_of_ne_stuck (isRename := isRename) F xs ts bvs
      hXsEnv hBvsEnv hTs hNotApply hNotVar hNotStuck hHeadNe

set_option linter.unusedSimpArgs false in
theorem eo_typeof_to_real_arg_arith_of_ne_stuck {A : Term}
    (h : __eo_typeof_to_real A ≠ Term.Stuck) :
    A = Term.UOp UserOp.Int := by
  cases A <;>
    simp [__eo_typeof_to_real, __is_arith_type, __eo_requires,
      native_ite, native_teq, native_not, SmtEval.native_not] at h ⊢
  case UOp op =>
    cases op <;>
      simp [__eo_typeof_to_real, __is_arith_type, __eo_requires,
        native_ite, native_teq, native_not, SmtEval.native_not] at h ⊢

set_option linter.unusedSimpArgs false in
theorem eo_typeof_to_int_arg_real_of_ne_stuck {A : Term}
    (h : __eo_typeof_to_int A ≠ Term.Stuck) :
    A = Term.UOp UserOp.Real := by
  cases A <;> simp [__eo_typeof_to_int] at h ⊢
  case UOp op =>
    cases op <;> simp [__eo_typeof_to_int] at h ⊢

set_option linter.unusedSimpArgs false in
theorem eo_typeof_is_int_arg_real_of_ne_stuck {A : Term}
    (h : __eo_typeof_is_int A ≠ Term.Stuck) :
    A = Term.UOp UserOp.Real := by
  cases A <;> simp [__eo_typeof_is_int] at h ⊢
  case UOp op =>
    cases op <;> simp [__eo_typeof_is_int] at h ⊢

set_option linter.unusedSimpArgs false in
theorem eo_typeof_abs_arg_arith_of_ne_stuck {A : Term}
    (h : __eo_typeof_abs A ≠ Term.Stuck) :
    A = Term.UOp UserOp.Int ∨ A = Term.UOp UserOp.Real := by
  cases A <;>
    simp [__eo_typeof_abs, __is_arith_type, __eo_requires,
      native_ite, native_teq, native_not, SmtEval.native_not] at h ⊢
  case UOp op =>
    cases op <;>
      simp [__eo_typeof_abs, __is_arith_type, __eo_requires,
        native_ite, native_teq, native_not, SmtEval.native_not] at h ⊢

set_option linter.unusedSimpArgs false in
theorem eo_typeof_int_pow2_arg_int_of_ne_stuck {A : Term}
    (h : __eo_typeof_int_pow2 A ≠ Term.Stuck) :
    A = Term.UOp UserOp.Int := by
  cases A <;> simp [__eo_typeof_int_pow2] at h ⊢
  case UOp op =>
    cases op <;> simp [__eo_typeof_int_pow2] at h ⊢

set_option linter.unusedSimpArgs false in
theorem eo_typeof_int_ispow2_arg_int_of_ne_stuck {A : Term}
    (h : __eo_typeof_int_ispow2 A ≠ Term.Stuck) :
    A = Term.UOp UserOp.Int := by
  cases A <;> simp [__eo_typeof_int_ispow2] at h ⊢
  case UOp op =>
    cases op <;> simp [__eo_typeof_int_ispow2] at h ⊢

theorem eo_typeof_at_div_by_zero_arg_real_of_ne_stuck {A : Term}
    (h : __eo_typeof__at_div_by_zero A ≠ Term.Stuck) :
    A = Term.UOp UserOp.Real := by
  cases A <;> simp [__eo_typeof__at_div_by_zero] at h ⊢
  case UOp op =>
    cases op <;> simp at h ⊢

theorem eo_typeof_purify_eq (A : Term) :
    __eo_typeof__at_purify A = A := by
  cases A <;> rfl

theorem eo_typeof_bvnot_arg_bitvec_of_ne_stuck {A : Term}
    (h : __eo_typeof_bvnot A ≠ Term.Stuck) :
    ∃ w, A = Term.Apply (Term.UOp UserOp.BitVec) w := by
  cases A <;> simp [__eo_typeof_bvnot] at h ⊢
  case Apply f w =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢

theorem eo_typeof_bvnego_arg_bitvec_of_ne_stuck {A : Term}
    (h : __eo_typeof_bvnego A ≠ Term.Stuck) :
    ∃ w, A = Term.Apply (Term.UOp UserOp.BitVec) w := by
  cases A <;> simp [__eo_typeof_bvnego] at h ⊢
  case Apply f w =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢

theorem smt_typeof_bvnot_eq (t : SmtTerm) :
    __smtx_typeof (SmtTerm.bvnot t) =
      __smtx_typeof_bv_op_1 (__smtx_typeof t) := by
  rw [__smtx_typeof.eq_39]

theorem smt_typeof_bvneg_eq (t : SmtTerm) :
    __smtx_typeof (SmtTerm.bvneg t) =
      __smtx_typeof_bv_op_1 (__smtx_typeof t) := by
  rw [__smtx_typeof.eq_47]

theorem smt_typeof_bvnego_eq (t : SmtTerm) :
    __smtx_typeof (SmtTerm.bvnego t) =
      __smtx_typeof_bv_op_1_ret (__smtx_typeof t) SmtType.Bool := by
  rw [__smtx_typeof.eq_72]

theorem smt_typeof_bvcomp_eq (t u : SmtTerm) :
    __smtx_typeof (SmtTerm.bvcomp t u) =
      __smtx_typeof_bv_op_2_ret
        (__smtx_typeof t) (__smtx_typeof u) (SmtType.BitVec 1) := by
  rw [__smtx_typeof.eq_def] <;> simp only

theorem smt_typeof_binary_nat_to_int_zero (w : native_Nat) :
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

theorem smt_typeof_ubv_to_int_eq (t : SmtTerm) :
    __smtx_typeof (SmtTerm.ubv_to_int t) =
      __smtx_typeof_bv_op_1_ret (__smtx_typeof t) SmtType.Int := by
  rw [__smtx_typeof.eq_def] <;> simp only

theorem smt_typeof_sbv_to_int_eq (t : SmtTerm) :
    __smtx_typeof (SmtTerm.sbv_to_int t) =
      __smtx_typeof_bv_op_1_ret (__smtx_typeof t) SmtType.Int := by
  rw [__smtx_typeof.eq_def] <;> simp only

theorem smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
    {X w : Term}
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hXTy : __eo_typeof X = Term.Apply (Term.UOp UserOp.BitVec) w) :
    ∃ n : native_Nat, __smtx_typeof (__eo_to_smt X) = SmtType.BitVec n := by
  have hXMatch :
      __smtx_typeof (__eo_to_smt X) =
        __eo_to_smt_type (__eo_typeof X) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hXNonNone :
      __smtx_typeof (__eo_to_smt X) ≠ SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hXTrans
  rw [hXTy] at hXMatch
  cases w <;> simp [__eo_to_smt_type] at hXMatch hXNonNone
  case Numeral n =>
    by_cases hn : native_zleq 0 n = true
    · refine ⟨native_int_to_nat n, ?_⟩
      rw [hXMatch]
      simp [hn, native_ite]
    · rw [hXMatch] at hXNonNone
      simp [hn, native_ite] at hXNonNone
  all_goals
    exact False.elim (hXNonNone hXMatch)

theorem eo_typeof_str_len_arg_seq_of_ne_stuck {A : Term}
    (h : __eo_typeof_str_len A ≠ Term.Stuck) :
    ∃ V, A = Term.Apply (Term.UOp UserOp.Seq) V := by
  cases A <;> simp [__eo_typeof_str_len] at h ⊢
  case Apply f V =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢

theorem eo_typeof_str_rev_arg_seq_of_ne_stuck {A : Term}
    (h : __eo_typeof_str_rev A ≠ Term.Stuck) :
    ∃ V, A = Term.Apply (Term.UOp UserOp.Seq) V := by
  cases A <;> simp [__eo_typeof_str_rev] at h ⊢
  case Apply f V =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢

theorem eo_typeof_str_to_lower_arg_seq_char_of_ne_stuck {A : Term}
    (h : __eo_typeof_str_to_lower A ≠ Term.Stuck) :
    A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases A <;> simp [__eo_typeof_str_to_lower] at h ⊢
  case Apply f V =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      cases V <;> simp at h ⊢
      case UOp vop =>
        cases vop <;> simp at h ⊢

theorem eo_typeof_str_to_code_arg_seq_char_of_ne_stuck {A : Term}
    (h : __eo_typeof_str_to_code A ≠ Term.Stuck) :
    A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases A <;> simp [__eo_typeof_str_to_code] at h ⊢
  case Apply f V =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      cases V <;> simp at h ⊢
      case UOp vop =>
        cases vop <;> simp at h ⊢

theorem eo_typeof_str_from_code_arg_int_of_ne_stuck {A : Term}
    (h : __eo_typeof_str_from_code A ≠ Term.Stuck) :
    A = Term.UOp UserOp.Int := by
  cases A <;> simp [__eo_typeof_str_from_code] at h ⊢
  case UOp op =>
    cases op <;> simp at h ⊢

theorem eo_typeof_str_is_digit_arg_seq_char_of_ne_stuck {A : Term}
    (h : __eo_typeof_str_is_digit A ≠ Term.Stuck) :
    A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases A <;> simp [__eo_typeof_str_is_digit] at h ⊢
  case Apply f V =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      cases V <;> simp at h ⊢
      case UOp vop =>
        cases vop <;> simp at h ⊢

theorem eo_typeof_str_to_re_arg_seq_char_of_ne_stuck {A : Term}
    (h : __eo_typeof_str_to_re A ≠ Term.Stuck) :
    A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases A <;> simp [__eo_typeof_str_to_re] at h ⊢
  case Apply f V =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      cases V <;> simp at h ⊢
      case UOp vop =>
        cases vop <;> simp at h ⊢

theorem eo_typeof_re_mult_arg_reglan_of_ne_stuck {A : Term}
    (h : __eo_typeof_re_mult A ≠ Term.Stuck) :
    A = Term.UOp UserOp.RegLan := by
  cases A <;> simp [__eo_typeof_re_mult] at h ⊢
  case UOp op =>
    cases op <;> simp at h ⊢

theorem eo_typeof_bvsize_arg_bitvec_of_ne_stuck {A : Term}
    (h : __eo_typeof__at_bvsize A ≠ Term.Stuck) :
    ∃ w, A = Term.Apply (Term.UOp UserOp.BitVec) w := by
  cases A <;> simp [__eo_typeof__at_bvsize] at h ⊢
  case Apply f w =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢

theorem eo_typeof_bvredand_arg_bitvec_of_ne_stuck {A : Term}
    (h : __eo_typeof_bvredand A ≠ Term.Stuck) :
    ∃ w, A = Term.Apply (Term.UOp UserOp.BitVec) w := by
  cases A <;> simp [__eo_typeof_bvredand] at h ⊢
  case Apply f w =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢

theorem eo_typeof_set_choose_arg_set_of_ne_stuck {A : Term}
    (h : __eo_typeof_set_choose A ≠ Term.Stuck) :
    ∃ T, A = Term.Apply (Term.UOp UserOp.Set) T := by
  cases A <;> simp [__eo_typeof_set_choose] at h ⊢
  case Apply f T =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢

theorem eo_typeof_set_is_empty_arg_set_of_ne_stuck {A : Term}
    (h : __eo_typeof_set_is_empty A ≠ Term.Stuck) :
    ∃ T, A = Term.Apply (Term.UOp UserOp.Set) T := by
  cases A <;> simp [__eo_typeof_set_is_empty] at h ⊢
  case Apply f T =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢

theorem smt_typeof_eo_to_smt_set_of_typeof_set
    {X T : Term}
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hXTy : __eo_typeof X = Term.Apply (Term.UOp UserOp.Set) T) :
    __smtx_typeof (__eo_to_smt X) = SmtType.Set (__eo_to_smt_type T) := by
  have hXMatch :
      __smtx_typeof (__eo_to_smt X) =
        __eo_to_smt_type (__eo_typeof X) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hXSetGuard :
      __smtx_typeof (__eo_to_smt X) =
        __smtx_typeof_guard (__eo_to_smt_type T)
          (SmtType.Set (__eo_to_smt_type T)) := by
    simpa [hXTy, __eo_to_smt_type] using hXMatch
  have hGuardNS :
      __smtx_typeof_guard (__eo_to_smt_type T)
          (SmtType.Set (__eo_to_smt_type T)) ≠ SmtType.None := by
    intro hNone
    exact hXTrans (hXSetGuard.trans hNone)
  have hGuard :
      __smtx_typeof_guard (__eo_to_smt_type T)
          (SmtType.Set (__eo_to_smt_type T)) =
        SmtType.Set (__eo_to_smt_type T) := by
    unfold __smtx_typeof_guard at hGuardNS ⊢
    cases hT : native_Teq (__eo_to_smt_type T) SmtType.None <;>
      simp [native_ite, hT] at hGuardNS ⊢
  rw [hXSetGuard, hGuard]

theorem smt_typeof_set_empty_of_eo_set_arg
    {X T : Term}
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hXTy : __eo_typeof X = Term.Apply (Term.UOp UserOp.Set) T) :
    __smtx_typeof
        (SmtTerm.set_empty
          (__eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt X)))) =
      __smtx_typeof (__eo_to_smt X) := by
  have hXSet := smt_typeof_eo_to_smt_set_of_typeof_set hXTrans hXTy
  have hSetWf :
      __smtx_type_wf (SmtType.Set (__eo_to_smt_type T)) = true :=
    Smtm.smt_term_set_type_wf_of_non_none (__eo_to_smt X) hXTrans hXSet
  rw [smtx_typeof_set_empty_term_eq, hXSet]
  simp [__eo_to_smt_set_elem_type, __smtx_typeof_guard_wf, hSetWf,
    native_ite]

theorem smt_typeof_eo_to_smt_set_elem_ne_none_of_typeof_set
    {X T : Term}
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hXTy : __eo_typeof X = Term.Apply (Term.UOp UserOp.Set) T) :
    __eo_to_smt_type T ≠ SmtType.None := by
  have hXSet := smt_typeof_eo_to_smt_set_of_typeof_set hXTrans hXTy
  have hSetWf :
      __smtx_type_wf (SmtType.Set (__eo_to_smt_type T)) = true :=
    Smtm.smt_term_set_type_wf_of_non_none (__eo_to_smt X) hXTrans hXSet
  intro hNone
  rw [hNone] at hSetWf
  simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
    native_and, SmtEval.native_and] at hSetWf

theorem smt_typeof_eo_to_smt_seq_of_typeof_seq
    {X V : Term}
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hXTy : __eo_typeof X = Term.Apply (Term.UOp UserOp.Seq) V) :
    ∃ T : SmtType, __smtx_typeof (__eo_to_smt X) = SmtType.Seq T := by
  have hXMatch :
      __smtx_typeof (__eo_to_smt X) =
        __eo_to_smt_type (__eo_typeof X) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hXNonNone :
      __smtx_typeof (__eo_to_smt X) ≠ SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hXTrans
  rw [hXTy] at hXMatch
  cases hV : __eo_to_smt_type V <;>
    simp [__eo_to_smt_type, __smtx_typeof_guard, hV] at hXMatch hXNonNone
  case None =>
    exact False.elim (hXNonNone hXMatch)
  all_goals
    exact ⟨_, hXMatch⟩

theorem smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char
    {X : Term}
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hXTy :
      __eo_typeof X =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __smtx_typeof (__eo_to_smt X) = SmtType.Seq SmtType.Char := by
  have hXMatch :
      __smtx_typeof (__eo_to_smt X) =
        __eo_to_smt_type (__eo_typeof X) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  rw [hXMatch, hXTy]
  rfl

theorem smt_typeof_eo_to_smt_reglan_of_typeof_reglan
    {X : Term}
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hXTy : __eo_typeof X = Term.UOp UserOp.RegLan) :
    __smtx_typeof (__eo_to_smt X) = SmtType.RegLan := by
  have hXMatch :
      __smtx_typeof (__eo_to_smt X) =
        __eo_to_smt_type (__eo_typeof X) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  rw [hXMatch, hXTy]
  rfl

theorem smt_typeof_eo_to_smt_int_of_typeof_int
    {X : Term}
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hXTy : __eo_typeof X = Term.UOp UserOp.Int) :
    __smtx_typeof (__eo_to_smt X) = SmtType.Int := by
  have hXMatch :
      __smtx_typeof (__eo_to_smt X) =
        __eo_to_smt_type (__eo_typeof X) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  rw [hXMatch, hXTy]
  rfl

theorem instantiate_smt_term_ne_dt_sel_of_non_none_type
    {F : SmtTerm}
    (hF : __smtx_typeof F ≠ SmtType.None) :
    ∀ s d i j, F ≠ SmtTerm.DtSel s d i j := by
  intro s d i j h
  subst h
  exact hF (by simp)

theorem instantiate_smt_term_ne_dt_tester_of_non_none_type
    {F : SmtTerm}
    (hF : __smtx_typeof F ≠ SmtType.None) :
    ∀ s d i, F ≠ SmtTerm.DtTester s d i := by
  intro s d i h
  subst h
  exact hF (by simp)

theorem instantiate_generic_apply_type_of_has_smt_translation
    (f x : Term)
    (hF : RuleProofs.eo_has_smt_translation f) :
    generic_apply_type (__eo_to_smt f) (__eo_to_smt x) :=
  generic_apply_type_of_non_datatype_head
    (instantiate_smt_term_ne_dt_sel_of_non_none_type hF)
    (instantiate_smt_term_ne_dt_tester_of_non_none_type hF)

theorem instantiate_eo_typeof_apply_arg_stuck (F : Term) :
    __eo_typeof_apply F Term.Stuck = Term.Stuck := by
  cases F <;> rfl

theorem instantiate_eo_typeof_apply_dtc_eq_of_arg_ne_stuck
    (T U X : Term)
    (hX : X ≠ Term.Stuck) :
    __eo_typeof_apply (Term.DtcAppType T U) X =
      __eo_requires T X U := by
  cases X <;> simp [__eo_typeof_apply] at hX ⊢

theorem instantiate_eo_typeof_apply_fun_eq_of_arg_ne_stuck
    (T U X : Term)
    (hX : X ≠ Term.Stuck) :
    __eo_typeof_apply (Term.Apply (Term.Apply Term.FunType T) U) X =
      __eo_requires T X U := by
  cases X <;> simp [__eo_typeof_apply] at hX ⊢

theorem instantiate_eo_requires_arg_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> x = y := by
  intro h
  unfold __eo_requires at h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [hxy, native_ite] at h

theorem instantiate_eo_requires_result_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> __eo_requires x y z = z := by
  intro h
  unfold __eo_requires at h ⊢
  by_cases hxy : native_teq x y = true
  · by_cases hx : native_teq x Term.Stuck = true
    · simp [hxy, hx, native_ite, SmtEval.native_not] at h
    · simp [hxy, hx, native_ite, SmtEval.native_not]
  · simp [hxy, native_ite] at h

private theorem eo_type_valid_rec_dtc_app_args
    {refs : List native_String} {T U : Term}
    (h :
      TranslationProofs.eo_type_valid_rec refs
        (Term.DtcAppType T U)) :
    TranslationProofs.eo_type_valid_rec [] T ∧
      TranslationProofs.eo_type_valid_rec [] U := by
  unfold TranslationProofs.eo_type_valid_rec at h ⊢
  cases hT : __eo_to_smt_type T <;>
    cases hU : __eo_to_smt_type U <;>
      simp [__eo_to_smt_type, hT, hU, TranslationProofs.noNoneTy,
        __smtx_typeof_guard, native_ite, native_Teq, native_and] at h ⊢
  all_goals assumption

theorem instantiate_smtx_typeof_apply_non_none_of_eo_typeof_apply_non_stuck
    (F X : Term)
    (hFValid : TranslationProofs.eo_type_valid F)
    (hApp : __eo_typeof_apply F X ≠ Term.Stuck) :
    __smtx_typeof_apply (__eo_to_smt_type F) (__eo_to_smt_type X) ≠
      SmtType.None := by
  cases F with
  | DtcAppType T U =>
      have hXNN : X ≠ Term.Stuck := by
        intro hX
        subst X
        exact hApp (instantiate_eo_typeof_apply_arg_stuck _)
      rw [instantiate_eo_typeof_apply_dtc_eq_of_arg_ne_stuck T U X hXNN] at hApp
      have hAppReq : __eo_requires T X U ≠ Term.Stuck := hApp
      have hX : T = X := instantiate_eo_requires_arg_eq_of_ne_stuck hAppReq
      subst X
      have hValid : TranslationProofs.eo_type_valid_rec [] (Term.DtcAppType T U) := by
        simpa [TranslationProofs.eo_type_valid, TranslationProofs.eo_type_valid_rec, __eo_to_smt, __eo_to_smt_type, __smtx_typeof_guard] using hFValid
      rcases eo_type_valid_rec_dtc_app_args hValid with ⟨hT, hU⟩
      have hTNN : __eo_to_smt_type T ≠ SmtType.None :=
        TranslationProofs.eo_type_valid_rec_non_none hT
      have hUNN : __eo_to_smt_type U ≠ SmtType.None :=
        TranslationProofs.eo_type_valid_rec_non_none hU
      simp [__eo_to_smt_type, __smtx_typeof_apply, __smtx_typeof_guard,
        native_ite, native_Teq, hTNN, hUNN]
  | Apply f U =>
      cases f with
      | Apply f' T =>
          cases f' with
          | FunType =>
              have hXNN : X ≠ Term.Stuck := by
                intro hX
                subst X
                exact hApp (instantiate_eo_typeof_apply_arg_stuck _)
              rw [instantiate_eo_typeof_apply_fun_eq_of_arg_ne_stuck T U X hXNN] at hApp
              have hAppReq : __eo_requires T X U ≠ Term.Stuck := hApp
              have hX : T = X := instantiate_eo_requires_arg_eq_of_ne_stuck hAppReq
              subst X
              have hValid :
                  TranslationProofs.eo_type_valid_rec []
                    (Term.Apply (Term.Apply Term.FunType T) U) := by
                simpa [TranslationProofs.eo_type_valid, TranslationProofs.eo_type_valid_rec, __eo_to_smt, __eo_to_smt_type, __smtx_typeof_guard] using hFValid
              rcases eo_type_valid_rec_fun_args hValid with
                ⟨hT, hU⟩
              have hTNN : __eo_to_smt_type T ≠ SmtType.None :=
                TranslationProofs.eo_type_valid_rec_non_none hT
              have hUNN : __eo_to_smt_type U ≠ SmtType.None :=
                TranslationProofs.eo_type_valid_rec_non_none hU
              simp [TranslationProofs.eo_to_smt_type_fun,
                __smtx_typeof_apply, __smtx_typeof_guard, native_ite,
                native_Teq, hTNN, hUNN]
          | _ =>
              exact False.elim (hApp (by cases X <;> simp [__eo_typeof_apply]))
      | _ =>
          exact False.elim (hApp (by cases X <;> simp [__eo_typeof_apply]))
  | _ =>
      exact False.elim (hApp (by cases X <;> simp [__eo_typeof_apply]))

theorem instantiate_eo_to_smt_apply_generic_of_has_smt_translation
    (f x : Term)
    (hTransF : RuleProofs.eo_has_smt_translation f) :
    __eo_to_smt (Term.Apply f x) =
      SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x) := by
  unfold RuleProofs.eo_has_smt_translation at hTransF
  cases f <;> try rfl
  case UOp op =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hTransF
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case UOp1 op i =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hTransF
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case UOp2 op i j =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hTransF
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> try rfl
      all_goals
        exfalso
        apply hTransF
        change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt a)) =
          SmtType.None
        simp [__smtx_typeof, __smtx_typeof_apply]
    case UOp1 op i =>
      cases op <;> try rfl
      all_goals
        exfalso
        apply hTransF
        change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt a)) =
          SmtType.None
        simp [__smtx_typeof, __smtx_typeof_apply]
    case Apply f' b =>
      cases f' <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        all_goals
          exfalso
          apply hTransF
          change
            __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt b))
                (__eo_to_smt a)) = SmtType.None
          simp [__smtx_typeof, __smtx_typeof_apply]
      case Apply f'' c =>
        cases f'' <;> try rfl
        case UOp op =>
          cases op <;> try rfl
          all_goals
            exfalso
            apply hTransF
            change
              __smtx_typeof
                  (SmtTerm.Apply
                    (SmtTerm.Apply
                      (SmtTerm.Apply SmtTerm.None (__eo_to_smt c))
                      (__eo_to_smt b))
                    (__eo_to_smt a)) =
                SmtType.None
            simp [__smtx_typeof, __smtx_typeof_apply]

theorem instantiate_eo_typeof_apply_eq_of_has_smt_translation
    (f x : Term)
    (hTransF : RuleProofs.eo_has_smt_translation f) :
    __eo_typeof (Term.Apply f x) =
      __eo_typeof_apply (__eo_typeof f) (__eo_typeof x) := by
  exact TranslationProofs.eo_typeof_apply_eq_of_non_none_translation
    f x hTransF

theorem eo_has_smt_translation_apply_of_head_arg_translation_and_type
    (f x : Term)
    (hF : RuleProofs.eo_has_smt_translation f)
    (hX : RuleProofs.eo_has_smt_translation x)
    (hTy : __eo_typeof (Term.Apply f x) ≠ Term.Stuck) :
    RuleProofs.eo_has_smt_translation (Term.Apply f x) := by
  unfold RuleProofs.eo_has_smt_translation
  rw [instantiate_eo_to_smt_apply_generic_of_has_smt_translation f x hF]
  have hGeneric : generic_apply_type (__eo_to_smt f) (__eo_to_smt x) :=
    instantiate_generic_apply_type_of_has_smt_translation f x hF
  unfold generic_apply_type at hGeneric
  rw [hGeneric]
  have hFMatch :
      __smtx_typeof (__eo_to_smt f) = __eo_to_smt_type (__eo_typeof f) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation f hF
  have hXMatch :
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hX
  rw [hFMatch, hXMatch]
  have hEoApply :
      __eo_typeof_apply (__eo_typeof f) (__eo_typeof x) ≠ Term.Stuck := by
    have hEq := instantiate_eo_typeof_apply_eq_of_has_smt_translation f x hF
    rwa [← hEq]
  have hFValid :
      TranslationProofs.eo_type_valid (__eo_typeof f) :=
    TranslationProofs.eo_type_valid_typeof_of_smt_translation f hF
  exact instantiate_smtx_typeof_apply_non_none_of_eo_typeof_apply_non_stuck
    (__eo_typeof f) (__eo_typeof x) hFValid hEoApply

theorem eo_has_smt_translation_mk_apply_of_head_arg_translation_and_type
    (f x : Term)
    (hF : RuleProofs.eo_has_smt_translation f)
    (hX : RuleProofs.eo_has_smt_translation x)
    (hTy : __eo_typeof (__eo_mk_apply f x) ≠ Term.Stuck) :
    RuleProofs.eo_has_smt_translation (__eo_mk_apply f x) := by
  have hfNe : f ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation f hF
  have hxNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hX
  have hMk : __eo_mk_apply f x = Term.Apply f x := by
    cases f <;> cases x <;> simp [__eo_mk_apply] at hfNe hxNe ⊢
  rw [hMk] at hTy ⊢
  exact eo_has_smt_translation_apply_of_head_arg_translation_and_type
    f x hF hX hTy

theorem instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck {f x : Term} :
    __eo_mk_apply f x ≠ Term.Stuck ->
      f ≠ Term.Stuck := by
  intro h hf
  subst f
  cases x <;> simp [__eo_mk_apply] at h

theorem instantiate_eo_mk_apply_arg_ne_stuck_of_ne_stuck {f x : Term} :
    __eo_mk_apply f x ≠ Term.Stuck ->
      x ≠ Term.Stuck := by
  intro h hx
  subst x
  cases f <;> simp [__eo_mk_apply] at h

theorem instantiate_eo_mk_apply_eq_apply_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  have hf := instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck h
  have hx := instantiate_eo_mk_apply_arg_ne_stuck_of_ne_stuck h
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

theorem instantiate_eo_mk_apply_ne_stuck_of_typeof_ne_stuck {f x : Term}
    (hTy : __eo_typeof (__eo_mk_apply f x) ≠ Term.Stuck) :
    __eo_mk_apply f x ≠ Term.Stuck := by
  intro hStuck
  apply hTy
  rw [hStuck]
  rfl

theorem instantiate_eo_mk_apply_eq_apply_of_typeof_ne_stuck (f x : Term)
    (hTy : __eo_typeof (__eo_mk_apply f x) ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x :=
  instantiate_eo_mk_apply_eq_apply_of_ne_stuck f x
    (instantiate_eo_mk_apply_ne_stuck_of_typeof_ne_stuck hTy)

theorem eo_typeof_eo_var_env_eq_list
    {xs : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv xs vars) :
    __eo_typeof xs = Term.__eo_List := by
  induction hEnv with
  | nil => rfl
  | cons hTail ih =>
      exact TranslationProofs.eo_typeof_list_cons_var _ _ _ ih

theorem eo_typeof_forall_body_bool_of_ne_stuck {T U : Term}
    (hT : T = Term.__eo_List)
    (hTy : __eo_typeof_forall T U ≠ Term.Stuck) :
    U = Term.Bool := by
  subst T
  cases U <;> try rfl
  all_goals
    exfalso
    apply hTy
    simp [__eo_typeof_forall]

theorem eo_typeof_body_bool_of_quant_type_ne_stuck
    {q xs body : Term} {vars : List EoVarKey}
    (hQ : q = Term.UOp UserOp.forall ∨ q = Term.UOp UserOp.exists)
    (hEnv : EoVarEnv xs vars)
    (hTy :
      __eo_typeof (Term.Apply (Term.Apply q xs) body) ≠ Term.Stuck) :
    __eo_typeof body = Term.Bool := by
  rcases hQ with rfl | rfl
  · change
      __eo_typeof_forall (__eo_typeof xs) (__eo_typeof body) ≠
        Term.Stuck at hTy
    exact eo_typeof_forall_body_bool_of_ne_stuck
      (eo_typeof_eo_var_env_eq_list hEnv) hTy
  · change
      __eo_typeof_forall (__eo_typeof xs) (__eo_typeof body) ≠
        Term.Stuck at hTy
    exact eo_typeof_forall_body_bool_of_ne_stuck
      (eo_typeof_eo_var_env_eq_list hEnv) hTy

theorem eo_has_smt_translation_quant_of_body_translation_and_type
    (q xs body : Term)
    {vars : List EoVarKey}
    (hQ : q = Term.UOp UserOp.forall ∨ q = Term.UOp UserOp.exists)
    (hEnv : EoVarEnv xs vars)
    (hNonNil : xs ≠ Term.__eo_List_nil)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hBodyTrans : RuleProofs.eo_has_smt_translation body)
    (hTy : __eo_typeof (Term.Apply (Term.Apply q xs) body) ≠ Term.Stuck) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply q xs) body) := by
  have hBodyEoBool : __eo_typeof body = Term.Bool :=
    eo_typeof_body_bool_of_quant_type_ne_stuck hQ hEnv hTy
  have hBodySmtBool : __smtx_typeof (__eo_to_smt body) = SmtType.Bool := by
    have hMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation body hBodyTrans
    rw [hMatch, hBodyEoBool]
    rfl
  rcases hQ with rfl | rfl
  · cases hEnv with
    | nil =>
        exact False.elim (hNonNil rfl)
    | cons hTail =>
      rename_i s T env tailVars
      unfold RuleProofs.eo_has_smt_translation
      change
        __smtx_typeof
            (SmtTerm.not
              (__eo_to_smt_exists
                (Term.Apply (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s) T)) env)
                (SmtTerm.not (__eo_to_smt body)))) ≠
          SmtType.None
      have hNotBodyBool :
          __smtx_typeof (SmtTerm.not (__eo_to_smt body)) = SmtType.Bool :=
        smtx_typeof_not_of_arg_bool (__eo_to_smt body) hBodySmtBool
      have hExistsBool :
          __smtx_typeof
              (__eo_to_smt_exists
                (Term.Apply (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s) T)) env)
                (SmtTerm.not (__eo_to_smt body))) =
            SmtType.Bool :=
        smtx_typeof_eo_to_smt_exists_eq_bool_of_eo_var_env
          (EoVarEnv.cons (s := s) (T := T) hTail)
          hWf hNotBodyBool
      have hForallBool :
          __smtx_typeof
              (SmtTerm.not
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) env)
                  (SmtTerm.not (__eo_to_smt body)))) =
            SmtType.Bool :=
        smtx_typeof_not_of_arg_bool
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) env)
            (SmtTerm.not (__eo_to_smt body))) hExistsBool
      intro hNone
      rw [hForallBool] at hNone
      cases hNone
  · cases hEnv with
    | nil =>
        exact False.elim (hNonNil rfl)
    | cons hTail =>
      rename_i s T env tailVars
      unfold RuleProofs.eo_has_smt_translation
      change
        __smtx_typeof
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons
                (Term.Var (Term.String s) T)) env)
              (__eo_to_smt body)) ≠
          SmtType.None
      have hExistsBool :
          __smtx_typeof
              (__eo_to_smt_exists
                (Term.Apply (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s) T)) env)
                (__eo_to_smt body)) =
            SmtType.Bool :=
        smtx_typeof_eo_to_smt_exists_eq_bool_of_eo_var_env
          (EoVarEnv.cons (s := s) (T := T) hTail)
          hWf hBodySmtBool
      intro hNone
      rw [hExistsBool] at hNone
      cases hNone

theorem quant_binder_types_wf_of_has_smt_translation
    {Q xs F : Term} {vars : List EoVarKey}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply Q xs) F))
    (hEnv : EoVarEnv xs vars) :
    ∀ s T, (s, T) ∈ vars ->
      __smtx_type_wf (__eo_to_smt_type T) = true := by
  rcases hQ with hForall | hExists
  · subst Q
    cases hEnv with
    | nil =>
        intro s T hMem
        cases hMem
    | cons hTail =>
        rename_i s T env tailVars
        have hNotTy :
            __smtx_typeof
                (SmtTerm.not
                  (__eo_to_smt_exists
                    (Term.Apply (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String s) T)) env)
                    (SmtTerm.not (__eo_to_smt F)))) =
              SmtType.Bool :=
          smtx_typeof_not_eq_bool_of_non_none
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons
                (Term.Var (Term.String s) T)) env)
              (SmtTerm.not (__eo_to_smt F)))
            (by
              change
                __smtx_typeof
                    (SmtTerm.not
                      (__eo_to_smt_exists
                        (Term.Apply (Term.Apply Term.__eo_List_cons
                          (Term.Var (Term.String s) T)) env)
                        (SmtTerm.not (__eo_to_smt F)))) ≠
                  SmtType.None
              simpa [RuleProofs.eo_has_smt_translation, __eo_to_smt, __eo_to_smt_exists, __eo_to_smt_type] using hTrans)
        have hExistsTy :
            __smtx_typeof
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) env)
                  (SmtTerm.not (__eo_to_smt F))) =
              SmtType.Bool :=
          smtx_typeof_not_arg_eq_bool
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons
                (Term.Var (Term.String s) T)) env)
              (SmtTerm.not (__eo_to_smt F))) hNotTy
        exact
          smtx_type_wf_of_eo_var_env_exists_bool
            (EoVarEnv.cons (s := s) (T := T) hTail) hExistsTy
  · subst Q
    cases hEnv with
    | nil =>
        intro s T hMem
        cases hMem
    | cons hTail =>
        rename_i s T env tailVars
        have hExistsTy :
            __smtx_typeof
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) env)
                  (__eo_to_smt F)) =
              SmtType.Bool :=
          smtx_typeof_eo_to_smt_exists_cons_eq_bool_of_non_none
            (Term.Var (Term.String s) T) env (__eo_to_smt F)
            (by
              change
                __smtx_typeof
                    (__eo_to_smt_exists
                      (Term.Apply (Term.Apply Term.__eo_List_cons
                        (Term.Var (Term.String s) T)) env)
                      (__eo_to_smt F)) ≠
                  SmtType.None
              simpa [RuleProofs.eo_has_smt_translation, __eo_to_smt, __eo_to_smt_exists, __eo_to_smt_type] using hTrans)
        exact
          smtx_type_wf_of_eo_var_env_exists_bool
            (EoVarEnv.cons (s := s) (T := T) hTail) hExistsTy

/-- Non-binder application case for substitution-result translatability. The
recursive calls provide translatability for the substituted head and argument;
the non-`Stuck` result type then reconstructs translatability of the rebuilt
application. -/
theorem substitute_simul_apply_has_smt_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (f a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        f ≠ Term.Apply q
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFSubTrans :
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename) f xs ts bvs))
    (hASubTrans :
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply f a) xs ts bvs) ≠
        Term.Stuck) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean isRename)
        (Term.Apply f a) xs ts bvs) := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply f a) xs ts bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename) f xs ts bvs)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) :=
    SubstituteSupport.substitute_simul_rec_apply
      (Term.Boolean isRename) f a xs ts bvs
      hisr hxs hts hbvs hNotBinder
  rw [hSubstEq] at hTy ⊢
  exact
    eo_has_smt_translation_mk_apply_of_head_arg_translation_and_type
      (__substitute_simul_rec (Term.Boolean isRename) f xs ts bvs)
      (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs)
      hFSubTrans hASubTrans hTy

/-- Common substitution-result translatability proof for unary special heads.

The bare operator head is not necessarily an SMT-translatable term, so the
generic application lemma cannot be used directly. This helper performs the
shared substitution/mk-apply reconstruction and leaves only the operator's
argument translatability and rebuilt application translatability to the caller.
-/
theorem substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (op : UserOp) (a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.UOp op ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp op) a))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) a) xs ts bvs) ≠
        Term.Stuck)
    (hArgExtract :
      eoHasSmtTranslation (Term.Apply (Term.UOp op) a) ->
        eoHasSmtTranslation a)
    (hArgTyNe :
      ∀ X,
        __eo_typeof (Term.Apply (Term.UOp op) X) ≠ Term.Stuck ->
          __eo_typeof X ≠ Term.Stuck)
    (hBuild :
      ∀ X,
        RuleProofs.eo_has_smt_translation X ->
          __eo_typeof (Term.Apply (Term.UOp op) X) ≠ Term.Stuck ->
            RuleProofs.eo_has_smt_translation
              (Term.Apply (Term.UOp op) X))
    (hRecArg :
      RuleProofs.eo_has_smt_translation a ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) ≠
          Term.Stuck ->
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs)) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean isRename)
        (Term.Apply (Term.UOp op) a) xs ts bvs) := by
  let aSub := __substitute_simul_rec (Term.Boolean isRename) a xs ts bvs
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp op) xs ts bvs =
        Term.UOp op :=
    substitute_simul_rec_uop_eq_self op xs ts bvs hXsEnv hBvsEnv hTs
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) a) xs ts bvs =
        __eo_mk_apply (Term.UOp op) aSub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.UOp op) a xs ts bvs
        hisr hxs hts hbvs hNotBinder
    simpa [aSub, hHeadSub] using hApplyEq
  have hTyMk :
      __eo_typeof (__eo_mk_apply (Term.UOp op) aSub) ≠ Term.Stuck := by
    rwa [hSubstEq] at hTy
  have hMk :
      __eo_mk_apply (Term.UOp op) aSub =
        Term.Apply (Term.UOp op) aSub :=
    instantiate_eo_mk_apply_eq_apply_of_typeof_ne_stuck
      (Term.UOp op) aSub hTyMk
  have hTyApply :
      __eo_typeof (Term.Apply (Term.UOp op) aSub) ≠ Term.Stuck := by
    rwa [hMk] at hTyMk
  have hFTransEo :
      eoHasSmtTranslation (Term.Apply (Term.UOp op) a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hFTrans
  have hATrans :
      RuleProofs.eo_has_smt_translation a := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hArgExtract hFTransEo
  have hASubTrans :
      RuleProofs.eo_has_smt_translation aSub :=
    hRecArg hATrans (hArgTyNe aSub hTyApply)
  rw [hSubstEq, hMk]
  exact hBuild aSub hASubTrans hTyApply

/-- Common substitution-result translatability proof for binary special heads.

Partial binary operator heads such as `(and x)` are not themselves SMT
translatable, so the generic application helper cannot recurse through the
head. This helper substitutes the two operands directly and lets the caller
provide the operator-specific argument inversion and rebuilt-application proof.
-/
theorem substitute_simul_binary_op_has_smt_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (op : UserOp) (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp op) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) ≠
        Term.Stuck)
    (hArgExtract :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x) y) ->
        eoHasSmtTranslation x ∧ eoHasSmtTranslation y)
    (hArgTyNe :
      ∀ X Y,
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) X) Y) ≠
          Term.Stuck ->
        __eo_typeof X ≠ Term.Stuck ∧ __eo_typeof Y ≠ Term.Stuck)
    (hBuild :
      ∀ X Y,
        RuleProofs.eo_has_smt_translation X ->
          RuleProofs.eo_has_smt_translation Y ->
          __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) X) Y) ≠
            Term.Stuck ->
          RuleProofs.eo_has_smt_translation
            (Term.Apply (Term.Apply (Term.UOp op) X) Y))
    (hRecX :
      RuleProofs.eo_has_smt_translation x ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs) ≠
          Term.Stuck ->
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs))
    (hRecY :
      RuleProofs.eo_has_smt_translation y ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs) ≠
          Term.Stuck ->
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs)) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean isRename)
        (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) := by
  let xSub := __substitute_simul_rec (Term.Boolean isRename) x xs ts bvs
  let ySub := __substitute_simul_rec (Term.Boolean isRename) y xs ts bvs
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp op) xs ts bvs =
        Term.UOp op :=
    substitute_simul_rec_uop_eq_self op xs ts bvs hXsEnv hBvsEnv hTs
  have hInnerSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) x) xs ts bvs =
        __eo_mk_apply (Term.UOp op) xSub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.UOp op) x xs ts bvs
        hisr hxs hts hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [xSub, hHeadSub] using hApplyEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs =
        __eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.Apply (Term.UOp op) x) y xs ts bvs
        hisr hxs hts hbvs hNotBinder
    simpa [ySub, hInnerSub] using hApplyEq
  have hTyMk :
      __eo_typeof
          (__eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub) ≠
        Term.Stuck := by
    rwa [hSubstEq] at hTy
  have hOuterNe :
      __eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_ne_stuck_of_typeof_ne_stuck hTyMk
  have hInnerNe :
      __eo_mk_apply (Term.UOp op) xSub ≠ Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNe
  have hInnerMk :
      __eo_mk_apply (Term.UOp op) xSub =
        Term.Apply (Term.UOp op) xSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck
      (Term.UOp op) xSub hInnerNe
  have hOuterMk :
      __eo_mk_apply (Term.Apply (Term.UOp op) xSub) ySub =
        Term.Apply (Term.Apply (Term.UOp op) xSub) ySub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp op) xSub) ySub (by
        rw [← hInnerMk]
        exact hOuterNe)
  have hTyApply :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) xSub) ySub) ≠
        Term.Stuck := by
    rwa [hInnerMk, hOuterMk] at hTyMk
  have hFTransEo :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x) y) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hFTrans
  rcases hArgExtract hFTransEo with ⟨hXTransEo, hYTransEo⟩
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hXTransEo
  have hYTrans : RuleProofs.eo_has_smt_translation y := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hYTransEo
  rcases hArgTyNe xSub ySub hTyApply with ⟨hXSubTy, hYSubTy⟩
  have hXSubTrans : RuleProofs.eo_has_smt_translation xSub :=
    hRecX hXTrans hXSubTy
  have hYSubTrans : RuleProofs.eo_has_smt_translation ySub :=
    hRecY hYTrans hYSubTy
  rw [hSubstEq, hInnerMk, hOuterMk]
  exact hBuild xSub ySub hXSubTrans hYSubTrans hTyApply

/-- Quantifier-shaped substitution case: a non-`Stuck` type for the whole
substitution result forces the capture-avoidance `requires` guard to return the
rebuilt quantified body. This isolates the binder-specific unfolding from the
ordinary application case. -/
theorem substitute_simul_quant_eq_of_typeof_ne_stuck
    (q v vs a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
          xs ts bvs) ≠
        Term.Stuck) :
    __substitute_simul_rec (Term.Boolean false)
        (Term.Apply (Term.Apply q
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
        xs ts bvs =
      __eo_mk_apply
        (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
        (__substitute_simul_rec (Term.Boolean false) a xs ts
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs)) := by
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
          xs ts bvs =
        __eo_requires
          (__contains_atomic_term_list_free_rec ts
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply
            (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            (__substitute_simul_rec (Term.Boolean false) a xs ts
              (__eo_list_concat Term.__eo_List_cons
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs))) :=
    SubstituteSupport.substFalse_quant q v vs a xs ts bvs hxs hts hbvs
  have hReqNe :
      __eo_requires
          (__contains_atomic_term_list_free_rec ts
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply
            (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            (__substitute_simul_rec (Term.Boolean false) a xs ts
              (__eo_list_concat Term.__eo_List_cons
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs))) ≠
        Term.Stuck := by
    intro hReqStuck
    apply hTy
    rw [hSubstEq, hReqStuck]
    rfl
  rw [hSubstEq]
  exact instantiate_eo_requires_result_eq_of_ne_stuck hReqNe

theorem substitute_simul_quant_guard_false_of_ne_stuck
    (q v vs a xs ts bvs : Term)
    (hxs : xs ≠ Term.Stuck) (hts : ts ≠ Term.Stuck)
    (hbvs : bvs ≠ Term.Stuck)
    (hNe :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
          xs ts bvs ≠
        Term.Stuck) :
    __contains_atomic_term_list_free_rec ts
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
        Term.__eo_List_nil =
      Term.Boolean false := by
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
          xs ts bvs =
        __eo_requires
          (__contains_atomic_term_list_free_rec ts
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply
            (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            (__substitute_simul_rec (Term.Boolean false) a xs ts
              (__eo_list_concat Term.__eo_List_cons
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs))) :=
    SubstituteSupport.substFalse_quant q v vs a xs ts bvs hxs hts hbvs
  have hReqNe :
      __eo_requires
          (__contains_atomic_term_list_free_rec ts
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply
            (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            (__substitute_simul_rec (Term.Boolean false) a xs ts
              (__eo_list_concat Term.__eo_List_cons
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs))) ≠
        Term.Stuck := by
    intro hReqStuck
    exact hNe (by rw [hSubstEq, hReqStuck])
  exact instantiate_eo_requires_arg_eq_of_ne_stuck hReqNe

theorem eo_mk_apply_apply_head_eq_apply_of_typeof_ne_stuck
    (f x y : Term)
    (hTy : __eo_typeof (__eo_mk_apply (Term.Apply f x) y) ≠ Term.Stuck) :
    __eo_mk_apply (Term.Apply f x) y =
      Term.Apply (Term.Apply f x) y := by
  cases y <;> simp [__eo_mk_apply] at hTy ⊢
  exact False.elim (hTy rfl)

theorem substitute_simul_quant_eq_of_ne_stuck
    (q v vs a xs ts bvs : Term)
    (hxs : xs ≠ Term.Stuck) (hts : ts ≠ Term.Stuck)
    (hbvs : bvs ≠ Term.Stuck)
    (hNe :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
          xs ts bvs ≠
        Term.Stuck) :
    __substitute_simul_rec (Term.Boolean false)
        (Term.Apply (Term.Apply q
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
        xs ts bvs =
      __eo_mk_apply
        (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
        (__substitute_simul_rec (Term.Boolean false) a xs ts
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs)) := by
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
          xs ts bvs =
        __eo_requires
          (__contains_atomic_term_list_free_rec ts
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply
            (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            (__substitute_simul_rec (Term.Boolean false) a xs ts
              (__eo_list_concat Term.__eo_List_cons
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs))) :=
    SubstituteSupport.substFalse_quant q v vs a xs ts bvs hxs hts hbvs
  have hReqNe :
      __eo_requires
          (__contains_atomic_term_list_free_rec ts
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply
            (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            (__substitute_simul_rec (Term.Boolean false) a xs ts
              (__eo_list_concat Term.__eo_List_cons
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs))) ≠
        Term.Stuck := by
    intro hReqStuck
    exact hNe (by rw [hSubstEq, hReqStuck])
  rw [hSubstEq]
  exact instantiate_eo_requires_result_eq_of_ne_stuck hReqNe

/-- In either substitution mode, a successful binder substitution is still a
binder application.  The binder list and body accumulator differ by mode, but
the outer application shape does not. -/
theorem substitute_simul_quant_apply_shape_of_ne_stuck
    {isRename : Bool}
    (q v vs a xs ts bvs : Term)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hts : ts ≠ Term.Stuck)
    (hbvs : bvs ≠ Term.Stuck)
    (hNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
          xs ts bvs ≠
        Term.Stuck) :
    ∃ binderSub bodySub,
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
          xs ts bvs =
        __eo_mk_apply (Term.Apply q binderSub) bodySub := by
  cases isRename with
  | false =>
      let binder := Term.Apply (Term.Apply Term.__eo_List_cons v) vs
      let bodySub :=
        __substitute_simul_rec (Term.Boolean false) a xs ts
          (__eo_list_concat Term.__eo_List_cons binder bvs)
      refine ⟨binder, bodySub, ?_⟩
      simpa [binder, bodySub] using
        substitute_simul_quant_eq_of_ne_stuck
          q v vs a xs ts bvs hxs hts hbvs hNe
  | true =>
      let binder := Term.Apply (Term.Apply Term.__eo_List_cons v) vs
      let binderSub :=
        __substitute_simul_rec (Term.Boolean true) binder xs ts bvs
      let bodySub :=
        __substitute_simul_rec (Term.Boolean true) a xs ts bvs
      have hRaw :
          __substitute_simul_rec (Term.Boolean true)
              (Term.Apply (Term.Apply q binder) a) xs ts bvs =
            __eo_requires
              (__contains_atomic_term_list_free_rec ts binder
                Term.__eo_List_nil)
              (Term.Boolean false)
              (__eo_mk_apply (__eo_mk_apply q binderSub) bodySub) := by
        simpa [binder, binderSub, bodySub] using
          SubstituteSupport.substTrue_quant q v vs a xs ts bvs hxs hts hbvs
      have hReqNe :
          __eo_requires
              (__contains_atomic_term_list_free_rec ts binder
                Term.__eo_List_nil)
              (Term.Boolean false)
              (__eo_mk_apply (__eo_mk_apply q binderSub) bodySub) ≠
            Term.Stuck := by
        rw [← hRaw]
        simpa [binder] using hNe
      have hReqEq :
          __eo_requires
              (__contains_atomic_term_list_free_rec ts binder
                Term.__eo_List_nil)
              (Term.Boolean false)
              (__eo_mk_apply (__eo_mk_apply q binderSub) bodySub) =
            __eo_mk_apply (__eo_mk_apply q binderSub) bodySub :=
        instantiate_eo_requires_result_eq_of_ne_stuck hReqNe
      have hOuterNe :
          __eo_mk_apply (__eo_mk_apply q binderSub) bodySub ≠ Term.Stuck := by
        rwa [hReqEq] at hReqNe
      have hInnerNe : __eo_mk_apply q binderSub ≠ Term.Stuck :=
        instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNe
      have hInnerEq :
          __eo_mk_apply q binderSub = Term.Apply q binderSub :=
        instantiate_eo_mk_apply_eq_apply_of_ne_stuck q binderSub hInnerNe
      refine ⟨binderSub, bodySub, ?_⟩
      rw [hRaw, hReqEq, hInnerEq]

/-- Exact successful quantifier shape in rename mode.  Unlike the
mode-independent shape lemma, the returned binder and body are definitionally
the true-mode substitutions of the original binder and body. -/
theorem substitute_simul_true_quant_eq_of_ne_stuck
    (q v vs a xs ts bvs : Term)
    (hxs : xs ≠ Term.Stuck) (hts : ts ≠ Term.Stuck)
    (hbvs : bvs ≠ Term.Stuck)
    (hNe :
      __substitute_simul_rec (Term.Boolean true)
          (Term.Apply (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
          xs ts bvs ≠ Term.Stuck) :
    __substitute_simul_rec (Term.Boolean true)
        (Term.Apply (Term.Apply q
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
        xs ts bvs =
      __eo_mk_apply
        (Term.Apply q
          (__substitute_simul_rec (Term.Boolean true)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            xs ts bvs))
        (__substitute_simul_rec (Term.Boolean true) a xs ts bvs) := by
  let binder := Term.Apply (Term.Apply Term.__eo_List_cons v) vs
  let binderSub :=
    __substitute_simul_rec (Term.Boolean true) binder xs ts bvs
  let bodySub :=
    __substitute_simul_rec (Term.Boolean true) a xs ts bvs
  have hRaw :
      __substitute_simul_rec (Term.Boolean true)
          (Term.Apply (Term.Apply q binder) a) xs ts bvs =
        __eo_requires
          (__contains_atomic_term_list_free_rec ts binder Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply (__eo_mk_apply q binderSub) bodySub) := by
    simpa [binder, binderSub, bodySub] using
      SubstituteSupport.substTrue_quant q v vs a xs ts bvs hxs hts hbvs
  have hReqNe :
      __eo_requires
          (__contains_atomic_term_list_free_rec ts binder Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply (__eo_mk_apply q binderSub) bodySub) ≠
        Term.Stuck := by
    rw [← hRaw]
    simpa [binder] using hNe
  have hReqEq :
      __eo_requires
          (__contains_atomic_term_list_free_rec ts binder Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply (__eo_mk_apply q binderSub) bodySub) =
        __eo_mk_apply (__eo_mk_apply q binderSub) bodySub :=
    instantiate_eo_requires_result_eq_of_ne_stuck hReqNe
  have hOuterNe :
      __eo_mk_apply (__eo_mk_apply q binderSub) bodySub ≠ Term.Stuck := by
    rwa [hReqEq] at hReqNe
  have hInnerNe : __eo_mk_apply q binderSub ≠ Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNe
  have hInnerEq : __eo_mk_apply q binderSub = Term.Apply q binderSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck q binderSub hInnerNe
  simpa [binder, binderSub, bodySub] using
    (show
      __substitute_simul_rec (Term.Boolean true)
          (Term.Apply (Term.Apply q binder) a) xs ts bvs =
        __eo_mk_apply (Term.Apply q binderSub) bodySub by
      rw [hRaw, hReqEq, hInnerEq])

theorem substitute_simul_rec_apply_eq_apply_of_ne_stuck
    {isRename : Bool}
    (f a xs ts bvs : Term)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hts : ts ≠ Term.Stuck)
    (hbvs : bvs ≠ Term.Stuck)
    (hNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply f a) xs ts bvs ≠
        Term.Stuck) :
    ∃ fSub aSub,
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply f a) xs ts bvs =
        Term.Apply fSub aSub := by
  by_cases hBinder :
      ∃ q v vs,
        f = Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
  · rcases hBinder with ⟨q, v, vs, rfl⟩
    rcases substitute_simul_quant_apply_shape_of_ne_stuck
        q v vs a xs ts bvs hisr hxs hts hbvs hNe with
      ⟨binderSub, bodySub, hEq⟩
    have hMkNe :
        __eo_mk_apply (Term.Apply q binderSub) bodySub ≠ Term.Stuck := by
      rw [← hEq]
      exact hNe
    have hMk :
        __eo_mk_apply (Term.Apply q binderSub) bodySub =
          Term.Apply (Term.Apply q binderSub) bodySub :=
      instantiate_eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply q binderSub) bodySub hMkNe
    exact ⟨Term.Apply q binderSub, bodySub, by rw [hEq, hMk]⟩
  · let fSub := __substitute_simul_rec (Term.Boolean isRename) f xs ts bvs
    let aSub := __substitute_simul_rec (Term.Boolean isRename) a xs ts bvs
    have hEq :
        __substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply f a) xs ts bvs =
          __eo_mk_apply fSub aSub := by
      simpa [fSub, aSub] using
        SubstituteSupport.substitute_simul_rec_apply
          (Term.Boolean isRename) f a xs ts bvs
          hisr hxs hts hbvs
          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
    have hMkNe : __eo_mk_apply fSub aSub ≠ Term.Stuck := by
      rw [← hEq]
      exact hNe
    have hMk : __eo_mk_apply fSub aSub = Term.Apply fSub aSub :=
      instantiate_eo_mk_apply_eq_apply_of_ne_stuck fSub aSub hMkNe
    exact ⟨fSub, aSub, by rw [hEq, hMk]⟩

theorem substitute_simul_rec_apply_apply_eq_apply_apply_of_ne_stuck
    {isRename : Bool}
    (f x y xs ts bvs : Term)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hts : ts ≠ Term.Stuck)
    (hbvs : bvs ≠ Term.Stuck)
    (hNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply f x) y) xs ts bvs ≠
        Term.Stuck) :
    ∃ fSub xSub ySub,
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply f x) y) xs ts bvs =
        Term.Apply (Term.Apply fSub xSub) ySub := by
  by_cases hBinder :
      ∃ q v vs,
        Term.Apply f x =
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
  · rcases hBinder with ⟨q, v, vs, hEqHead⟩
    cases hEqHead
    rcases substitute_simul_quant_apply_shape_of_ne_stuck
        f v vs y xs ts bvs hisr hxs hts hbvs hNe with
      ⟨binderSub, bodySub, hEq⟩
    have hMkNe :
        __eo_mk_apply (Term.Apply f binderSub) bodySub ≠ Term.Stuck := by
      rw [← hEq]
      exact hNe
    have hMk :
        __eo_mk_apply (Term.Apply f binderSub) bodySub =
          Term.Apply (Term.Apply f binderSub) bodySub :=
      instantiate_eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply f binderSub) bodySub hMkNe
    exact ⟨f, binderSub, bodySub, by rw [hEq, hMk]⟩
  · let innerSub :=
      __substitute_simul_rec (Term.Boolean isRename) (Term.Apply f x) xs ts bvs
    let ySub := __substitute_simul_rec (Term.Boolean isRename) y xs ts bvs
    have hEq :
        __substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply f x) y) xs ts bvs =
          __eo_mk_apply innerSub ySub := by
      simpa [innerSub, ySub] using
        SubstituteSupport.substitute_simul_rec_apply
          (Term.Boolean isRename) (Term.Apply f x) y xs ts bvs
          hisr hxs hts hbvs
          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
    have hMkNe : __eo_mk_apply innerSub ySub ≠ Term.Stuck := by
      rw [← hEq]
      exact hNe
    have hInnerNe : innerSub ≠ Term.Stuck :=
      instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hMkNe
    rcases
        substitute_simul_rec_apply_eq_apply_of_ne_stuck
          f x xs ts bvs hisr hxs hts hbvs (by simpa [innerSub] using hInnerNe)
      with ⟨fSub, xSub, hInnerShape⟩
    have hMk : __eo_mk_apply innerSub ySub = Term.Apply innerSub ySub :=
      instantiate_eo_mk_apply_eq_apply_of_ne_stuck innerSub ySub hMkNe
    have hInnerShape' : innerSub = Term.Apply fSub xSub := by
      simpa [innerSub] using hInnerShape
    exact ⟨fSub, xSub, ySub, by rw [hEq, hMk, hInnerShape']⟩

theorem substitute_simul_rec_apply_apply_apply_eq_apply_apply_apply_of_ne_stuck
    {isRename : Bool}
    (g y x0 x1 xs ts bvs : Term)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hts : ts ≠ Term.Stuck)
    (hbvs : bvs ≠ Term.Stuck)
    (hNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) xs ts bvs ≠
        Term.Stuck) :
    ∃ gSub ySub x0Sub x1Sub,
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) xs ts bvs =
        Term.Apply (Term.Apply (Term.Apply gSub ySub) x0Sub) x1Sub := by
  by_cases hBinder :
      ∃ q v vs,
        Term.Apply (Term.Apply g y) x0 =
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
  · rcases hBinder with ⟨q, v, vs, hEqHead⟩
    cases hEqHead
    rcases substitute_simul_quant_apply_shape_of_ne_stuck
        (Term.Apply g y) v vs x1 xs ts bvs hisr hxs hts hbvs hNe with
      ⟨binderSub, bodySub, hEq⟩
    have hMkNe :
        __eo_mk_apply (Term.Apply (Term.Apply g y) binderSub) bodySub ≠
          Term.Stuck := by
      rw [← hEq]
      exact hNe
    have hMk :
        __eo_mk_apply (Term.Apply (Term.Apply g y) binderSub) bodySub =
          Term.Apply (Term.Apply (Term.Apply g y) binderSub) bodySub :=
      instantiate_eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.Apply g y) binderSub) bodySub hMkNe
    exact ⟨g, y, binderSub, bodySub, by rw [hEq, hMk]⟩
  · let headSub :=
      __substitute_simul_rec (Term.Boolean isRename)
        (Term.Apply (Term.Apply g y) x0) xs ts bvs
    let x1Sub := __substitute_simul_rec (Term.Boolean isRename) x1 xs ts bvs
    have hEq :
        __substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) xs ts bvs =
          __eo_mk_apply headSub x1Sub := by
      simpa [headSub, x1Sub] using
        SubstituteSupport.substitute_simul_rec_apply
          (Term.Boolean isRename) (Term.Apply (Term.Apply g y) x0) x1 xs ts bvs
          hisr hxs hts hbvs
          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
    have hMkNe : __eo_mk_apply headSub x1Sub ≠ Term.Stuck := by
      rw [← hEq]
      exact hNe
    have hHeadNe : headSub ≠ Term.Stuck :=
      instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hMkNe
    rcases
        substitute_simul_rec_apply_apply_eq_apply_apply_of_ne_stuck
          g y x0 xs ts bvs hisr hxs hts hbvs
          (by simpa [headSub] using hHeadNe)
      with ⟨gSub, ySub, x0Sub, hHeadShape⟩
    have hMk : __eo_mk_apply headSub x1Sub = Term.Apply headSub x1Sub :=
      instantiate_eo_mk_apply_eq_apply_of_ne_stuck headSub x1Sub hMkNe
    have hHeadShape' : headSub = Term.Apply (Term.Apply gSub ySub) x0Sub := by
      simpa [headSub] using hHeadShape
    exact ⟨gSub, ySub, x0Sub, x1Sub, by rw [hEq, hMk, hHeadShape']⟩

theorem substitute_simul_quant_has_smt_translation_of_typeof_ne_stuck
    (q v vs a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hQuantTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply q
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a))
    (hBodySubTrans :
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false) a xs ts
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs)))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
          xs ts bvs) ≠
        Term.Stuck) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false)
        (Term.Apply (Term.Apply q
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
        xs ts bvs) := by
  have hSubstEq :=
    substitute_simul_quant_eq_of_typeof_ne_stuck
      q v vs a xs ts bvs hXsEnv hBvsEnv hTs hTy
  rw [hSubstEq] at hTy ⊢
  have hMk :
      __eo_mk_apply
          (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          (__substitute_simul_rec (Term.Boolean false) a xs ts
            (__eo_list_concat Term.__eo_List_cons
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs)) =
        Term.Apply
          (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          (__substitute_simul_rec (Term.Boolean false) a xs ts
            (__eo_list_concat Term.__eo_List_cons
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs)) :=
    eo_mk_apply_apply_head_eq_apply_of_typeof_ne_stuck
      q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
      (__substitute_simul_rec (Term.Boolean false) a xs ts
        (__eo_list_concat Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs))
      hTy
  rw [hMk] at hTy ⊢
  have hQuantTrans' :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply q
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hQuantTrans
  have hQ :
      q = Term.UOp UserOp.forall ∨ q = Term.UOp UserOp.exists :=
    is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
      hQuantTrans'
  rcases eo_var_env_of_list_branch_has_smt_translation hQuantTrans' with
    ⟨binderVars, hBinderEnv⟩
  have hBinderNonNil :
      Term.Apply (Term.Apply Term.__eo_List_cons v) vs ≠
        Term.__eo_List_nil := by
    intro h
    cases h
  exact
    eo_has_smt_translation_quant_of_body_translation_and_type
      q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
      (__substitute_simul_rec (Term.Boolean false) a xs ts
        (__eo_list_concat Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs))
      hQ hBinderEnv hBinderNonNil
      (quant_binder_types_wf_of_has_smt_translation
        hQ hQuantTrans hBinderEnv)
      hBodySubTrans hTy

/-- A variable whose name is not an EO string cannot have an SMT translation. -/
theorem false_of_non_string_var_has_smt_translation
    {name S : Term} {P : Prop}
    (hName : ∀ s, name ≠ Term.String s)
    (hTrans : RuleProofs.eo_has_smt_translation (Term.Var name S)) :
    P := by
  exfalso
  apply hTrans
  cases name <;>
    try
      (change __smtx_typeof SmtTerm.None = SmtType.None
       exact TranslationProofs.smtx_typeof_none)
  case String s =>
    exact False.elim (hName s rfl)

/-- Variable case for substitution-result translatability under an arbitrary
bound-variable accumulator, in the general non-`Stuck` typing form needed by
recursive application cases. -/
theorem substitute_simul_var_has_smt_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (s : native_String) (S xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hVarTrans : RuleProofs.eo_has_smt_translation (Term.Var (Term.String s) S))
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Var (Term.String s) S) xs ts bvs) ≠
        Term.Stuck) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean isRename)
        (Term.Var (Term.String s) S) xs ts bvs) := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  rcases hBvsEnv with ⟨bvsExact, hBvsExact, _hBvsEquiv⟩
  by_cases hBound : (s, S) ∈ bvsExact
  · have hb :
        __eo_is_neg
            (__eo_list_find Term.__eo_List_cons bvs
              (Term.Var (Term.String s) S)) =
          Term.Boolean false :=
      hBvsExact.find_neg_false_of_mem hBound
    have hSubstEq :
        __substitute_simul_rec (Term.Boolean isRename)
            (Term.Var (Term.String s) S) xs ts bvs =
          Term.Var (Term.String s) S :=
      SubstituteSupport.substitute_simul_rec_var_bound
        (Term.Boolean isRename) (Term.String s) S xs ts bvs
        hisr hxs hts hbvs hb
    simpa [hSubstEq] using hVarTrans
  · have hFree :
        __eo_is_neg
            (__eo_list_find Term.__eo_List_cons bvs
              (Term.Var (Term.String s) S)) =
          Term.Boolean true :=
      hBvsExact.find_neg_true_of_not_mem hBound
    rcases hXsEnv with ⟨xsExact, hXsExact, _hXsEquiv⟩
    by_cases hMapped : (s, S) ∈ xsExact
    · have hx :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) S)) =
            Term.Boolean false :=
        hXsExact.find_neg_false_of_mem hMapped
      have hSubstEq :
          __substitute_simul_rec (Term.Boolean isRename)
              (Term.Var (Term.String s) S) xs ts bvs =
            __assoc_nil_nth Term.__eo_List_cons ts
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) S)) :=
        SubstituteSupport.substitute_simul_rec_var_mapped
          (Term.Boolean isRename) (Term.String s) S xs ts bvs
          hisr hxs hts hbvs hFree hx
      rw [hSubstEq] at hTy ⊢
      exact
        SubstituteSupport.assoc_nil_nth_has_smt_translation_of_list_all_and_typeof_ne_stuck
          ts
          (__eo_list_find Term.__eo_List_cons xs (Term.Var (Term.String s) S))
          hTs hTy
    · have hx :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) S)) =
            Term.Boolean true :=
        hXsExact.find_neg_true_of_not_mem hMapped
      have hSubstEq :
          __substitute_simul_rec (Term.Boolean isRename)
              (Term.Var (Term.String s) S) xs ts bvs =
            Term.Var (Term.String s) S :=
        SubstituteSupport.substitute_simul_rec_var_unmapped
          (Term.Boolean isRename) (Term.String s) S xs ts bvs
          hisr hxs hts hbvs hFree hx
      simpa [hSubstEq] using hVarTrans

/-- Variable case for arbitrary EO variable names. Non-string names are ruled
out by the translation hypothesis; string names use the main variable helper. -/
theorem substitute_simul_var_any_has_smt_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (name S xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hVarTrans : RuleProofs.eo_has_smt_translation (Term.Var name S))
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Var name S) xs ts bvs) ≠
        Term.Stuck) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean isRename)
        (Term.Var name S) xs ts bvs) := by
  by_cases hString : ∃ s, name = Term.String s
  · rcases hString with ⟨s, rfl⟩
    exact
      substitute_simul_var_has_smt_translation_of_typeof_ne_stuck
        s S xs ts bvs hXsEnv hBvsEnv hVarTrans hTs hTy
  · exact
      false_of_non_string_var_has_smt_translation
        (fun s hEq => hString ⟨s, hEq⟩) hVarTrans

/-- Variant of the variable substitution translatability helper that uses the
substitution result being non-`Stuck`, rather than its EO type being non-`Stuck`.
This is useful when the result occurs as the function position of a rebuilt
application: `__eo_mk_apply` exposes non-`Stuck` of the head syntactically. -/
theorem substitute_simul_var_has_smt_translation_of_ne_stuck
    {isRename : Bool} (s : native_String) (S xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hVarTrans : RuleProofs.eo_has_smt_translation (Term.Var (Term.String s) S))
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Var (Term.String s) S) xs ts bvs ≠
        Term.Stuck) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean isRename)
        (Term.Var (Term.String s) S) xs ts bvs) := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by
    cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  rcases hBvsEnv with ⟨bvsExact, hBvsExact, _hBvsEquiv⟩
  by_cases hBound : (s, S) ∈ bvsExact
  · have hb :
        __eo_is_neg
            (__eo_list_find Term.__eo_List_cons bvs
              (Term.Var (Term.String s) S)) =
          Term.Boolean false :=
      hBvsExact.find_neg_false_of_mem hBound
    have hSubstEq :
        __substitute_simul_rec (Term.Boolean isRename)
            (Term.Var (Term.String s) S) xs ts bvs =
          Term.Var (Term.String s) S :=
      SubstituteSupport.substitute_simul_rec_var_bound
        (Term.Boolean isRename) (Term.String s) S xs ts bvs
        hisr hxs hts hbvs hb
    simpa [hSubstEq] using hVarTrans
  · have hFree :
        __eo_is_neg
            (__eo_list_find Term.__eo_List_cons bvs
              (Term.Var (Term.String s) S)) =
          Term.Boolean true :=
      hBvsExact.find_neg_true_of_not_mem hBound
    rcases hXsEnv with ⟨xsExact, hXsExact, _hXsEquiv⟩
    by_cases hMapped : (s, S) ∈ xsExact
    · have hx :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) S)) =
            Term.Boolean false :=
        hXsExact.find_neg_false_of_mem hMapped
      have hSubstEq :
          __substitute_simul_rec (Term.Boolean isRename)
              (Term.Var (Term.String s) S) xs ts bvs =
            __assoc_nil_nth Term.__eo_List_cons ts
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) S)) :=
        SubstituteSupport.substitute_simul_rec_var_mapped
          (Term.Boolean isRename) (Term.String s) S xs ts bvs
          hisr hxs hts hbvs hFree hx
      rw [hSubstEq] at hNe ⊢
      exact
        SubstituteSupport.assoc_nil_nth_has_smt_translation_of_list_all_and_ne_stuck
          ts
          (__eo_list_find Term.__eo_List_cons xs (Term.Var (Term.String s) S))
          hTs hNe
    · have hx :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) S)) =
            Term.Boolean true :=
        hXsExact.find_neg_true_of_not_mem hMapped
      have hSubstEq :
          __substitute_simul_rec (Term.Boolean isRename)
              (Term.Var (Term.String s) S) xs ts bvs =
            Term.Var (Term.String s) S :=
        SubstituteSupport.substitute_simul_rec_var_unmapped
          (Term.Boolean isRename) (Term.String s) S xs ts bvs
          hisr hxs hts hbvs hFree hx
      simpa [hSubstEq] using hVarTrans

/-- Arbitrary-name wrapper for
`substitute_simul_var_has_smt_translation_of_ne_stuck`. -/
theorem substitute_simul_var_any_has_smt_translation_of_ne_stuck
    {isRename : Bool} (name S xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hVarTrans : RuleProofs.eo_has_smt_translation (Term.Var name S))
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Var name S) xs ts bvs ≠
        Term.Stuck) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean isRename)
        (Term.Var name S) xs ts bvs) := by
  by_cases hString : ∃ s, name = Term.String s
  · rcases hString with ⟨s, rfl⟩
    exact
      substitute_simul_var_has_smt_translation_of_ne_stuck (isRename := isRename)
        s S xs ts bvs hXsEnv hBvsEnv hVarTrans hTs hNe
  · exact
      false_of_non_string_var_has_smt_translation
        (fun s hEq => hString ⟨s, hEq⟩) hVarTrans

/-- Atom/default case for substitution-result translatability under an arbitrary
bound-variable accumulator, in the general non-`Stuck` typing form needed by
recursive application cases. -/
theorem substitute_simul_atom_has_smt_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (F xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotApply : ∀ f a, F ≠ Term.Apply f a)
    (hNotVar : ∀ s S, F ≠ Term.Var s S)
    (hNotStuck : F ≠ Term.Stuck)
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename) F xs ts bvs) ≠
        Term.Stuck) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean isRename) F xs ts bvs) := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename) F xs ts bvs =
        __eo_requires (__is_closed_rec F Term.__eo_List_nil) (Term.Boolean true) F :=
    SubstituteSupport.substitute_simul_rec_atom
      (Term.Boolean isRename) F xs ts bvs
      hisr hxs hts hbvs hNotApply hNotVar hNotStuck
  rw [hSubstEq] at hTy ⊢
  by_cases hck :
      native_teq (__is_closed_rec F Term.__eo_List_nil) (Term.Boolean true) = true
  · have hcTrue : __is_closed_rec F Term.__eo_List_nil = Term.Boolean true := by
      simpa only [native_teq, decide_eq_true_eq] using hck
    have hReq :
        __eo_requires (__is_closed_rec F Term.__eo_List_nil) (Term.Boolean true) F =
          F := by
      simp [__eo_requires, hcTrue, native_ite, native_teq, native_not,
        SmtEval.native_not]
    simpa [hReq] using hFTrans
  · have hReq :
        __eo_requires (__is_closed_rec F Term.__eo_List_nil) (Term.Boolean true) F =
          Term.Stuck := by
      simp [__eo_requires, native_ite, hck]
    exfalso
    apply hTy
    rw [hReq]
    rfl

end SubstituteTranslatabilitySupport
