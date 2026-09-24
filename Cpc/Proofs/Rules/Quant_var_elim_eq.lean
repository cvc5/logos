module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.CongSupport
import all Cpc.Proofs.RuleSupport.CongSupport
public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport
public import Cpc.Proofs.RuleSupport.RelCoincidenceSupport
import all Cpc.Proofs.RuleSupport.RelCoincidenceSupport
public import Cpc.Proofs.RuleSupport.InstantiateSupport
import all Cpc.Proofs.RuleSupport.InstantiateSupport

open Eo
open SmtEval
open Smtm
open SubstituteTranslatabilitySupport
open SubstitutePreservationSupport

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace QuantVarElimEqRule

private def qeq (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B

private def qnot (A : Term) : Term :=
  Term.Apply (Term.UOp UserOp.not) A

private def qor (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B

private def qforall (xs F : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F

private def qcons (x xs : Term) : Term :=
  Term.Apply (Term.Apply Term.__eo_List_cons x) xs

private def qsingle (x : Term) : Term :=
  qcons x Term.__eo_List_nil

private def qsubst (body x t : Term) : Term :=
  __substitute_simul_rec (Term.Boolean false) body
    (qsingle x) (qsingle t) Term.__eo_List_nil

private def quantVarElimEqFormula (x F G : Term) : Term :=
  qeq (qforall (qsingle x) F) G

private inductive QuantVarElimEqCase (x F G : Term) : Prop where
  | diseq (t : Term) :
      F = qnot (qeq x t) ->
      __contains_atomic_term_list_free_rec t (qsingle x) Term.__eo_List_nil =
        Term.Boolean false ->
      G = qsubst (Term.Boolean false) x t ->
      QuantVarElimEqCase x F G
  | orTail (t tail : Term) :
      F = qor (qnot (qeq x t)) tail ->
      __contains_atomic_term_list_free_rec t (qsingle x) Term.__eo_List_nil =
        Term.Boolean false ->
      __eo_is_list (Term.UOp UserOp.or) tail = Term.Boolean true ->
      G = qsubst (__eo_list_singleton_elim (Term.UOp UserOp.or) tail) x t ->
      QuantVarElimEqCase x F G

private theorem eo_eq_self_true (x : Term) (hx : x ≠ Term.Stuck) :
    __eo_eq x x = Term.Boolean true := by
  cases x <;> simp [__eo_eq, native_teq] at hx ⊢

private theorem eval_eo_var_lookup (M : SmtModel) (s : native_String) (T : Term) :
    __smtx_model_eval M (__eo_to_smt (Term.Var (Term.String s) T)) =
      native_model_var_lookup M s (__eo_to_smt_type T) := by
  rw [__smtx_model_eval.eq_def]
  rfl

private theorem singleton_subst_actuals_of_eq_bool
    (x t F : Term)
    (hForallTrans :
      RuleProofs.eo_has_smt_translation (qforall (qsingle x) F))
    (hEqBool : RuleProofs.eo_has_bool_type (qeq x t)) :
    EoListAllHaveSmtTranslation (qsingle t) ∧
      SubstActualsHaveSmtTypes (qsingle x) (qsingle t) := by
  rcases forall_binders_env_of_has_smt_translation
      (qsingle x) F hForallTrans with
    ⟨vars, hEnv⟩
  have hWf :=
    forall_binder_types_wf_of_has_smt_translation hForallTrans hEnv
  change EoVarEnv ((Term.__eo_List_cons.Apply x).Apply Term.__eo_List_nil)
    vars at hEnv
  cases hEnv with
  | cons hTail =>
      rename_i s T tailVars
      cases hTail
      have hHeadWf :
          __smtx_type_wf (__eo_to_smt_type T) = true :=
        hWf s T (by simp)
      have hTypes :=
        RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
          (Term.Var (Term.String s) T) t hEqBool
      have hTTrans : RuleProofs.eo_has_smt_translation t := by
        intro hNone
        exact hTypes.2 (by rw [hTypes.1, hNone])
      have hTy :
          __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type T := by
        simpa [smtx_typeof_var_term_eq, __smtx_typeof_guard_wf, hHeadWf,
          native_ite] using hTypes.1.symm
      refine ⟨?_, ?_⟩
      · simpa [qsingle, qcons, EoListAllHaveSmtTranslation] using
          And.intro hTTrans True.intro
      · exact SubstActualsHaveSmtTypes.cons hHeadWf hTTrans hTy
          (SubstActualsHaveSmtTypes.nil Term.__eo_List_nil)

private theorem qsubst_eval_eq_push
    (M : SmtModel) (hM : model_wf M)
    (x t F body : Term)
    (hForallTrans :
      RuleProofs.eo_has_smt_translation (qforall (qsingle x) F))
    (hEqBool : RuleProofs.eo_has_bool_type (qeq x t))
    (hBodyTrans : RuleProofs.eo_has_smt_translation body)
    (hSubstTrans :
      RuleProofs.eo_has_smt_translation (qsubst body x t)) :
    __smtx_model_eval M (__eo_to_smt (qsubst body x t)) =
      __smtx_model_eval (InstantiateRule.pushSubstModel M (qsingle x) (qsingle t))
        (__eo_to_smt body) := by
  rcases singleton_subst_actuals_of_eq_bool x t F hForallTrans hEqBool with
    ⟨hTs, hActuals⟩
  simpa [qsubst] using
      InstantiateRule.substitute_simul_eval M hM body (qsingle x) (qsingle t)
        hBodyTrans hTs hActuals hSubstTrans

private theorem qforall_single_has_bool_type_of_has_smt_translation
    (x F : Term)
    (hForallTrans :
      RuleProofs.eo_has_smt_translation (qforall (qsingle x) F)) :
    RuleProofs.eo_has_bool_type (qforall (qsingle x) F) := by
  have hXsNonNil :
      qsingle x ≠ Term.__eo_List_nil :=
    forall_binders_non_nil_of_has_smt_translation (qsingle x) F
      hForallTrans
  have hNN :
      __smtx_typeof
          (SmtTerm.not
            (__eo_to_smt_exists (qsingle x) (SmtTerm.not (__eo_to_smt F)))) ≠
        SmtType.None := by
    have hsimpa := hForallTrans
    try simp [qforall] at hsimpa ⊢
    exact hsimpa
  unfold RuleProofs.eo_has_bool_type
  rw [qforall, eo_to_smt_forall_eq_of_non_nil (qsingle x) F hXsNonNil]
  exact smtx_typeof_not_eq_bool_of_non_none
    (__eo_to_smt_exists (qsingle x) (SmtTerm.not (__eo_to_smt F))) hNN

private theorem qeq_true_in_single_subst_model
    (M : SmtModel) (hM : model_wf M)
    (x t F : Term)
    (hForallTrans :
      RuleProofs.eo_has_smt_translation (qforall (qsingle x) F))
    (hEqBool : RuleProofs.eo_has_bool_type (qeq x t))
    (hNoFree :
      __contains_atomic_term_list_free_rec t (qsingle x) Term.__eo_List_nil =
        Term.Boolean false) :
    eo_interprets
      (InstantiateRule.pushSubstModel M (qsingle x) (qsingle t))
      (qeq x t) true := by
  rcases forall_binders_env_of_has_smt_translation
      (qsingle x) F hForallTrans with
    ⟨vars, hEnv⟩
  change EoVarEnv ((Term.__eo_List_cons.Apply x).Apply Term.__eo_List_nil)
    vars at hEnv
  cases hEnv with
  | cons hTail =>
      rename_i s T tailVars
      cases hTail
      let N := InstantiateRule.pushSubstModel M
        (qsingle (Term.Var (Term.String s) T)) (qsingle t)
      have hTypes :=
        RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
          (Term.Var (Term.String s) T) t hEqBool
      have hTTrans : RuleProofs.eo_has_smt_translation t := by
        intro hNone
        exact hTypes.2 (by rw [hTypes.1, hNone])
      have hEvalX :
          __smtx_model_eval N
              (__eo_to_smt (Term.Var (Term.String s) T)) =
            __smtx_model_eval M (__eo_to_smt t) := by
        rw [eval_eo_var_lookup]
        simp [N, InstantiateRule.pushSubstModel, qsingle, qcons,
          native_model_var_lookup, native_model_push]
      have hNoFree' :
          __contains_atomic_term_list_free_rec t
              (qsingle (Term.Var (Term.String s) T)) Term.__eo_List_nil =
            Term.Boolean false := by
        simpa [qsingle, qcons] using hNoFree
      have hEvalT :
          __smtx_model_eval N (__eo_to_smt t) =
            __smtx_model_eval M (__eo_to_smt t) := by
        have hExcept :
            EoVarEnvPerm (qsingle (Term.Var (Term.String s) T))
              ([(s, T)] : List EoVarKey) :=
          EoVarEnvPerm.of_exact (EoVarEnv.cons EoVarEnv.nil)
        have hBound :
            EoVarEnvPerm Term.__eo_List_nil ([] : List EoVarKey) :=
          EoVarEnvPerm.of_exact EoVarEnv.nil
        have hAgree :
            model_agrees_except_on_env
              ([(s, __eo_to_smt_type T)] : List SmtVarKey) []
              N M := by
          simpa [N, qsingle, qcons, EoVarKey.toSmt] using
            InstantiateRule.pushSubstModel_agrees_except M
              (qsingle t) (EoVarEnv.cons EoVarEnv.nil)
        exact
          smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
            hExcept hBound hTTrans hNoFree' hAgree
      apply RuleProofs.eo_interprets_eq_of_rel N
        (Term.Var (Term.String s) T) t hEqBool
      rw [hEvalX, hEvalT]
      exact RuleProofs.smt_value_rel_refl
        (__smtx_model_eval M (__eo_to_smt t))

/-! ### Evaluation and typing unfolding helpers -/

private theorem smtx_eval_not_term (M : SmtModel) (u : SmtTerm) :
    __smtx_model_eval M (SmtTerm.not u) =
      __smtx_model_eval_not (__smtx_model_eval M u) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_or_term (M : SmtModel) (u1 u2 : SmtTerm) :
    __smtx_model_eval M (SmtTerm.or u1 u2) =
      __smtx_model_eval_or (__smtx_model_eval M u1) (__smtx_model_eval M u2) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_eq_term (M : SmtModel) (u1 u2 : SmtTerm) :
    __smtx_model_eval M (SmtTerm.eq u1 u2) =
      __smtx_model_eval_eq (__smtx_model_eval M u1) (__smtx_model_eval M u2) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_bool_lit (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem qnot_to_smt (A : Term) :
    __eo_to_smt (qnot A) = SmtTerm.not (__eo_to_smt A) := rfl

private theorem qor_to_smt (A B : Term) :
    __eo_to_smt (qor A B) = SmtTerm.or (__eo_to_smt A) (__eo_to_smt B) := rfl

private theorem qeq_to_smt (A B : Term) :
    __eo_to_smt (qeq A B) = SmtTerm.eq (__eo_to_smt A) (__eo_to_smt B) := rfl

private theorem false_to_smt :
    __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false := rfl

private theorem smtx_typeof_not_arg_of_bool (u : SmtTerm) :
    __smtx_typeof (SmtTerm.not u) = SmtType.Bool ->
    __smtx_typeof u = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq] at hTy
  cases h : __smtx_typeof u <;> simp [h, native_ite, native_Teq] at hTy ⊢

private theorem smtx_typeof_or_args_of_bool (A B : SmtTerm) :
    __smtx_typeof (SmtTerm.or A B) = SmtType.Bool ->
    __smtx_typeof A = SmtType.Bool ∧ __smtx_typeof B = SmtType.Bool := by
  intro hTy
  rw [typeof_or_eq] at hTy
  cases hA : __smtx_typeof A <;> cases hB : __smtx_typeof B <;>
    simp [hA, hB, native_ite, native_Teq] at hTy ⊢

private theorem qnot_arg_has_bool_type {A : Term}
    (h : RuleProofs.eo_has_bool_type (qnot A)) :
    RuleProofs.eo_has_bool_type A := by
  unfold RuleProofs.eo_has_bool_type at h ⊢
  rw [qnot_to_smt] at h
  exact smtx_typeof_not_arg_of_bool _ h

private theorem qor_args_have_bool_type {A B : Term}
    (h : RuleProofs.eo_has_bool_type (qor A B)) :
    RuleProofs.eo_has_bool_type A ∧ RuleProofs.eo_has_bool_type B := by
  unfold RuleProofs.eo_has_bool_type at h ⊢
  rw [qor_to_smt] at h
  exact smtx_typeof_or_args_of_bool _ _ h

private theorem bool_lit_has_smt_translation (b : native_Bool) :
    RuleProofs.eo_has_smt_translation (Term.Boolean b) := by
  unfold RuleProofs.eo_has_smt_translation
  intro hNone
  rw [show __eo_to_smt (Term.Boolean b) = SmtTerm.Boolean b from rfl] at hNone
  rw [show __smtx_typeof (SmtTerm.Boolean b) = SmtType.Bool from by
    rw [__smtx_typeof.eq_def] <;> simp only] at hNone
  cases hNone

/-! ### Boolean value computation helpers -/

private theorem or_eval_true_right_of_left_false {b : SmtValue}
    (h : __smtx_model_eval_or (SmtValue.Boolean false) b = SmtValue.Boolean true) :
    b = SmtValue.Boolean true := by
  cases b <;> simp_all [__smtx_model_eval_or, SmtEval.native_or]

private theorem eval_eq_is_boolean (v w : SmtValue) :
    ∃ b, __smtx_model_eval_eq v w = SmtValue.Boolean b := by
  unfold __smtx_model_eval_eq
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-! ### EO combinator helpers -/

private theorem requires_facts_of_eq_ne_stuck {a b c G : Term}
    (hMk : __eo_requires a b c = G) (hG : G ≠ Term.Stuck) :
    a = b ∧ G = c := by
  have hNe : __eo_requires a b c ≠ Term.Stuck := by
    rw [hMk]
    exact hG
  exact ⟨instantiate_eo_requires_arg_eq_of_ne_stuck hNe,
    hMk.symm.trans (instantiate_eo_requires_result_eq_of_ne_stuck hNe)⟩

private theorem eo_ite_eq_true_branch {c : Term} (a b : Term)
    (hc : c = Term.Boolean true) : __eo_ite c a b = a := by
  subst hc
  simp [native_ite, native_teq]

private theorem eo_ite_eq_false_branch {c : Term} (a b : Term)
    (hc : c = Term.Boolean false) : __eo_ite c a b = b := by
  subst hc
  simp [native_ite, native_teq]

/- The `eq_of_eo_ite_*` variants are applied (rather than used as rewrite
rules) so that `let`-bindings in checker-program match arms are handled by
definitional unfolding during unification. -/

private theorem eq_of_eo_ite_true {c a b G : Term}
    (hc : c = Term.Boolean true) (hMk : __eo_ite c a b = G) : a = G := by
  rw [← hMk]
  exact (eo_ite_eq_true_branch a b hc).symm

private theorem eq_of_eo_ite_false {c a b G : Term}
    (hc : c = Term.Boolean false) (hMk : __eo_ite c a b = G) : b = G := by
  rw [← hMk]
  exact (eo_ite_eq_false_branch a b hc).symm

private theorem eo_eq_eq_of_ne_stuck {a b : Term}
    (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    __eo_eq a b = Term.Boolean (native_teq b a) := by
  unfold __eo_eq
  split
  · exact absurd rfl (by assumption)
  · exact absurd rfl (by assumption)
  · rfl

private theorem eo_is_list_eq_of_ne_stuck {f a : Term}
    (hf : f ≠ Term.Stuck) (ha : a ≠ Term.Stuck) :
    __eo_is_list f a = __eo_is_ok (__eo_get_nil_rec f a) := by
  unfold __eo_is_list
  split
  · exact absurd rfl (by assumption)
  · exact absurd rfl (by assumption)
  · rfl

/-! ### Or-list (`is_list`/`singleton_elim`) structure -/

private theorem is_list_or_cases (tail : Term)
    (hIsList : __eo_is_list (Term.UOp UserOp.or) tail = Term.Boolean true) :
    tail = Term.Boolean false ∨
      ∃ b rest, tail = qor b rest ∧
        __eo_is_list (Term.UOp UserOp.or) rest = Term.Boolean true := by
  cases tail with
  | Boolean b =>
      cases b with
      | false => exact Or.inl rfl
      | true =>
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil, __eo_is_ok,
            __eo_requires, native_ite, native_teq, SmtEval.native_not] at hIsList
  | Apply f1 rest =>
      cases f1 with
      | Apply g b =>
          have hRecNe :
              __eo_get_nil_rec (Term.UOp UserOp.or)
                  (Term.Apply (Term.Apply g b) rest) ≠ Term.Stuck := by
            intro hEq
            rw [show __eo_is_list (Term.UOp UserOp.or)
                  (Term.Apply (Term.Apply g b) rest) =
                __eo_is_ok (__eo_get_nil_rec (Term.UOp UserOp.or)
                  (Term.Apply (Term.Apply g b) rest)) from rfl,
              hEq] at hIsList
            simp [__eo_is_ok, native_teq, SmtEval.native_not] at hIsList
          rw [show __eo_get_nil_rec (Term.UOp UserOp.or)
                (Term.Apply (Term.Apply g b) rest) =
              __eo_requires (Term.UOp UserOp.or) g
                (__eo_get_nil_rec (Term.UOp UserOp.or) rest) from rfl] at hRecNe
          have hg : (Term.UOp UserOp.or) = g :=
            instantiate_eo_requires_arg_eq_of_ne_stuck hRecNe
          have hTailRec :
              __eo_get_nil_rec (Term.UOp UserOp.or) rest ≠ Term.Stuck := by
            intro hEq
            rw [instantiate_eo_requires_result_eq_of_ne_stuck hRecNe, hEq]
              at hRecNe
            exact hRecNe rfl
          have hRestNe : rest ≠ Term.Stuck := by
            intro hEq
            rw [hEq] at hTailRec
            exact hTailRec rfl
          refine Or.inr ⟨b, rest, by rw [← hg]; rfl, ?_⟩
          rw [eo_is_list_eq_of_ne_stuck (f := Term.UOp UserOp.or)
            (a := rest) (by simp) hRestNe]
          simp [__eo_is_ok, native_teq, SmtEval.native_not, hTailRec]
      | _ =>
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil, __eo_is_ok,
            __eo_requires, native_ite, native_teq, SmtEval.native_not] at hIsList
  | _ =>
      simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil, __eo_is_ok,
        __eo_requires, native_ite, native_teq, SmtEval.native_not] at hIsList

private theorem singleton_elim_or_eq_elim2_of_is_list (tail : Term)
    (hIsList : __eo_is_list (Term.UOp UserOp.or) tail = Term.Boolean true) :
    __eo_list_singleton_elim (Term.UOp UserOp.or) tail =
      __eo_list_singleton_elim_2 tail := by
  show __eo_requires (__eo_is_list (Term.UOp UserOp.or) tail) (Term.Boolean true)
      (__eo_list_singleton_elim_2 tail) = __eo_list_singleton_elim_2 tail
  rw [hIsList]
  simp [__eo_requires, native_ite, native_teq, SmtEval.native_not]

/-- Structure of `singleton_elim` on a proper or-list, together with the facts
needed downstream: it stays Boolean-typed and evaluates like the or-list itself
in every total-typed model. -/
private theorem singleton_elim_or_facts (tail : Term)
    (hIsList : __eo_is_list (Term.UOp UserOp.or) tail = Term.Boolean true)
    (hTailBool : RuleProofs.eo_has_bool_type tail) :
    RuleProofs.eo_has_bool_type
        (__eo_list_singleton_elim (Term.UOp UserOp.or) tail) ∧
      ∀ (N : SmtModel), model_wf N ->
        __smtx_model_eval N
            (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.or) tail)) =
          __smtx_model_eval N (__eo_to_smt tail) := by
  rw [singleton_elim_or_eq_elim2_of_is_list tail hIsList]
  rcases is_list_or_cases tail hIsList with hNil | ⟨b, rest, hCons, hRestList⟩
  · subst hNil
    exact ⟨hTailBool, fun N _ => rfl⟩
  · subst hCons
    rcases is_list_or_cases rest hRestList with hNil | ⟨b2, rest2, hCons2, _⟩
    · subst hNil
      have hElim2 :
          __eo_list_singleton_elim_2 (qor b (Term.Boolean false)) = b := by
        show __eo_ite
            (__eo_is_list_nil (Term.UOp UserOp.or) (Term.Boolean false)) b
            (qor b (Term.Boolean false)) = b
        rw [show __eo_is_list_nil (Term.UOp UserOp.or) (Term.Boolean false) =
          Term.Boolean true from rfl]
        exact eo_ite_eq_true_branch _ _ rfl
      rw [hElim2]
      have hArgs := qor_args_have_bool_type hTailBool
      refine ⟨hArgs.1, ?_⟩
      intro N hN
      rw [qor_to_smt, smtx_eval_or_term, false_to_smt, smtx_eval_bool_lit]
      rcases smt_model_eval_bool_is_boolean N hN (__eo_to_smt b) hArgs.1 with
        ⟨b1, hb1⟩
      rw [hb1]
      cases b1 <;> simp [__smtx_model_eval_or, SmtEval.native_or]
    · subst hCons2
      have hElim2 :
          __eo_list_singleton_elim_2 (qor b (qor b2 rest2)) =
            qor b (qor b2 rest2) := by
        show __eo_ite
            (__eo_is_list_nil (Term.UOp UserOp.or) (qor b2 rest2)) b
            (qor b (qor b2 rest2)) = qor b (qor b2 rest2)
        rw [show __eo_is_list_nil (Term.UOp UserOp.or) (qor b2 rest2) =
          Term.Boolean false from rfl]
        exact eo_ite_eq_false_branch _ _ rfl
      rw [hElim2]
      exact ⟨hTailBool, fun N _ => rfl⟩

/-! ### Binder and substitution-term facts -/

private theorem qsingle_binder_shape_of_forall_trans (x F : Term)
    (hForallTrans :
      RuleProofs.eo_has_smt_translation (qforall (qsingle x) F)) :
    ∃ (s : native_String) (T : Term),
      x = Term.Var (Term.String s) T ∧
      __smtx_type_wf (__eo_to_smt_type T) = true := by
  rcases forall_binders_env_of_has_smt_translation (qsingle x) F hForallTrans with
    ⟨vars, hEnv⟩
  have hWf := forall_binder_types_wf_of_has_smt_translation hForallTrans hEnv
  change EoVarEnv ((Term.__eo_List_cons.Apply x).Apply Term.__eo_List_nil)
    vars at hEnv
  cases hEnv with
  | cons hTail =>
      rename_i s T tailVars
      cases hTail
      exact ⟨s, T, rfl, hWf s T (by simp)⟩

private theorem subst_term_facts_of_eq_bool
    (s : native_String) (T t : Term)
    (hTWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hEqBool :
      RuleProofs.eo_has_bool_type (qeq (Term.Var (Term.String s) T) t)) :
    RuleProofs.eo_has_smt_translation t ∧
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type T := by
  have hTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (Term.Var (Term.String s) T) t hEqBool
  have hTTrans : RuleProofs.eo_has_smt_translation t := by
    intro hNone
    exact hTypes.2 (by rw [hTypes.1, hNone])
  refine ⟨hTTrans, ?_⟩
  simpa [smtx_typeof_var_term_eq, __smtx_typeof_guard_wf, hTWf, native_ite]
    using hTypes.1.symm

private theorem eval_value_facts
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t) :
    __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) ∧
      __smtx_value_canonical (__smtx_model_eval M (__eo_to_smt t)) = true := by
  rcases InstantiateRule.eo_to_smt_eval_typed_canonical M hM t hTTrans with ⟨h1, h2⟩
  exact ⟨h1, by simpa [value_canonical] using h2⟩

/-! ### Push-model facts -/

private theorem push_subst_model_singleton_eq
    (M : SmtModel) (s : native_String) (T t : Term) :
    InstantiateRule.pushSubstModel M
        (qsingle (Term.Var (Term.String s) T)) (qsingle t) =
      native_model_push M s (__eo_to_smt_type T)
        (__smtx_model_eval M (__eo_to_smt t)) := by
  simp [qsingle, qcons]

private theorem eval_var_after_push
    (M : SmtModel) (s : native_String) (T : Term) (v : SmtValue) :
    __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
        (__eo_to_smt (Term.Var (Term.String s) T)) = v := by
  rw [eval_eo_var_lookup]
  simp [native_model_var_lookup, native_model_push]

private theorem eval_t_after_push_eq
    (M : SmtModel) (s : native_String) (T t : Term) (v : SmtValue)
    (hTWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hvTy : __smtx_typeof_value v = __eo_to_smt_type T)
    (hvCanon : __smtx_value_canonical v = true)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hNoFree :
      __contains_atomic_term_list_free_rec t
          (qsingle (Term.Var (Term.String s) T)) Term.__eo_List_nil =
        Term.Boolean false) :
    __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
        (__eo_to_smt t) =
      __smtx_model_eval M (__eo_to_smt t) := by
  have hInst :
      InstantiateRule.ForallInstantiationModel M
        (qsingle (Term.Var (Term.String s) T))
        (native_model_push M s (__eo_to_smt_type T) v) :=
    InstantiateRule.ForallInstantiationModel.cons hTWf hvTy hvCanon
      (InstantiateRule.ForallInstantiationModel.nil _)
  have hAgree :
      model_agrees_except_on_env
        ([(s, __eo_to_smt_type T)] : List SmtVarKey) []
        (native_model_push M s (__eo_to_smt_type T) v) M := by
    simpa [EoVarKey.toSmt] using
      InstantiateRule.ForallInstantiationModel.agrees_except hInst
        (EoVarEnv.cons EoVarEnv.nil)
  have hExcept :
      EoVarEnvPerm (qsingle (Term.Var (Term.String s) T))
        ([(s, T)] : List EoVarKey) :=
    EoVarEnvPerm.of_exact (EoVarEnv.cons EoVarEnv.nil)
  have hBound : EoVarEnvPerm Term.__eo_List_nil ([] : List EoVarKey) :=
    EoVarEnvPerm.of_exact EoVarEnv.nil
  exact
    smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
      hExcept hBound hTTrans hNoFree hAgree

/-- Truth of a translated Boolean term is transported between pushes of two
semantically related values. This is the congruence ("cong") core —
extensionally equal canonical regexes make the two models rel-related rather
than equal — discharged by the rel-coincidence development
(`RelCoincidenceSupport`). -/
private theorem eval_true_push_of_rel
    (M : SmtModel) (hM : model_wf M)
    (s : native_String) (ST : SmtType) (v w : SmtValue) (u : Term)
    (hSTWf : __smtx_type_wf ST = true)
    (hvTy : __smtx_typeof_value v = ST)
    (hwTy : __smtx_typeof_value w = ST)
    (hvCanon : __smtx_value_canonical v = true)
    (hwCanon : __smtx_value_canonical w = true)
    (hRel : __smtx_model_eval_eq v w = SmtValue.Boolean true)
    (hTrans : RuleProofs.eo_has_smt_translation u)
    (hBool : RuleProofs.eo_has_bool_type u)
    (hTrue :
      __smtx_model_eval (native_model_push M s ST w) (__eo_to_smt u) =
        SmtValue.Boolean true) :
    __smtx_model_eval (native_model_push M s ST v) (__eo_to_smt u) =
      SmtValue.Boolean true :=
  RelCoincidence.smt_model_eval_true_push_of_rel M hM s ST v w
    (__eo_to_smt u) hSTWf hvTy hwTy hvCanon hwCanon hRel hTrans hTrue

/-! ### Formula-level facts -/

private theorem formula_operand_facts (x F G : Term)
    (hFormulaBool :
      RuleProofs.eo_has_bool_type (quantVarElimEqFormula x F G)) :
    RuleProofs.eo_has_smt_translation (qforall (qsingle x) F) ∧
      RuleProofs.eo_has_smt_translation G ∧
      __smtx_typeof (__eo_to_smt G) =
        __smtx_typeof (__eo_to_smt (qforall (qsingle x) F)) := by
  have hOps :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (qforall (qsingle x) F) G hFormulaBool
  refine ⟨?_, ?_, hOps.1.symm⟩
  · intro hNone
    exact hOps.2 hNone
  · intro hNone
    exact hOps.2 (by rw [hOps.1, hNone])

private theorem quant_var_elim_eq_shape_of_not_stuck
    (a1 : Term) :
    __eo_prog_quant_var_elim_eq a1 ≠ Term.Stuck ->
    ∃ x F G,
      a1 = quantVarElimEqFormula x F G ∧
      __mk_quant_var_elim_eq x F = G ∧
      __eo_prog_quant_var_elim_eq a1 = quantVarElimEqFormula x F G := by
  intro hProg
  cases a1 with
  | Apply lhs G =>
      cases lhs with
      | Apply eqHead lhsArg =>
          cases eqHead with
          | UOp opEq =>
              cases opEq with
              | eq =>
                  cases lhsArg with
                  | Apply forallHead F =>
                      cases forallHead with
                      | Apply forallOp xs =>
                          cases forallOp with
                          | UOp opForall =>
                              cases opForall with
                              | «forall» =>
                                  cases xs with
                                  | Apply consHead nilTerm =>
                                      cases consHead with
                                      | Apply consOp x =>
                                          cases consOp <;>
                                            try simp [__eo_prog_quant_var_elim_eq]
                                              at hProg
                                          case __eo_List_cons =>
                                            cases nilTerm <;>
                                              try simp at hProg
                                            case __eo_List_nil =>
                                              let formula := quantVarElimEqFormula x F G
                                              let guard := __mk_quant_var_elim_eq x F
                                              have hReqNe :
                                                  __eo_requires guard G formula ≠
                                                    Term.Stuck := by
                                                simpa [formula, guard,
                                                  __eo_prog_quant_var_elim_eq,
                                                  quantVarElimEqFormula, qeq,
                                                  qforall, qsingle, qcons] using hProg
                                              have hGuard : guard = G :=
                                                instantiate_eo_requires_arg_eq_of_ne_stuck
                                                  hReqNe
                                              have hProgEq :
                                                  __eo_prog_quant_var_elim_eq formula =
                                                    formula := by
                                                change __eo_requires guard G formula =
                                                  formula
                                                exact
                                                  instantiate_eo_requires_result_eq_of_ne_stuck
                                                    hReqNe
                                              exact ⟨x, F, G, rfl, by simpa [guard] using hGuard,
                                                hProgEq⟩
                                      | _ =>
                                          simp [__eo_prog_quant_var_elim_eq] at hProg
                                  | _ =>
                                      simp [__eo_prog_quant_var_elim_eq] at hProg
                              | _ =>
                                  simp [__eo_prog_quant_var_elim_eq] at hProg
                          | _ =>
                              simp [__eo_prog_quant_var_elim_eq] at hProg
                      | _ =>
                          simp [__eo_prog_quant_var_elim_eq] at hProg
                  | _ =>
                      simp [__eo_prog_quant_var_elim_eq] at hProg
              | _ =>
                  simp [__eo_prog_quant_var_elim_eq] at hProg
          | _ =>
              simp [__eo_prog_quant_var_elim_eq] at hProg
      | _ =>
          simp [__eo_prog_quant_var_elim_eq] at hProg
  | _ =>
      simp [__eo_prog_quant_var_elim_eq] at hProg

/-! ### The `diseq` case: `(forall x. ¬(x = t)) = false` -/

private theorem quant_var_elim_eq_diseq_interprets
    (M : SmtModel) (hM : model_wf M)
    (s : native_String) (T t : Term)
    (hTWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hForallTrans :
      RuleProofs.eo_has_smt_translation
        (qforall (qsingle (Term.Var (Term.String s) T))
          (qnot (qeq (Term.Var (Term.String s) T) t))))
    (hFormulaBool :
      RuleProofs.eo_has_bool_type
        (quantVarElimEqFormula (Term.Var (Term.String s) T)
          (qnot (qeq (Term.Var (Term.String s) T) t))
          (qsubst (Term.Boolean false) (Term.Var (Term.String s) T) t)))
    (hGTrans :
      RuleProofs.eo_has_smt_translation
        (qsubst (Term.Boolean false) (Term.Var (Term.String s) T) t))
    (hNoFree :
      __contains_atomic_term_list_free_rec t
          (qsingle (Term.Var (Term.String s) T)) Term.__eo_List_nil =
        Term.Boolean false) :
    eo_interprets M
      (quantVarElimEqFormula (Term.Var (Term.String s) T)
        (qnot (qeq (Term.Var (Term.String s) T) t))
        (qsubst (Term.Boolean false) (Term.Var (Term.String s) T) t)) true := by
  have hFBool : RuleProofs.eo_has_bool_type
      (qnot (qeq (Term.Var (Term.String s) T) t)) :=
    forall_body_has_bool_type_of_has_smt_translation _ _ hForallTrans
  have hEqBool : RuleProofs.eo_has_bool_type
      (qeq (Term.Var (Term.String s) T) t) :=
    qnot_arg_has_bool_type hFBool
  rcases subst_term_facts_of_eq_bool s T t hTWf hEqBool with ⟨hTTrans, hTy⟩
  rcases eval_value_facts M hM t hTTrans with ⟨hwTyRaw, hwCanon⟩
  have hwTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __eo_to_smt_type T := by
    rw [hwTyRaw, hTy]
  -- The equality `x = t` is true when `x` is pushed to the value of `t`.
  have hEqTrueI :
      eo_interprets
        (native_model_push M s (__eo_to_smt_type T)
          (__smtx_model_eval M (__eo_to_smt t)))
        (qeq (Term.Var (Term.String s) T) t) true := by
    rw [← push_subst_model_singleton_eq M s T t]
    exact qeq_true_in_single_subst_model M hM (Term.Var (Term.String s) T) t
      (qnot (qeq (Term.Var (Term.String s) T) t)) hForallTrans hEqBool hNoFree
  have hEqEval :
      __smtx_model_eval
          (native_model_push M s (__eo_to_smt_type T)
            (__smtx_model_eval M (__eo_to_smt t)))
          (__eo_to_smt (qeq (Term.Var (Term.String s) T) t)) =
        SmtValue.Boolean true := by
    cases hEqTrueI with
    | intro_true _ hEval => exact hEval
  -- Witness for the existential encoding of the negated forall.
  have hBodyEval :
      __smtx_model_eval_not
        (__smtx_model_eval
          (native_model_push M s (__eo_to_smt_type T)
            (__smtx_model_eval M (__eo_to_smt t)))
          (__eo_to_smt (qnot (qeq (Term.Var (Term.String s) T) t)))) =
        SmtValue.Boolean true := by
    rw [qnot_to_smt, smtx_eval_not_term, hEqEval]
    simp [__smtx_model_eval_not, SmtEval.native_not]
  have hSat : ∃ v : SmtValue,
      __smtx_typeof_value v = __eo_to_smt_type T ∧
      __smtx_value_canonical v = true ∧
      __smtx_model_eval_not
          (__smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
            (__eo_to_smt (qnot (qeq (Term.Var (Term.String s) T) t)))) =
        SmtValue.Boolean true :=
    ⟨__smtx_model_eval M (__eo_to_smt t), hwTy, hwCanon, hBodyEval⟩
  have hExistsTrue :
      __smtx_model_eval M
          (SmtTerm.exists s (__eo_to_smt_type T)
            (SmtTerm.not
              (__eo_to_smt (qnot (qeq (Term.Var (Term.String s) T) t))))) =
        SmtValue.Boolean true := by
    simp [__smtx_model_eval]
    -- the `dite` no longer reduces under `simp`; pick the branch explicitly
    exact dif_pos hSat
  have hXsNonNil :
      qsingle (Term.Var (Term.String s) T) ≠ Term.__eo_List_nil := by
    simp [qsingle, qcons]
  have hForallEval :
      __smtx_model_eval M
          (__eo_to_smt (qforall (qsingle (Term.Var (Term.String s) T))
            (qnot (qeq (Term.Var (Term.String s) T) t)))) =
        SmtValue.Boolean false := by
    rw [qforall, eo_to_smt_forall_eq_of_non_nil _ _ hXsNonNil]
    rw [show __eo_to_smt_exists (qsingle (Term.Var (Term.String s) T))
          (SmtTerm.not
            (__eo_to_smt (qnot (qeq (Term.Var (Term.String s) T) t)))) =
        SmtTerm.exists s (__eo_to_smt_type T)
          (SmtTerm.not
            (__eo_to_smt (qnot (qeq (Term.Var (Term.String s) T) t))))
      from rfl]
    rw [smtx_eval_not_term, hExistsTrue]
    simp [__smtx_model_eval_not, SmtEval.native_not]
  -- The substituted side evaluates to `false` as well.
  have hGEval :
      __smtx_model_eval M
          (__eo_to_smt
            (qsubst (Term.Boolean false) (Term.Var (Term.String s) T) t)) =
        SmtValue.Boolean false := by
    rw [qsubst_eval_eq_push M hM (Term.Var (Term.String s) T) t
      (qnot (qeq (Term.Var (Term.String s) T) t)) (Term.Boolean false)
      hForallTrans hEqBool (bool_lit_has_smt_translation false) hGTrans]
    rw [false_to_smt, smtx_eval_bool_lit]
  -- Both sides of the equality evaluate to `false`.
  apply RuleProofs.eo_interprets_eq_of_rel M
    (qforall (qsingle (Term.Var (Term.String s) T))
      (qnot (qeq (Term.Var (Term.String s) T) t)))
    (qsubst (Term.Boolean false) (Term.Var (Term.String s) T) t)
    hFormulaBool
  rw [hForallEval, hGEval]
  exact RuleProofs.smt_value_rel_refl _

/-! ### The `orTail` case: `(forall x. ¬(x = t) ∨ tail) = tail[x ↦ t]` -/

private theorem quant_var_elim_eq_or_interprets
    (M : SmtModel) (hM : model_wf M)
    (s : native_String) (T t tail : Term)
    (hTWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hForallTrans :
      RuleProofs.eo_has_smt_translation
        (qforall (qsingle (Term.Var (Term.String s) T))
          (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail)))
    (hFormulaBool :
      RuleProofs.eo_has_bool_type
        (quantVarElimEqFormula (Term.Var (Term.String s) T)
          (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail)
          (qsubst (__eo_list_singleton_elim (Term.UOp UserOp.or) tail)
            (Term.Var (Term.String s) T) t)))
    (hGTrans :
      RuleProofs.eo_has_smt_translation
        (qsubst (__eo_list_singleton_elim (Term.UOp UserOp.or) tail)
          (Term.Var (Term.String s) T) t))
    (hNoFree :
      __contains_atomic_term_list_free_rec t
          (qsingle (Term.Var (Term.String s) T)) Term.__eo_List_nil =
        Term.Boolean false)
    (hIsList : __eo_is_list (Term.UOp UserOp.or) tail = Term.Boolean true) :
    eo_interprets M
      (quantVarElimEqFormula (Term.Var (Term.String s) T)
        (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail)
        (qsubst (__eo_list_singleton_elim (Term.UOp UserOp.or) tail)
          (Term.Var (Term.String s) T) t)) true := by
  -- Typing of the body components.
  have hFBool : RuleProofs.eo_has_bool_type
      (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail) :=
    forall_body_has_bool_type_of_has_smt_translation _ _ hForallTrans
  rcases qor_args_have_bool_type hFBool with ⟨hNEBool, hTailBool⟩
  have hEqBool : RuleProofs.eo_has_bool_type
      (qeq (Term.Var (Term.String s) T) t) :=
    qnot_arg_has_bool_type hNEBool
  have hTailTrans : RuleProofs.eo_has_smt_translation tail :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type _ hTailBool
  rcases subst_term_facts_of_eq_bool s T t hTWf hEqBool with ⟨hTTrans, hTy⟩
  rcases eval_value_facts M hM t hTTrans with ⟨hwTyRaw, hwCanon⟩
  have hwTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __eo_to_smt_type T := by
    rw [hwTyRaw, hTy]
  have hPWTotal :
      model_wf
        (native_model_push M s (__eo_to_smt_type T)
          (__smtx_model_eval M (__eo_to_smt t))) :=
    model_total_typed_push hM s (__eo_to_smt_type T) _ hTWf hwTy
      (by simpa [value_canonical] using hwCanon)
  -- `singleton_elim` facts.
  rcases singleton_elim_or_facts tail hIsList hTailBool with ⟨hElimBool, hElimEval⟩
  have hElimTrans :
      RuleProofs.eo_has_smt_translation
        (__eo_list_singleton_elim (Term.UOp UserOp.or) tail) :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type _ hElimBool
  -- The substituted side evaluates like `tail` under the substitution model.
  have hGEvalChain :
      __smtx_model_eval M
          (__eo_to_smt
            (qsubst (__eo_list_singleton_elim (Term.UOp UserOp.or) tail)
              (Term.Var (Term.String s) T) t)) =
        __smtx_model_eval
          (native_model_push M s (__eo_to_smt_type T)
            (__smtx_model_eval M (__eo_to_smt t)))
          (__eo_to_smt tail) := by
    rw [qsubst_eval_eq_push M hM (Term.Var (Term.String s) T) t
      (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail)
      (__eo_list_singleton_elim (Term.UOp UserOp.or) tail)
      hForallTrans hEqBool hElimTrans hGTrans]
    rw [push_subst_model_singleton_eq M s T t]
    exact hElimEval _ hPWTotal
  -- The equality is true in the substitution model.
  have hEqTrueI :
      eo_interprets
        (native_model_push M s (__eo_to_smt_type T)
          (__smtx_model_eval M (__eo_to_smt t)))
        (qeq (Term.Var (Term.String s) T) t) true := by
    rw [← push_subst_model_singleton_eq M s T t]
    exact qeq_true_in_single_subst_model M hM (Term.Var (Term.String s) T) t
      (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail)
      hForallTrans hEqBool hNoFree
  have hEqEvalW :
      __smtx_model_eval
          (native_model_push M s (__eo_to_smt_type T)
            (__smtx_model_eval M (__eo_to_smt t)))
          (__eo_to_smt (qeq (Term.Var (Term.String s) T) t)) =
        SmtValue.Boolean true := by
    cases hEqTrueI with
    | intro_true _ hEval => exact hEval
  -- Typing of the two equality operands.
  have hForallBool : RuleProofs.eo_has_bool_type
      (qforall (qsingle (Term.Var (Term.String s) T))
        (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail)) :=
    qforall_single_has_bool_type_of_has_smt_translation _ _ hForallTrans
  rcases formula_operand_facts (Term.Var (Term.String s) T)
      (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail)
      (qsubst (__eo_list_singleton_elim (Term.UOp UserOp.or) tail)
        (Term.Var (Term.String s) T) t) hFormulaBool with
    ⟨_, _, hGTyEq⟩
  have hGTy :
      __smtx_typeof
          (__eo_to_smt
            (qsubst (__eo_list_singleton_elim (Term.UOp UserOp.or) tail)
              (Term.Var (Term.String s) T) t)) = SmtType.Bool := by
    rw [hGTyEq]
    exact hForallBool
  have hXsNonNil :
      qsingle (Term.Var (Term.String s) T) ≠ Term.__eo_List_nil := by
    simp [qsingle, qcons]
  -- Direction A: the forall is true → the substituted side is true.
  have dirA :
      __smtx_model_eval M
          (__eo_to_smt (qforall (qsingle (Term.Var (Term.String s) T))
            (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail))) =
        SmtValue.Boolean true ->
      __smtx_model_eval M
          (__eo_to_smt
            (qsubst (__eo_list_singleton_elim (Term.UOp UserOp.or) tail)
              (Term.Var (Term.String s) T) t)) =
        SmtValue.Boolean true := by
    intro hFa
    have hPrem :
        eo_interprets M
          (qforall (qsingle (Term.Var (Term.String s) T))
            (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail)) true :=
      smt_interprets.intro_true M _ hForallBool hFa
    have hActuals :=
      (singleton_subst_actuals_of_eq_bool (Term.Var (Term.String s) T) t
        (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail)
        hForallTrans hEqBool).2
    have hBodyTrue :=
      InstantiateRule.instantiate_body_true M hM
        (qsingle (Term.Var (Term.String s) T))
        (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail)
        (qsingle t) hPrem hForallTrans hActuals
    rw [push_subst_model_singleton_eq M s T t] at hBodyTrue
    rw [qor_to_smt, smtx_eval_or_term, qnot_to_smt, smtx_eval_not_term,
      hEqEvalW] at hBodyTrue
    simp only [__smtx_model_eval_not, SmtEval.native_not] at hBodyTrue
    have hTailTrue :
        __smtx_model_eval
            (native_model_push M s (__eo_to_smt_type T)
              (__smtx_model_eval M (__eo_to_smt t)))
            (__eo_to_smt tail) = SmtValue.Boolean true :=
      or_eval_true_right_of_left_false (by simpa using hBodyTrue)
    rw [hGEvalChain]
    exact hTailTrue
  -- Direction B: the substituted side is true → the forall is true.
  have dirB :
      __smtx_model_eval M
          (__eo_to_smt
            (qsubst (__eo_list_singleton_elim (Term.UOp UserOp.or) tail)
              (Term.Var (Term.String s) T) t)) =
        SmtValue.Boolean true ->
      __smtx_model_eval M
          (__eo_to_smt (qforall (qsingle (Term.Var (Term.String s) T))
            (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail))) =
        SmtValue.Boolean true := by
    intro hGtrue
    have hTailTrueW :
        __smtx_model_eval
            (native_model_push M s (__eo_to_smt_type T)
              (__smtx_model_eval M (__eo_to_smt t)))
            (__eo_to_smt tail) = SmtValue.Boolean true :=
      hGEvalChain.symm.trans hGtrue
    rw [qforall, eo_to_smt_forall_eq_of_non_nil _ _ hXsNonNil]
    rw [show __eo_to_smt_exists (qsingle (Term.Var (Term.String s) T))
          (SmtTerm.not
            (__eo_to_smt (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail))) =
        SmtTerm.exists s (__eo_to_smt_type T)
          (SmtTerm.not
            (__eo_to_smt (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail)))
      from rfl]
    have hNoSat : ∀ v : SmtValue,
        __smtx_typeof_value v = __eo_to_smt_type T →
        __smtx_value_canonical v = true →
        ¬ __smtx_model_eval_not
            (__smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
              (__eo_to_smt
                (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail))) =
          SmtValue.Boolean true := by
      intro v hvTy hvCanon hvBody
      have hPushTot :
          model_wf (native_model_push M s (__eo_to_smt_type T) v) :=
        model_total_typed_push hM s (__eo_to_smt_type T) v hTWf hvTy
          (by simpa [value_canonical] using hvCanon)
      rcases smt_model_eval_bool_is_boolean _ hPushTot
          (__eo_to_smt (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail))
          hFBool with ⟨bF, hbF⟩
      rw [hbF] at hvBody
      cases bF with
      | true => simp [__smtx_model_eval_not, SmtEval.native_not] at hvBody
      | false =>
        have hFTrue :
            __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
                (__eo_to_smt
                  (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail)) =
              SmtValue.Boolean true := by
          have hEvalX :
              __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
                  (__eo_to_smt (Term.Var (Term.String s) T)) = v :=
            eval_var_after_push M s T v
          have hEvalTv :
              __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
                  (__eo_to_smt t) =
                __smtx_model_eval M (__eo_to_smt t) :=
            eval_t_after_push_eq M s T t v hTWf hvTy hvCanon hTTrans hNoFree
          have hEqEv :
              __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
                  (__eo_to_smt (qeq (Term.Var (Term.String s) T) t)) =
                __smtx_model_eval_eq v (__smtx_model_eval M (__eo_to_smt t)) := by
            rw [qeq_to_smt, smtx_eval_eq_term, hEvalX, hEvalTv]
          rcases smt_model_eval_bool_is_boolean _ hPushTot
              (__eo_to_smt tail) hTailBool with ⟨bT, hbT⟩
          rcases eval_eq_is_boolean v (__smtx_model_eval M (__eo_to_smt t)) with
            ⟨bE, hbE⟩
          cases bE with
          | false =>
              rw [qor_to_smt, smtx_eval_or_term, qnot_to_smt,
                smtx_eval_not_term, hEqEv, hbE, hbT]
              cases bT <;>
                simp [__smtx_model_eval_not, __smtx_model_eval_or,
                  SmtEval.native_not, SmtEval.native_or]
          | true =>
              have hTailTruePV :
                  __smtx_model_eval
                      (native_model_push M s (__eo_to_smt_type T) v)
                      (__eo_to_smt tail) = SmtValue.Boolean true :=
                eval_true_push_of_rel M hM s (__eo_to_smt_type T) v
                  (__smtx_model_eval M (__eo_to_smt t)) tail hTWf hvTy hwTy
                  hvCanon hwCanon hbE hTailTrans hTailBool hTailTrueW
              rw [qor_to_smt, smtx_eval_or_term, qnot_to_smt,
                smtx_eval_not_term, hEqEv, hbE, hTailTruePV]
              simp [__smtx_model_eval_not, __smtx_model_eval_or,
                SmtEval.native_not, SmtEval.native_or]
        rw [hFTrue] at hbF
        cases hbF
    have hExistsFalse :
        __smtx_model_eval M
            (SmtTerm.exists s (__eo_to_smt_type T)
              (SmtTerm.not
                (__eo_to_smt
                  (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail)))) =
          SmtValue.Boolean false := by
      simp [__smtx_model_eval]
      exact dif_neg (fun h => by
        rcases h with ⟨v, hvTy, hvCanon, hvEval⟩
        exact hNoSat v hvTy hvCanon hvEval)
    rw [smtx_eval_not_term, hExistsFalse]
    simp [__smtx_model_eval_not, SmtEval.native_not]
  -- Both sides evaluate to the same Boolean.
  rcases smt_model_eval_bool_is_boolean M hM
      (__eo_to_smt (qforall (qsingle (Term.Var (Term.String s) T))
        (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail)))
      hForallBool with ⟨b1, hb1⟩
  rcases smt_model_eval_bool_is_boolean M hM
      (__eo_to_smt
        (qsubst (__eo_list_singleton_elim (Term.UOp UserOp.or) tail)
          (Term.Var (Term.String s) T) t))
      hGTy with ⟨b2, hb2⟩
  have hb12 : b1 = b2 := by
    cases b1 <;> cases b2
    · rfl
    · have := dirB hb2
      rw [hb1] at this
      cases this
    · have := dirA hb1
      rw [hb2] at this
      cases this
    · rfl
  apply RuleProofs.eo_interprets_eq_of_rel M
    (qforall (qsingle (Term.Var (Term.String s) T))
      (qor (qnot (qeq (Term.Var (Term.String s) T) t)) tail))
    (qsubst (__eo_list_singleton_elim (Term.UOp UserOp.or) tail)
      (Term.Var (Term.String s) T) t)
    hFormulaBool
  rw [hb1, hb2, hb12]
  exact RuleProofs.smt_value_rel_refl _

/-! ### Case extraction from the checker program -/

/-- The `¬(x2 = t)` arm of `__mk_quant_var_elim_eq`, as a standalone lemma so
that the `split`-generated inaccessible pattern variables are named by
unification. -/
private theorem mk_case_not_arm (xn xT x2 t G : Term)
    (hMk : __eo_ite (__eo_eq (Term.Var xn xT) x2)
        (__eo_requires
          (__contains_atomic_term_list_free_rec t
            ((Term.__eo_List_cons.Apply (Term.Var xn xT)).Apply
              Term.__eo_List_nil)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__substitute_simul_rec (Term.Boolean false) (Term.Boolean false)
            ((Term.__eo_List_cons.Apply (Term.Var xn xT)).Apply
              Term.__eo_List_nil)
            ((Term.__eo_List_cons.Apply t).Apply Term.__eo_List_nil)
            Term.__eo_List_nil))
        Term.Stuck = G)
    (hG : G ≠ Term.Stuck) :
    QuantVarElimEqCase (Term.Var xn xT) (qnot (qeq x2 t)) G := by
  have hxne : (Term.Var xn xT) ≠ Term.Stuck := by simp
  by_cases hx2 : x2 = Term.Var xn xT
  · subst hx2
    have hMk2 := eq_of_eo_ite_true (eo_eq_self_true _ hxne) hMk
    obtain ⟨hCond, hGeq⟩ := requires_facts_of_eq_ne_stuck hMk2 hG
    refine QuantVarElimEqCase.diseq t rfl ?_ ?_
    · simpa [qsingle, qcons] using hCond
    · simpa [qsubst, qsingle, qcons] using hGeq
  · by_cases hx2s : x2 = Term.Stuck
    · subst hx2s
      exact absurd (show Term.Stuck = G from hMk).symm hG
    · have hEqFalse : __eo_eq (Term.Var xn xT) x2 = Term.Boolean false := by
        rw [eo_eq_eq_of_ne_stuck hxne hx2s]
        simp [native_teq, hx2]
      exact absurd (eq_of_eo_ite_false hEqFalse hMk).symm hG

/-- The or-list arm of `__eo_l_1___mk_quant_var_elim_eq`, as a standalone
lemma (see `mk_case_not_arm`). -/
private theorem mk_case_or_arm (xn xT x2 t tail G : Term)
    (hMk : __eo_requires (__eo_eq (Term.Var xn xT) x2) (Term.Boolean true)
        (__eo_requires
          (__contains_atomic_term_list_free_rec t
            ((Term.__eo_List_cons.Apply (Term.Var xn xT)).Apply
              Term.__eo_List_nil)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__substitute_simul_rec (Term.Boolean false)
            (__eo_list_singleton_elim (Term.UOp UserOp.or) tail)
            ((Term.__eo_List_cons.Apply (Term.Var xn xT)).Apply
              Term.__eo_List_nil)
            ((Term.__eo_List_cons.Apply t).Apply Term.__eo_List_nil)
            Term.__eo_List_nil)) = G)
    (hG : G ≠ Term.Stuck) :
    QuantVarElimEqCase (Term.Var xn xT) (qor (qnot (qeq x2 t)) tail) G := by
  obtain ⟨hEqTrue, hGeq1⟩ := requires_facts_of_eq_ne_stuck hMk hG
  have hx2 : x2 = Term.Var xn xT :=
    support_eq_of_eo_eq_true (Term.Var xn xT) x2 hEqTrue
  subst hx2
  obtain ⟨hCond, hGeq2⟩ := requires_facts_of_eq_ne_stuck hGeq1.symm hG
  have hElimNe :
      __eo_list_singleton_elim (Term.UOp UserOp.or) tail ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hGeq2
    exact hG (hGeq2.trans
      (show __substitute_simul_rec (Term.Boolean false) Term.Stuck
          ((Term.__eo_List_cons.Apply (Term.Var xn xT)).Apply
            Term.__eo_List_nil)
          ((Term.__eo_List_cons.Apply t).Apply Term.__eo_List_nil)
          Term.__eo_List_nil = Term.Stuck from rfl))
  have hIsList :
      __eo_is_list (Term.UOp UserOp.or) tail = Term.Boolean true :=
    (requires_facts_of_eq_ne_stuck
      (show __eo_requires (__eo_is_list (Term.UOp UserOp.or) tail)
          (Term.Boolean true) (__eo_list_singleton_elim_2 tail) =
        __eo_list_singleton_elim (Term.UOp UserOp.or) tail from rfl)
      hElimNe).1
  refine QuantVarElimEqCase.orTail t tail rfl ?_ hIsList ?_
  · simpa [qsingle, qcons] using hCond
  · simpa [qsubst, qsingle, qcons] using hGeq2

private theorem mk_case_l1 (xn xT F G : Term)
    (hMk : __eo_l_1___mk_quant_var_elim_eq (Term.Var xn xT) F = G)
    (hG : G ≠ Term.Stuck) :
    QuantVarElimEqCase (Term.Var xn xT) F G := by
  rw [__eo_l_1___mk_quant_var_elim_eq.eq_def] at hMk
  split at hMk
  · exact absurd hMk.symm hG
  · exact mk_case_or_arm _ _ _ _ _ _ hMk hG
  · exact absurd hMk.symm hG

private theorem mk_quant_var_elim_eq_case_of_ne_stuck
    (xn xT F G : Term)
    (hMk : __mk_quant_var_elim_eq (Term.Var xn xT) F = G)
    (hG : G ≠ Term.Stuck) :
    QuantVarElimEqCase (Term.Var xn xT) F G := by
  rw [__mk_quant_var_elim_eq.eq_def] at hMk
  split at hMk
  · exact absurd hMk.symm hG
  · exact absurd hMk.symm hG
  · exact mk_case_not_arm _ _ _ _ _ hMk hG
  · exact mk_case_l1 _ _ _ _ hMk hG

private theorem quant_var_elim_eq_formula_true
    (M : SmtModel) (hM : model_wf M)
    (x F G : Term) :
    RuleProofs.eo_has_smt_translation
        (quantVarElimEqFormula x F G) ->
    __eo_typeof (quantVarElimEqFormula x F G) = Term.Bool ->
    __mk_quant_var_elim_eq x F = G ->
    eo_interprets M (quantVarElimEqFormula x F G) true := by
  intro hTrans hType hMk
  have hFormulaBool : RuleProofs.eo_has_bool_type (quantVarElimEqFormula x F G) :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type _ hTrans hType
  rcases formula_operand_facts x F G hFormulaBool with
    ⟨hForallTrans, hGTrans, _⟩
  rcases qsingle_binder_shape_of_forall_trans x F hForallTrans with
    ⟨s, T, rfl, hTWf⟩
  have hGne : G ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation G hGTrans
  cases mk_quant_var_elim_eq_case_of_ne_stuck (Term.String s) T F G hMk hGne with
  | diseq t hF hNoFree hGeq =>
      subst hF
      subst hGeq
      exact quant_var_elim_eq_diseq_interprets M hM s T t hTWf hForallTrans
        hFormulaBool hGTrans hNoFree
  | orTail t tail hF hNoFree hIsList hGeq =>
      subst hF
      subst hGeq
      exact quant_var_elim_eq_or_interprets M hM s T t tail hTWf hForallTrans
        hFormulaBool hGTrans hNoFree hIsList

end QuantVarElimEqRule

public theorem cmd_step_quant_var_elim_eq_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_var_elim_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.quant_var_elim_eq args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_var_elim_eq args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.quant_var_elim_eq args premises ≠
        Term.Stuck :=
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
              have hTransA1 : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using
                  hCmdTrans
              have hProgQuant :
                  __eo_prog_quant_var_elim_eq a1 ≠ Term.Stuck := by
                change __eo_prog_quant_var_elim_eq a1 ≠ Term.Stuck at hProg
                simpa using hProg
              rcases QuantVarElimEqRule.quant_var_elim_eq_shape_of_not_stuck
                  a1 hProgQuant with
                ⟨x, F, G, ha1, hMk, hProgEq⟩
              have hTransFormula :
                  RuleProofs.eo_has_smt_translation
                    (QuantVarElimEqRule.quantVarElimEqFormula x F G) := by
                simpa [ha1] using hTransA1
              have hFormulaType :
                  __eo_typeof
                      (QuantVarElimEqRule.quantVarElimEqFormula x F G) =
                    Term.Bool := by
                change __eo_typeof (__eo_prog_quant_var_elim_eq a1) =
                  Term.Bool at hResultTy
                rw [hProgEq] at hResultTy
                exact hResultTy
              have hFormulaBool :
                  RuleProofs.eo_has_bool_type
                    (QuantVarElimEqRule.quantVarElimEqFormula x F G) :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  (QuantVarElimEqRule.quantVarElimEqFormula x F G)
                  hTransFormula hFormulaType
              have hFact :
                  eo_interprets M
                    (QuantVarElimEqRule.quantVarElimEqFormula x F G) true :=
                QuantVarElimEqRule.quant_var_elim_eq_formula_true M hM x F G
                  hTransFormula hFormulaType hMk
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M
                  (__eo_prog_quant_var_elim_eq a1) true
                rw [hProgEq]
                exact hFact
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_quant_var_elim_eq a1)
                rw [hProgEq]
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  hFormulaBool
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
