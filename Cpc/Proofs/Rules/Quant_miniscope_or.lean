module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.StringSupport
import all Cpc.Proofs.RuleSupport.StringSupport
public import Cpc.Proofs.Closed.ContainsAtomicTermListFree
import all Cpc.Proofs.Closed.ContainsAtomicTermListFree

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def qforall (x F : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.forall) x) F

private def qor (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B

private def qeq (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B

private def qcons (x xs : Term) : Term :=
  Term.Apply (Term.Apply Term.__eo_List_cons x) xs

private def quantMiniscopeOrFormula (x F G : Term) : Term :=
  qeq (qforall x F) G

private def smtForall (xs : Term) (body : SmtTerm) : SmtTerm :=
  SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not body))

private def miniToSmt : Term -> SmtTerm
  | Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B =>
      SmtTerm.or (miniToSmt A) (miniToSmt B)
  | Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F =>
      smtForall xs (__eo_to_smt F)
  | t => __eo_to_smt t

private theorem eo_to_smt_or_eq (A B : Term) :
    __eo_to_smt (qor A B) =
      SmtTerm.or (__eo_to_smt A) (__eo_to_smt B) := by
  rfl

private theorem eo_to_smt_forall_eq (x F : Term)
    (hx : x ≠ Term.__eo_List_nil) :
    __eo_to_smt (qforall x F) =
      smtForall x (__eo_to_smt F) := by
  cases x <;> first | rfl | exact False.elim (hx rfl)

private theorem smtx_typeof_not_arg_of_bool
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool ->
    __smtx_typeof t = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq] at hTy
  cases h : __smtx_typeof t <;>
    simp [h, native_ite, native_Teq] at hTy ⊢

private theorem smtx_typeof_not_bool_of_arg_bool
    (t : SmtTerm) :
    __smtx_typeof t = SmtType.Bool ->
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq]
  simp [hTy, native_ite, native_Teq]

private theorem smtx_typeof_not_bool_of_non_none
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool := by
  intro hNN
  have hArg : __smtx_typeof t = SmtType.Bool := by
    cases h : __smtx_typeof t <;>
      simp [typeof_not_eq, h, native_ite, native_Teq] at hNN ⊢
  exact smtx_typeof_not_bool_of_arg_bool t hArg

private theorem smtx_typeof_not_arg_of_non_none
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) ≠ SmtType.None ->
    __smtx_typeof t = SmtType.Bool := by
  intro hNN
  exact smtx_typeof_not_arg_of_bool t
    (smtx_typeof_not_bool_of_non_none t hNN)

private theorem smtx_typeof_or_args_of_bool
    (A B : SmtTerm) :
    __smtx_typeof (SmtTerm.or A B) = SmtType.Bool ->
    __smtx_typeof A = SmtType.Bool ∧
      __smtx_typeof B = SmtType.Bool := by
  intro hTy
  rw [typeof_or_eq] at hTy
  cases hA : __smtx_typeof A <;>
    cases hB : __smtx_typeof B <;>
    simp [hA, hB, native_ite, native_Teq] at hTy ⊢

private theorem smtx_typeof_or_bool_of_args
    (A B : SmtTerm) :
    __smtx_typeof A = SmtType.Bool ->
    __smtx_typeof B = SmtType.Bool ->
    __smtx_typeof (SmtTerm.or A B) = SmtType.Bool := by
  intro hA hB
  rw [typeof_or_eq]
  simp [hA, hB, native_ite, native_Teq]

private theorem smtx_typeof_exists_tail_bool_of_cons_bool
    (s : native_String) (T xs : Term) (body : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs)
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

private theorem smtx_type_wf_of_exists_cons_bool
    (s : native_String) (T xs : Term) (body : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs)
          body) = SmtType.Bool ->
    __smtx_type_wf (__eo_to_smt_type T) = true := by
  intro hTy
  have hTail :
      __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool :=
    smtx_typeof_exists_tail_bool_of_cons_bool s T xs body hTy
  have hGuardNN :
      __smtx_typeof_guard_wf (__eo_to_smt_type T) SmtType.Bool ≠ SmtType.None := by
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

private theorem smtx_typeof_eo_to_smt_exists_same_binders
    (xs : Term) (body body' : SmtTerm) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
    __smtx_typeof body' = SmtType.Bool ->
    __smtx_typeof (__eo_to_smt_exists xs body') = SmtType.Bool := by
  intro hTy hBody'
  cases hxs : xs
  case __eo_List_nil =>
      subst hxs
      simpa [__eo_to_smt_exists] using hBody'
  case Apply f a =>
      subst hxs
      cases f with
      | Apply g y =>
          cases g with
          | __eo_List_cons =>
              cases y with
              | Var name T =>
                  cases name with
                  | String s =>
                      have hTail :
                          __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool :=
                        smtx_typeof_exists_tail_bool_of_cons_bool s T a body hTy
                      have hTail' :
                          __smtx_typeof (__eo_to_smt_exists a body') = SmtType.Bool :=
                        smtx_typeof_eo_to_smt_exists_same_binders a body body'
                          hTail hBody'
                      have hWF :
                          __smtx_type_wf (__eo_to_smt_type T) = true :=
                        smtx_type_wf_of_exists_cons_bool s T a body hTy
                      change
                        __smtx_typeof
                          (SmtTerm.exists s (__eo_to_smt_type T)
                            (__eo_to_smt_exists a body')) = SmtType.Bool
                      rw [smtx_typeof_exists_term_eq, hTail']
                      simp [native_ite, native_Teq, __smtx_typeof_guard_wf, hWF]
                  | _ =>
                      simp [__eo_to_smt_exists] at hTy
              | _ =>
                  simp [__eo_to_smt_exists] at hTy
          | _ =>
              simp [__eo_to_smt_exists] at hTy
      | _ =>
          simp [__eo_to_smt_exists] at hTy
  all_goals
      subst hxs
      simp [__eo_to_smt_exists] at hTy

private theorem qforall_non_nil_of_non_none
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None ->
    x ≠ Term.__eo_List_nil := by
  intro hNN hx
  subst x
  apply hNN
  change __smtx_typeof SmtTerm.None = SmtType.None
  exact TranslationProofs.smtx_typeof_none

private theorem qforall_exists_type_bool_of_non_none
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None ->
    __smtx_typeof
        (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
      SmtType.Bool := by
  intro hNN
  have hx : x ≠ Term.__eo_List_nil :=
    qforall_non_nil_of_non_none x F hNN
  exact smtx_typeof_not_arg_of_non_none
    (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) (by
      simpa [eo_to_smt_forall_eq x F hx, smtForall] using hNN)

private theorem smtx_eval_exists_term_eq
    (M : SmtModel) (s : native_String) (T : SmtType)
    (body : SmtTerm) :
    __smtx_model_eval M (SmtTerm.exists s T body) =
      native_eval_exists M s T body := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_model_eval_not_eq_of_arg_eq_same
    {M : SmtModel} {x y : SmtTerm}
    (h : __smtx_model_eval M x = __smtx_model_eval M y) :
    __smtx_model_eval M (SmtTerm.not x) =
      __smtx_model_eval M (SmtTerm.not y) := by
  simp [__smtx_model_eval, h]

private theorem smtx_model_eval_or_eq_of_args_eq_same
    {M : SmtModel} {x x' y y' : SmtTerm}
    (hx : __smtx_model_eval M x = __smtx_model_eval M x')
    (hy : __smtx_model_eval M y = __smtx_model_eval M y') :
    __smtx_model_eval M (SmtTerm.or x y) =
      __smtx_model_eval M (SmtTerm.or x' y') := by
  simp [__smtx_model_eval, hx, hy]

private theorem native_eval_texists_eq_of_body_eval_eq_same_typed
    {M : SmtModel} {s : native_String} {T : SmtType}
    {body body' : SmtTerm}
    (hBody : ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
      __smtx_value_canonical v = true ->
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval (native_model_push M s T v) body') :
    native_eval_exists M s T body =
      native_eval_exists M s T body' := by
  classical
  let P : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push M s T v) body =
          SmtValue.Boolean true
  let Q : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push M s T v) body' =
          SmtValue.Boolean true
  change (if _ : P then SmtValue.Boolean true else SmtValue.Boolean false) =
    (if _ : Q then SmtValue.Boolean true else SmtValue.Boolean false)
  have hIff : P ↔ Q := by
    constructor
    · intro h
      rcases h with ⟨v, hTy, hCanon, hEval⟩
      exact ⟨v, hTy, hCanon, by
        simpa [hBody v hTy hCanon] using hEval⟩
    · intro h
      rcases h with ⟨v, hTy, hCanon, hEval⟩
      exact ⟨v, hTy, hCanon, by
        simpa [← hBody v hTy hCanon] using hEval⟩
  by_cases hP : P
  · have hQ : Q := hIff.mp hP
    simp [hP, hQ]
  · have hQ : ¬ Q := fun h => hP (hIff.mpr h)
    simp [hP, hQ]

private theorem smt_model_eval_eo_to_smt_exists_eq_of_body_eval_eq_same_mapped_typed
    {vs : Term} {binderVars : List EoVarKey}
    {exceptVars : List SmtVarKey} {M N : SmtModel}
    {body body' : SmtTerm}
    (hEnv : EoVarEnv vs binderVars)
    (hWF :
      ∀ s T, (s, T) ∈ binderVars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hSub :
      ∀ key, key ∈ binderVars.map EoVarKey.toSmt -> key ∈ exceptVars)
    (hM : model_wf M)
    (hAgree : model_agrees_except_on_env exceptVars [] M N)
    (hBody :
      ∀ {M' : SmtModel},
        model_wf M' ->
        model_agrees_except_on_env exceptVars [] M' N ->
          __smtx_model_eval M' body =
            __smtx_model_eval M' body') :
  __smtx_model_eval M (__eo_to_smt_exists vs body) =
    __smtx_model_eval M (__eo_to_smt_exists vs body') := by
  induction hEnv generalizing M with
  | nil =>
      simpa [__eo_to_smt_exists] using hBody hM hAgree
  | cons hTail ih =>
      rename_i s T env tailVars
      change
        __smtx_model_eval M
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists env body)) =
          __smtx_model_eval M
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists env body'))
      rw [smtx_eval_exists_term_eq, smtx_eval_exists_term_eq]
      apply native_eval_texists_eq_of_body_eval_eq_same_typed
      intro v hv hCan
      have hHeadWF :
          __smtx_type_wf (__eo_to_smt_type T) = true :=
        hWF s T (by simp)
      have hPush :
          model_wf
            (native_model_push M s (__eo_to_smt_type T) v) :=
        model_total_typed_push hM s (__eo_to_smt_type T) v hHeadWF
          hv (by
            rw [value_canonical_bool_eq_true]
            exact hCan)
      have hHeadMem :
          (s, __eo_to_smt_type T) ∈ exceptVars :=
        hSub (s, __eo_to_smt_type T) (by
          simp [EoVarKey.toSmt])
      have hAgreePush :
          model_agrees_except_on_env exceptVars []
            (native_model_push M s (__eo_to_smt_type T) v) N :=
        model_agrees_except_on_env_push_left hAgree hHeadMem (by simp)
      apply ih
      · intro s' T' hMem
        exact hWF s' T' (by simp [hMem])
      · intro key hMem
        apply hSub
        rcases List.mem_map.1 hMem with ⟨eoKey, hEoMem, hKeyEq⟩
        exact List.mem_map.2 ⟨eoKey, List.mem_cons_of_mem _ hEoMem, hKeyEq⟩
      · exact hPush
      · exact hAgreePush

private theorem smt_model_eval_smtForall_eq_of_body_eval_eq_same_mapped_typed
    {vs : Term} {binderVars : List EoVarKey}
    {exceptVars : List SmtVarKey} {M N : SmtModel}
    {body body' : SmtTerm}
    (hEnv : EoVarEnv vs binderVars)
    (hWF :
      ∀ s T, (s, T) ∈ binderVars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hSub :
      ∀ key, key ∈ binderVars.map EoVarKey.toSmt -> key ∈ exceptVars)
    (hM : model_wf M)
    (hAgree : model_agrees_except_on_env exceptVars [] M N)
    (hBody :
      ∀ {M' : SmtModel},
        model_wf M' ->
        model_agrees_except_on_env exceptVars [] M' N ->
          __smtx_model_eval M' body =
            __smtx_model_eval M' body') :
  __smtx_model_eval M (smtForall vs body) =
    __smtx_model_eval M (smtForall vs body') := by
  unfold smtForall
  apply smtx_model_eval_not_eq_of_arg_eq_same
  apply smt_model_eval_eo_to_smt_exists_eq_of_body_eval_eq_same_mapped_typed
    hEnv hWF hSub hM hAgree
  intro M' hM' hAgree'
  exact smtx_model_eval_not_eq_of_arg_eq_same (hBody hM' hAgree')

private theorem smtx_model_eval_exists_not_true_false_of_env :
    ∀ {xs : Term} {vars : List EoVarKey},
      EoVarEnv xs vars ->
      ∀ M : SmtModel,
        __smtx_model_eval M
            (__eo_to_smt_exists xs
              (SmtTerm.not (SmtTerm.Boolean true))) =
          SmtValue.Boolean false
  | _, _, EoVarEnv.nil => by
      intro M
      simp [__eo_to_smt_exists, __smtx_model_eval,
        __smtx_model_eval_not, SmtEval.native_not]
  | _, _, EoVarEnv.cons hTail => by
      intro M
      rename_i s T env tailVars
      change
        __smtx_model_eval M
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists env
                (SmtTerm.not (SmtTerm.Boolean true)))) =
          SmtValue.Boolean false
      rw [smtx_eval_exists_term_eq]
      classical
      let P : Prop :=
        ∃ v : SmtValue,
          __smtx_typeof_value v = __eo_to_smt_type T ∧
            __smtx_value_canonical v = true ∧
            __smtx_model_eval
                (native_model_push M s (__eo_to_smt_type T) v)
                (__eo_to_smt_exists env
                  (SmtTerm.not (SmtTerm.Boolean true))) =
              SmtValue.Boolean true
      have hPFalse : ¬ P := by
        intro hP
        rcases hP with ⟨v, _hv, _hCan, hEval⟩
        have hRec :=
          smtx_model_eval_exists_not_true_false_of_env hTail
            (native_model_push M s (__eo_to_smt_type T) v)
        rw [hRec] at hEval
        cases hEval
      change (if _ : P then SmtValue.Boolean true else SmtValue.Boolean false) =
        SmtValue.Boolean false
      simp [hPFalse]

private theorem smtx_model_eval_smtForall_true_of_env
    {xs : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv xs vars) (M : SmtModel) :
    __smtx_model_eval M (smtForall xs (SmtTerm.Boolean true)) =
      SmtValue.Boolean true := by
  unfold smtForall
  have hExistsFalse :=
    smtx_model_eval_exists_not_true_false_of_env hEnv M
  simp [__smtx_model_eval, hExistsFalse, __smtx_model_eval_not,
    SmtEval.native_not]

private theorem smtx_typeof_eo_to_smt_exists_bool_of_env
    {xs : Term} {vars : List EoVarKey} {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hWF :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hBody : __smtx_typeof body = SmtType.Bool) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool := by
  induction hEnv generalizing body with
  | nil =>
      simpa [__eo_to_smt_exists] using hBody
  | cons hTail ih =>
      rename_i s T env tailVars
      have hTailTy :
          __smtx_typeof (__eo_to_smt_exists env body) = SmtType.Bool :=
        ih
          (by
            intro s' T' hMem
            exact hWF s' T' (by simp [hMem]))
          hBody
      have hHeadWF :
          __smtx_type_wf (__eo_to_smt_type T) = true :=
        hWF s T (by simp)
      change
        __smtx_typeof
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists env body)) = SmtType.Bool
      rw [smtx_typeof_exists_term_eq, hTailTy]
      simp [native_ite, native_Teq, __smtx_typeof_guard_wf, hHeadWF]

private theorem smtx_typeof_smtForall_bool_of_env
    {xs : Term} {vars : List EoVarKey} {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hWF :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hBody : __smtx_typeof body = SmtType.Bool) :
    __smtx_typeof (smtForall xs body) = SmtType.Bool := by
  unfold smtForall
  apply smtx_typeof_not_bool_of_arg_bool
  apply smtx_typeof_eo_to_smt_exists_bool_of_env hEnv hWF
  exact smtx_typeof_not_bool_of_arg_bool body hBody

private theorem smtx_typeof_smtForall_body_of_bool
    (xs : Term) (body : SmtTerm) :
    __smtx_typeof (smtForall xs body) = SmtType.Bool ->
      __smtx_typeof body = SmtType.Bool := by
  intro hTy
  have hExists :
      __smtx_typeof
          (__eo_to_smt_exists xs (SmtTerm.not body)) =
        SmtType.Bool := by
    unfold smtForall at hTy
    exact smtx_typeof_not_arg_of_bool
      (__eo_to_smt_exists xs (SmtTerm.not body)) hTy
  have hNotBody :
      __smtx_typeof (SmtTerm.not body) = SmtType.Bool :=
    TranslationProofs.eo_to_smt_exists_body_bool_of_bool
      xs (SmtTerm.not body) hExists
  exact smtx_typeof_not_arg_of_bool body hNotBody

private theorem smtx_type_wf_of_smtForall_env_bool
    {xs : Term} {vars : List EoVarKey} {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hTy : __smtx_typeof (smtForall xs body) = SmtType.Bool) :
    ∀ s T, (s, T) ∈ vars ->
      __smtx_type_wf (__eo_to_smt_type T) = true := by
  match hEnv with
  | EoVarEnv.nil =>
      intro s T hMem
      cases hMem
  | @EoVarEnv.cons sHead THead env tailVars hTail =>
        intro s' T' hMem
        simp at hMem
        rcases hMem with hHead | hTailMem
        · rcases hHead with ⟨rfl, rfl⟩
          have hExistsTy :
              __smtx_typeof
                  (__eo_to_smt_exists
                    (Term.Apply
                      (Term.Apply Term.__eo_List_cons
                        (Term.Var (Term.String s') T')) env)
                    (SmtTerm.not body)) =
                SmtType.Bool := by
            unfold smtForall at hTy
            exact smtx_typeof_not_arg_of_bool _ hTy
          exact smtx_type_wf_of_exists_cons_bool s' T' env
            (SmtTerm.not body) hExistsTy
        · have hExistsTy :
              __smtx_typeof
                  (__eo_to_smt_exists
                    (Term.Apply
                      (Term.Apply Term.__eo_List_cons
                        (Term.Var (Term.String sHead) THead)) env)
                    (SmtTerm.not body)) =
                SmtType.Bool := by
            unfold smtForall at hTy
            exact smtx_typeof_not_arg_of_bool _ hTy
          have hTailExistsTy :
              __smtx_typeof
                  (__eo_to_smt_exists env (SmtTerm.not body)) =
                SmtType.Bool :=
            smtx_typeof_exists_tail_bool_of_cons_bool sHead THead env
              (SmtTerm.not body) hExistsTy
          have hTailForallTy :
              __smtx_typeof (smtForall env body) = SmtType.Bool := by
            unfold smtForall
            exact smtx_typeof_not_bool_of_arg_bool
              (__eo_to_smt_exists env (SmtTerm.not body)) hTailExistsTy
          exact smtx_type_wf_of_smtForall_env_bool
            hTail hTailForallTy s' T' hTailMem

private theorem smtx_model_eval_not_not_eq_self_of_bool
    (M : SmtModel) (hM : model_wf M) (body : SmtTerm)
    (hBodyTy : __smtx_typeof body = SmtType.Bool) :
  __smtx_model_eval M (SmtTerm.not (SmtTerm.not body)) =
    __smtx_model_eval M body := by
  rcases smt_model_eval_bool_is_boolean M hM body hBodyTy with
    ⟨b, hEval⟩
  rw [hEval]
  cases b <;>
    simp [__smtx_model_eval, hEval, __smtx_model_eval_not,
      SmtEval.native_not]

private theorem smtx_model_eval_smtForall_nil_eq_body
    (M : SmtModel) (hM : model_wf M) (body : SmtTerm)
    (hBodyTy : __smtx_typeof body = SmtType.Bool) :
    __smtx_model_eval M (smtForall Term.__eo_List_nil body) =
      __smtx_model_eval M body := by
  unfold smtForall
  simpa [__eo_to_smt_exists] using
    smtx_model_eval_not_not_eq_self_of_bool M hM body hBodyTy

private theorem smtx_model_eval_smtForall_cons_split
    (M : SmtModel) (hM : model_wf M)
    (s : native_String) (T xs : Term) (body : SmtTerm)
    (hHeadWF : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hTailTy :
      __smtx_typeof
          (__eo_to_smt_exists xs (SmtTerm.not body)) =
        SmtType.Bool) :
    __smtx_model_eval M
        (smtForall
          (qcons (Term.Var (Term.String s) T) xs) body) =
      __smtx_model_eval M
        (smtForall
          (qcons (Term.Var (Term.String s) T) Term.__eo_List_nil)
          (smtForall xs body)) := by
  unfold smtForall
  change
    __smtx_model_eval M
        (SmtTerm.not
          (SmtTerm.exists s (__eo_to_smt_type T)
            (__eo_to_smt_exists xs (SmtTerm.not body)))) =
      __smtx_model_eval M
        (SmtTerm.not
          (SmtTerm.exists s (__eo_to_smt_type T)
            (SmtTerm.not
              (SmtTerm.not
                (__eo_to_smt_exists xs (SmtTerm.not body))))))
  apply smtx_model_eval_not_eq_of_arg_eq_same
  rw [smtx_eval_exists_term_eq, smtx_eval_exists_term_eq]
  apply native_eval_texists_eq_of_body_eval_eq_same_typed
  intro v hv hCan
  have hPush :
      model_wf
        (native_model_push M s (__eo_to_smt_type T) v) :=
    model_total_typed_push hM s (__eo_to_smt_type T) v hHeadWF
      hv (by
        rw [value_canonical_bool_eq_true]
        exact hCan)
  exact
    (smtx_model_eval_not_not_eq_self_of_bool
      (native_model_push M s (__eo_to_smt_type T) v) hPush
      (__eo_to_smt_exists xs (SmtTerm.not body)) hTailTy).symm

private theorem smtx_model_eval_smtForall_or_left_invariant
    (M : SmtModel) (hM : model_wf M)
    {xs : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv xs vars)
    (hWF :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (A B : SmtTerm)
    (hATy : __smtx_typeof A = SmtType.Bool)
    (hBTy : __smtx_typeof B = SmtType.Bool)
    (hAInv :
      ∀ {N : SmtModel},
        model_wf N ->
        model_agrees_except_on_env (vars.map EoVarKey.toSmt) [] N M ->
          __smtx_model_eval N A = __smtx_model_eval M A) :
    __smtx_model_eval M (smtForall xs (SmtTerm.or A B)) =
      __smtx_model_eval M (SmtTerm.or A (smtForall xs B)) := by
  have hForallBTy :
      __smtx_typeof (smtForall xs B) = SmtType.Bool :=
    smtx_typeof_smtForall_bool_of_env hEnv hWF hBTy
  rcases smt_model_eval_bool_is_boolean M hM A hATy with ⟨a, hAEval⟩
  rcases smt_model_eval_bool_is_boolean M hM (smtForall xs B)
      hForallBTy with ⟨bForall, hForallBEval⟩
  cases a with
  | false =>
      have hLeftEq :
          __smtx_model_eval M (smtForall xs (SmtTerm.or A B)) =
            __smtx_model_eval M (smtForall xs B) := by
        apply smt_model_eval_smtForall_eq_of_body_eval_eq_same_mapped_typed
          hEnv hWF (by intro key hMem; exact hMem) hM
          (model_agrees_except_on_env_refl (vars.map EoVarKey.toSmt) [] M)
        intro M' hM' hAgree'
        have hA' : __smtx_model_eval M' A = SmtValue.Boolean false := by
          rw [hAInv hM' hAgree', hAEval]
        rcases smt_model_eval_bool_is_boolean M' hM' B hBTy with
          ⟨b, hBEval⟩
        cases b <;>
          simp [__smtx_model_eval, hA', hBEval, __smtx_model_eval_or,
            SmtEval.native_or]
      rw [hLeftEq]
      rw [smtx_eval_or_term_eq, hAEval, hForallBEval]
      cases bForall <;> simp [__smtx_model_eval_or, SmtEval.native_or]
  | true =>
      have hLeftEq :
          __smtx_model_eval M (smtForall xs (SmtTerm.or A B)) =
            __smtx_model_eval M (smtForall xs (SmtTerm.Boolean true)) := by
        apply smt_model_eval_smtForall_eq_of_body_eval_eq_same_mapped_typed
          hEnv hWF (by intro key hMem; exact hMem) hM
          (model_agrees_except_on_env_refl (vars.map EoVarKey.toSmt) [] M)
        intro M' hM' hAgree'
        have hA' : __smtx_model_eval M' A = SmtValue.Boolean true := by
          rw [hAInv hM' hAgree', hAEval]
        rcases smt_model_eval_bool_is_boolean M' hM' B hBTy with
          ⟨b, hBEval⟩
        cases b <;>
          simp [__smtx_model_eval, hA', hBEval, __smtx_model_eval_or,
            SmtEval.native_or]
      rw [hLeftEq]
      rw [smtx_model_eval_smtForall_true_of_env hEnv M]
      rw [smtx_eval_or_term_eq, hAEval, hForallBEval]
      cases bForall <;> simp [__smtx_model_eval_or, SmtEval.native_or]

private theorem smtx_model_eval_smtForall_or_right_invariant
    (M : SmtModel) (hM : model_wf M)
    {xs : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv xs vars)
    (hWF :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (A B : SmtTerm)
    (hATy : __smtx_typeof A = SmtType.Bool)
    (hBTy : __smtx_typeof B = SmtType.Bool)
    (hBInv :
      ∀ {N : SmtModel},
        model_wf N ->
        model_agrees_except_on_env (vars.map EoVarKey.toSmt) [] N M ->
          __smtx_model_eval N B = __smtx_model_eval M B) :
    __smtx_model_eval M (smtForall xs (SmtTerm.or A B)) =
      __smtx_model_eval M (SmtTerm.or (smtForall xs A) B) := by
  have hForallATy :
      __smtx_typeof (smtForall xs A) = SmtType.Bool :=
    smtx_typeof_smtForall_bool_of_env hEnv hWF hATy
  rcases smt_model_eval_bool_is_boolean M hM B hBTy with ⟨b, hBEval⟩
  rcases smt_model_eval_bool_is_boolean M hM (smtForall xs A)
      hForallATy with ⟨aForall, hForallAEval⟩
  cases b with
  | false =>
      have hLeftEq :
          __smtx_model_eval M (smtForall xs (SmtTerm.or A B)) =
            __smtx_model_eval M (smtForall xs A) := by
        apply smt_model_eval_smtForall_eq_of_body_eval_eq_same_mapped_typed
          hEnv hWF (by intro key hMem; exact hMem) hM
          (model_agrees_except_on_env_refl (vars.map EoVarKey.toSmt) [] M)
        intro M' hM' hAgree'
        have hB' : __smtx_model_eval M' B = SmtValue.Boolean false := by
          rw [hBInv hM' hAgree', hBEval]
        rcases smt_model_eval_bool_is_boolean M' hM' A hATy with
          ⟨a, hAEval⟩
        cases a <;>
          simp [__smtx_model_eval, hAEval, hB', __smtx_model_eval_or,
            SmtEval.native_or]
      rw [hLeftEq]
      rw [smtx_eval_or_term_eq, hForallAEval, hBEval]
      cases aForall <;> simp [__smtx_model_eval_or, SmtEval.native_or]
  | true =>
      have hLeftEq :
          __smtx_model_eval M (smtForall xs (SmtTerm.or A B)) =
            __smtx_model_eval M (smtForall xs (SmtTerm.Boolean true)) := by
        apply smt_model_eval_smtForall_eq_of_body_eval_eq_same_mapped_typed
          hEnv hWF (by intro key hMem; exact hMem) hM
          (model_agrees_except_on_env_refl (vars.map EoVarKey.toSmt) [] M)
        intro M' hM' hAgree'
        have hB' : __smtx_model_eval M' B = SmtValue.Boolean true := by
          rw [hBInv hM' hAgree', hBEval]
        rcases smt_model_eval_bool_is_boolean M' hM' A hATy with
          ⟨a, hAEval⟩
        cases a <;>
          simp [__smtx_model_eval, hAEval, hB', __smtx_model_eval_or,
            SmtEval.native_or]
      rw [hLeftEq]
      rw [smtx_model_eval_smtForall_true_of_env hEnv M]
      rw [smtx_eval_or_term_eq, hForallAEval, hBEval]
      cases aForall <;> simp [__smtx_model_eval_or, SmtEval.native_or]

private theorem miniToSmt_eq_eo_to_smt_of_has_smt_translation :
    ∀ t : Term,
      RuleProofs.eo_has_smt_translation t ->
      miniToSmt t = __eo_to_smt t
  | Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B => by
      intro hTrans
      have hTy :
          __smtx_typeof (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) ≠
            SmtType.None := by
        simpa [RuleProofs.eo_has_smt_translation] using hTrans
      have hArgs :
          __smtx_typeof (__eo_to_smt A) = SmtType.Bool ∧
            __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
        rw [typeof_or_eq] at hTy
        cases hA : __smtx_typeof (__eo_to_smt A) <;>
          cases hB : __smtx_typeof (__eo_to_smt B) <;>
          simp [hA, hB, native_ite, native_Teq] at hTy ⊢
      have hATrans : RuleProofs.eo_has_smt_translation A := by
        intro hNone
        have hNoneOr :
            __smtx_typeof (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) =
              SmtType.None := by
          rw [typeof_or_eq, hNone]
          simp [native_ite, native_Teq]
        exact hTrans (by simpa using hNoneOr)
      have hBTrans : RuleProofs.eo_has_smt_translation B := by
        intro hNone
        have hNoneOr :
            __smtx_typeof (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) =
              SmtType.None := by
          rw [typeof_or_eq, hArgs.1, hNone]
          simp [native_ite, native_Teq]
        exact hTrans (by simpa using hNoneOr)
      rw [miniToSmt]
      rw [miniToSmt_eq_eo_to_smt_of_has_smt_translation A hATrans]
      rw [miniToSmt_eq_eo_to_smt_of_has_smt_translation B hBTrans]
      rfl
  | Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F => by
      intro hTrans
      have hx : xs ≠ Term.__eo_List_nil := by
        intro hxs
        subst xs
        exact hTrans (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none)
      rw [miniToSmt]
      exact (eo_to_smt_forall_eq xs F hx).symm
  | t => by
      intro hTrans
      cases t with
      | Apply f a =>
          cases f with
          | Apply g y =>
              cases g with
              | UOp op =>
                  cases op with
                  | or =>
                      have hTy :
                          __smtx_typeof
                              (SmtTerm.or (__eo_to_smt y) (__eo_to_smt a)) ≠
                            SmtType.None := by
                        simpa [RuleProofs.eo_has_smt_translation] using hTrans
                      have hArgs :
                          __smtx_typeof (__eo_to_smt y) = SmtType.Bool ∧
                            __smtx_typeof (__eo_to_smt a) = SmtType.Bool := by
                        rw [typeof_or_eq] at hTy
                        cases hY : __smtx_typeof (__eo_to_smt y) <;>
                          cases hA : __smtx_typeof (__eo_to_smt a) <;>
                          simp [hY, hA, native_ite, native_Teq] at hTy ⊢
                      have hYTrans : RuleProofs.eo_has_smt_translation y := by
                        intro hNone
                        apply hTrans
                        rw [show
                            __eo_to_smt (((Term.UOp UserOp.or).Apply y).Apply a) =
                              SmtTerm.or (__eo_to_smt y) (__eo_to_smt a) by rfl]
                        rw [typeof_or_eq, hNone]
                        simp [native_ite, native_Teq]
                      have hATrans : RuleProofs.eo_has_smt_translation a := by
                        intro hNone
                        apply hTrans
                        rw [show
                            __eo_to_smt (((Term.UOp UserOp.or).Apply y).Apply a) =
                              SmtTerm.or (__eo_to_smt y) (__eo_to_smt a) by rfl]
                        rw [typeof_or_eq, hArgs.1, hNone]
                        simp [native_ite, native_Teq]
                      rw [miniToSmt]
                      rw [miniToSmt_eq_eo_to_smt_of_has_smt_translation y hYTrans]
                      rw [miniToSmt_eq_eo_to_smt_of_has_smt_translation a hATrans]
                      rfl
                  | «forall» =>
                      have hx : y ≠ Term.__eo_List_nil := by
                        intro hy
                        subst y
                        exact hTrans (by
                          change __smtx_typeof SmtTerm.None = SmtType.None
                          exact TranslationProofs.smtx_typeof_none)
                      rw [miniToSmt]
                      exact (eo_to_smt_forall_eq y a hx).symm
                  | _ =>
                      rfl
              | _ =>
                  rfl
          | _ =>
              rfl
      | _ =>
          rfl
termination_by t => sizeOf t

private theorem miniToSmt_fallback_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
    {t except : Term} {exceptVars : List EoVarKey}
    {M N : SmtModel}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hEq : miniToSmt t = __eo_to_smt t)
    (hTy : __smtx_typeof (miniToSmt t) = SmtType.Bool)
    (hNoFree :
      __contains_atomic_term_list_free_rec t except Term.__eo_List_nil =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) [] M N) :
    __smtx_model_eval M (miniToSmt t) =
      __smtx_model_eval N (miniToSmt t) := by
  have hEoTy :
      __smtx_typeof (__eo_to_smt t) = SmtType.Bool := by
    simpa [hEq] using hTy
  have hTrans : eoHasSmtTranslation t := by
    intro hNone
    rw [hNone] at hEoTy
    cases hEoTy
  rw [hEq]
  exact
    smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
      hExcept (EoVarEnvPerm.of_exact EoVarEnv.nil)
      hTrans hNoFree hAgree

private theorem miniToSmt_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped_lt
    (n : Nat) {t except : Term} {exceptVars : List EoVarKey}
    {M N : SmtModel}
    (hLt : sizeOf t < n)
    (hM : model_wf M)
    (hN : model_wf N)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hTy : __smtx_typeof (miniToSmt t) = SmtType.Bool)
    (hNoFree :
      __contains_atomic_term_list_free_rec t except Term.__eo_List_nil =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) [] M N) :
    __smtx_model_eval M (miniToSmt t) =
      __smtx_model_eval N (miniToSmt t) := by
  cases n with
  | zero =>
      omega
  | succ n =>
      let hRec :
          ∀ {u except' : Term} {exceptVars' : List EoVarKey}
            {M' N' : SmtModel},
            sizeOf u < sizeOf t ->
              model_wf M' ->
              model_wf N' ->
              EoVarEnvPerm except' exceptVars' ->
              __smtx_typeof (miniToSmt u) = SmtType.Bool ->
              __contains_atomic_term_list_free_rec u except'
                  Term.__eo_List_nil =
                Term.Boolean false ->
              model_agrees_except_on_env
                (exceptVars'.map EoVarKey.toSmt) [] M' N' ->
              __smtx_model_eval M' (miniToSmt u) =
                __smtx_model_eval N' (miniToSmt u) :=
        fun {u except'} {exceptVars'} {M' N'} hULt hM' hN'
            hExcept' hTy' hNoFree' hAgree' =>
          miniToSmt_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped_lt
            n (t := u) (except := except') (exceptVars := exceptVars')
            (M := M') (N := N') (by omega)
            hM' hN' hExcept' hTy' hNoFree' hAgree'
      cases t
      case Apply f a =>
        cases f
        case Apply g y =>
          cases g
          case UOp op =>
            cases op
            case or =>
              have hOrTy :
                  __smtx_typeof (SmtTerm.or (miniToSmt y) (miniToSmt a)) =
                    SmtType.Bool := by
                simpa [miniToSmt] using hTy
              rcases smtx_typeof_or_args_of_bool
                  (miniToSmt y) (miniToSmt a) hOrTy with
                ⟨hYTy, hATy⟩
              have hYNotList :
                  ∀ v vs,
                    y ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs := by
                intro v vs hy
                subst y
                have hRawTy :
                    __smtx_typeof
                        (__eo_to_smt
                          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) =
                      SmtType.Bool := by
                  simpa [miniToSmt] using hYTy
                rw [smtx_typeof_eo_list_cons_eq_none v vs] at hRawTy
                cases hRawTy
              rcases
                contains_atomic_term_list_free_rec_apply_apply_uop_false_args
                  hExcept (EoVarEnvPerm.of_exact EoVarEnv.nil)
                  hYNotList hNoFree with
                ⟨hYNoFree, hANoFree⟩
              have hYEval :
                  __smtx_model_eval M (miniToSmt y) =
                    __smtx_model_eval N (miniToSmt y) :=
                hRec (u := y) (except' := except)
                  (exceptVars' := exceptVars) (M' := M) (N' := N)
                  (by simp; omega) hM hN hExcept hYTy hYNoFree hAgree
              have hAEval :
                  __smtx_model_eval M (miniToSmt a) =
                    __smtx_model_eval N (miniToSmt a) :=
                hRec (u := a) (except' := except)
                  (exceptVars' := exceptVars) (M' := M) (N' := N)
                  (by simp; omega) hM hN hExcept hATy hANoFree hAgree
              change
                __smtx_model_eval M (SmtTerm.or (miniToSmt y) (miniToSmt a)) =
                  __smtx_model_eval N
                    (SmtTerm.or (miniToSmt y) (miniToSmt a))
              exact smtx_model_eval_or_eq_of_eval_eq hYEval hAEval
            case «forall» =>
              have hForallTy :
                  __smtx_typeof (smtForall y (__eo_to_smt a)) =
                    SmtType.Bool := by
                simpa [miniToSmt] using hTy
              by_cases hyNil : y = Term.__eo_List_nil
              · subst y
                have hBodyTy :
                    __smtx_typeof (__eo_to_smt a) = SmtType.Bool :=
                  smtx_typeof_smtForall_body_of_bool
                    Term.__eo_List_nil (__eo_to_smt a) hForallTy
                rcases
                  contains_atomic_term_list_free_rec_apply_apply_uop_false_args
                    hExcept (EoVarEnvPerm.of_exact EoVarEnv.nil)
                    (by intro v vs h; cases h) hNoFree with
                  ⟨_hNilNoFree, hBodyNoFree⟩
                have hBodyTrans : eoHasSmtTranslation a := by
                  intro hNone
                  rw [hNone] at hBodyTy
                  cases hBodyTy
                have hBodyEval :
                    __smtx_model_eval M (__eo_to_smt a) =
                      __smtx_model_eval N (__eo_to_smt a) :=
                  smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
                    hExcept (EoVarEnvPerm.of_exact EoVarEnv.nil)
                    hBodyTrans hBodyNoFree hAgree
                have hNilM :
                    __smtx_model_eval M
                        (smtForall Term.__eo_List_nil (__eo_to_smt a)) =
                      __smtx_model_eval M (__eo_to_smt a) :=
                  smtx_model_eval_smtForall_nil_eq_body M hM
                    (__eo_to_smt a) hBodyTy
                have hNilN :
                    __smtx_model_eval N
                        (smtForall Term.__eo_List_nil (__eo_to_smt a)) =
                      __smtx_model_eval N (__eo_to_smt a) :=
                  smtx_model_eval_smtForall_nil_eq_body N hN
                    (__eo_to_smt a) hBodyTy
                change
                  __smtx_model_eval M
                      (smtForall Term.__eo_List_nil (__eo_to_smt a)) =
                    __smtx_model_eval N
                      (smtForall Term.__eo_List_nil (__eo_to_smt a))
                rw [hNilM, hNilN]
                exact hBodyEval
              · have hMiniEq :
                    miniToSmt
                        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) y)
                          a) =
                      __eo_to_smt
                        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) y)
                          a) := by
                  change
                    smtForall y (__eo_to_smt a) =
                      __eo_to_smt
                        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) y)
                          a)
                  exact (eo_to_smt_forall_eq y a hyNil).symm
                exact
                  miniToSmt_fallback_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
                    hExcept hMiniEq hTy hNoFree hAgree
            all_goals
              exact
                miniToSmt_fallback_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
                  hExcept rfl hTy hNoFree hAgree
          all_goals
            exact
              miniToSmt_fallback_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
                hExcept rfl hTy hNoFree hAgree
        all_goals
          exact
            miniToSmt_fallback_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
              hExcept rfl hTy hNoFree hAgree
      all_goals
        exact
          miniToSmt_fallback_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
            hExcept rfl hTy hNoFree hAgree
termination_by n
decreasing_by
  all_goals omega

private theorem miniToSmt_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
    {t except : Term} {exceptVars : List EoVarKey}
    {M N : SmtModel}
    (hM : model_wf M)
    (hN : model_wf N)
    (hExcept : EoVarEnvPerm except exceptVars)
    (hTy : __smtx_typeof (miniToSmt t) = SmtType.Bool)
    (hNoFree :
      __contains_atomic_term_list_free_rec t except Term.__eo_List_nil =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_env
        (exceptVars.map EoVarKey.toSmt) [] M N) :
    __smtx_model_eval M (miniToSmt t) =
      __smtx_model_eval N (miniToSmt t) :=
  miniToSmt_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped_lt
    (sizeOf t + 1) (by omega) hM hN hExcept hTy hNoFree hAgree

private theorem eo_requires_arg_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> x = y := by
  intro h
  unfold __eo_requires at h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [hxy, native_ite] at h

private theorem eo_requires_result_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> __eo_requires x y z = z := by
  intro h
  unfold __eo_requires at h ⊢
  by_cases hxy : native_teq x y = true
  · by_cases hx : native_teq x Term.Stuck = true
    · simp [hxy, hx, native_ite, SmtEval.native_not] at h
    · simp [hxy, hx, native_ite, SmtEval.native_not]
  · simp [hxy, native_ite] at h

private theorem eo_ite_eq_true_cases (c t e : Term) :
    __eo_ite c t e = Term.Boolean true ->
    (c = Term.Boolean true ∧ t = Term.Boolean true) ∨
      (c = Term.Boolean false ∧ e = Term.Boolean true) := by
  intro h
  cases c <;> simp [__eo_ite, native_teq, native_ite] at h
  case Boolean b =>
    cases b <;> simp at h
    · exact Or.inr ⟨rfl, h⟩
    · exact Or.inl ⟨rfl, h⟩

private theorem eo_eq_true_eq
    {a b : Term}
    (hEq : __eo_eq a b = Term.Boolean true) :
  a = b := by
  have hEqSymm : b = a := by
    cases a <;> cases b <;> simp [__eo_eq, native_teq] at hEq ⊢
    all_goals exact hEq
  exact hEqSymm.symm

private inductive MiniOr : Term -> Term -> Term -> Prop where
  | base :
      MiniOr Term.__eo_List_nil (Term.Boolean false) (Term.Boolean false)
  | keep
      {x f fs gs : Term}
      (hNoFree :
        __contains_atomic_term_list_free_rec f x Term.__eo_List_nil =
          Term.Boolean false)
      (hTail : MiniOr x fs gs) :
      MiniOr x (qor f fs) (qor f gs)
  | keepNil
      {x f fs gs : Term}
      (hNoFree :
        __contains_atomic_term_list_free_rec f x Term.__eo_List_nil =
          Term.Boolean false)
      (hTail : MiniOr x fs gs) :
      MiniOr x (qor f fs) (qor (qforall Term.__eo_List_nil f) gs)
  | peel
      {x xs f fs ys gs : Term}
      (hNoFree :
        __contains_atomic_term_list_free_rec gs
            (qcons x Term.__eo_List_nil) Term.__eo_List_nil =
          Term.Boolean false)
      (hTail :
        MiniOr xs (qor f fs) (qor (qforall ys f) gs)) :
      MiniOr (qcons x xs) (qor f fs) (qor (qforall (qcons x ys) f) gs)

private theorem mini_or_of_l3_true
    (x F G : Term) :
    __eo_l_3___is_quant_miniscope_or x F G = Term.Boolean true ->
      MiniOr x F G := by
  intro h
  rw [__eo_l_3___is_quant_miniscope_or.eq_def] at h
  split at h <;> simp at h
  exact MiniOr.base

private theorem mini_or_of_is_true
    (x F G : Term) :
    __is_quant_miniscope_or x F G = Term.Boolean true ->
      MiniOr x F G := by
  refine
    __is_quant_miniscope_or.induct
      (motive1 := fun x F G =>
        __eo_l_2___is_quant_miniscope_or x F G = Term.Boolean true ->
          MiniOr x F G)
      (motive2 := fun x F G =>
        __is_quant_miniscope_or x F G = Term.Boolean true ->
          MiniOr x F G)
      (motive3 := fun x F G =>
        __eo_l_1___is_quant_miniscope_or x F G = Term.Boolean true ->
          MiniOr x F G)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ x F G
  · intro _ _
    intro h
    rw [__eo_l_2___is_quant_miniscope_or.eq_def] at h
    simp at h
  · intro _ _ _hNe
    intro h
    rw [__eo_l_2___is_quant_miniscope_or.eq_def] at h
    simp at h
  · intro _ _ _hNe _hNe'
    intro h
    rw [__eo_l_2___is_quant_miniscope_or.eq_def] at h
    simp at h
  · intro x xs f fs x2 ys g gs _tailOr ih
    intro h
    have hIte :
        __eo_ite
          (__eo_and (__eo_eq x x2) (__eo_eq f g))
          (__eo_requires
            (__contains_atomic_term_list_free_rec gs
              (qcons x Term.__eo_List_nil) Term.__eo_List_nil)
            (Term.Boolean false)
            (__is_quant_miniscope_or xs (qor f fs)
              (qor (qforall ys f) gs)))
          (__eo_l_3___is_quant_miniscope_or
            (qcons x xs) (qor f fs)
            (qor (qforall (qcons x2 ys) g) gs)) =
            Term.Boolean true := by
      rw [__eo_l_2___is_quant_miniscope_or.eq_def] at h
      simpa [qcons, qor, qforall] using h
    rcases eo_ite_eq_true_cases
        (__eo_and (__eo_eq x x2) (__eo_eq f g))
        (__eo_requires
          (__contains_atomic_term_list_free_rec gs
            (qcons x Term.__eo_List_nil) Term.__eo_List_nil)
          (Term.Boolean false)
          (__is_quant_miniscope_or xs (qor f fs)
            (qor (qforall ys f) gs)))
        (__eo_l_3___is_quant_miniscope_or
          (qcons x xs) (qor f fs)
          (qor (qforall (qcons x2 ys) g) gs))
        hIte with
      hThen | hElse
    · have hParts := eo_and_eq_true_cases hThen.1
      have hxEq : x = x2 := eo_eq_true_eq hParts.1
      have hfEq : f = g := eo_eq_true_eq hParts.2
      subst x2
      subst g
      have hReqNe :
          __eo_requires
            (__contains_atomic_term_list_free_rec gs
              (qcons x Term.__eo_List_nil) Term.__eo_List_nil)
            (Term.Boolean false)
            (__is_quant_miniscope_or xs (qor f fs)
              (qor (qforall ys f) gs)) ≠ Term.Stuck := by
        rw [hThen.2]
        simp
      have hNoFree :
          __contains_atomic_term_list_free_rec gs
              (qcons x Term.__eo_List_nil) Term.__eo_List_nil =
            Term.Boolean false :=
        eo_requires_arg_eq_of_ne_stuck hReqNe
      have hTailGuard :
          __is_quant_miniscope_or xs (qor f fs)
              (qor (qforall ys f) gs) =
            Term.Boolean true := by
        have hReqEq := eo_requires_result_eq_of_ne_stuck hReqNe
        simpa [hThen.2] using hReqEq.symm
      exact MiniOr.peel hNoFree (ih hTailGuard)
    · exact mini_or_of_l3_true (qcons x xs) (qor f fs)
        (qor (qforall (qcons x2 ys) g) gs)
        (by simpa [qcons, qor, qforall] using hElse.2)
  · intro dv1 dv2 dv3 hNe1 hNe2 hNe3 hNoShape
    intro h
    have hL3 :
        __eo_l_3___is_quant_miniscope_or dv1 dv2 dv3 =
          Term.Boolean true := by
      rw [__eo_l_2___is_quant_miniscope_or.eq_def] at h
      split at h <;> try simp at h
      · exact False.elim (hNoShape _ _ _ _ _ _ _ _ rfl rfl rfl)
      · exact h
    exact mini_or_of_l3_true dv1 dv2 dv3 hL3
  · intro _ _
    intro h
    rw [__is_quant_miniscope_or.eq_def] at h
    simp at h
  · intro _ _ _hNe
    intro h
    rw [__is_quant_miniscope_or.eq_def] at h
    simp at h
  · intro _ _ _hNe _hNe'
    intro h
    rw [__is_quant_miniscope_or.eq_def] at h
    simp at h
  · intro x f fs g gs _hNe ihTail ihL1
    intro h
    have hIte :
        __eo_ite (__eo_eq f g)
          (__eo_requires
            (__contains_atomic_term_list_free_rec f x Term.__eo_List_nil)
            (Term.Boolean false)
            (__is_quant_miniscope_or x fs gs))
          (__eo_l_1___is_quant_miniscope_or x (qor f fs) (qor g gs)) =
          Term.Boolean true := by
      rw [__is_quant_miniscope_or.eq_def] at h
      simpa [qor] using h
    rcases eo_ite_eq_true_cases (__eo_eq f g)
        (__eo_requires
          (__contains_atomic_term_list_free_rec f x Term.__eo_List_nil)
          (Term.Boolean false)
          (__is_quant_miniscope_or x fs gs))
        (__eo_l_1___is_quant_miniscope_or x (qor f fs) (qor g gs))
        hIte with
      hThen | hElse
    · have hfg : f = g := eo_eq_true_eq hThen.1
      subst g
      have hReqNe :
          __eo_requires
            (__contains_atomic_term_list_free_rec f x Term.__eo_List_nil)
            (Term.Boolean false)
            (__is_quant_miniscope_or x fs gs) ≠ Term.Stuck := by
        rw [hThen.2]
        simp
      have hNoFree :
          __contains_atomic_term_list_free_rec f x Term.__eo_List_nil =
            Term.Boolean false :=
        eo_requires_arg_eq_of_ne_stuck hReqNe
      have hTailGuard :
          __is_quant_miniscope_or x fs gs = Term.Boolean true := by
        have hReqEq := eo_requires_result_eq_of_ne_stuck hReqNe
        simpa [hThen.2] using hReqEq.symm
      exact MiniOr.keep hNoFree (ihTail hTailGuard)
    · exact ihL1 (by simpa [qor] using hElse.2)
  · intro dv1 dv2 dv3 hNe1 hNe2 hNe3 hNoShape ihL1
    intro h
    have hL1 :
        __eo_l_1___is_quant_miniscope_or dv1 dv2 dv3 =
          Term.Boolean true := by
      rw [__is_quant_miniscope_or.eq_def] at h
      split at h <;> try simp at h
      · exact False.elim (hNoShape _ _ _ _ rfl rfl)
      · exact h
    exact ihL1 hL1
  · intro _ _
    intro h
    rw [__eo_l_1___is_quant_miniscope_or.eq_def] at h
    simp at h
  · intro _ _ _hNe
    intro h
    rw [__eo_l_1___is_quant_miniscope_or.eq_def] at h
    simp at h
  · intro _ _ _hNe _hNe'
    intro h
    rw [__eo_l_1___is_quant_miniscope_or.eq_def] at h
    simp at h
  · intro x f fs g gs _hNe ihTail ihL2
    intro h
    have hIte :
        __eo_ite (__eo_eq f g)
          (__eo_requires
            (__contains_atomic_term_list_free_rec f x Term.__eo_List_nil)
            (Term.Boolean false)
            (__is_quant_miniscope_or x fs gs))
          (__eo_l_2___is_quant_miniscope_or x
            (qor f fs) (qor (qforall Term.__eo_List_nil g) gs)) =
          Term.Boolean true := by
      rw [__eo_l_1___is_quant_miniscope_or.eq_def] at h
      simpa [qor, qforall] using h
    rcases eo_ite_eq_true_cases (__eo_eq f g)
        (__eo_requires
          (__contains_atomic_term_list_free_rec f x Term.__eo_List_nil)
          (Term.Boolean false)
          (__is_quant_miniscope_or x fs gs))
        (__eo_l_2___is_quant_miniscope_or x
          (qor f fs) (qor (qforall Term.__eo_List_nil g) gs))
        hIte with
      hThen | hElse
    · have hfg : f = g := eo_eq_true_eq hThen.1
      subst g
      have hReqNe :
          __eo_requires
            (__contains_atomic_term_list_free_rec f x Term.__eo_List_nil)
            (Term.Boolean false)
            (__is_quant_miniscope_or x fs gs) ≠ Term.Stuck := by
        rw [hThen.2]
        simp
      have hNoFree :
          __contains_atomic_term_list_free_rec f x Term.__eo_List_nil =
            Term.Boolean false :=
        eo_requires_arg_eq_of_ne_stuck hReqNe
      have hTailGuard :
          __is_quant_miniscope_or x fs gs = Term.Boolean true := by
        have hReqEq := eo_requires_result_eq_of_ne_stuck hReqNe
        simpa [hThen.2] using hReqEq.symm
      exact MiniOr.keepNil hNoFree (ihTail hTailGuard)
    · exact ihL2 (by simpa [qor, qforall] using hElse.2)
  · intro dv1 dv2 dv3 hNe1 hNe2 hNe3 hNoShape ihL2
    intro h
    have hL2 :
        __eo_l_2___is_quant_miniscope_or dv1 dv2 dv3 =
          Term.Boolean true := by
      rw [__eo_l_1___is_quant_miniscope_or.eq_def] at h
      split at h <;> try simp at h
      · exact False.elim (hNoShape _ _ _ _ rfl rfl)
      · exact h
    exact ihL2 hL2

private theorem mini_or_eval_eq
    (M : SmtModel) (hM : model_wf M)
    (hMiniInv :
      ∀ {t except : Term} {exceptVars : List EoVarKey}
        {M N : SmtModel},
        model_wf M ->
        model_wf N ->
        EoVarEnvPerm except exceptVars ->
        __smtx_typeof (miniToSmt t) = SmtType.Bool ->
        __contains_atomic_term_list_free_rec t except Term.__eo_List_nil =
          Term.Boolean false ->
        model_agrees_except_on_env
          (exceptVars.map EoVarKey.toSmt) [] M N ->
        __smtx_model_eval M (miniToSmt t) =
          __smtx_model_eval N (miniToSmt t))
    {x F G : Term} {vars : List EoVarKey}
    (hRel : MiniOr x F G)
    (hEnv : EoVarEnv x vars)
    (hWF :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hLeftTy :
      __smtx_typeof (smtForall x (__eo_to_smt F)) = SmtType.Bool)
    (hRightTy :
      __smtx_typeof (miniToSmt G) = SmtType.Bool) :
    __smtx_model_eval M (smtForall x (__eo_to_smt F)) =
      __smtx_model_eval M (miniToSmt G) := by
  induction hRel generalizing M vars with
  | base =>
      simp [smtForall, miniToSmt, __eo_to_smt_exists,
        __smtx_model_eval, __smtx_model_eval_not, SmtEval.native_not]
  | keep hNoFree hTail ih =>
      rename_i x f fs gs
      have hBodyTy :
          __smtx_typeof
              (SmtTerm.or (__eo_to_smt f) (__eo_to_smt fs)) =
            SmtType.Bool :=
        smtx_typeof_smtForall_body_of_bool x
          (SmtTerm.or (__eo_to_smt f) (__eo_to_smt fs))
          (by simpa [eo_to_smt_or_eq, qor] using hLeftTy)
      rcases smtx_typeof_or_args_of_bool
          (__eo_to_smt f) (__eo_to_smt fs) hBodyTy with
        ⟨hFTy, hFsTy⟩
      have hRightArgs :
          __smtx_typeof (miniToSmt f) = SmtType.Bool ∧
            __smtx_typeof (miniToSmt gs) = SmtType.Bool :=
        smtx_typeof_or_args_of_bool (miniToSmt f) (miniToSmt gs)
          (by simpa [miniToSmt, qor] using hRightTy)
      have hFTrans :
          RuleProofs.eo_has_smt_translation f :=
        RuleProofs.eo_has_smt_translation_of_has_bool_type f hFTy
      have hMiniF :
          miniToSmt f = __eo_to_smt f :=
        miniToSmt_eq_eo_to_smt_of_has_smt_translation f hFTrans
      have hGsTy :
          __smtx_typeof (miniToSmt gs) = SmtType.Bool :=
        hRightArgs.2
      have hTailLeftTy :
          __smtx_typeof (smtForall x (__eo_to_smt fs)) =
            SmtType.Bool :=
        smtx_typeof_smtForall_bool_of_env hEnv hWF hFsTy
      have hTailEval :
          __smtx_model_eval M (smtForall x (__eo_to_smt fs)) =
            __smtx_model_eval M (miniToSmt gs) :=
        ih M hM hEnv hWF hTailLeftTy hGsTy
      have hInv :
          ∀ {N : SmtModel},
            model_wf N ->
            model_agrees_except_on_env (vars.map EoVarKey.toSmt) [] N M ->
              __smtx_model_eval N (__eo_to_smt f) =
                __smtx_model_eval M (__eo_to_smt f) := by
        intro N _hN hAgree
        exact
          smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
            (EoVarEnvPerm.of_exact hEnv)
            (EoVarEnvPerm.of_exact EoVarEnv.nil)
            hFTrans hNoFree hAgree
      have hDist :
          __smtx_model_eval M
              (smtForall x
                (SmtTerm.or (__eo_to_smt f) (__eo_to_smt fs))) =
            __smtx_model_eval M
              (SmtTerm.or (__eo_to_smt f)
                (smtForall x (__eo_to_smt fs))) :=
        smtx_model_eval_smtForall_or_left_invariant
          M hM hEnv hWF (__eo_to_smt f) (__eo_to_smt fs)
          hFTy hFsTy hInv
      rw [show
          smtForall x (__eo_to_smt (qor f fs)) =
            smtForall x
              (SmtTerm.or (__eo_to_smt f) (__eo_to_smt fs)) by
            rw [eo_to_smt_or_eq]]
      rw [hDist]
      change
        __smtx_model_eval M
            (SmtTerm.or (__eo_to_smt f) (smtForall x (__eo_to_smt fs))) =
          __smtx_model_eval M (SmtTerm.or (miniToSmt f) (miniToSmt gs))
      rw [hMiniF]
      exact smtx_model_eval_or_eq_of_args_eq_same rfl hTailEval
  | keepNil hNoFree hTail ih =>
      rename_i x f fs gs
      have hBodyTy :
          __smtx_typeof
              (SmtTerm.or (__eo_to_smt f) (__eo_to_smt fs)) =
            SmtType.Bool :=
        smtx_typeof_smtForall_body_of_bool x
          (SmtTerm.or (__eo_to_smt f) (__eo_to_smt fs))
          (by simpa [eo_to_smt_or_eq, qor] using hLeftTy)
      rcases smtx_typeof_or_args_of_bool
          (__eo_to_smt f) (__eo_to_smt fs) hBodyTy with
        ⟨hFTy, hFsTy⟩
      have hRightArgs :
          __smtx_typeof (smtForall Term.__eo_List_nil (__eo_to_smt f)) =
              SmtType.Bool ∧
            __smtx_typeof (miniToSmt gs) = SmtType.Bool :=
        smtx_typeof_or_args_of_bool
          (smtForall Term.__eo_List_nil (__eo_to_smt f))
          (miniToSmt gs)
          (by simpa [miniToSmt, qforall, qor] using hRightTy)
      have hFTrans :
          RuleProofs.eo_has_smt_translation f :=
        RuleProofs.eo_has_smt_translation_of_has_bool_type f hFTy
      have hGsTy :
          __smtx_typeof (miniToSmt gs) = SmtType.Bool :=
        hRightArgs.2
      have hTailLeftTy :
          __smtx_typeof (smtForall x (__eo_to_smt fs)) =
            SmtType.Bool :=
        smtx_typeof_smtForall_bool_of_env hEnv hWF hFsTy
      have hTailEval :
          __smtx_model_eval M (smtForall x (__eo_to_smt fs)) =
            __smtx_model_eval M (miniToSmt gs) :=
        ih M hM hEnv hWF hTailLeftTy hGsTy
      have hInv :
          ∀ {N : SmtModel},
            model_wf N ->
            model_agrees_except_on_env (vars.map EoVarKey.toSmt) [] N M ->
              __smtx_model_eval N (__eo_to_smt f) =
                __smtx_model_eval M (__eo_to_smt f) := by
        intro N _hN hAgree
        exact
          smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
            (EoVarEnvPerm.of_exact hEnv)
            (EoVarEnvPerm.of_exact EoVarEnv.nil)
            hFTrans hNoFree hAgree
      have hDist :
          __smtx_model_eval M
              (smtForall x
                (SmtTerm.or (__eo_to_smt f) (__eo_to_smt fs))) =
            __smtx_model_eval M
              (SmtTerm.or (__eo_to_smt f)
                (smtForall x (__eo_to_smt fs))) :=
        smtx_model_eval_smtForall_or_left_invariant
          M hM hEnv hWF (__eo_to_smt f) (__eo_to_smt fs)
          hFTy hFsTy hInv
      have hNil :
          __smtx_model_eval M
              (smtForall Term.__eo_List_nil (__eo_to_smt f)) =
            __smtx_model_eval M (__eo_to_smt f) :=
        smtx_model_eval_smtForall_nil_eq_body M hM
          (__eo_to_smt f) hFTy
      rw [show
          smtForall x (__eo_to_smt (qor f fs)) =
            smtForall x
              (SmtTerm.or (__eo_to_smt f) (__eo_to_smt fs)) by
            rw [eo_to_smt_or_eq]]
      rw [hDist]
      change
        __smtx_model_eval M
            (SmtTerm.or (__eo_to_smt f) (smtForall x (__eo_to_smt fs))) =
          __smtx_model_eval M
            (SmtTerm.or (smtForall Term.__eo_List_nil (__eo_to_smt f))
              (miniToSmt gs))
      exact smtx_model_eval_or_eq_of_args_eq_same hNil.symm hTailEval
  | peel hNoFree hTail ih =>
      rename_i x xs f fs ys gs
      cases hEnv with
      | cons hXsEnv =>
          rename_i s T envVars
          have hHeadWF :
              __smtx_type_wf (__eo_to_smt_type T) = true :=
            hWF s T (by simp)
          have hXsWF :
              ∀ s' T', (s', T') ∈ envVars ->
                __smtx_type_wf (__eo_to_smt_type T') = true := by
            intro s' T' hMem
            exact hWF s' T' (by simp [hMem])
          have hBodyTy :
              __smtx_typeof
                  (SmtTerm.or (__eo_to_smt f) (__eo_to_smt fs)) =
                SmtType.Bool :=
            smtx_typeof_smtForall_body_of_bool
              (qcons (Term.Var (Term.String s) T) xs)
              (SmtTerm.or (__eo_to_smt f) (__eo_to_smt fs))
              (by simpa [qcons, eo_to_smt_or_eq, qor] using hLeftTy)
          rcases smtx_typeof_or_args_of_bool
              (__eo_to_smt f) (__eo_to_smt fs) hBodyTy with
            ⟨hFTy, hFsTy⟩
          have hNotBodyTy :
              __smtx_typeof
                  (SmtTerm.not
                    (SmtTerm.or (__eo_to_smt f) (__eo_to_smt fs))) =
                SmtType.Bool :=
            smtx_typeof_not_bool_of_arg_bool
              (SmtTerm.or (__eo_to_smt f) (__eo_to_smt fs)) hBodyTy
          have hXsExistsTy :
              __smtx_typeof
                  (__eo_to_smt_exists xs
                    (SmtTerm.not
                      (SmtTerm.or (__eo_to_smt f) (__eo_to_smt fs)))) =
                SmtType.Bool :=
            smtx_typeof_eo_to_smt_exists_bool_of_env hXsEnv hXsWF
              hNotBodyTy
          have hLeftSplit :
              __smtx_model_eval M
                  (smtForall
                    (qcons (Term.Var (Term.String s) T) xs)
                    (SmtTerm.or (__eo_to_smt f) (__eo_to_smt fs))) =
                __smtx_model_eval M
                  (smtForall
                    (qcons (Term.Var (Term.String s) T) Term.__eo_List_nil)
                    (smtForall xs
                      (SmtTerm.or (__eo_to_smt f) (__eo_to_smt fs)))) :=
            smtx_model_eval_smtForall_cons_split M hM s T xs
              (SmtTerm.or (__eo_to_smt f) (__eo_to_smt fs))
              hHeadWF hXsExistsTy
          have hTailLeftTy :
              __smtx_typeof
                  (smtForall xs
                    (SmtTerm.or (__eo_to_smt f) (__eo_to_smt fs))) =
                SmtType.Bool :=
            smtx_typeof_smtForall_bool_of_env hXsEnv hXsWF hBodyTy
          have hRightArgs :
              __smtx_typeof (smtForall (qcons (Term.Var (Term.String s) T) ys)
                    (__eo_to_smt f)) = SmtType.Bool ∧
                __smtx_typeof (miniToSmt gs) = SmtType.Bool :=
            smtx_typeof_or_args_of_bool
              (smtForall (qcons (Term.Var (Term.String s) T) ys)
                (__eo_to_smt f))
              (miniToSmt gs)
              (by simpa [qcons, miniToSmt, qforall, qor] using hRightTy)
          have hConsYsTy :
              __smtx_typeof
                (smtForall (qcons (Term.Var (Term.String s) T) ys)
                  (__eo_to_smt f)) = SmtType.Bool :=
            hRightArgs.1
          have hGsTy :
              __smtx_typeof (miniToSmt gs) = SmtType.Bool :=
            hRightArgs.2
          have hYsExistsTy :
              __smtx_typeof
                  (__eo_to_smt_exists ys
                    (SmtTerm.not (__eo_to_smt f))) =
                SmtType.Bool := by
            have hConsExists :
                __smtx_typeof
                    (__eo_to_smt_exists
                      (qcons (Term.Var (Term.String s) T) ys)
                      (SmtTerm.not (__eo_to_smt f))) =
                  SmtType.Bool := by
              unfold smtForall at hConsYsTy
              exact smtx_typeof_not_arg_of_bool
                (__eo_to_smt_exists
                  (qcons (Term.Var (Term.String s) T) ys)
                  (SmtTerm.not (__eo_to_smt f))) hConsYsTy
            simpa [qcons] using
              smtx_typeof_exists_tail_bool_of_cons_bool
                s T ys (SmtTerm.not (__eo_to_smt f)) hConsExists
          have hYsForallTy :
              __smtx_typeof (smtForall ys (__eo_to_smt f)) =
                SmtType.Bool := by
            unfold smtForall
            exact smtx_typeof_not_bool_of_arg_bool
              (__eo_to_smt_exists ys (SmtTerm.not (__eo_to_smt f)))
              hYsExistsTy
          have hTailRightTy :
              __smtx_typeof
                  (miniToSmt (qor (qforall ys f) gs)) =
                SmtType.Bool := by
            change
              __smtx_typeof
                (SmtTerm.or (smtForall ys (__eo_to_smt f))
                  (miniToSmt gs)) =
              SmtType.Bool
            exact smtx_typeof_or_bool_of_args
              (smtForall ys (__eo_to_smt f)) (miniToSmt gs)
              hYsForallTy hGsTy
          have hTailEval :
              __smtx_model_eval M
                  (smtForall xs
                    (SmtTerm.or (__eo_to_smt f) (__eo_to_smt fs))) =
                __smtx_model_eval M
                  (miniToSmt (qor (qforall ys f) gs)) :=
            ih M hM hXsEnv hXsWF
              (by simpa [eo_to_smt_or_eq, qor] using hTailLeftTy)
              hTailRightTy
          have hSingleEnv :
              EoVarEnv
                (qcons (Term.Var (Term.String s) T) Term.__eo_List_nil)
                [(s, T)] :=
            EoVarEnv.cons EoVarEnv.nil
          have hSingleWF :
              ∀ s' T', (s', T') ∈ [(s, T)] ->
                __smtx_type_wf (__eo_to_smt_type T') = true := by
            intro s' T' hMem
            simp at hMem
            rcases hMem with ⟨rfl, rfl⟩
            exact hHeadWF
          have hTailOrTy :
              __smtx_typeof
                  (SmtTerm.or
                    (smtForall ys (__eo_to_smt f)) (miniToSmt gs)) =
                SmtType.Bool :=
            smtx_typeof_or_bool_of_args
              (smtForall ys (__eo_to_smt f)) (miniToSmt gs)
              hYsForallTy hGsTy
          have hGsInv :
              ∀ {N : SmtModel},
                model_wf N ->
                model_agrees_except_on_env
                    ([(s, T)].map EoVarKey.toSmt) [] N M ->
                  __smtx_model_eval N (miniToSmt gs) =
                    __smtx_model_eval M (miniToSmt gs) := by
            intro N _hN hAgree
            exact
              hMiniInv _hN hM (EoVarEnvPerm.of_exact hSingleEnv)
                hGsTy hNoFree hAgree
          have hDistRight :
              __smtx_model_eval M
                  (smtForall
                    (qcons (Term.Var (Term.String s) T) Term.__eo_List_nil)
                    (SmtTerm.or (smtForall ys (__eo_to_smt f))
                      (miniToSmt gs))) =
                __smtx_model_eval M
                  (SmtTerm.or
                    (smtForall
                      (qcons (Term.Var (Term.String s) T)
                        Term.__eo_List_nil)
                      (smtForall ys (__eo_to_smt f)))
                    (miniToSmt gs)) :=
            smtx_model_eval_smtForall_or_right_invariant
              M hM hSingleEnv hSingleWF
              (smtForall ys (__eo_to_smt f)) (miniToSmt gs)
              hYsForallTy hGsTy hGsInv
          have hConsYsExistsTy :
              __smtx_typeof
                  (__eo_to_smt_exists ys
                    (SmtTerm.not (__eo_to_smt f))) =
                SmtType.Bool :=
            hYsExistsTy
          have hRightSplit :
              __smtx_model_eval M
                  (smtForall
                    (qcons (Term.Var (Term.String s) T)
                      Term.__eo_List_nil)
                    (smtForall ys (__eo_to_smt f))) =
                __smtx_model_eval M
                  (smtForall
                    (qcons (Term.Var (Term.String s) T) ys)
                    (__eo_to_smt f)) := by
            exact
              (smtx_model_eval_smtForall_cons_split M hM s T ys
                (__eo_to_smt f) hHeadWF hConsYsExistsTy).symm
          rw [show
              smtForall
                (qcons (Term.Var (Term.String s) T) xs)
                (__eo_to_smt (qor f fs)) =
                smtForall
                  (qcons (Term.Var (Term.String s) T) xs)
                  (SmtTerm.or (__eo_to_smt f) (__eo_to_smt fs)) by
                rw [eo_to_smt_or_eq]]
          rw [hLeftSplit]
          apply Eq.trans
          · apply smt_model_eval_smtForall_eq_of_body_eval_eq_same_mapped_typed
              hSingleEnv hSingleWF (by intro key hMem; exact hMem) hM
              (model_agrees_except_on_env_refl
                ([(s, T)].map EoVarKey.toSmt) [] M)
            intro M' hM' _hAgree
            exact
              ih M' hM' hXsEnv hXsWF
                (by simpa [eo_to_smt_or_eq, qor] using hTailLeftTy)
                hTailRightTy
          · change
              __smtx_model_eval M
                  (smtForall
                    (qcons (Term.Var (Term.String s) T)
                      Term.__eo_List_nil)
                    (SmtTerm.or (smtForall ys (__eo_to_smt f))
                      (miniToSmt gs))) =
                __smtx_model_eval M
                  (SmtTerm.or
                    (smtForall
                      (qcons (Term.Var (Term.String s) T) ys)
                      (__eo_to_smt f))
                    (miniToSmt gs))
            rw [hDistRight]
            change
              __smtx_model_eval M
                  (SmtTerm.or
                    (smtForall
                      (qcons (Term.Var (Term.String s) T)
                        Term.__eo_List_nil)
                      (smtForall ys (__eo_to_smt f)))
                    (miniToSmt gs)) =
                __smtx_model_eval M
                  (SmtTerm.or
                    (smtForall
                      (qcons (Term.Var (Term.String s) T) ys)
                      (__eo_to_smt f))
                    (miniToSmt gs))
            exact smtx_model_eval_or_eq_of_args_eq_same hRightSplit rfl

private theorem quant_miniscope_or_shape_of_not_stuck
    (a1 : Term) :
    __eo_prog_quant_miniscope_or a1 ≠ Term.Stuck ->
    ∃ x F G,
      a1 = quantMiniscopeOrFormula x F G ∧
      __is_quant_miniscope_or x F G = Term.Boolean true ∧
      __eo_prog_quant_miniscope_or a1 =
        quantMiniscopeOrFormula x F G := by
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
                      | Apply forallOp x =>
                          cases forallOp with
                          | UOp opForall =>
                              cases opForall with
                              | «forall» =>
                                  let body :=
                                    quantMiniscopeOrFormula x F G
                                  let guard := __is_quant_miniscope_or x F G
                                  have hReq :
                                      __eo_requires guard
                                          (Term.Boolean true) body ≠
                                        Term.Stuck := by
                                    simpa [guard, body, quantMiniscopeOrFormula,
                                      qeq, qforall, __eo_prog_quant_miniscope_or]
                                      using hProg
                                  have hGuard :
                                      guard = Term.Boolean true :=
                                    eo_requires_arg_eq_of_ne_stuck hReq
                                  have hProgEq :
                                      __eo_prog_quant_miniscope_or
                                          (quantMiniscopeOrFormula x F G) =
                                        quantMiniscopeOrFormula x F G := by
                                    change
                                      __eo_requires guard
                                          (Term.Boolean true) body =
                                        body
                                    exact eo_requires_result_eq_of_ne_stuck hReq
                                  exact ⟨x, F, G, rfl, by simpa [guard] using hGuard,
                                    hProgEq⟩
                              | _ =>
                                  simp [__eo_prog_quant_miniscope_or] at hProg
                          | _ =>
                              simp [__eo_prog_quant_miniscope_or] at hProg
                      | _ =>
                          simp [__eo_prog_quant_miniscope_or] at hProg
                  | _ =>
                      simp [__eo_prog_quant_miniscope_or] at hProg
              | _ =>
                  simp [__eo_prog_quant_miniscope_or] at hProg
          | _ =>
              simp [__eo_prog_quant_miniscope_or] at hProg
      | _ =>
          simp [__eo_prog_quant_miniscope_or] at hProg
  | _ =>
      simp [__eo_prog_quant_miniscope_or] at hProg

private theorem quant_miniscope_or_formula_true
    (M : SmtModel) (hM : model_wf M)
    (x F G : Term) :
    RuleProofs.eo_has_smt_translation
        (quantMiniscopeOrFormula x F G) ->
    __eo_typeof (quantMiniscopeOrFormula x F G) = Term.Bool ->
    __is_quant_miniscope_or x F G = Term.Boolean true ->
    eo_interprets M (quantMiniscopeOrFormula x F G) true := by
  intro hTransFormula hFormulaType hGuard
  have hFormulaBool :
      RuleProofs.eo_has_bool_type (quantMiniscopeOrFormula x F G) :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type
      (quantMiniscopeOrFormula x F G) hTransFormula hFormulaType
  rcases
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (qforall x F) G hFormulaBool with
    ⟨hSameTy, hLeftNN⟩
  have hxNonNil : x ≠ Term.__eo_List_nil :=
    qforall_non_nil_of_non_none x F hLeftNN
  have hLeftOrdTy :
      __smtx_typeof (__eo_to_smt (qforall x F)) = SmtType.Bool := by
    have hExistsTy :
        __smtx_typeof
            (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
          SmtType.Bool :=
      qforall_exists_type_bool_of_non_none x F hLeftNN
    rw [eo_to_smt_forall_eq x F hxNonNil]
    unfold smtForall
    exact smtx_typeof_not_bool_of_arg_bool
      (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) hExistsTy
  have hLeftTy :
      __smtx_typeof (smtForall x (__eo_to_smt F)) = SmtType.Bool := by
    simpa [eo_to_smt_forall_eq x F hxNonNil] using hLeftOrdTy
  have hRightOrdTy :
      __smtx_typeof (__eo_to_smt G) = SmtType.Bool := by
    rw [← hSameTy]
    exact hLeftOrdTy
  have hGTrans : RuleProofs.eo_has_smt_translation G := by
    intro hNone
    rw [hNone] at hRightOrdTy
    cases hRightOrdTy
  have hMiniG :
      miniToSmt G = __eo_to_smt G :=
    miniToSmt_eq_eo_to_smt_of_has_smt_translation G hGTrans
  have hRightTy :
      __smtx_typeof (miniToSmt G) = SmtType.Bool := by
    rw [hMiniG]
    exact hRightOrdTy
  rcases
      eo_var_env_of_quant_has_smt_translation
        (Q := Term.UOp UserOp.forall) (xs := x) (body := F)
        (Or.inl rfl) hLeftNN with
    ⟨xVars, hXEnv⟩
  have hXWF :
      ∀ s T, (s, T) ∈ xVars ->
        __smtx_type_wf (__eo_to_smt_type T) = true :=
    smtx_type_wf_of_smtForall_env_bool hXEnv hLeftTy
  have hRel : MiniOr x F G :=
    mini_or_of_is_true x F G hGuard
  have hEvalMini :
      __smtx_model_eval M (smtForall x (__eo_to_smt F)) =
        __smtx_model_eval M (miniToSmt G) :=
    mini_or_eval_eq M hM
      (fun {t except exceptVars M N} hMt hNt hExcept hTy hNoFree hAgree =>
        miniToSmt_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
          hMt hNt hExcept hTy hNoFree hAgree)
      hRel hXEnv hXWF hLeftTy hRightTy
  have hEval :
      __smtx_model_eval M (__eo_to_smt (qforall x F)) =
        __smtx_model_eval M (__eo_to_smt G) := by
    simpa [eo_to_smt_forall_eq x F hxNonNil, hMiniG] using hEvalMini
  apply RuleProofs.eo_interprets_eq_of_rel M (qforall x F) G hFormulaBool
  rw [hEval]
  exact RuleProofs.smt_value_rel_refl
    (__smtx_model_eval M (__eo_to_smt G))

public theorem cmd_step_quant_miniscope_or_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_miniscope_or args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.quant_miniscope_or args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_miniscope_or args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.quant_miniscope_or args premises ≠
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
                  __eo_prog_quant_miniscope_or a1 ≠ Term.Stuck := by
                change __eo_prog_quant_miniscope_or a1 ≠ Term.Stuck at hProg
                simpa using hProg
              rcases quant_miniscope_or_shape_of_not_stuck a1 hProgQuant with
                ⟨x, F, G, ha1, hGuard, hProgEq⟩
              have hTransFormula :
                  RuleProofs.eo_has_smt_translation
                    (quantMiniscopeOrFormula x F G) := by
                simpa [ha1] using hTransA1
              have hFormulaType :
                  __eo_typeof (quantMiniscopeOrFormula x F G) =
                    Term.Bool := by
                change __eo_typeof (__eo_prog_quant_miniscope_or a1) =
                  Term.Bool at hResultTy
                rw [hProgEq] at hResultTy
                exact hResultTy
              have hFormulaBool :
                  RuleProofs.eo_has_bool_type
                    (quantMiniscopeOrFormula x F G) :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  (quantMiniscopeOrFormula x F G)
                  hTransFormula hFormulaType
              have hFact :
                  eo_interprets M (quantMiniscopeOrFormula x F G) true :=
                quant_miniscope_or_formula_true M hM x F G
                  hTransFormula hFormulaType hGuard
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M
                  (__eo_prog_quant_miniscope_or a1) true
                rw [hProgEq]
                exact hFact
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_quant_miniscope_or a1)
                rw [hProgEq]
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  hFormulaBool
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
