module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport
public import Cpc.Proofs.Closed.ContainsAtomicTermListFree
import all Cpc.Proofs.Closed.ContainsAtomicTermListFree

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private def qforall (x F : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.forall) x) F

private def qite (A F1 F2 : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) A) F1) F2

private def qeq (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B

private def quantMiniscopeIteFormula
    (x A F1 F2 : Term) : Term :=
  qeq (qforall x (qite A F1 F2))
    (qite A (qforall x F1) (qforall x F2))

private theorem eo_to_smt_forall_eq (x F : Term)
    (hx : x ≠ Term.__eo_List_nil) :
    __eo_to_smt (qforall x F) =
      SmtTerm.not (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) := by
  cases x <;> first | rfl | exact False.elim (hx rfl)

private theorem qforall_non_nil_of_has_smt_translation
    (x F : Term) :
    RuleProofs.eo_has_smt_translation (qforall x F) ->
    x ≠ Term.__eo_List_nil := by
  intro hTrans hx
  subst x
  exact hTrans (by
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none)

private theorem smtx_typeof_not_arg_of_bool
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool ->
    __smtx_typeof t = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq] at hTy
  cases h : __smtx_typeof t <;>
    simp [h, native_ite, native_Teq] at hTy ⊢

private theorem smtx_typeof_not_bool_of_non_none
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool := by
  intro hNN
  have hArg : __smtx_typeof t = SmtType.Bool := by
    cases h : __smtx_typeof t <;>
      simp [typeof_not_eq, h, native_ite, native_Teq] at hNN ⊢
  rw [typeof_not_eq]
  simp [hArg, native_ite, native_Teq]

private theorem qforall_exists_type_bool_of_has_smt_translation
    (x F : Term) :
    RuleProofs.eo_has_smt_translation (qforall x F) ->
    __smtx_typeof
        (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
      SmtType.Bool := by
  intro hTrans
  have hx : x ≠ Term.__eo_List_nil :=
    qforall_non_nil_of_has_smt_translation x F hTrans
  exact smtx_typeof_not_arg_of_bool
    (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F)))
    (smtx_typeof_not_bool_of_non_none
      (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) (by
        simpa [RuleProofs.eo_has_smt_translation,
          eo_to_smt_forall_eq x F hx] using hTrans))

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

private theorem body_ne_stuck_of_requires_ne_stuck {x y B : Term} :
    __eo_requires x y B ≠ Term.Stuck ->
    B ≠ Term.Stuck := by
  intro hReq hB
  subst B
  unfold __eo_requires at hReq
  by_cases hEq : native_teq x y = true
  · by_cases hStuck : native_teq x Term.Stuck = true
    · simp [hEq, hStuck, native_ite] at hReq
    · have hStuckFalse : native_teq x Term.Stuck = false := by
        cases h : native_teq x Term.Stuck <;> simp [h] at hStuck ⊢
      simp [hEq, hStuckFalse, native_ite] at hReq
  · have hEqFalse : native_teq x y = false := by
      cases h : native_teq x y <;> simp [h] at hEq ⊢
    simp [hEqFalse, native_ite] at hReq

private theorem eo_eq_true_eq
    {a b : Term}
    (hEq : __eo_eq a b = Term.Boolean true) :
  a = b := by
  have hEqSymm : b = a := by
    cases a <;> cases b <;> simp [__eo_eq, native_teq] at hEq ⊢
    all_goals exact hEq
  exact hEqSymm.symm


private theorem qforall_body_has_bool_type
    (x F : Term) :
    RuleProofs.eo_has_smt_translation (qforall x F) ->
    RuleProofs.eo_has_bool_type F := by
  intro hTrans
  have hExistsTy :=
    qforall_exists_type_bool_of_has_smt_translation x F hTrans
  have hNotBodyTy :
      __smtx_typeof (SmtTerm.not (__eo_to_smt F)) = SmtType.Bool :=
    TranslationProofs.eo_to_smt_exists_body_bool_of_bool
      x (SmtTerm.not (__eo_to_smt F)) hExistsTy
  exact smtx_typeof_not_arg_of_bool (__eo_to_smt F) hNotBodyTy

private theorem qforall_body_has_smt_translation
    (x F : Term) :
    RuleProofs.eo_has_smt_translation (qforall x F) ->
    RuleProofs.eo_has_smt_translation F := by
  intro hTrans
  exact RuleProofs.eo_has_smt_translation_of_has_bool_type F
    (qforall_body_has_bool_type x F hTrans)

private theorem native_eval_texists_eq_of_body_eval_eq_same
    {M : SmtModel} {s : native_String} {T : SmtType}
    {body body' : SmtTerm}
    (hBody : ∀ v : SmtValue,
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
      exact ⟨v, hTy, hCanon, by simpa [hBody v] using hEval⟩
    · intro h
      rcases h with ⟨v, hTy, hCanon, hEval⟩
      exact ⟨v, hTy, hCanon, by simpa [← hBody v] using hEval⟩
  by_cases hP : P
  · have hQ : Q := hIff.mp hP
    simp [hP, hQ]
  · have hQ : ¬ Q := fun h => hP (hIff.mpr h)
    simp [hP, hQ]

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

private theorem smt_model_eval_eo_to_smt_exists_eq_of_body_eval_eq_same_mapped
    {vs : Term} {binderVars : List EoVarKey}
    {exceptVars : List SmtVarKey} {M N : SmtModel}
    {body body' : SmtTerm}
    (hEnv : EoVarEnv vs binderVars)
    (hSub :
      ∀ key, key ∈ binderVars.map EoVarKey.toSmt -> key ∈ exceptVars)
    (hAgree : model_agrees_except_on_env exceptVars [] M N)
    (hBody :
      ∀ {M' : SmtModel},
        model_agrees_except_on_env exceptVars [] M' N ->
          __smtx_model_eval M' body =
            __smtx_model_eval M' body') :
  __smtx_model_eval M (__eo_to_smt_exists vs body) =
    __smtx_model_eval M (__eo_to_smt_exists vs body') := by
  induction hEnv generalizing M with
  | nil =>
      simpa [__eo_to_smt_exists] using hBody hAgree
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
      apply native_eval_texists_eq_of_body_eval_eq_same
      intro v
      have hHeadMem :
          (s, __eo_to_smt_type T) ∈ exceptVars :=
        hSub (s, __eo_to_smt_type T) (by
          simp [EoVarKey.toSmt])
      have hAgreePush :
          model_agrees_except_on_env exceptVars []
            (native_model_push M s (__eo_to_smt_type T) v) N :=
        model_agrees_except_on_env_push_left hAgree hHeadMem (by simp)
      apply ih
      · intro key hMem
        apply hSub
        rcases List.mem_map.1 hMem with ⟨eoKey, hEoMem, hKeyEq⟩
        exact List.mem_map.2 ⟨eoKey, List.mem_cons_of_mem _ hEoMem, hKeyEq⟩
      · exact hAgreePush

private theorem smtx_model_eval_qforall_ite_eq
    (M : SmtModel) (hM : model_wf M)
    (xVars : List EoVarKey)
    (x A F1 F2 : Term)
    (hLeftTrans :
      RuleProofs.eo_has_smt_translation (qforall x (qite A F1 F2)))
    (hXEnv : EoVarEnv x xVars)
    (hATrans : RuleProofs.eo_has_smt_translation A)
    (hABool : RuleProofs.eo_has_bool_type A)
    (hNoFree :
      __contains_atomic_term_list_free_rec A x Term.__eo_List_nil =
        Term.Boolean false) :
    __smtx_model_eval M (__eo_to_smt (qforall x (qite A F1 F2))) =
      __smtx_model_eval M
        (__eo_to_smt (qite A (qforall x F1) (qforall x F2))) := by
  have hx : x ≠ Term.__eo_List_nil :=
    qforall_non_nil_of_has_smt_translation x (qite A F1 F2)
      hLeftTrans
  rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M
      hM A hABool with
    ⟨a, hAEval⟩
  have hAInvariant :
      ∀ {N : SmtModel},
        model_agrees_except_on_env (xVars.map EoVarKey.toSmt) [] N M ->
          __smtx_model_eval N (__eo_to_smt A) =
            __smtx_model_eval M (__eo_to_smt A) := by
    intro N hAgree
    exact
      smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
        (EoVarEnvPerm.of_exact hXEnv)
        (EoVarEnvPerm.of_exact EoVarEnv.nil)
        hATrans hNoFree hAgree
  cases a with
  | false =>
      have hExistsEq :
          __smtx_model_eval M
              (__eo_to_smt_exists x
                (SmtTerm.not (__eo_to_smt (qite A F1 F2)))) =
            __smtx_model_eval M
              (__eo_to_smt_exists x
                (SmtTerm.not (__eo_to_smt F2))) :=
        smt_model_eval_eo_to_smt_exists_eq_of_body_eval_eq_same_mapped
          hXEnv (by intro key hMem; exact hMem)
          (model_agrees_except_on_env_refl
            (xVars.map EoVarKey.toSmt) [] M)
          (by
            intro N hAgree
            have hAN := hAInvariant hAgree
            rw [show __eo_to_smt (qite A F1 F2) =
                SmtTerm.ite (__eo_to_smt A) (__eo_to_smt F1)
                  (__eo_to_smt F2) by rfl]
            rw [smtx_eval_not_term_eq, smtx_eval_ite_term_eq,
              smtx_eval_not_term_eq]
            rw [hAN, hAEval]
            simp [__smtx_model_eval_ite, __smtx_model_eval_not])
      have hLeft :
          __smtx_model_eval M (__eo_to_smt (qforall x (qite A F1 F2))) =
            __smtx_model_eval M (__eo_to_smt (qforall x F2)) := by
        rw [eo_to_smt_forall_eq x (qite A F1 F2) hx]
        rw [eo_to_smt_forall_eq x F2 hx]
        exact smtx_model_eval_not_eq_of_arg_eq_same hExistsEq
      have hRight :
          __smtx_model_eval M
              (__eo_to_smt (qite A (qforall x F1) (qforall x F2))) =
            __smtx_model_eval M (__eo_to_smt (qforall x F2)) := by
        rw [show __eo_to_smt (qite A (qforall x F1) (qforall x F2)) =
          SmtTerm.ite (__eo_to_smt A) (__eo_to_smt (qforall x F1))
            (__eo_to_smt (qforall x F2)) by rfl]
        rw [smtx_eval_ite_term_eq, hAEval]
        simp [__smtx_model_eval_ite]
      exact hLeft.trans hRight.symm
  | true =>
      have hExistsEq :
          __smtx_model_eval M
              (__eo_to_smt_exists x
                (SmtTerm.not (__eo_to_smt (qite A F1 F2)))) =
            __smtx_model_eval M
              (__eo_to_smt_exists x
                (SmtTerm.not (__eo_to_smt F1))) :=
        smt_model_eval_eo_to_smt_exists_eq_of_body_eval_eq_same_mapped
          hXEnv (by intro key hMem; exact hMem)
          (model_agrees_except_on_env_refl
            (xVars.map EoVarKey.toSmt) [] M)
          (by
            intro N hAgree
            have hAN := hAInvariant hAgree
            rw [show __eo_to_smt (qite A F1 F2) =
                SmtTerm.ite (__eo_to_smt A) (__eo_to_smt F1)
                  (__eo_to_smt F2) by rfl]
            rw [smtx_eval_not_term_eq, smtx_eval_ite_term_eq,
              smtx_eval_not_term_eq]
            rw [hAN, hAEval]
            simp [__smtx_model_eval_ite, __smtx_model_eval_not])
      have hLeft :
          __smtx_model_eval M (__eo_to_smt (qforall x (qite A F1 F2))) =
            __smtx_model_eval M (__eo_to_smt (qforall x F1)) := by
        rw [eo_to_smt_forall_eq x (qite A F1 F2) hx]
        rw [eo_to_smt_forall_eq x F1 hx]
        exact smtx_model_eval_not_eq_of_arg_eq_same hExistsEq
      have hRight :
          __smtx_model_eval M
              (__eo_to_smt (qite A (qforall x F1) (qforall x F2))) =
            __smtx_model_eval M (__eo_to_smt (qforall x F1)) := by
        rw [show __eo_to_smt (qite A (qforall x F1) (qforall x F2)) =
          SmtTerm.ite (__eo_to_smt A) (__eo_to_smt (qforall x F1))
            (__eo_to_smt (qforall x F2)) by rfl]
        rw [smtx_eval_ite_term_eq, hAEval]
        simp [__smtx_model_eval_ite]
      exact hLeft.trans hRight.symm

private theorem smtx_model_eval_quant_miniscope_ite
    (M : SmtModel) (hM : model_wf M)
    (x A F1 F2 : Term)
    (hBool :
      RuleProofs.eo_has_bool_type
        (quantMiniscopeIteFormula x A F1 F2))
    (hNoFree :
      __contains_atomic_term_list_free_rec A x Term.__eo_List_nil =
        Term.Boolean false) :
    __smtx_model_eval M (__eo_to_smt (qforall x (qite A F1 F2))) =
      __smtx_model_eval M
        (__eo_to_smt (qite A (qforall x F1) (qforall x F2))) := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (qforall x (qite A F1 F2))
      (qite A (qforall x F1) (qforall x F2))
      hBool with
    ⟨_hSameTy, hLeftTrans⟩
  have hLeftTrans' :
      RuleProofs.eo_has_smt_translation
        (qforall x (qite A F1 F2)) := hLeftTrans
  have hBodyTrans :
      RuleProofs.eo_has_smt_translation (qite A F1 F2) :=
    qforall_body_has_smt_translation x (qite A F1 F2)
      hLeftTrans'
  have hABool :
      RuleProofs.eo_has_bool_type A :=
    CnfSupport.ite_cond_has_bool_type_of_translation A F1 F2 hBodyTrans
  have hATrans :
      RuleProofs.eo_has_smt_translation A :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type A hABool
  rcases
      eo_var_env_of_quant_has_smt_translation
        (Q := Term.UOp UserOp.forall) (xs := x) (body := qite A F1 F2)
        (Or.inl rfl) hLeftTrans' with
    ⟨xVars, hXEnv⟩
  exact
    smtx_model_eval_qforall_ite_eq M hM xVars x A F1 F2
      hLeftTrans' hXEnv hATrans hABool hNoFree

private theorem quant_miniscope_ite_shape_of_not_stuck
    (a1 : Term) :
    __eo_prog_quant_miniscope_ite a1 ≠ Term.Stuck ->
    ∃ x A F1 F2,
      a1 = quantMiniscopeIteFormula x A F1 F2 ∧
      __contains_atomic_term_list_free_rec A x Term.__eo_List_nil =
        Term.Boolean false ∧
      __eo_prog_quant_miniscope_ite a1 =
        quantMiniscopeIteFormula x A F1 F2 := by
  intro hProg
  cases a1 with
  | Apply lhs rhs =>
      cases lhs with
      | Apply eqHead lhsArg =>
          cases eqHead with
          | UOp opEq =>
              cases opEq with
              | eq =>
                  cases lhsArg with
                  | Apply forallHead body =>
                      cases forallHead with
                      | Apply forallOp x =>
                          cases forallOp with
                          | UOp opForall =>
                              cases opForall with
                              | «forall» =>
                                  cases body with
                                  | Apply iteElseHead F2 =>
                                      cases iteElseHead with
                                      | Apply iteThenHead F1 =>
                                          cases iteThenHead with
                                          | Apply iteOp A =>
                                              cases iteOp with
                                              | UOp opIte =>
                                                  cases opIte with
                                                  | ite =>
                                                      cases rhs with
                                                      | Apply rhsElseHead rhsElse =>
                                                          cases rhsElseHead with
                                                          | Apply rhsThenHead rhsThen =>
                                                              cases rhsThenHead with
                                                              | Apply rhsIteOp A₂ =>
                                                                  cases rhsIteOp with
                                                                  | UOp rhsOp =>
                                                                      cases rhsOp with
                                                                      | ite =>
                                                                          cases rhsThen with
                                                                          | Apply rhsThenQHead F1₂ =>
                                                                              cases rhsThenQHead with
                                                                              | Apply rhsThenQ x₂ =>
                                                                                  cases rhsThenQ with
                                                                                  | UOp rhsThenOp =>
                                                                                      cases rhsThenOp with
                                                                                      | «forall» =>
                                                                                          cases rhsElse with
                                                                                          | Apply rhsElseQHead F2₂ =>
                                                                                              cases rhsElseQHead with
                                                                                              | Apply rhsElseQ x₃ =>
                                                                                                  cases rhsElseQ with
                                                                                                  | UOp rhsElseOp =>
                                                                                                      cases rhsElseOp with
                                                                                                      | «forall» =>
                                                                                                          let guard :=
                                                                                                            __eo_and
                                                                                                              (__eo_and
                                                                                                                (__eo_and
                                                                                                                  (__eo_and (__eo_eq A A₂)
                                                                                                                    (__eo_eq x x₂))
                                                                                                                  (__eo_eq F1 F1₂))
                                                                                                                (__eo_eq x x₃))
                                                                                                              (__eo_eq F2 F2₂)
                                                                                                          let bodyReq :=
                                                                                                            __eo_requires
                                                                                                              (__contains_atomic_term_list_free_rec A x Term.__eo_List_nil)
                                                                                                              (Term.Boolean false)
                                                                                                              (quantMiniscopeIteFormula x A F1 F2)
                                                                                                          have hReq :
                                                                                                              __eo_requires guard
                                                                                                                (Term.Boolean true)
                                                                                                                bodyReq ≠
                                                                                                              Term.Stuck := by
                                                                                                            simpa [guard, bodyReq,
                                                                                                              quantMiniscopeIteFormula,
                                                                                                              qeq, qforall, qite,
                                                                                                              __eo_prog_quant_miniscope_ite]
                                                                                                              using hProg
                                                                                                          have hGuard :
                                                                                                              guard = Term.Boolean true :=
                                                                                                            eo_requires_arg_eq_of_ne_stuck hReq
                                                                                                          have hInnerNe :
                                                                                                              bodyReq ≠ Term.Stuck :=
                                                                                                            body_ne_stuck_of_requires_ne_stuck hReq
                                                                                                          have hNoFree :
                                                                                                              __contains_atomic_term_list_free_rec A x Term.__eo_List_nil =
                                                                                                                Term.Boolean false :=
                                                                                                            eo_requires_arg_eq_of_ne_stuck hInnerNe
                                                                                                          have hOuterEq :
                                                                                                              __eo_requires guard
                                                                                                                (Term.Boolean true)
                                                                                                                bodyReq =
                                                                                                              bodyReq :=
                                                                                                            eo_requires_result_eq_of_ne_stuck hReq
                                                                                                          have hInnerEq :
                                                                                                              bodyReq =
                                                                                                                quantMiniscopeIteFormula x A F1 F2 :=
                                                                                                            eo_requires_result_eq_of_ne_stuck hInnerNe
                                                                                                          have hG1 :=
                                                                                                            eo_and_eq_true_cases hGuard
                                                                                                          have hG2 :=
                                                                                                            eo_and_eq_true_cases hG1.1
                                                                                                          have hG3 :=
                                                                                                            eo_and_eq_true_cases hG2.1
                                                                                                          have hG4 :=
                                                                                                            eo_and_eq_true_cases hG3.1
                                                                                                          have hAEq : A = A₂ :=
                                                                                                            eo_eq_true_eq hG4.1
                                                                                                          have hxEq₂ : x = x₂ :=
                                                                                                            eo_eq_true_eq hG4.2
                                                                                                          have hF1Eq : F1 = F1₂ :=
                                                                                                            eo_eq_true_eq hG3.2
                                                                                                          have hxEq₃ : x = x₃ :=
                                                                                                            eo_eq_true_eq hG2.2
                                                                                                          have hF2Eq : F2 = F2₂ :=
                                                                                                            eo_eq_true_eq hG1.2
                                                                                                          subst A₂
                                                                                                          subst x₂
                                                                                                          subst F1₂
                                                                                                          subst x₃
                                                                                                          subst F2₂
                                                                                                          refine ⟨x, A, F1, F2, rfl, hNoFree, ?_⟩
                                                                                                          change __eo_prog_quant_miniscope_ite
                                                                                                              (quantMiniscopeIteFormula x A F1 F2) =
                                                                                                            quantMiniscopeIteFormula x A F1 F2
                                                                                                          calc
                                                                                                            __eo_prog_quant_miniscope_ite
                                                                                                                (quantMiniscopeIteFormula x A F1 F2)
                                                                                                                =
                                                                                                              __eo_requires guard
                                                                                                                (Term.Boolean true)
                                                                                                                bodyReq := by
                                                                                                                  simp [guard, bodyReq,
                                                                                                                    quantMiniscopeIteFormula,
                                                                                                                    qeq, qforall, qite,
                                                                                                                    __eo_prog_quant_miniscope_ite]
                                                                                                            _ = bodyReq := hOuterEq
                                                                                                            _ = quantMiniscopeIteFormula x A F1 F2 :=
                                                                                                              hInnerEq
                                                                                                      | _ =>
                                                                                                          simp [__eo_prog_quant_miniscope_ite] at hProg
                                                                                                  | _ =>
                                                                                                      simp [__eo_prog_quant_miniscope_ite] at hProg
                                                                                              | _ =>
                                                                                                  simp [__eo_prog_quant_miniscope_ite] at hProg
                                                                                          | _ =>
                                                                                              simp [__eo_prog_quant_miniscope_ite] at hProg
                                                                                      | _ =>
                                                                                          simp [__eo_prog_quant_miniscope_ite] at hProg
                                                                                  | _ =>
                                                                                      simp [__eo_prog_quant_miniscope_ite] at hProg
                                                                              | _ =>
                                                                                  simp [__eo_prog_quant_miniscope_ite] at hProg
                                                                          | _ =>
                                                                              simp [__eo_prog_quant_miniscope_ite] at hProg
                                                                      | _ =>
                                                                          simp [__eo_prog_quant_miniscope_ite] at hProg
                                                                  | _ =>
                                                                      simp [__eo_prog_quant_miniscope_ite] at hProg
                                                              | _ =>
                                                                  simp [__eo_prog_quant_miniscope_ite] at hProg
                                                          | _ =>
                                                              simp [__eo_prog_quant_miniscope_ite] at hProg
                                                      | _ =>
                                                          simp [__eo_prog_quant_miniscope_ite] at hProg
                                                  | _ =>
                                                      simp [__eo_prog_quant_miniscope_ite] at hProg
                                              | _ =>
                                                  simp [__eo_prog_quant_miniscope_ite] at hProg
                                          | _ =>
                                              simp [__eo_prog_quant_miniscope_ite] at hProg
                                      | _ =>
                                          simp [__eo_prog_quant_miniscope_ite] at hProg
                                  | _ =>
                                      simp [__eo_prog_quant_miniscope_ite] at hProg
                              | _ =>
                                  simp [__eo_prog_quant_miniscope_ite] at hProg
                          | _ =>
                              simp [__eo_prog_quant_miniscope_ite] at hProg
                      | _ =>
                          simp [__eo_prog_quant_miniscope_ite] at hProg
                  | _ =>
                      simp [__eo_prog_quant_miniscope_ite] at hProg
              | _ =>
                  simp [__eo_prog_quant_miniscope_ite] at hProg
          | _ =>
              simp [__eo_prog_quant_miniscope_ite] at hProg
      | _ =>
          simp [__eo_prog_quant_miniscope_ite] at hProg
  | _ =>
      simp [__eo_prog_quant_miniscope_ite] at hProg

public theorem cmd_step_quant_miniscope_ite_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_miniscope_ite args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.quant_miniscope_ite args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_miniscope_ite args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.quant_miniscope_ite args premises ≠
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
                  __eo_prog_quant_miniscope_ite a1 ≠ Term.Stuck := by
                change __eo_prog_quant_miniscope_ite a1 ≠ Term.Stuck at hProg
                simpa using hProg
              rcases quant_miniscope_ite_shape_of_not_stuck a1 hProgQuant with
                ⟨x, A, F1, F2, ha1, hNoFree, hProgEq⟩
              have hTransFormula :
                  RuleProofs.eo_has_smt_translation
                    (quantMiniscopeIteFormula x A F1 F2) := by
                simpa [ha1] using hTransA1
              have hFormulaType :
                  __eo_typeof (quantMiniscopeIteFormula x A F1 F2) =
                    Term.Bool := by
                change __eo_typeof (__eo_prog_quant_miniscope_ite a1) =
                  Term.Bool at hResultTy
                rw [hProgEq] at hResultTy
                exact hResultTy
              have hFormulaBool :
                  RuleProofs.eo_has_bool_type
                    (quantMiniscopeIteFormula x A F1 F2) :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  (quantMiniscopeIteFormula x A F1 F2)
                  hTransFormula hFormulaType
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M
                  (__eo_prog_quant_miniscope_ite a1) true
                rw [hProgEq]
                apply RuleProofs.eo_interprets_eq_of_rel M
                  (qforall x (qite A F1 F2))
                  (qite A (qforall x F1) (qforall x F2))
                · exact hFormulaBool
                · have hEvalEq :=
                    smtx_model_eval_quant_miniscope_ite M hM
                      x A F1 F2 hFormulaBool hNoFree
                  rw [hEvalEq]
                  exact RuleProofs.smt_value_rel_refl
                    (__smtx_model_eval M
                      (__eo_to_smt
                        (qite A (qforall x F1) (qforall x F2))))
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_quant_miniscope_ite a1)
                rw [hProgEq]
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  hFormulaBool
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
