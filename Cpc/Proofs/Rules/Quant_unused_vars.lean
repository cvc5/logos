module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.Closed.ContainsAtomicTermListFree
import all Cpc.Proofs.Closed.ContainsAtomicTermListFree

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def qterm (Q x F : Term) : Term :=
  Term.Apply (Term.Apply Q x) F

private def qeq (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

private theorem eo_to_smt_qterm_exists_eq (x F : Term)
    (hx : x ≠ Term.__eo_List_nil) :
    __eo_to_smt (qterm (Term.UOp UserOp.exists) x F) =
      __eo_to_smt_exists x (__eo_to_smt F) := by
  unfold qterm
  cases x <;> first | rfl | exact False.elim (hx rfl)

private theorem eo_to_smt_qterm_forall_eq (x F : Term)
    (hx : x ≠ Term.__eo_List_nil) :
    __eo_to_smt (qterm (Term.UOp UserOp.forall) x F) =
      SmtTerm.not (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) := by
  unfold qterm
  cases x <;> first | rfl | exact False.elim (hx rfl)

private abbrev QuantBinder := native_String × SmtType

private def smtExistsOfBinders : List QuantBinder -> SmtTerm -> SmtTerm
  | [], body => body
  | b :: bs, body => SmtTerm.exists b.1 b.2 (smtExistsOfBinders bs body)

private theorem native_model_push_same
    (M : SmtModel) (s : native_String) (T : SmtType) (v w : SmtValue) :
    native_model_push (native_model_push M s T v) s T w =
      native_model_push M s T w := by
  cases M with
  | mk values nativeFuns =>
      change
        SmtModel.mk
            (fun k =>
              if k = ({ isVar := true, name := s, ty := T } : SmtModelKey) then w
              else
                (if k = ({ isVar := true, name := s, ty := T } : SmtModelKey) then v
                else values k))
            nativeFuns =
          SmtModel.mk
            (fun k =>
              if k = ({ isVar := true, name := s, ty := T } : SmtModelKey) then w
              else values k)
            nativeFuns
      congr
      funext k
      by_cases hk : k = ({ isVar := true, name := s, ty := T } : SmtModelKey)
      · simp [hk]
      · simp [hk]

private theorem native_model_push_comm
    (M : SmtModel) (s1 s2 : native_String) (T1 T2 : SmtType)
    (v1 v2 : SmtValue)
    (hNe :
      ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) ≠
        { isVar := true, name := s2, ty := T2 }) :
    native_model_push (native_model_push M s1 T1 v1) s2 T2 v2 =
      native_model_push (native_model_push M s2 T2 v2) s1 T1 v1 := by
  cases M with
  | mk values nativeFuns =>
      change
        SmtModel.mk
            (fun k =>
              if k = ({ isVar := true, name := s2, ty := T2 } : SmtModelKey) then v2
              else
                (if k = ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) then v1
                else values k))
            nativeFuns =
          SmtModel.mk
            (fun k =>
              if k = ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) then v1
              else
                (if k = ({ isVar := true, name := s2, ty := T2 } : SmtModelKey) then v2
                else values k))
            nativeFuns
      congr
      funext k
      by_cases h1 : k = ({ isVar := true, name := s1, ty := T1 } : SmtModelKey)
      · subst k
        by_cases h2 :
            ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) =
              { isVar := true, name := s2, ty := T2 }
        · exact False.elim (hNe h2)
        · simp [h2]
      · by_cases h2 : k = ({ isVar := true, name := s2, ty := T2 } : SmtModelKey)
        · subst k
          have h21 :
              ¬ ({ isVar := true, name := s2, ty := T2 } : SmtModelKey) =
                { isVar := true, name := s1, ty := T1 } := by
            intro h
            exact hNe h.symm
          simp [h21]
        · simp [h1, h2]

private theorem smtExistsOfBinders_cons_congr
    (M : SmtModel) (b : QuantBinder) (t u : SmtTerm) :
    (∀ M2, __smtx_model_eval M2 t = __smtx_model_eval M2 u) ->
    __smtx_model_eval M (smtExistsOfBinders [b] t) =
      __smtx_model_eval M (smtExistsOfBinders [b] u) := by
  rcases b with ⟨s, T⟩
  intro hEval
  classical
  let P : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push M s T v) t =
          SmtValue.Boolean true
  let Q : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push M s T v) u =
          SmtValue.Boolean true
  have hPQ : P ↔ Q := by
    constructor
    · intro hSat
      rcases hSat with ⟨v, hv, hCan, hT⟩
      exact ⟨v, hv, hCan, by
        simpa [hEval (native_model_push M s T v)] using hT⟩
    · intro hSat
      rcases hSat with ⟨v, hv, hCan, hU⟩
      exact ⟨v, hv, hCan, by
        simpa [hEval (native_model_push M s T v)] using hU⟩
  have hPropEq : P = Q := propext hPQ
  simp [smtExistsOfBinders, __smtx_model_eval, P, Q, hPropEq]

private theorem smtExistsOfBinders_swap
    (M : SmtModel) (b1 b2 : QuantBinder) (tail : List QuantBinder)
    (body : SmtTerm) :
    __smtx_model_eval M (smtExistsOfBinders (b1 :: b2 :: tail) body) =
      __smtx_model_eval M (smtExistsOfBinders (b2 :: b1 :: tail) body) := by
  rcases b1 with ⟨s1, T1⟩
  rcases b2 with ⟨s2, T2⟩
  classical
  let rest := smtExistsOfBinders tail body
  let P : Prop :=
    ∃ v1 : SmtValue,
      __smtx_typeof_value v1 = T1 ∧
        __smtx_value_canonical v1 = true ∧
        ∃ v2 : SmtValue,
          __smtx_typeof_value v2 = T2 ∧
            __smtx_value_canonical v2 = true ∧
            __smtx_model_eval
                (native_model_push (native_model_push M s1 T1 v1) s2 T2 v2)
                rest =
              SmtValue.Boolean true
  let Q : Prop :=
    ∃ v2 : SmtValue,
      __smtx_typeof_value v2 = T2 ∧
        __smtx_value_canonical v2 = true ∧
        ∃ v1 : SmtValue,
          __smtx_typeof_value v1 = T1 ∧
            __smtx_value_canonical v1 = true ∧
            __smtx_model_eval
                (native_model_push (native_model_push M s2 T2 v2) s1 T1 v1)
                rest =
              SmtValue.Boolean true
  have hPQ : P ↔ Q := by
    by_cases hKey :
        ({ isVar := true, name := s1, ty := T1 } : SmtModelKey) =
          { isVar := true, name := s2, ty := T2 }
    · cases hKey
      constructor
      · intro hSat
        rcases hSat with ⟨v1, hv1, hc1, v2, hv2, hc2, hEval⟩
        exact ⟨v1, hv1, hc1, v2, hv2, hc2, by
          simpa [native_model_push_same] using hEval⟩
      · intro hSat
        rcases hSat with ⟨v1, hv1, hc1, v2, hv2, hc2, hEval⟩
        exact ⟨v1, hv1, hc1, v2, hv2, hc2, by
          simpa [native_model_push_same] using hEval⟩
    · constructor
      · intro hSat
        rcases hSat with ⟨v1, hv1, hc1, v2, hv2, hc2, hEval⟩
        refine ⟨v2, hv2, hc2, v1, hv1, hc1, ?_⟩
        simpa [native_model_push_comm M s1 s2 T1 T2 v1 v2 hKey] using
          hEval
      · intro hSat
        rcases hSat with ⟨v2, hv2, hc2, v1, hv1, hc1, hEval⟩
        refine ⟨v1, hv1, hc1, v2, hv2, hc2, ?_⟩
        simpa [native_model_push_comm M s1 s2 T1 T2 v1 v2 hKey] using
          hEval
  have hPropEq : P = Q := propext hPQ
  simp [smtExistsOfBinders, __smtx_model_eval, P, Q, rest, hPropEq]

private theorem smtExistsOfBinders_eval_perm
    (body : SmtTerm) {xs ys : List QuantBinder}
    (hperm : xs.Perm ys) :
    ∀ M, __smtx_model_eval M (smtExistsOfBinders xs body) =
      __smtx_model_eval M (smtExistsOfBinders ys body) := by
  induction hperm with
  | nil =>
      intro M
      rfl
  | cons b _h ih =>
      intro M
      exact smtExistsOfBinders_cons_congr M b
        (smtExistsOfBinders _ body) (smtExistsOfBinders _ body) ih
  | swap b1 b2 tail =>
      intro M
      exact (smtExistsOfBinders_swap M b1 b2 tail body).symm
  | trans _h1 _h2 ih1 ih2 =>
      intro M
      exact (ih1 M).trans (ih2 M)

private theorem smtExistsOfBinders_dup
    (M : SmtModel) (b : QuantBinder) (tail : List QuantBinder)
    (body : SmtTerm) :
    __smtx_model_eval M (smtExistsOfBinders (b :: b :: tail) body) =
      __smtx_model_eval M (smtExistsOfBinders (b :: tail) body) := by
  rcases b with ⟨s, T⟩
  classical
  let rest := smtExistsOfBinders tail body
  let P : Prop :=
    ∃ v1 : SmtValue,
      __smtx_typeof_value v1 = T ∧
        __smtx_value_canonical v1 = true ∧
        ∃ v2 : SmtValue,
          __smtx_typeof_value v2 = T ∧
            __smtx_value_canonical v2 = true ∧
            __smtx_model_eval
                (native_model_push (native_model_push M s T v1) s T v2)
                rest =
              SmtValue.Boolean true
  let Q : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push M s T v) rest =
          SmtValue.Boolean true
  have hPQ : P ↔ Q := by
    constructor
    · intro hSat
      rcases hSat with ⟨v1, hv1, hc1, v2, hv2, hc2, hEval⟩
      exact ⟨v2, hv2, hc2, by
        simpa [native_model_push_same] using hEval⟩
    · intro hSat
      rcases hSat with ⟨v, hv, hc, hEval⟩
      exact ⟨v, hv, hc, v, hv, hc, by
        simpa [native_model_push_same] using hEval⟩
  have hPropEq : P = Q := propext hPQ
  simp [smtExistsOfBinders, __smtx_model_eval, P, Q, rest, hPropEq]

private theorem smtExistsOfBinders_append
    (xs ys : List QuantBinder) (body : SmtTerm) :
  smtExistsOfBinders xs (smtExistsOfBinders ys body) =
    smtExistsOfBinders (xs ++ ys) body :=
by
  induction xs with
  | nil =>
      simp [smtExistsOfBinders]
  | cons b xs ih =>
      simp [smtExistsOfBinders, ih]

private theorem smtExistsOfBinders_eval_append_singleton_of_mem
    (body : SmtTerm) {xs : List QuantBinder} {b : QuantBinder}
    (hMem : b ∈ xs) :
    ∀ M,
      __smtx_model_eval M (smtExistsOfBinders (xs ++ [b]) body) =
        __smtx_model_eval M (smtExistsOfBinders xs body) := by
  intro M
  have hPermXs : xs.Perm (b :: xs.erase b) :=
    List.perm_cons_erase hMem
  have hPermAppend :
      (xs ++ [b]).Perm (b :: b :: xs.erase b) := by
    have h1 : (xs ++ [b]).Perm ((b :: xs.erase b) ++ [b]) :=
      List.Perm.append_right [b] hPermXs
    have h2 :
        ((b :: xs.erase b) ++ [b]).Perm (b :: b :: xs.erase b) := by
      exact
        List.Perm.cons b
          (List.perm_append_comm (l₁ := xs.erase b) (l₂ := [b]))
    exact h1.trans h2
  exact
    (smtExistsOfBinders_eval_perm body hPermAppend M).trans
      ((smtExistsOfBinders_dup M b (xs.erase b) body).trans
        (smtExistsOfBinders_eval_perm body hPermXs M).symm)

private theorem smtExistsOfBinders_eval_append_of_subset
    (body : SmtTerm) {xs ys : List QuantBinder}
    (hSub : ∀ b, b ∈ ys -> b ∈ xs) :
    ∀ M,
      __smtx_model_eval M (smtExistsOfBinders (xs ++ ys) body) =
        __smtx_model_eval M (smtExistsOfBinders xs body) := by
  induction ys generalizing xs with
  | nil =>
      intro M
      simp
  | cons b ys ih =>
      intro M
      have hTailSub :
          ∀ c, c ∈ ys -> c ∈ xs ++ [b] := by
        intro c hMem
        exact List.mem_append.2 (Or.inl (hSub c (List.Mem.tail _ hMem)))
      have hTailEval :=
        ih (xs := xs ++ [b]) hTailSub M
      have hHeadEval :=
        smtExistsOfBinders_eval_append_singleton_of_mem
          body (xs := xs) (b := b) (hSub b (List.Mem.head _)) M
      simpa [List.append_assoc] using hTailEval.trans hHeadEval

private theorem eo_to_smt_exists_eq_smtExistsOfBinders
    {xs : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv xs vars) (body : SmtTerm) :
  __eo_to_smt_exists xs body =
    smtExistsOfBinders (vars.map EoVarKey.toSmt) body :=
by
  induction hEnv generalizing body with
  | nil =>
      simp [smtExistsOfBinders]
  | cons hTail ih =>
      rename_i s T env tailVars
      simp [smtExistsOfBinders, EoVarKey.toSmt, ih]

private theorem smtx_model_eval_eo_to_smt_exists_nested_of_subset
    (M : SmtModel) {xs ys : Term} {xVars yVars : List EoVarKey}
    (body : SmtTerm)
    (hX : EoVarEnv xs xVars)
    (hY : EoVarEnv ys yVars)
    (hSub :
      ∀ key, key ∈ yVars.map EoVarKey.toSmt ->
        key ∈ xVars.map EoVarKey.toSmt) :
  __smtx_model_eval M (__eo_to_smt_exists xs (__eo_to_smt_exists ys body)) =
    __smtx_model_eval M (__eo_to_smt_exists xs body) :=
by
  rw [eo_to_smt_exists_eq_smtExistsOfBinders hY body]
  rw [eo_to_smt_exists_eq_smtExistsOfBinders hX
    (smtExistsOfBinders (yVars.map EoVarKey.toSmt) body)]
  rw [eo_to_smt_exists_eq_smtExistsOfBinders hX body]
  rw [smtExistsOfBinders_append]
  exact smtExistsOfBinders_eval_append_of_subset body hSub M

private theorem model_agrees_except_on_env_bound_equiv
    {except bound bound' : List SmtVarKey} {M N : SmtModel}
    (hBound : ∀ key, key ∈ bound' ↔ key ∈ bound)
    (hAgree : model_agrees_except_on_env except bound M N) :
  model_agrees_except_on_env except bound' M N :=
by
  refine ⟨hAgree.globals, ?_⟩
  intro s T hAllowed
  apply hAgree.vars_eq
  rcases hAllowed with hInBound' | hNotExcept
  · exact Or.inl ((hBound (s, T)).1 hInBound')
  · exact Or.inr hNotExcept

private theorem smtx_model_eval_eo_to_smt_exists_eq_of_body_eval_eq_bound_aux
    {ys : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv ys vars)
    {except bound fullBound : List SmtVarKey}
    {M N : SmtModel} {body : SmtTerm}
    (hFull :
      ∀ key, key ∈ fullBound ↔
        key ∈ vars.map EoVarKey.toSmt ++ bound)
    (hBody :
      ∀ {M' N' : SmtModel},
        model_agrees_except_on_env except fullBound M' N' ->
          __smtx_model_eval M' body =
            __smtx_model_eval N' body)
    (hAgree : model_agrees_except_on_env except bound M N) :
  __smtx_model_eval M (__eo_to_smt_exists ys body) =
    __smtx_model_eval N (__eo_to_smt_exists ys body) :=
by
  induction hEnv generalizing bound M N body with
  | nil =>
      have hAgreeFull :
          model_agrees_except_on_env except fullBound M N :=
        model_agrees_except_on_env_bound_equiv
          (by
            intro key
            simpa using hFull key)
          hAgree
      simpa [__eo_to_smt_exists] using hBody hAgreeFull
  | cons hTail ih =>
      rename_i s T env tailVars
      let head : SmtVarKey := (s, __eo_to_smt_type T)
      change
        __smtx_model_eval M
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists env body)) =
          __smtx_model_eval N
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists env body))
      apply smtx_model_eval_exists_eq_of_body_eval_eq
      intro v
      have hPush :
          model_agrees_except_on_env except (head :: bound)
            (native_model_push M s (__eo_to_smt_type T) v)
            (native_model_push N s (__eo_to_smt_type T) v) := by
        simpa [head] using model_agrees_except_on_env_push_same hAgree
      have hFullTail :
          ∀ key, key ∈ fullBound ↔
            key ∈ tailVars.map EoVarKey.toSmt ++ head :: bound := by
        intro key
        constructor
        · intro hKey
          have hKey' := (hFull key).1 hKey
          simp [EoVarKey.toSmt, head, List.mem_append] at hKey' ⊢
          rcases hKey' with hHead | hTailMem | hBoundMem
          · exact Or.inr (Or.inl hHead)
          · exact Or.inl hTailMem
          · exact Or.inr (Or.inr hBoundMem)
        · intro hKey
          apply (hFull key).2
          simp [EoVarKey.toSmt, head, List.mem_append] at hKey ⊢
          rcases hKey with hTailMem | hHead | hBoundMem
          · exact Or.inr (Or.inl hTailMem)
          · exact Or.inl hHead
          · exact Or.inr (Or.inr hBoundMem)
      exact ih hFullTail hBody hPush

private theorem smtx_model_eval_eo_to_smt_exists_eq_of_body_eval_eq_bound
    {ys : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv ys vars)
    {except : List SmtVarKey}
    {M N : SmtModel} {body : SmtTerm}
    (hBody :
      ∀ {M' N' : SmtModel},
        model_agrees_except_on_env except
            (vars.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' body =
            __smtx_model_eval N' body)
    (hAgree : model_agrees_except_on_env except [] M N) :
  __smtx_model_eval M (__eo_to_smt_exists ys body) =
    __smtx_model_eval N (__eo_to_smt_exists ys body) :=
by
  exact
    smtx_model_eval_eo_to_smt_exists_eq_of_body_eval_eq_bound_aux
      hEnv
      (by intro key; simp)
      hBody hAgree

private theorem smtx_model_eval_none_eq (M N : SmtModel) :
  __smtx_model_eval M SmtTerm.None =
    __smtx_model_eval N SmtTerm.None :=
by
  rw [__smtx_model_eval.eq_def]
  rw [__smtx_model_eval.eq_def]

private theorem smtx_model_eval_qterm_eq_of_body_eval_eq_bound
    {Q ys F : Term} {vars : List EoVarKey}
    {except : List SmtVarKey} {M N : SmtModel}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hEnv : EoVarEnv ys vars)
    (hBody :
      ∀ {M' N' : SmtModel},
        model_agrees_except_on_env except
            (vars.map EoVarKey.toSmt) M' N' ->
          __smtx_model_eval M' (__eo_to_smt F) =
            __smtx_model_eval N' (__eo_to_smt F))
    (hAgree : model_agrees_except_on_env except [] M N) :
  __smtx_model_eval M (__eo_to_smt (qterm Q ys F)) =
    __smtx_model_eval N (__eo_to_smt (qterm Q ys F)) :=
by
  rcases hQ with hForall | hExists
  · subst Q
    cases hEnv with
    | nil =>
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval N SmtTerm.None
        exact smtx_model_eval_none_eq M N
    | cons hTail =>
        rename_i s T env tailVars
        have hBodyNot :
            ∀ {M' N' : SmtModel},
              model_agrees_except_on_env
                  except (((s, T) :: tailVars).map EoVarKey.toSmt)
                  M' N' ->
                __smtx_model_eval M'
                    (SmtTerm.not (__eo_to_smt F)) =
                  __smtx_model_eval N'
                    (SmtTerm.not (__eo_to_smt F)) := by
          intro M' N' hAgree'
          exact smtx_model_eval_not_eq_of_eval_eq (hBody hAgree')
        have hExistsEq :
            __smtx_model_eval M
                (__eo_to_smt_exists
                  (Term.Apply
                    (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String s) T)) env)
                  (SmtTerm.not (__eo_to_smt F))) =
              __smtx_model_eval N
                (__eo_to_smt_exists
                  (Term.Apply
                    (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String s) T)) env)
                  (SmtTerm.not (__eo_to_smt F))) :=
          smtx_model_eval_eo_to_smt_exists_eq_of_body_eval_eq_bound
            (EoVarEnv.cons (s := s) (T := T) hTail)
            hBodyNot hAgree
        change
          __smtx_model_eval M
              (SmtTerm.not
                (__eo_to_smt_exists
                  (Term.Apply
                    (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String s) T)) env)
                  (SmtTerm.not (__eo_to_smt F)))) =
            __smtx_model_eval N
              (SmtTerm.not
                (__eo_to_smt_exists
                  (Term.Apply
                    (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s) T)) env)
                  (SmtTerm.not (__eo_to_smt F))))
        exact smtx_model_eval_not_eq_of_eval_eq hExistsEq
  · subst Q
    cases hEnv with
    | nil =>
        change __smtx_model_eval M SmtTerm.None =
          __smtx_model_eval N SmtTerm.None
        exact smtx_model_eval_none_eq M N
    | cons hTail =>
        rename_i s T env tailVars
        have hExistsEq :
            __smtx_model_eval M
                (__eo_to_smt_exists
                  (Term.Apply
                    (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String s) T)) env)
                  (__eo_to_smt F)) =
              __smtx_model_eval N
                (__eo_to_smt_exists
                  (Term.Apply
                    (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String s) T)) env)
                  (__eo_to_smt F)) :=
          smtx_model_eval_eo_to_smt_exists_eq_of_body_eval_eq_bound
            (EoVarEnv.cons (s := s) (T := T) hTail)
            hBody hAgree
        change
          __smtx_model_eval M
              (__eo_to_smt_exists
                (Term.Apply
                  (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) env)
                (__eo_to_smt F)) =
            __smtx_model_eval N
              (__eo_to_smt_exists
                (Term.Apply
                  (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) env)
                (__eo_to_smt F))
        exact hExistsEq

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

private theorem eo_or_eq_true_cases_local (x y : Term) :
    __eo_or x y = Term.Boolean true ->
    x = Term.Boolean true ∨ y = Term.Boolean true := by
  intro h
  cases x <;> cases y <;> simp [__eo_or] at h ⊢
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp [native_or] at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hW : w1 = w2
    · subst w2
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at h
    · have hNumNe : Term.Numeral w1 ≠ Term.Numeral w2 := by
        intro hEq
        cases hEq
        exact hW rfl
      simp [__eo_requires, hNumNe, native_ite, native_teq] at h

private theorem eo_requires_true_nonstuck_eq
    {c r : Term}
    (hNonstuck : __eo_requires c (Term.Boolean true) r ≠ Term.Stuck) :
  __eo_requires c (Term.Boolean true) r = r :=
by
  by_cases hC : c = Term.Boolean true
  · subst c
    simp [__eo_requires, native_ite, native_teq, native_not]
  · exfalso
    apply hNonstuck
    simp [__eo_requires, native_ite, native_teq, hC]

private theorem eo_l1_get_unused_vars_nonstuck_eq
    {Q x F G : Term}
    (hG : G ≠ Term.Stuck) :
  __eo_l_1___get_unused_vars (Term.Apply (Term.Apply Q x) F) G =
    __eo_requires (__eo_eq F G) (Term.Boolean true)
      (__eo_list_setof Term.__eo_List_cons x) :=
by
  cases G <;> simp [__eo_l_1___get_unused_vars] at hG ⊢

private theorem eo_eq_self_true
    {t : Term}
    (hT : t ≠ Term.Stuck) :
  __eo_eq t t = Term.Boolean true :=
by
  cases t <;> simp [__eo_eq, native_teq] at hT ⊢

private theorem eo_eq_true_eq
    {a b : Term}
    (hEq : __eo_eq a b = Term.Boolean true) :
  a = b :=
by
  have hEqSymm : b = a := by
    cases a <;> cases b <;> simp [__eo_eq, native_teq] at hEq ⊢
    all_goals exact hEq
  exact hEqSymm.symm

private theorem eo_eq_false_of_ne_local
    {x y : Term}
    (hNe : x ≠ y)
    (hX : x ≠ Term.Stuck)
    (hY : y ≠ Term.Stuck) :
  __eo_eq x y = Term.Boolean false :=
by
  have hNeSymm : y ≠ x := by
    intro h
    exact hNe h.symm
  cases x <;> cases y <;>
    simp [__eo_eq, native_teq, hNe, hNeSymm] at hX hY ⊢
  all_goals exact False.elim (hNe rfl)

private theorem eo_prepend_if_true_eq_local
    {f x res : Term}
    (hF : f ≠ Term.Stuck)
    (hX : x ≠ Term.Stuck)
    (hRes : res ≠ Term.Stuck) :
  __eo_prepend_if (Term.Boolean true) f x res =
    Term.Apply (Term.Apply f x) res :=
by
  cases f <;> cases x <;> cases res <;>
    simp [__eo_prepend_if] at hF hX hRes ⊢

private theorem eo_prepend_if_false_eq_local
    {f x res : Term}
    (hF : f ≠ Term.Stuck)
    (hX : x ≠ Term.Stuck)
    (hRes : res ≠ Term.Stuck) :
  __eo_prepend_if (Term.Boolean false) f x res = res :=
by
  cases f <;> cases x <;> cases res <;>
    simp [__eo_prepend_if] at hF hX hRes ⊢

private theorem eo_var_env_erase_rec_eq_self_of_not_mem :
    ∀ {env : Term} {vars : List EoVarKey}
      (hEnv : EoVarEnv env vars)
      {s : native_String} {T : Term},
      (s, T) ∉ vars ->
        __eo_list_erase_rec env (Term.Var (Term.String s) T) = env
  | _, _, EoVarEnv.nil, s, T, _ =>
      by
        simp [__eo_list_erase_rec]
  | _, _, EoVarEnv.cons (s := sHead) (T := THead)
      (vars := tailVars) hTail,
      s, T, hNotMem =>
      by
        by_cases hVarEq :
            Term.Var (Term.String sHead) THead =
              Term.Var (Term.String s) T
        · injection hVarEq with hName hTy
          injection hName with hString
          cases hString
          cases hTy
          exact False.elim (hNotMem (List.Mem.head _))
        · have hVarEqSymm :
              Term.Var (Term.String s) T ≠
                Term.Var (Term.String sHead) THead := by
            intro h
            exact hVarEq h.symm
          have hTailNotMem : (s, T) ∉ tailVars := by
            intro hMem
            exact hNotMem (List.Mem.tail _ hMem)
          have hTailErase :=
            eo_var_env_erase_rec_eq_self_of_not_mem hTail hTailNotMem
          simp [__eo_list_erase_rec, __eo_eq, native_teq,
            hVarEqSymm, __eo_ite, native_ite, hTailErase,
            __eo_mk_apply, hTail.ne_stuck]

private theorem eo_var_env_erase_rec_mem_subset :
    ∀ {env : Term} {vars : List EoVarKey}
      (hEnv : EoVarEnv env vars)
      {sErase : native_String} {TErase : Term}
      {eraseVars : List EoVarKey},
      EoVarEnv
        (__eo_list_erase_rec env
          (Term.Var (Term.String sErase) TErase))
        eraseVars ->
        ∀ key, key ∈ eraseVars -> key ∈ vars
  | _, _, EoVarEnv.nil, sErase, TErase, eraseVars, hErase =>
      by
        intro key hMem
        have hNil : EoVarEnv
            (__eo_list_erase_rec Term.__eo_List_nil
              (Term.Var (Term.String sErase) TErase)) [] := by
          simpa [__eo_list_erase_rec] using EoVarEnv.nil
        have hEq : eraseVars = [] :=
          EoVarEnv.vars_eq_of_same_env hErase hNil
        subst eraseVars
        cases hMem
  | _, _, EoVarEnv.cons (s := sHead) (T := THead)
      (env := envTail) (vars := tailVars) hTail,
      sErase, TErase, eraseVars, hErase =>
      by
        intro key hMem
        by_cases hVarEq :
            Term.Var (Term.String sHead) THead =
              Term.Var (Term.String sErase) TErase
        · have hTailEnv :
              EoVarEnv
                (__eo_list_erase_rec
                  (Term.Apply
                    (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String sHead) THead))
                    envTail)
                  (Term.Var (Term.String sErase) TErase))
                tailVars := by
            simpa [__eo_list_erase_rec, __eo_eq, native_teq,
              hVarEq, __eo_ite, native_ite] using hTail
          have hEq : eraseVars = tailVars :=
            EoVarEnv.vars_eq_of_same_env hErase hTailEnv
          subst eraseVars
          exact List.Mem.tail _ hMem
        · have hVarEqSymm :
              Term.Var (Term.String sErase) TErase ≠
                Term.Var (Term.String sHead) THead := by
            intro h
            exact hVarEq h.symm
          rcases EoVarEnv.erase_rec_var sErase TErase hTail with
            ⟨tailEraseVars, hTailErase⟩
          have hOut :
              EoVarEnv
                (__eo_list_erase_rec
                  (Term.Apply
                    (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String sHead) THead))
                    envTail)
                  (Term.Var (Term.String sErase) TErase))
                ((sHead, THead) :: tailEraseVars) := by
            simpa [__eo_list_erase_rec, __eo_eq, native_teq,
              hVarEq, hVarEqSymm, __eo_ite, native_ite] using
              EoVarEnv.cons_mk_apply (s := sHead) (T := THead)
                hTailErase
          have hEq : eraseVars = (sHead, THead) :: tailEraseVars :=
            EoVarEnv.vars_eq_of_same_env hErase hOut
          subst eraseVars
          cases hMem with
          | head =>
              exact List.Mem.head _
          | tail _ hTailMem =>
              exact List.Mem.tail _
                (eo_var_env_erase_rec_mem_subset hTail hTailErase
                  key hTailMem)

private theorem eo_var_env_erase_all_rec_mem_subset :
    ∀ {env : Term} {vars : List EoVarKey}
      (hEnv : EoVarEnv env vars)
      {sErase : native_String} {TErase : Term}
      {eraseVars : List EoVarKey},
      EoVarEnv
        (__eo_list_erase_all_rec env
          (Term.Var (Term.String sErase) TErase))
        eraseVars ->
        ∀ key, key ∈ eraseVars -> key ∈ vars
  | _, _, EoVarEnv.nil, sErase, TErase, eraseVars, hErase =>
      by
        intro key hMem
        have hNil : EoVarEnv
            (__eo_list_erase_all_rec Term.__eo_List_nil
              (Term.Var (Term.String sErase) TErase)) [] := by
          simpa [__eo_list_erase_all_rec] using EoVarEnv.nil
        have hEq : eraseVars = [] :=
          EoVarEnv.vars_eq_of_same_env hErase hNil
        subst eraseVars
        cases hMem
  | _, _, EoVarEnv.cons (s := sHead) (T := THead)
      (env := envTail) (vars := tailVars) hTail,
      sErase, TErase, eraseVars, hErase =>
      by
        intro key hMem
        by_cases hVarEq :
            Term.Var (Term.String sErase) TErase =
              Term.Var (Term.String sHead) THead
        · cases hVarEq
          rcases EoVarEnv.erase_all_rec_var sHead THead hTail with
            ⟨tailEraseVars, hTailErase⟩
          have hTailEraseNe := hTailErase.ne_stuck
          have hPrep :
              __eo_prepend_if (Term.Boolean false) Term.__eo_List_cons
                  (Term.Var (Term.String sHead) THead)
                  (__eo_list_erase_all_rec envTail
                    (Term.Var (Term.String sHead) THead)) =
                __eo_list_erase_all_rec envTail
                  (Term.Var (Term.String sHead) THead) :=
            eo_prepend_if_false_eq_local
              (by intro h; cases h) (by intro h; cases h) hTailEraseNe
          have hOut :
              EoVarEnv
                (__eo_list_erase_all_rec
                  (Term.Apply
                    (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String sHead) THead))
                    envTail)
                  (Term.Var (Term.String sHead) THead))
                tailEraseVars := by
            simpa [__eo_list_erase_all_rec, __eo_eq, native_teq,
              __eo_not, native_not, __eo_prepend_if, hPrep] using
              hTailErase
          have hEq : eraseVars = tailEraseVars :=
            EoVarEnv.vars_eq_of_same_env hErase hOut
          subst eraseVars
          exact List.Mem.tail _
            (eo_var_env_erase_all_rec_mem_subset hTail hTailErase
              key hMem)
        · have hVarEqSymm :
              Term.Var (Term.String sHead) THead ≠
                Term.Var (Term.String sErase) TErase := by
            intro h
            exact hVarEq h.symm
          rcases EoVarEnv.erase_all_rec_var sErase TErase hTail with
            ⟨tailEraseVars, hTailErase⟩
          have hTailEraseNe := hTailErase.ne_stuck
          have hPrep :
              __eo_prepend_if (Term.Boolean true) Term.__eo_List_cons
                  (Term.Var (Term.String sHead) THead)
                  (__eo_list_erase_all_rec envTail
                    (Term.Var (Term.String sErase) TErase)) =
                Term.Apply
                  (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String sHead) THead))
                  (__eo_list_erase_all_rec envTail
                    (Term.Var (Term.String sErase) TErase)) :=
            eo_prepend_if_true_eq_local
              (by intro h; cases h) (by intro h; cases h) hTailEraseNe
          have hOut :
              EoVarEnv
                (__eo_list_erase_all_rec
                  (Term.Apply
                    (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String sHead) THead))
                    envTail)
                  (Term.Var (Term.String sErase) TErase))
                ((sHead, THead) :: tailEraseVars) := by
            simpa [__eo_list_erase_all_rec, __eo_eq, native_teq,
              hVarEq, hVarEqSymm, __eo_not, native_not,
              __eo_prepend_if, hPrep] using
              EoVarEnv.cons (s := sHead) (T := THead) hTailErase
          have hEq : eraseVars = (sHead, THead) :: tailEraseVars :=
            EoVarEnv.vars_eq_of_same_env hErase hOut
          subst eraseVars
          cases hMem with
          | head =>
              exact List.Mem.head _
          | tail _ hTailMem =>
              exact List.Mem.tail _
                (eo_var_env_erase_all_rec_mem_subset hTail hTailErase
                  key hTailMem)

private theorem eo_var_env_setof_rec_mem_subset :
    ∀ {env : Term} {vars setVars : List EoVarKey}
      (hEnv : EoVarEnv env vars),
      EoVarEnv (__eo_list_setof_rec env) setVars ->
        ∀ key, key ∈ setVars -> key ∈ vars
  | _, _, setVars, EoVarEnv.nil, hSet =>
      by
        intro key hMem
        have hNil : EoVarEnv (__eo_list_setof_rec Term.__eo_List_nil) [] := by
          simpa [__eo_list_setof_rec] using EoVarEnv.nil
        have hEq : setVars = [] :=
          EoVarEnv.vars_eq_of_same_env hSet hNil
        subst setVars
        cases hMem
  | _, _, setVars, EoVarEnv.cons (s := s) (T := T)
      (env := envTail) (vars := tailVars) hTail,
      hSet =>
      by
        intro key hMem
        rcases EoVarEnv.setof_rec hTail with
          ⟨tailSetVars, hTailSet⟩
        rcases EoVarEnv.erase_all_rec_var s T hTailSet with
          ⟨eraseVars, hErase⟩
        have hOut :
            EoVarEnv
              (__eo_list_setof_rec
                (Term.Apply
                  (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T))
                  envTail))
              ((s, T) :: eraseVars) := by
          simpa [__eo_list_setof_rec] using
            EoVarEnv.cons_mk_apply (s := s) (T := T) hErase
        have hEq : setVars = (s, T) :: eraseVars :=
          EoVarEnv.vars_eq_of_same_env hSet hOut
        subst setVars
        cases hMem with
        | head =>
            exact List.Mem.head _
        | tail _ hEraseMem =>
            have hTailSetMem :
                key ∈ tailSetVars :=
              eo_var_env_erase_all_rec_mem_subset hTailSet hErase
                key hEraseMem
            exact List.Mem.tail _
              (eo_var_env_setof_rec_mem_subset hTail hTailSet
                key hTailSetMem)

private theorem eo_var_env_setof_mem_subset
    {env : Term} {vars setVars : List EoVarKey}
    (hEnv : EoVarEnv env vars)
    (hSet : EoVarEnv
      (__eo_list_setof Term.__eo_List_cons env) setVars) :
  ∀ key, key ∈ setVars -> key ∈ vars :=
by
  have hList := hEnv.is_list
  rcases EoVarEnv.setof_rec hEnv with ⟨recVars, hRec⟩
  have hTop :
      EoVarEnv (__eo_list_setof Term.__eo_List_cons env) recVars := by
    simpa [__eo_list_setof, __eo_requires, hList, native_ite, native_teq,
      native_not] using hRec
  have hEq : setVars = recVars :=
    EoVarEnv.vars_eq_of_same_env hSet hTop
  subst setVars
  exact eo_var_env_setof_rec_mem_subset hEnv hRec

private theorem eo_var_env_get_elements_rec :
    ∀ {env : Term} {vars : List EoVarKey},
      EoVarEnv env vars ->
        __eo_get_elements_rec env = env
  | _, _, EoVarEnv.nil =>
      by
        simp [__eo_get_elements_rec]
  | _, _, EoVarEnv.cons hTail =>
      by
        have hTailGet := eo_var_env_get_elements_rec hTail
        simp [__eo_get_elements_rec, __eo_mk_apply, hTailGet,
          hTail.ne_stuck]

private theorem eo_minclude_rec_true_flag_true
    {y z orig : Term} :
    y ≠ Term.Stuck ->
    z ≠ Term.Stuck ->
    orig ≠ Term.Stuck ->
    __eo_list_minclude_rec y z (__eo_not (__eo_eq y orig)) =
      Term.Boolean true ->
    __eo_not (__eo_eq y orig) = Term.Boolean true := by
  intro hY hZ hOrig hIncl
  by_cases hEq : y = orig
  · have hEqTerm : __eo_eq y orig = Term.Boolean true := by
      subst orig
      exact eo_eq_self_true hY
    have hFlag :
        __eo_not (__eo_eq y orig) = Term.Boolean false := by
      simp [__eo_not, hEqTerm, native_not]
    rw [hFlag] at hIncl
    cases y <;> cases z <;> simp [__eo_list_minclude_rec] at hIncl hY hZ
  · have hEqTerm : __eo_eq y orig = Term.Boolean false :=
      eo_eq_false_of_ne_local hEq hY hOrig
    simp [__eo_not, hEqTerm, native_not]

private theorem eo_var_env_minclude_rec_mem_subset :
    ∀ {a b : Term} {aVars bVars : List EoVarKey}
      (hA : EoVarEnv a aVars)
      (hB : EoVarEnv b bVars),
      __eo_list_minclude_rec a b (Term.Boolean true) =
        Term.Boolean true ->
        ∀ key, key ∈ bVars -> key ∈ aVars
  | _, _, _, _, hA, EoVarEnv.nil, _ =>
      by
        intro key hMem
        cases hMem
  | a, _, aVars, _, hA,
      EoVarEnv.cons (s := s) (T := T) (env := bTail)
        (vars := bTailVars) hBTail,
      hIncl =>
      by
        intro key hMem
        let erased := __eo_list_erase_rec a (Term.Var (Term.String s) T)
        rcases EoVarEnv.erase_rec_var s T hA with
          ⟨erasedVars, hErased⟩
        have hErased' : EoVarEnv erased erasedVars := by
          simpa [erased] using hErased
        have hInclRaw :
            __eo_list_minclude_rec erased bTail
                (__eo_not (__eo_eq erased a)) =
              Term.Boolean true := by
          simpa [__eo_list_minclude_rec, erased, hA.ne_stuck] using hIncl
        have hFlag :
            __eo_not (__eo_eq erased a) = Term.Boolean true :=
          eo_minclude_rec_true_flag_true
            hErased'.ne_stuck hBTail.ne_stuck hA.ne_stuck hInclRaw
        have hTailIncl :
            __eo_list_minclude_rec erased bTail (Term.Boolean true) =
              Term.Boolean true := by
          rw [hFlag] at hInclRaw
          exact hInclRaw
        cases hMem with
        | head =>
            by_cases hMemA : (s, T) ∈ aVars
            · exact hMemA
            · have hEraseEq :
                  __eo_list_erase_rec a (Term.Var (Term.String s) T) =
                    a :=
                eo_var_env_erase_rec_eq_self_of_not_mem hA hMemA
              have hEqTerm : __eo_eq erased a = Term.Boolean true := by
                simpa [erased, hEraseEq] using eo_eq_self_true hA.ne_stuck
              simp [__eo_not, hEqTerm, native_not] at hFlag
        | tail _ hTailMem =>
            have hErasedMem :
                key ∈ erasedVars :=
              eo_var_env_minclude_rec_mem_subset hErased' hBTail
                hTailIncl key hTailMem
            exact
              eo_var_env_erase_rec_mem_subset hA hErased key hErasedMem

private theorem eo_var_env_minclude_mem_subset
    {a b : Term} {aVars bVars : List EoVarKey}
    (hA : EoVarEnv a aVars)
    (hB : EoVarEnv b bVars)
    (hIncl :
      __eo_list_minclude Term.__eo_List_cons a b =
        Term.Boolean true) :
  ∀ key, key ∈ bVars -> key ∈ aVars :=
by
  have hAList := hA.is_list
  have hBList := hB.is_list
  have hAGet := eo_var_env_get_elements_rec hA
  have hBGet := eo_var_env_get_elements_rec hB
  have hInclRec :
      __eo_list_minclude_rec a b (Term.Boolean true) =
        Term.Boolean true := by
    simpa [__eo_list_minclude, __eo_requires, hAList, hBList, hAGet, hBGet,
      native_ite, native_teq, native_not] using hIncl
  exact eo_var_env_minclude_rec_mem_subset hA hB hInclRec

private theorem eo_var_env_diff_rec_mem_or :
    ∀ {a b : Term} {aVars bVars diffVars : List EoVarKey}
      (hA : EoVarEnv a aVars)
      (hB : EoVarEnv b bVars),
      EoVarEnv (__eo_list_diff_rec a b) diffVars ->
        ∀ key, key ∈ aVars -> key ∈ bVars ∨ key ∈ diffVars
  | _, _, _, _, _, EoVarEnv.nil, hB, hDiff =>
      by
        intro key hMem
        cases hMem
  | _, b, _, bVars, diffVars,
      EoVarEnv.cons (s := s) (T := T) (env := aTail) hTail,
      hB, hDiff =>
      by
        intro key hMem
        let erased := __eo_list_erase_rec b (Term.Var (Term.String s) T)
        rcases EoVarEnv.erase_rec_var s T hB with
          ⟨erasedVars, hErased⟩
        have hErased' : EoVarEnv erased erasedVars := by
          simpa [erased] using hErased
        rcases EoVarEnv.diff_rec hTail hErased' with
          ⟨tailDiffVars, hTailDiff⟩
        by_cases hEq : erased = b
        · have hOut :
              EoVarEnv
                (__eo_list_diff_rec
                  (Term.Apply
                    (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String s) T))
                    aTail)
                  b)
                ((s, T) :: tailDiffVars) := by
            have hCond : __eo_eq erased b = Term.Boolean true := by
              subst erased
              rw [hEq]
              exact eo_eq_self_true hB.ne_stuck
            have hPrep :
                __eo_prepend_if (Term.Boolean true) Term.__eo_List_cons
                    (Term.Var (Term.String s) T)
                    (__eo_list_diff_rec aTail erased) =
                  Term.Apply
                    (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T))
                    (__eo_list_diff_rec aTail erased) := by
              exact
                eo_prepend_if_true_eq_local
                  (by intro h; cases h) (by intro h; cases h)
                  hTailDiff.ne_stuck
            have hUnfold :
                __eo_list_diff_rec
                    (Term.Apply
                      (Term.Apply Term.__eo_List_cons
                        (Term.Var (Term.String s) T))
                      aTail)
                    b =
                  __eo_prepend_if (__eo_eq erased b)
                    Term.__eo_List_cons
                    (Term.Var (Term.String s) T)
                    (__eo_list_diff_rec aTail erased) := by
              cases hB <;> simp [__eo_list_diff_rec, erased]
            rw [hUnfold, hCond, hPrep]
            exact EoVarEnv.cons (s := s) (T := T) hTailDiff
          have hVarsEq :
              diffVars = (s, T) :: tailDiffVars :=
            EoVarEnv.vars_eq_of_same_env hDiff hOut
          subst diffVars
          cases hMem with
          | head =>
              exact Or.inr (List.Mem.head _)
          | tail _ hTailMem =>
              rcases
                eo_var_env_diff_rec_mem_or hTail hErased'
                  hTailDiff key hTailMem with
                hMemErased | hMemDiff
              · exact Or.inl
                  (eo_var_env_erase_rec_mem_subset hB hErased
                    key hMemErased)
              · exact Or.inr (List.Mem.tail _ hMemDiff)
        · have hHeadMem : (s, T) ∈ bVars := by
            by_cases hMemB : (s, T) ∈ bVars
            · exact hMemB
            · have hEraseEq :
                __eo_list_erase_rec b (Term.Var (Term.String s) T) = b :=
                eo_var_env_erase_rec_eq_self_of_not_mem hB hMemB
              exact False.elim (hEq hEraseEq)
          have hOut :
              EoVarEnv
                (__eo_list_diff_rec
                  (Term.Apply
                    (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String s) T))
                    aTail)
                  b)
                tailDiffVars := by
            have hEqSymm : b ≠ erased := by
              intro h
              exact hEq h.symm
            have hCond : __eo_eq erased b = Term.Boolean false :=
              eo_eq_false_of_ne_local hEq hErased'.ne_stuck hB.ne_stuck
            have hPrep :
                __eo_prepend_if (Term.Boolean false) Term.__eo_List_cons
                    (Term.Var (Term.String s) T)
                    (__eo_list_diff_rec aTail erased) =
                  __eo_list_diff_rec aTail erased := by
              exact
                eo_prepend_if_false_eq_local
                  (by intro h; cases h) (by intro h; cases h)
                  hTailDiff.ne_stuck
            have hUnfold :
                __eo_list_diff_rec
                    (Term.Apply
                      (Term.Apply Term.__eo_List_cons
                        (Term.Var (Term.String s) T))
                      aTail)
                    b =
                  __eo_prepend_if (__eo_eq erased b)
                    Term.__eo_List_cons
                    (Term.Var (Term.String s) T)
                    (__eo_list_diff_rec aTail erased) := by
              cases hB <;> simp [__eo_list_diff_rec, erased]
            rw [hUnfold, hCond, hPrep]
            exact hTailDiff
          have hVarsEq : diffVars = tailDiffVars :=
            EoVarEnv.vars_eq_of_same_env hDiff hOut
          subst diffVars
          cases hMem with
          | head =>
              exact Or.inl hHeadMem
          | tail _ hTailMem =>
              rcases
                eo_var_env_diff_rec_mem_or hTail hErased'
                  hTailDiff key hTailMem with
                hMemErased | hMemDiff
              · exact Or.inl
                  (eo_var_env_erase_rec_mem_subset hB hErased
                    key hMemErased)
              · exact Or.inr hMemDiff

private theorem eo_var_env_diff_mem_or
    {a b : Term} {aVars bVars diffVars : List EoVarKey}
    (hA : EoVarEnv a aVars)
    (hB : EoVarEnv b bVars)
    (hDiff :
      EoVarEnv (__eo_list_diff Term.__eo_List_cons a b) diffVars) :
  ∀ key, key ∈ aVars -> key ∈ bVars ∨ key ∈ diffVars :=
by
  rcases EoVarEnv.diff_rec hA hB with ⟨knownDiffVars, hKnownDiffRec⟩
  have hAList := hA.is_list
  have hBList := hB.is_list
  have hKnownDiff :
      EoVarEnv (__eo_list_diff Term.__eo_List_cons a b)
        knownDiffVars := by
    simpa [__eo_list_diff, __eo_requires, hAList, hBList, native_ite,
      native_teq, native_not] using hKnownDiffRec
  have hVarsEq : diffVars = knownDiffVars :=
    EoVarEnv.vars_eq_of_same_env hDiff hKnownDiff
  subst diffVars
  exact eo_var_env_diff_rec_mem_or hA hB hKnownDiffRec

private theorem eo_ite_nonstuck_guard_cases
    {c t e : Term}
    (hNonstuck : __eo_ite c t e ≠ Term.Stuck) :
  c = Term.Boolean true ∨ c = Term.Boolean false :=
by
  cases c <;> simp [__eo_ite, native_ite, native_teq] at hNonstuck ⊢

private theorem get_unused_vars_same_quant_body_eq
    {Q x F y : Term}
    (hQ : Q ≠ Term.Stuck)
    (hF : F ≠ Term.Stuck) :
  __get_unused_vars (Term.Apply (Term.Apply Q x) F)
      (Term.Apply (Term.Apply Q y) F) =
    __eo_requires
      (__eo_list_minclude Term.__eo_List_cons
        (__eo_list_setof Term.__eo_List_cons x) y)
      (Term.Boolean true)
      (__eo_list_diff Term.__eo_List_cons
        (__eo_list_setof Term.__eo_List_cons x) y) :=
by
  have hQEq : __eo_eq Q Q = Term.Boolean true :=
    eo_eq_self_true hQ
  have hFEq : __eo_eq F F = Term.Boolean true :=
    eo_eq_self_true hF
  simp [__get_unused_vars, hQEq, hFEq, __eo_and, __eo_ite, native_and,
    native_ite, native_teq]

private theorem eo_var_env_of_l1_get_unused_vars_ne_stuck
    {Q x F G : Term} {xVars : List EoVarKey}
    (hX : EoVarEnv x xVars)
    (hNonstuck :
      __eo_l_1___get_unused_vars (Term.Apply (Term.Apply Q x) F) G ≠
        Term.Stuck) :
  ∃ vars,
    EoVarEnv
      (__eo_l_1___get_unused_vars (Term.Apply (Term.Apply Q x) F) G)
      vars :=
by
  rcases EoVarEnv.setof hX with ⟨setVars, hSet⟩
  by_cases hG : G = Term.Stuck
  · subst G
    exfalso
    exact hNonstuck (by simp [__eo_l_1___get_unused_vars])
  · have hL1Eq :=
      eo_l1_get_unused_vars_nonstuck_eq
        (Q := Q) (x := x) (F := F) hG
    refine ⟨setVars, ?_⟩
    have hReqNonstuck :
        __eo_requires (__eo_eq F G) (Term.Boolean true)
            (__eo_list_setof Term.__eo_List_cons x) ≠
          Term.Stuck := by
      intro hReq
      apply hNonstuck
      rw [hL1Eq, hReq]
    have hReqEq := eo_requires_true_nonstuck_eq hReqNonstuck
    rw [hL1Eq, hReqEq]
    exact hSet

private theorem eo_var_env_of_get_unused_vars_same_quant_body_ne_stuck
    {Q x F y : Term} {xVars yVars : List EoVarKey}
    (hQ : Q ≠ Term.Stuck)
    (hF : F ≠ Term.Stuck)
    (hX : EoVarEnv x xVars)
    (hY : EoVarEnv y yVars)
    (hNonstuck :
      __get_unused_vars (Term.Apply (Term.Apply Q x) F)
          (Term.Apply (Term.Apply Q y) F) ≠
        Term.Stuck) :
  ∃ vars,
    EoVarEnv
      (__get_unused_vars (Term.Apply (Term.Apply Q x) F)
        (Term.Apply (Term.Apply Q y) F))
      vars :=
by
  rcases EoVarEnv.setof hX with ⟨setVars, hSet⟩
  rcases EoVarEnv.diff hSet hY with ⟨diffVars, hDiff⟩
  have hGetEq :=
    get_unused_vars_same_quant_body_eq
      (Q := Q) (x := x) (F := F) (y := y) hQ hF
  refine ⟨diffVars, ?_⟩
  have hReqNonstuck :
      __eo_requires
          (__eo_list_minclude Term.__eo_List_cons
            (__eo_list_setof Term.__eo_List_cons x) y)
          (Term.Boolean true)
          (__eo_list_diff Term.__eo_List_cons
            (__eo_list_setof Term.__eo_List_cons x) y) ≠
        Term.Stuck := by
    intro hReq
    apply hNonstuck
    rw [hGetEq, hReq]
  have hReqEq := eo_requires_true_nonstuck_eq hReqNonstuck
  rw [hGetEq, hReqEq]
  exact hDiff

private theorem contains_atomic_term_list_free_rec_false_except_ne_stuck
    {t except bound : Term}
    (hNoFree :
      __contains_atomic_term_list_free_rec t except bound =
        Term.Boolean false) :
  except ≠ Term.Stuck :=
by
  intro hExcept
  subst except
  cases t <;> simp [__contains_atomic_term_list_free_rec] at hNoFree

private theorem eo_var_env_of_get_unused_vars_same_quant_body_of_contains_false
    {Q x F y : Term} {xVars yVars : List EoVarKey}
    (hQ : Q ≠ Term.Stuck)
    (hF : F ≠ Term.Stuck)
    (hX : EoVarEnv x xVars)
    (hY : EoVarEnv y yVars)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply Q y) F)
          (__get_unused_vars (Term.Apply (Term.Apply Q x) F)
            (Term.Apply (Term.Apply Q y) F))
          Term.__eo_List_nil =
        Term.Boolean false) :
  ∃ vars,
    EoVarEnv
      (__get_unused_vars (Term.Apply (Term.Apply Q x) F)
        (Term.Apply (Term.Apply Q y) F))
      vars :=
by
  have hGetNonstuck :
      __get_unused_vars (Term.Apply (Term.Apply Q x) F)
          (Term.Apply (Term.Apply Q y) F) ≠
        Term.Stuck :=
    contains_atomic_term_list_free_rec_false_except_ne_stuck hNoFree
  exact
    eo_var_env_of_get_unused_vars_same_quant_body_ne_stuck
      hQ hF hX hY hGetNonstuck

private theorem eo_var_env_of_get_unused_vars_quant_branch_of_contains_false
    {Q x F Q₂ y F₂ : Term}
    {xVars : List EoVarKey}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hX : EoVarEnv x xVars)
    (hGTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply Q₂ y) F₂))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply Q₂ y) F₂)
          (__get_unused_vars (Term.Apply (Term.Apply Q x) F)
            (Term.Apply (Term.Apply Q₂ y) F₂))
          Term.__eo_List_nil =
        Term.Boolean false) :
  ∃ vars,
    EoVarEnv
      (__get_unused_vars (Term.Apply (Term.Apply Q x) F)
        (Term.Apply (Term.Apply Q₂ y) F₂))
      vars :=
by
  have hGetNonstuck :
      __get_unused_vars (Term.Apply (Term.Apply Q x) F)
          (Term.Apply (Term.Apply Q₂ y) F₂) ≠
        Term.Stuck :=
    contains_atomic_term_list_free_rec_false_except_ne_stuck hNoFree
  have hIteNonstuck :
      __eo_ite
          (__eo_and (__eo_eq Q Q₂) (__eo_eq F F₂))
          (__eo_requires
            (__eo_list_minclude Term.__eo_List_cons
              (__eo_list_setof Term.__eo_List_cons x) y)
            (Term.Boolean true)
            (__eo_list_diff Term.__eo_List_cons
              (__eo_list_setof Term.__eo_List_cons x) y))
          (__eo_l_1___get_unused_vars
            (Term.Apply (Term.Apply Q x) F)
            (Term.Apply (Term.Apply Q₂ y) F₂)) ≠
        Term.Stuck := by
    intro hStuck
    apply hGetNonstuck
    simpa [__get_unused_vars] using hStuck
  rcases eo_ite_nonstuck_guard_cases hIteNonstuck with hGuard | hGuard
  · have hParts := eo_and_eq_true_cases hGuard
    have hQEq : Q = Q₂ := eo_eq_true_eq hParts.1
    have hFEqTrue : __eo_eq F F₂ = Term.Boolean true := hParts.2
    have hFEq : F = F₂ := eo_eq_true_eq hFEqTrue
    subst Q₂
    subst F₂
    have hQNonstuck : Q ≠ Term.Stuck := by
      rcases hQ with hForall | hExists
      · rw [hForall]
        intro h
        cases h
      · rw [hExists]
        intro h
        cases h
    have hFNonstuck : F ≠ Term.Stuck := by
      intro hF
      subst F
      simp [__eo_eq] at hFEqTrue
    rcases eo_var_env_of_quant_has_smt_translation hQ hGTrans with
      ⟨yVars, hY⟩
    exact
      eo_var_env_of_get_unused_vars_same_quant_body_of_contains_false
        hQNonstuck hFNonstuck hX hY hNoFree
  · have hGetEqFallback :
        __get_unused_vars (Term.Apply (Term.Apply Q x) F)
            (Term.Apply (Term.Apply Q₂ y) F₂) =
          __eo_l_1___get_unused_vars
            (Term.Apply (Term.Apply Q x) F)
            (Term.Apply (Term.Apply Q₂ y) F₂) := by
      simp [__get_unused_vars, hGuard, __eo_ite, native_ite, native_teq]
    have hFallbackNonstuck :
        __eo_l_1___get_unused_vars
            (Term.Apply (Term.Apply Q x) F)
            (Term.Apply (Term.Apply Q₂ y) F₂) ≠
          Term.Stuck := by
      intro hStuck
      apply hGetNonstuck
      rw [hGetEqFallback, hStuck]
    rcases
      eo_var_env_of_l1_get_unused_vars_ne_stuck hX hFallbackNonstuck with
      ⟨vars, hEnv⟩
    exact ⟨vars, by rw [hGetEqFallback]; exact hEnv⟩

private theorem get_unused_vars_fallback_eq_of_not_quant_branch
    {Q x F G : Term}
    (hG : G ≠ Term.Stuck)
    (hNotQuant :
      ∀ Q₂ y F₂,
        G ≠ Term.Apply (Term.Apply Q₂ y) F₂) :
  __get_unused_vars (Term.Apply (Term.Apply Q x) F) G =
    __eo_l_1___get_unused_vars (Term.Apply (Term.Apply Q x) F) G :=
by
  cases G <;> simp [__get_unused_vars] at hG hNotQuant ⊢
  case Apply f a =>
    cases f <;> simp at hNotQuant ⊢
    all_goals
      exfalso
      exact hNotQuant _ _ rfl

private theorem eo_var_env_of_get_unused_vars_of_contains_false
    {Q x F G : Term} {xVars : List EoVarKey}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hX : EoVarEnv x xVars)
    (hGTrans : eoHasSmtTranslation G)
    (hNoFree :
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (Term.Apply (Term.Apply Q x) F) G)
          Term.__eo_List_nil =
        Term.Boolean false) :
  ∃ vars,
    EoVarEnv
      (__get_unused_vars (Term.Apply (Term.Apply Q x) F) G)
      vars :=
by
  by_cases hShape :
      ∃ Q₂ y F₂,
        G = Term.Apply (Term.Apply Q₂ y) F₂
  · rcases hShape with ⟨Q₂, y, F₂, rfl⟩
    exact
      eo_var_env_of_get_unused_vars_quant_branch_of_contains_false
        hQ hX hGTrans hNoFree
  · have hGetNonstuck :
        __get_unused_vars (Term.Apply (Term.Apply Q x) F) G ≠
          Term.Stuck :=
      contains_atomic_term_list_free_rec_false_except_ne_stuck hNoFree
    have hGNonstuck : G ≠ Term.Stuck := by
      intro hGStuck
      subst G
      apply hGetNonstuck
      simp [__get_unused_vars]
    have hGetEqFallback :
        __get_unused_vars (Term.Apply (Term.Apply Q x) F) G =
          __eo_l_1___get_unused_vars
            (Term.Apply (Term.Apply Q x) F) G :=
      get_unused_vars_fallback_eq_of_not_quant_branch
        hGNonstuck
        (by
          intro Q₂ y F₂ hEq
          exact hShape ⟨Q₂, y, F₂, hEq⟩)
    have hFallbackNonstuck :
        __eo_l_1___get_unused_vars
            (Term.Apply (Term.Apply Q x) F) G ≠
          Term.Stuck := by
      intro hStuck
      apply hGetNonstuck
      rw [hGetEqFallback, hStuck]
    rcases
      eo_var_env_of_l1_get_unused_vars_ne_stuck hX hFallbackNonstuck with
      ⟨vars, hEnv⟩
    exact ⟨vars, by rw [hGetEqFallback]; exact hEnv⟩

private theorem eo_var_env_of_get_unused_vars_of_quant_has_smt_translation
    {Q x F G : Term}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hLeftTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply Q x) F))
    (hGTrans : eoHasSmtTranslation G)
    (hNoFree :
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (Term.Apply (Term.Apply Q x) F) G)
          Term.__eo_List_nil =
        Term.Boolean false) :
  ∃ vars,
    EoVarEnv
      (__get_unused_vars (Term.Apply (Term.Apply Q x) F) G)
      vars :=
by
  rcases eo_var_env_of_quant_has_smt_translation hQ hLeftTrans with
    ⟨xVars, hX⟩
  exact
    eo_var_env_of_get_unused_vars_of_contains_false
      hQ hX hGTrans hNoFree

private theorem eo_var_env_perm_of_get_unused_vars_of_quant_has_smt_translation
    {Q x F G : Term}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hLeftTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply Q x) F))
    (hGTrans : eoHasSmtTranslation G)
    (hNoFree :
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (Term.Apply (Term.Apply Q x) F) G)
          Term.__eo_List_nil =
        Term.Boolean false) :
  ∃ vars,
    EoVarEnvPerm
      (__get_unused_vars (Term.Apply (Term.Apply Q x) F) G)
      vars :=
by
  rcases
    eo_var_env_of_get_unused_vars_of_quant_has_smt_translation
      hQ hLeftTrans hGTrans hNoFree with
    ⟨vars, hEnv⟩
  exact ⟨vars, EoVarEnvPerm.of_exact hEnv⟩

private theorem get_unused_vars_branch_of_contains_false
    {Q x F G : Term}
    (hNoFree :
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
        Term.Boolean false) :
  (G = F ∧
      __get_unused_vars (qterm Q x F) G =
        __eo_list_setof Term.__eo_List_cons x) ∨
    ∃ y,
      G = qterm Q y F ∧
        __eo_list_minclude Term.__eo_List_cons
            (__eo_list_setof Term.__eo_List_cons x) y =
          Term.Boolean true ∧
        __get_unused_vars (qterm Q x F) G =
          __eo_list_diff Term.__eo_List_cons
            (__eo_list_setof Term.__eo_List_cons x) y :=
by
  have hGetNonstuck :
      __get_unused_vars (qterm Q x F) G ≠ Term.Stuck :=
    contains_atomic_term_list_free_rec_false_except_ne_stuck hNoFree
  by_cases hShape :
      ∃ Q₂ y F₂,
        G = Term.Apply (Term.Apply Q₂ y) F₂
  · rcases hShape with ⟨Q₂, y, F₂, rfl⟩
    have hIteNonstuck :
        __eo_ite
            (__eo_and (__eo_eq Q Q₂) (__eo_eq F F₂))
            (__eo_requires
              (__eo_list_minclude Term.__eo_List_cons
                (__eo_list_setof Term.__eo_List_cons x) y)
              (Term.Boolean true)
              (__eo_list_diff Term.__eo_List_cons
                (__eo_list_setof Term.__eo_List_cons x) y))
            (__eo_l_1___get_unused_vars
              (Term.Apply (Term.Apply Q x) F)
              (Term.Apply (Term.Apply Q₂ y) F₂)) ≠
          Term.Stuck := by
      intro hStuck
      apply hGetNonstuck
      simpa [qterm, __get_unused_vars] using hStuck
    rcases eo_ite_nonstuck_guard_cases hIteNonstuck with hGuard | hGuard
    · have hParts := eo_and_eq_true_cases hGuard
      have hQEq : Q = Q₂ := eo_eq_true_eq hParts.1
      have hFEq : F = F₂ := eo_eq_true_eq hParts.2
      subst Q₂
      subst F₂
      have hReqNonstuck :
          __eo_requires
              (__eo_list_minclude Term.__eo_List_cons
                (__eo_list_setof Term.__eo_List_cons x) y)
              (Term.Boolean true)
              (__eo_list_diff Term.__eo_List_cons
                (__eo_list_setof Term.__eo_List_cons x) y) ≠
            Term.Stuck := by
        intro hStuck
        apply hGetNonstuck
        simpa [qterm, __get_unused_vars, hGuard, __eo_ite,
          native_ite, native_teq] using hStuck
      have hMinclude :
          __eo_list_minclude Term.__eo_List_cons
              (__eo_list_setof Term.__eo_List_cons x) y =
            Term.Boolean true :=
        eo_requires_arg_eq_of_ne_stuck hReqNonstuck
      have hReqEq :=
        eo_requires_true_nonstuck_eq hReqNonstuck
      right
      refine ⟨y, rfl, hMinclude, ?_⟩
      simp [qterm, __get_unused_vars, hGuard, __eo_ite,
        native_ite, native_teq, hReqEq]
    · have hGetEqFallback :
          __get_unused_vars (qterm Q x F)
              (Term.Apply (Term.Apply Q₂ y) F₂) =
            __eo_l_1___get_unused_vars
              (Term.Apply (Term.Apply Q x) F)
              (Term.Apply (Term.Apply Q₂ y) F₂) := by
        simp [qterm, __get_unused_vars, hGuard, __eo_ite,
          native_ite, native_teq]
      have hFallbackNonstuck :
          __eo_l_1___get_unused_vars
              (Term.Apply (Term.Apply Q x) F)
              (Term.Apply (Term.Apply Q₂ y) F₂) ≠
            Term.Stuck := by
        intro hStuck
        apply hGetNonstuck
        rw [hGetEqFallback, hStuck]
      have hGNonstuck :
          Term.Apply (Term.Apply Q₂ y) F₂ ≠ Term.Stuck := by
        intro h
        cases h
      have hL1Eq :=
        eo_l1_get_unused_vars_nonstuck_eq
          (Q := Q) (x := x) (F := F)
          (G := Term.Apply (Term.Apply Q₂ y) F₂) hGNonstuck
      have hReqNonstuck :
          __eo_requires (__eo_eq F (Term.Apply (Term.Apply Q₂ y) F₂))
              (Term.Boolean true)
              (__eo_list_setof Term.__eo_List_cons x) ≠
            Term.Stuck := by
        intro hStuck
        apply hFallbackNonstuck
        rw [hL1Eq, hStuck]
      have hEqGuard :
          __eo_eq F (Term.Apply (Term.Apply Q₂ y) F₂) =
            Term.Boolean true :=
        eo_requires_arg_eq_of_ne_stuck hReqNonstuck
      have hFG :
          F = Term.Apply (Term.Apply Q₂ y) F₂ :=
        eo_eq_true_eq hEqGuard
      have hReqEq :=
        eo_requires_true_nonstuck_eq hReqNonstuck
      left
      constructor
      · exact hFG.symm
      · rw [hGetEqFallback, hL1Eq, hReqEq]
  · have hGNonstuck : G ≠ Term.Stuck := by
      intro hG
      subst G
      apply hGetNonstuck
      simp [qterm, __get_unused_vars]
    have hGetEqFallback :
        __get_unused_vars (qterm Q x F) G =
          __eo_l_1___get_unused_vars
            (Term.Apply (Term.Apply Q x) F) G :=
      get_unused_vars_fallback_eq_of_not_quant_branch
        hGNonstuck
        (by
          intro Q₂ y F₂ hEq
          exact hShape ⟨Q₂, y, F₂, hEq⟩)
    have hFallbackNonstuck :
        __eo_l_1___get_unused_vars
            (Term.Apply (Term.Apply Q x) F) G ≠
          Term.Stuck := by
      intro hStuck
      apply hGetNonstuck
      rw [hGetEqFallback, hStuck]
    have hL1Eq :=
      eo_l1_get_unused_vars_nonstuck_eq
        (Q := Q) (x := x) (F := F) hGNonstuck
    have hReqNonstuck :
        __eo_requires (__eo_eq F G) (Term.Boolean true)
            (__eo_list_setof Term.__eo_List_cons x) ≠
          Term.Stuck := by
      intro hStuck
      apply hFallbackNonstuck
      rw [hL1Eq, hStuck]
    have hEqGuard :
        __eo_eq F G = Term.Boolean true :=
      eo_requires_arg_eq_of_ne_stuck hReqNonstuck
    have hFG : F = G := eo_eq_true_eq hEqGuard
    have hReqEq := eo_requires_true_nonstuck_eq hReqNonstuck
    left
    constructor
    · exact hFG.symm
    · rw [hGetEqFallback, hL1Eq, hReqEq]

private theorem quant_body_has_smt_translation
    {Q x F : Term}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hTrans : RuleProofs.eo_has_smt_translation (qterm Q x F)) :
  RuleProofs.eo_has_smt_translation F :=
by
  rcases eo_var_env_of_quant_has_smt_translation hQ hTrans with
    ⟨vars, hEnv⟩
  cases hEnv with
  | nil =>
      rcases hQ with hForall | hExists
      · subst Q
        exact False.elim (hTrans (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none))
      · subst Q
        exact False.elim (hTrans (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none))
  | cons hTail =>
      rename_i s T env tailVars
      rcases hQ with hForall | hExists
      · subst Q
        exact
          body_has_smt_translation_of_forall_list_branch_has_smt_translation
            hTrans
      · subst Q
        exact
          body_has_smt_translation_of_exists_list_branch_has_smt_translation
            hTrans

private theorem quant_body_has_bool_type
    {Q x F : Term}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hTrans : RuleProofs.eo_has_smt_translation (qterm Q x F)) :
  __smtx_typeof (__eo_to_smt F) = SmtType.Bool :=
by
  rcases eo_var_env_of_quant_has_smt_translation hQ hTrans with
    ⟨vars, hEnv⟩
  cases hEnv with
  | nil =>
      rcases hQ with hForall | hExists
      · subst Q
        exact False.elim (hTrans (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none))
      · subst Q
        exact False.elim (hTrans (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none))
  | cons hTail =>
      rename_i s T env tailVars
      rcases hQ with hForall | hExists
      · subst Q
        have hNotBool :
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
              exact hTrans)
        have hExistsBool :
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
            hNotBool
        have hBodyNotBool :
            __smtx_typeof (SmtTerm.not (__eo_to_smt F)) =
              SmtType.Bool :=
          TranslationProofs.eo_to_smt_exists_body_bool_of_bool
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) env)
            (SmtTerm.not (__eo_to_smt F)) hExistsBool
        exact smtx_typeof_not_arg_eq_bool (__eo_to_smt F) hBodyNotBool
      · subst Q
        have hExistsBool :
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
              exact hTrans)
        exact
          TranslationProofs.eo_to_smt_exists_body_bool_of_bool
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) env)
            (__eo_to_smt F) hExistsBool

private theorem quant_qterm_has_bool_type
    {Q x F : Term}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hTrans : RuleProofs.eo_has_smt_translation (qterm Q x F)) :
  __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool :=
by
  rcases hQ with hForall | hExists
  · subst Q
    rcases
      smtx_typeof_eo_to_smt_forall_top_bool_or_none_closed F x with
      hBool | hNone
    · simpa [qterm] using hBool
    · exact False.elim (hTrans (by simpa [qterm] using hNone))
  · subst Q
    rcases
      smtx_typeof_eo_to_smt_exists_top_bool_or_none_closed F x with
      hBool | hNone
    · simpa [qterm] using hBool
    · exact False.elim (hTrans (by simpa [qterm] using hNone))

private theorem smtx_typeof_exists_tail_bool_of_cons_bool
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

private theorem smtx_type_wf_of_exists_cons_bool
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

private theorem smtx_type_wf_of_eo_var_env_exists_bool
    {xs : Term} {vars : List EoVarKey} {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hTy : __smtx_typeof (__eo_to_smt_exists xs body) =
      SmtType.Bool) :
  ∀ s T, (s, T) ∈ vars ->
    __smtx_type_wf (__eo_to_smt_type T) = true :=
by
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

private theorem quant_binder_types_wf
    {Q x F : Term} {vars : List EoVarKey}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hTrans : RuleProofs.eo_has_smt_translation (qterm Q x F))
    (hEnv : EoVarEnv x vars) :
  ∀ s T, (s, T) ∈ vars ->
    __smtx_type_wf (__eo_to_smt_type T) = true :=
by
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
              exact hTrans)
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
              exact hTrans)
        exact
          smtx_type_wf_of_eo_var_env_exists_bool
            (EoVarEnv.cons (s := s) (T := T) hTail) hExistsTy

private theorem smtx_model_eval_exists_eq_body_of_body_eval_eq
    (M : SmtModel) (hM : model_wf M)
    (s : native_String) (T : SmtType) (body : SmtTerm)
    (hWF : __smtx_type_wf T = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hBody :
      ∀ v : SmtValue,
        __smtx_typeof_value v = T ->
          __smtx_value_canonical v = true ->
            __smtx_model_eval (native_model_push M s T v) body =
              __smtx_model_eval M body) :
  __smtx_model_eval M (SmtTerm.exists s T body) =
    __smtx_model_eval M body :=
by
  classical
  rcases smt_model_eval_bool_is_boolean M hM body hBodyTy with
    ⟨b, hEvalBody⟩
  rcases canonical_type_inhabited_of_type_wf T hWF with
    ⟨w, hwTy, hwCan⟩
  have hwCanBool : __smtx_value_canonical w = true := by
    simpa [value_canonical] using hwCan
  cases b
  · rw [hEvalBody]
    by_cases hSat :
        ∃ v : SmtValue,
          __smtx_typeof_value v = T ∧
            __smtx_value_canonical v = true ∧
            __smtx_model_eval (native_model_push M s T v) body =
              SmtValue.Boolean true
    · rcases hSat with ⟨v, hvTy, hvCan, hvEval⟩
      have hConst := hBody v hvTy hvCan
      rw [hEvalBody] at hConst
      rw [hConst] at hvEval
      cases hvEval
    · simp [__smtx_model_eval, hSat]
  · rw [hEvalBody]
    have hSat :
        ∃ v : SmtValue,
          __smtx_typeof_value v = T ∧
            __smtx_value_canonical v = true ∧
            __smtx_model_eval (native_model_push M s T v) body =
              SmtValue.Boolean true := by
      refine ⟨w, hwTy, hwCanBool, ?_⟩
      rw [hBody w hwTy hwCanBool, hEvalBody]
    simp [__smtx_model_eval, hSat]

private theorem smtx_typeof_eo_to_smt_exists_eq_bool_of_eo_var_env
    {xs : Term} {vars : List EoVarKey} {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool) :
  __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool :=
by
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

private theorem smtx_model_eval_eo_to_smt_exists_eq_base_of_body_eval_eq
    {xs : Term} {vars : List EoVarKey} {except : List SmtVarKey}
    {M : SmtModel} {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hInExcept :
      ∀ s T, (s, T) ∈ vars ->
        (s, __eo_to_smt_type T) ∈ except)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hBodyInvariant :
      ∀ {N : SmtModel},
        model_wf N ->
          model_agrees_except_on_env except [] N M ->
            __smtx_model_eval N body =
              __smtx_model_eval M body) :
  ∀ {N : SmtModel},
    model_wf N ->
            model_agrees_except_on_env except [] N M ->
        __smtx_model_eval N (__eo_to_smt_exists xs body) =
          __smtx_model_eval M body :=
by
  induction hEnv generalizing except M body with
  | nil =>
      intro N hN hAgree
      simpa [__eo_to_smt_exists] using hBodyInvariant hN hAgree
  | cons hTail ih =>
      rename_i s T env tailVars
      intro N hN hAgree
      let ST := __eo_to_smt_type T
      have hHeadWf : __smtx_type_wf ST = true :=
        hWf s T (List.Mem.head _)
      have hTailWf :
          ∀ s' T', (s', T') ∈ tailVars ->
            __smtx_type_wf (__eo_to_smt_type T') = true := by
        intro s' T' hMem
        exact hWf s' T' (List.Mem.tail _ hMem)
      have hTailInExcept :
          ∀ s' T', (s', T') ∈ tailVars ->
            (s', __eo_to_smt_type T') ∈ except := by
        intro s' T' hMem
        exact hInExcept s' T' (List.Mem.tail _ hMem)
      have hTailTy :
          __smtx_typeof (__eo_to_smt_exists env body) =
            SmtType.Bool :=
        smtx_typeof_eo_to_smt_exists_eq_bool_of_eo_var_env
          hTail hTailWf hBodyTy
      have hNTail :
          __smtx_model_eval N (__eo_to_smt_exists env body) =
            __smtx_model_eval M body :=
        ih hTailWf hTailInExcept hBodyTy hBodyInvariant hN hAgree
      have hTailConst :
          ∀ v : SmtValue,
            __smtx_typeof_value v = ST ->
              __smtx_value_canonical v = true ->
                __smtx_model_eval
                    (native_model_push N s ST v)
                    (__eo_to_smt_exists env body) =
                  __smtx_model_eval N (__eo_to_smt_exists env body) := by
        intro v hvTy hvCan
        have hPushTotal :
            model_wf (native_model_push N s ST v) :=
          model_total_typed_push hN s ST v hHeadWf hvTy
            (by simpa [value_canonical] using hvCan)
        have hPushAgree :
            model_agrees_except_on_env except []
              (native_model_push N s ST v) M :=
          model_agrees_except_on_env_push_left hAgree
            (by
              simpa [ST] using hInExcept s T (List.Mem.head _))
            (by simp)
        have hPushTail :
            __smtx_model_eval
                (native_model_push N s ST v)
                (__eo_to_smt_exists env body) =
              __smtx_model_eval M body :=
          ih hTailWf hTailInExcept hBodyTy hBodyInvariant
            hPushTotal hPushAgree
        exact hPushTail.trans hNTail.symm
      have hDrop :
          __smtx_model_eval N
              (SmtTerm.exists s ST (__eo_to_smt_exists env body)) =
            __smtx_model_eval N (__eo_to_smt_exists env body) :=
        smtx_model_eval_exists_eq_body_of_body_eval_eq
          N hN s ST (__eo_to_smt_exists env body)
          hHeadWf hTailTy hTailConst
      change
        __smtx_model_eval N
            (SmtTerm.exists s ST (__eo_to_smt_exists env body)) =
          __smtx_model_eval M body
      exact hDrop.trans hNTail

private theorem smtx_model_eval_not_not_eq_self_of_bool
    (M : SmtModel) (hM : model_wf M) (body : SmtTerm)
    (hBodyTy : __smtx_typeof body = SmtType.Bool) :
  __smtx_model_eval M (SmtTerm.not (SmtTerm.not body)) =
    __smtx_model_eval M body :=
by
  rcases smt_model_eval_bool_is_boolean M hM body hBodyTy with
    ⟨b, hEval⟩
  rw [hEval]
  cases b <;>
    simp [__smtx_model_eval, hEval, __smtx_model_eval_not,
      SmtEval.native_not]

private theorem smtx_model_eval_not_congr
    (M : SmtModel) {x y : SmtTerm}
    (hEval : __smtx_model_eval M x = __smtx_model_eval M y) :
  __smtx_model_eval M (SmtTerm.not x) =
    __smtx_model_eval M (SmtTerm.not y) :=
by
  simp [__smtx_model_eval, hEval]

private theorem smtx_model_eval_not_not_true_iff
    (v : SmtValue) :
    __smtx_model_eval_not (__smtx_model_eval_not v) =
        SmtValue.Boolean true ↔
      v = SmtValue.Boolean true := by
  cases v <;> simp [__smtx_model_eval_not, SmtEval.native_not]

private theorem smtx_model_eval_eo_to_smt_exists_double_not_body_true_iff
    (M : SmtModel) (xs : Term) (body : SmtTerm) :
    __smtx_model_eval M
        (__eo_to_smt_exists xs (SmtTerm.not (SmtTerm.not body))) =
        SmtValue.Boolean true ↔
      __smtx_model_eval M (__eo_to_smt_exists xs body) =
        SmtValue.Boolean true := by
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    simpa [__eo_to_smt_exists, __smtx_model_eval] using
      smtx_model_eval_not_not_true_iff (__smtx_model_eval M body)
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
            classical
            let P : Prop :=
              ∃ v : SmtValue,
                __smtx_typeof_value v = __eo_to_smt_type T ∧
                  __smtx_value_canonical v = true ∧
                  __smtx_model_eval
                      (native_model_push M s (__eo_to_smt_type T) v)
                      (__eo_to_smt_exists a
                        (SmtTerm.not (SmtTerm.not body))) =
                    SmtValue.Boolean true
            let Q : Prop :=
              ∃ v : SmtValue,
                __smtx_typeof_value v = __eo_to_smt_type T ∧
                  __smtx_value_canonical v = true ∧
                  __smtx_model_eval
                      (native_model_push M s (__eo_to_smt_type T) v)
                      (__eo_to_smt_exists a body) =
                    SmtValue.Boolean true
            have hPQ : P ↔ Q := by
              constructor
              · intro hSat
                rcases hSat with ⟨v, hv, hCan, hEval⟩
                refine ⟨v, hv, hCan, ?_⟩
                exact
                  (smtx_model_eval_eo_to_smt_exists_double_not_body_true_iff
                    (native_model_push M s (__eo_to_smt_type T) v)
                    a body).1 hEval
              · intro hSat
                rcases hSat with ⟨v, hv, hCan, hEval⟩
                refine ⟨v, hv, hCan, ?_⟩
                exact
                  (smtx_model_eval_eo_to_smt_exists_double_not_body_true_iff
                    (native_model_push M s (__eo_to_smt_type T) v)
                    a body).2 hEval
            have hPropEq : P = Q := propext hPQ
            simp [P, Q, __eo_to_smt_exists, __smtx_model_eval, hPropEq]
          all_goals
            subst hname
            simp [__eo_to_smt_exists, __smtx_model_eval]
        all_goals
          subst hy
          simp [__eo_to_smt_exists, __smtx_model_eval]
      all_goals
        subst hg
        simp [__eo_to_smt_exists, __smtx_model_eval]
    all_goals
      subst hf
      simp [__eo_to_smt_exists, __smtx_model_eval]
  all_goals
    subst hxs
    simp [__eo_to_smt_exists, __smtx_model_eval]

private theorem smtx_model_eval_eo_to_smt_exists_double_not_body
    (M : SmtModel) (hM : model_wf M)
    (xs : Term) (body : SmtTerm)
    (hBody : __smtx_typeof body = SmtType.Bool) :
    __smtx_model_eval M
        (__eo_to_smt_exists xs (SmtTerm.not (SmtTerm.not body))) =
      __smtx_model_eval M (__eo_to_smt_exists xs body) := by
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    rcases smt_model_eval_bool_is_boolean M hM body hBody with ⟨b, hb⟩
    simp [__eo_to_smt_exists, __smtx_model_eval, hb, __smtx_model_eval_not,
      SmtEval.native_not]
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
            classical
            let P : Prop :=
              ∃ v : SmtValue,
                __smtx_typeof_value v = __eo_to_smt_type T ∧
                  __smtx_value_canonical v = true ∧
                  __smtx_model_eval
                      (native_model_push M s (__eo_to_smt_type T) v)
                      (__eo_to_smt_exists a
                        (SmtTerm.not (SmtTerm.not body))) =
                    SmtValue.Boolean true
            let Q : Prop :=
              ∃ v : SmtValue,
                __smtx_typeof_value v = __eo_to_smt_type T ∧
                  __smtx_value_canonical v = true ∧
                  __smtx_model_eval
                      (native_model_push M s (__eo_to_smt_type T) v)
                      (__eo_to_smt_exists a body) =
                    SmtValue.Boolean true
            have hPQ : P ↔ Q := by
              constructor
              · intro hSat
                rcases hSat with ⟨v, hv, hCan, hEval⟩
                refine ⟨v, hv, hCan, ?_⟩
                exact
                  (smtx_model_eval_eo_to_smt_exists_double_not_body_true_iff
                    (native_model_push M s (__eo_to_smt_type T) v)
                    a body).1 hEval
              · intro hSat
                rcases hSat with ⟨v, hv, hCan, hEval⟩
                refine ⟨v, hv, hCan, ?_⟩
                exact
                  (smtx_model_eval_eo_to_smt_exists_double_not_body_true_iff
                    (native_model_push M s (__eo_to_smt_type T) v)
                    a body).2 hEval
            have hPropEq : P = Q := propext hPQ
            simp [P, Q, __eo_to_smt_exists, __smtx_model_eval, hPropEq]
          all_goals
            subst hname
            simp [__eo_to_smt_exists, __smtx_model_eval]
        all_goals
          subst hy
          simp [__eo_to_smt_exists, __smtx_model_eval]
      all_goals
        subst hg
        simp [__eo_to_smt_exists, __smtx_model_eval]
    all_goals
      subst hf
      simp [__eo_to_smt_exists, __smtx_model_eval]
  all_goals
    subst hxs
    simp [__eo_to_smt_exists, __smtx_model_eval]

private theorem smtx_model_eval_eo_to_smt_forall_encoding_eq_base_of_body_eval_eq
    {xs : Term} {vars : List EoVarKey} {except : List SmtVarKey}
    {M : SmtModel} {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hM : model_wf M)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hInExcept :
      ∀ s T, (s, T) ∈ vars ->
        (s, __eo_to_smt_type T) ∈ except)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hBodyInvariant :
      ∀ {N : SmtModel},
        model_wf N ->
          model_agrees_except_on_env except [] N M ->
            __smtx_model_eval N body =
              __smtx_model_eval M body) :
  ∀ {N : SmtModel},
    model_wf N ->
      model_agrees_except_on_env except [] N M ->
        __smtx_model_eval N
            (SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not body))) =
          __smtx_model_eval M body :=
by
  intro N hN hAgree
  have hNotBodyTy :
      __smtx_typeof (SmtTerm.not body) = SmtType.Bool :=
    smtx_typeof_not_eq_bool_of_non_none body
      (by
        rw [typeof_not_eq, hBodyTy]
        simp [native_ite, native_Teq])
  have hNotInvariant :
      ∀ {N' : SmtModel},
        model_wf N' ->
          model_agrees_except_on_env except [] N' M ->
            __smtx_model_eval N' (SmtTerm.not body) =
              __smtx_model_eval M (SmtTerm.not body) := by
    intro N' hN' hAgree'
    exact smtx_model_eval_not_eq_of_eval_eq
      (hBodyInvariant hN' hAgree')
  have hExistsNot :
      __smtx_model_eval N (__eo_to_smt_exists xs (SmtTerm.not body)) =
        __smtx_model_eval M (SmtTerm.not body) :=
    smtx_model_eval_eo_to_smt_exists_eq_base_of_body_eval_eq
      hEnv hWf hInExcept hNotBodyTy hNotInvariant hN hAgree
  have hNotEval :
      __smtx_model_eval N
          (SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not body))) =
        __smtx_model_eval M (SmtTerm.not (SmtTerm.not body)) :=
    by
      simp [__smtx_model_eval, hExistsNot]
  exact hNotEval.trans
    (smtx_model_eval_not_not_eq_self_of_bool M hM body hBodyTy)

private theorem smtx_model_eval_qterm_eq_body_of_body_eval_eq
    {Q x F : Term} {vars : List EoVarKey} {except : List SmtVarKey}
    {M : SmtModel}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hTrans : RuleProofs.eo_has_smt_translation (qterm Q x F))
    (hEnv : EoVarEnv x vars)
    (hM : model_wf M)
    (hInExcept :
      ∀ s T, (s, T) ∈ vars ->
        (s, __eo_to_smt_type T) ∈ except)
    (hBodyInvariant :
      ∀ {N : SmtModel},
        model_wf N ->
          model_agrees_except_on_env except [] N M ->
            __smtx_model_eval N (__eo_to_smt F) =
              __smtx_model_eval M (__eo_to_smt F)) :
  ∀ {N : SmtModel},
    model_wf N ->
      model_agrees_except_on_env except [] N M ->
        __smtx_model_eval N (__eo_to_smt (qterm Q x F)) =
          __smtx_model_eval M (__eo_to_smt F) :=
by
  have hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true :=
    quant_binder_types_wf hQ hTrans hEnv
  have hBodyTy :
      __smtx_typeof (__eo_to_smt F) = SmtType.Bool :=
    quant_body_has_bool_type hQ hTrans
  rcases hQ with hForall | hExists
  · subst Q
    cases hEnv with
    | nil =>
        intro N hN hAgree
        exact False.elim (hTrans (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none))
    | cons hTail =>
        rename_i s T env tailVars
        intro N hN hAgree
        change
          __smtx_model_eval N
              (SmtTerm.not
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) env)
                  (SmtTerm.not (__eo_to_smt F)))) =
            __smtx_model_eval M (__eo_to_smt F)
        exact
          smtx_model_eval_eo_to_smt_forall_encoding_eq_base_of_body_eval_eq
            (EoVarEnv.cons (s := s) (T := T) hTail) hM hWf
            hInExcept hBodyTy hBodyInvariant hN hAgree
  · subst Q
    cases hEnv with
    | nil =>
        intro N hN hAgree
        exact False.elim (hTrans (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none))
    | cons hTail =>
        rename_i s T env tailVars
        intro N hN hAgree
        change
          __smtx_model_eval N
              (__eo_to_smt_exists
                (Term.Apply (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s) T)) env)
                (__eo_to_smt F)) =
            __smtx_model_eval M (__eo_to_smt F)
        exact
          smtx_model_eval_eo_to_smt_exists_eq_base_of_body_eval_eq
            (EoVarEnv.cons (s := s) (T := T) hTail) hWf
            hInExcept hBodyTy hBodyInvariant hN hAgree

private theorem smtx_model_eval_qterm_eq_body_of_body_eval_eq_typed
    {Q x B : Term} {vars : List EoVarKey} {except : List SmtVarKey}
    {M : SmtModel}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hEnv : EoVarEnv x vars)
    (hNonNil : x ≠ Term.__eo_List_nil)
    (hM : model_wf M)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hInExcept :
      ∀ s T, (s, T) ∈ vars ->
        (s, __eo_to_smt_type T) ∈ except)
    (hBodyTy : __smtx_typeof (__eo_to_smt B) = SmtType.Bool)
    (hBodyInvariant :
      ∀ {N : SmtModel},
        model_wf N ->
          model_agrees_except_on_env except [] N M ->
            __smtx_model_eval N (__eo_to_smt B) =
              __smtx_model_eval M (__eo_to_smt B)) :
  ∀ {N : SmtModel},
    model_wf N ->
      model_agrees_except_on_env except [] N M ->
        __smtx_model_eval N (__eo_to_smt (qterm Q x B)) =
          __smtx_model_eval M (__eo_to_smt B) :=
by
  rcases hQ with hForall | hExists
  · subst Q
    cases hEnv with
    | nil =>
        exact False.elim (hNonNil rfl)
    | cons hTail =>
        rename_i s T env tailVars
        intro N hN hAgree
        change
          __smtx_model_eval N
              (SmtTerm.not
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) env)
                  (SmtTerm.not (__eo_to_smt B)))) =
            __smtx_model_eval M (__eo_to_smt B)
        exact
          smtx_model_eval_eo_to_smt_forall_encoding_eq_base_of_body_eval_eq
            (EoVarEnv.cons hTail) hM hWf hInExcept hBodyTy
            hBodyInvariant hN hAgree
  · subst Q
    cases hEnv with
    | nil =>
        exact False.elim (hNonNil rfl)
    | cons hTail =>
        rename_i s T env tailVars
        intro N hN hAgree
        change
          __smtx_model_eval N
              (__eo_to_smt_exists
                (Term.Apply (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s) T)) env)
                (__eo_to_smt B)) =
            __smtx_model_eval M (__eo_to_smt B)
        exact
          smtx_model_eval_eo_to_smt_exists_eq_base_of_body_eval_eq
            (EoVarEnv.cons hTail) hWf hInExcept hBodyTy
            hBodyInvariant hN hAgree

private theorem smtx_model_eval_qterm_nested_of_subset
    (M : SmtModel) (hM : model_wf M)
    {Q x y F : Term} {xVars yVars : List EoVarKey}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hXEnv : EoVarEnv x xVars)
    (hYEnv : EoVarEnv y yVars)
    (hXNonNil : x ≠ Term.__eo_List_nil)
    (hYNonNil : y ≠ Term.__eo_List_nil)
    (hSub :
      ∀ key, key ∈ yVars.map EoVarKey.toSmt ->
        key ∈ xVars.map EoVarKey.toSmt)
    (hFBodyTy : __smtx_typeof (__eo_to_smt F) = SmtType.Bool)
    (hYWf :
      ∀ s T, (s, T) ∈ yVars ->
        __smtx_type_wf (__eo_to_smt_type T) = true) :
  __smtx_model_eval M (__eo_to_smt (qterm Q x (qterm Q y F))) =
    __smtx_model_eval M (__eo_to_smt (qterm Q x F)) :=
by
  rcases hQ with hForall | hExists
  · subst Q
    rw [eo_to_smt_qterm_forall_eq x F hXNonNil]
    rw [eo_to_smt_qterm_forall_eq x
      (qterm (Term.UOp UserOp.forall) y F) hXNonNil]
    rw [eo_to_smt_qterm_forall_eq y F hYNonNil]
    have hNotFTy :
        __smtx_typeof (SmtTerm.not (__eo_to_smt F)) = SmtType.Bool := by
      rw [typeof_not_eq, hFBodyTy]
      simp [native_ite, native_Teq]
    have hExistsYNotTy :
        __smtx_typeof
            (__eo_to_smt_exists y (SmtTerm.not (__eo_to_smt F))) =
          SmtType.Bool :=
      smtx_typeof_eo_to_smt_exists_eq_bool_of_eo_var_env
        hYEnv hYWf hNotFTy
    have hDouble :
        __smtx_model_eval M
            (__eo_to_smt_exists x
              (SmtTerm.not
                (SmtTerm.not
                  (__eo_to_smt_exists y
                    (SmtTerm.not (__eo_to_smt F)))))) =
          __smtx_model_eval M
            (__eo_to_smt_exists x
              (__eo_to_smt_exists y
                (SmtTerm.not (__eo_to_smt F)))) :=
      smtx_model_eval_eo_to_smt_exists_double_not_body
        M hM x
        (__eo_to_smt_exists y (SmtTerm.not (__eo_to_smt F)))
        hExistsYNotTy
    have hDup :
        __smtx_model_eval M
            (__eo_to_smt_exists x
              (__eo_to_smt_exists y
                (SmtTerm.not (__eo_to_smt F)))) =
          __smtx_model_eval M
            (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) :=
      smtx_model_eval_eo_to_smt_exists_nested_of_subset
        M (SmtTerm.not (__eo_to_smt F)) hXEnv hYEnv hSub
    exact smtx_model_eval_not_congr M (hDouble.trans hDup)
  · subst Q
    rw [eo_to_smt_qterm_exists_eq x F hXNonNil]
    rw [eo_to_smt_qterm_exists_eq x
      (qterm (Term.UOp UserOp.exists) y F) hXNonNil]
    rw [eo_to_smt_qterm_exists_eq y F hYNonNil]
    exact
      smtx_model_eval_eo_to_smt_exists_nested_of_subset
        M (__eo_to_smt F) hXEnv hYEnv hSub

private theorem quant_unused_vars_shape_of_not_stuck
    (x1 : Term) :
    __eo_prog_quant_unused_vars x1 ≠ Term.Stuck ->
    ∃ Q x F G,
      x1 = qeq (qterm Q x F) G ∧
      (Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists) ∧
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
        Term.Boolean false ∧
      __eo_prog_quant_unused_vars x1 = qeq (qterm Q x F) G := by
  intro hProg
  cases x1 with
  | Apply lhs G =>
      cases lhs with
      | Apply eqHead lhsArg =>
          cases eqHead with
          | UOp opEq =>
              cases opEq with
              | eq =>
                  cases lhsArg with
                  | Apply qHead F =>
                      cases qHead with
                      | Apply Q x =>
                          let v0 := qterm Q x F
                          let inner :=
                            __eo_requires
                              (__contains_atomic_term_list_free_rec G
                                (__get_unused_vars v0 G)
                                Term.__eo_List_nil)
                              (Term.Boolean false)
                              (qeq v0 G)
                          have hReq :
                              __eo_requires
                                  (__eo_or (__eo_eq Q (Term.UOp UserOp.forall))
                                    (__eo_eq Q (Term.UOp UserOp.exists)))
                                  (Term.Boolean true) inner ≠ Term.Stuck := by
                            simpa [qeq, qterm, v0, inner,
                              __eo_prog_quant_unused_vars] using hProg
                          have hGuard :
                              __eo_or (__eo_eq Q (Term.UOp UserOp.forall))
                                  (__eo_eq Q (Term.UOp UserOp.exists)) =
                                Term.Boolean true :=
                            eo_requires_arg_eq_of_ne_stuck hReq
                          have hInnerNe : inner ≠ Term.Stuck :=
                            body_ne_stuck_of_requires_ne_stuck hReq
                          have hNoFree :
                              __contains_atomic_term_list_free_rec G
                                  (__get_unused_vars v0 G)
                                  Term.__eo_List_nil =
                                Term.Boolean false :=
                            eo_requires_arg_eq_of_ne_stuck hInnerNe
                          have hOuterEq :
                              __eo_requires
                                  (__eo_or (__eo_eq Q (Term.UOp UserOp.forall))
                                    (__eo_eq Q (Term.UOp UserOp.exists)))
                                  (Term.Boolean true) inner =
                                inner :=
                            eo_requires_result_eq_of_ne_stuck hReq
                          have hInnerEq :
                              inner = qeq v0 G := by
                            exact eo_requires_result_eq_of_ne_stuck hInnerNe
                          rcases eo_or_eq_true_cases_local
                              (__eo_eq Q (Term.UOp UserOp.forall))
                              (__eo_eq Q (Term.UOp UserOp.exists)) hGuard with
                            hForall | hExists
                          · have hQ : Q = Term.UOp UserOp.forall :=
                              eo_eq_true_eq hForall
                            subst Q
                            refine
                              ⟨Term.UOp UserOp.forall, x, F, G, rfl,
                                Or.inl rfl, ?_, ?_⟩
                            · simpa [v0, qterm] using hNoFree
                            · change __eo_prog_quant_unused_vars
                                (qeq (qterm (Term.UOp UserOp.forall) x F) G) =
                                  qeq (qterm (Term.UOp UserOp.forall) x F) G
                              simpa [qeq, qterm, v0,
                                __eo_prog_quant_unused_vars, hOuterEq,
                                hInnerEq]
                          · have hQ : Q = Term.UOp UserOp.exists :=
                              eo_eq_true_eq hExists
                            subst Q
                            refine
                              ⟨Term.UOp UserOp.exists, x, F, G, rfl,
                                Or.inr rfl, ?_, ?_⟩
                            · simpa [v0, qterm] using hNoFree
                            · change __eo_prog_quant_unused_vars
                                (qeq (qterm (Term.UOp UserOp.exists) x F) G) =
                                  qeq (qterm (Term.UOp UserOp.exists) x F) G
                              simpa [qeq, qterm, v0,
                                __eo_prog_quant_unused_vars, hOuterEq,
                                hInnerEq]
                      | _ =>
                          simp [__eo_prog_quant_unused_vars] at hProg
                  | _ =>
                      simp [__eo_prog_quant_unused_vars] at hProg
              | _ =>
                  simp [__eo_prog_quant_unused_vars] at hProg
          | _ =>
              simp [__eo_prog_quant_unused_vars] at hProg
      | _ =>
          simp [__eo_prog_quant_unused_vars] at hProg
  | _ =>
      simp [__eo_prog_quant_unused_vars] at hProg

private theorem quant_unused_vars_eval
    (M : SmtModel) (hM : model_wf M)
    (Q x F G : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hBool : RuleProofs.eo_has_bool_type (qeq (qterm Q x F) G))
    (hNoFree :
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
        Term.Boolean false) :
  __smtx_model_eval M (__eo_to_smt (qterm Q x F)) =
    __smtx_model_eval M (__eo_to_smt G) :=
by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (qterm Q x F) G hBool with
    ⟨hSameTy, hLeftNN⟩
  have hLeftTrans :
      RuleProofs.eo_has_smt_translation (qterm Q x F) := by
    exact hLeftNN
  have hGTrans :
      RuleProofs.eo_has_smt_translation G := by
    intro hNone
    exact hLeftNN (by rw [hSameTy, hNone])
  have hFTrans :
      RuleProofs.eo_has_smt_translation F :=
    quant_body_has_smt_translation hQ hLeftTrans
  rcases eo_var_env_of_quant_has_smt_translation hQ hLeftTrans with
    ⟨xVars, hXEnv⟩
  rcases
    eo_var_env_perm_of_get_unused_vars_of_quant_has_smt_translation
      hQ hLeftTrans hGTrans hNoFree with
    ⟨exceptVars, hExceptEnv⟩
  rcases get_unused_vars_branch_of_contains_false hNoFree with
    hSameBody | hSameQuant
  · rcases hSameBody with ⟨hG, hGet⟩
    subst G
    have hGetSet :
        __get_unused_vars ((Q.Apply x).Apply F) F =
          __eo_list_setof Term.__eo_List_cons x := by
      simpa [qterm] using hGet
    have hExceptSet :
        EoVarEnvPerm (__eo_list_setof Term.__eo_List_cons x) exceptVars := by
      simpa [hGetSet] using hExceptEnv
    have hInExcept :
        ∀ s T, (s, T) ∈ xVars ->
          (s, __eo_to_smt_type T) ∈
            exceptVars.map EoVarKey.toSmt := by
      intro s T hMem
      rcases EoVarEnv.setof_mem_of_mem hXEnv hMem with
        ⟨setVars, hSetEnv, hSetMem⟩
      have hExceptMem :
          (s, T) ∈ exceptVars :=
        EoVarEnvPerm.mem_of_exact_env_mem
          hExceptSet hSetEnv hSetMem
      exact List.mem_map.2
        ⟨(s, T), hExceptMem, by simp [EoVarKey.toSmt]⟩
    have hNoFreeSet :
        __contains_atomic_term_list_free_rec F
            (__eo_list_setof Term.__eo_List_cons x) Term.__eo_List_nil =
          Term.Boolean false := by
      simpa [hGet] using hNoFree
    have hBodyInvariant :
        ∀ {N : SmtModel},
          model_wf N ->
            model_agrees_except_on_env
                (exceptVars.map EoVarKey.toSmt) [] N M ->
              __smtx_model_eval N (__eo_to_smt F) =
                __smtx_model_eval M (__eo_to_smt F) := by
      intro N _hN hAgree
      exact
        smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
          hExceptSet
          (EoVarEnvPerm.of_exact EoVarEnv.nil)
          hFTrans hNoFreeSet hAgree
    exact
      smtx_model_eval_qterm_eq_body_of_body_eval_eq
        hQ hLeftTrans hXEnv hM hInExcept hBodyInvariant
        hM
        (model_agrees_except_on_env_refl
          (exceptVars.map EoVarKey.toSmt) [] M)
  · rcases hSameQuant with ⟨y, hG, hMinclude, hGet⟩
    subst G
    have hNoFreeDiff :
        __contains_atomic_term_list_free_rec (qterm Q y F)
            (__eo_list_diff Term.__eo_List_cons
              (__eo_list_setof Term.__eo_List_cons x) y)
            Term.__eo_List_nil =
          Term.Boolean false := by
      simpa [hGet] using hNoFree
    rcases eo_var_env_of_quant_has_smt_translation hQ hGTrans with
      ⟨yVars, hYEnv⟩
    rcases EoVarEnv.setof hXEnv with
      ⟨setVars, hSetEnv⟩
    rcases EoVarEnv.diff hSetEnv hYEnv with
      ⟨diffVars, hDiffEnv⟩
    have hExceptDiff :
        EoVarEnvPerm
          (__eo_list_diff Term.__eo_List_cons
            (__eo_list_setof Term.__eo_List_cons x) y)
          exceptVars := by
      have hGetDiff :
          __get_unused_vars ((Q.Apply x).Apply F) (qterm Q y F) =
            __eo_list_diff Term.__eo_List_cons
              (__eo_list_setof Term.__eo_List_cons x) y := by
        simpa [qterm] using hGet
      rw [hGetDiff] at hExceptEnv
      exact hExceptEnv
    have hYSubsetSet :
        ∀ key, key ∈ yVars -> key ∈ setVars :=
      eo_var_env_minclude_mem_subset hSetEnv hYEnv hMinclude
    have hYSubsetSetSmt :
        ∀ key, key ∈ yVars.map EoVarKey.toSmt ->
          key ∈ setVars.map EoVarKey.toSmt := by
      intro key hMem
      rcases List.mem_map.1 hMem with ⟨eoKey, hEoMem, hKeyEq⟩
      exact List.mem_map.2
        ⟨eoKey, hYSubsetSet eoKey hEoMem, hKeyEq⟩
    have hSetSubsetXSmt :
        ∀ key, key ∈ setVars.map EoVarKey.toSmt ->
          key ∈ xVars.map EoVarKey.toSmt := by
      intro key hMem
      rcases List.mem_map.1 hMem with ⟨eoKey, hEoMem, hKeyEq⟩
      have hXMem :
          eoKey ∈ xVars :=
        eo_var_env_setof_mem_subset hXEnv hSetEnv eoKey hEoMem
      exact List.mem_map.2 ⟨eoKey, hXMem, hKeyEq⟩
    have hYSubsetXSmt :
        ∀ key, key ∈ yVars.map EoVarKey.toSmt ->
          key ∈ xVars.map EoVarKey.toSmt := by
      intro key hMem
      exact hSetSubsetXSmt key (hYSubsetSetSmt key hMem)
    have hXSubsetSetSmt :
        ∀ key, key ∈ xVars.map EoVarKey.toSmt ->
          key ∈ setVars.map EoVarKey.toSmt := by
      intro key hMem
      rcases List.mem_map.1 hMem with ⟨eoKey, hEoMem, hKeyEq⟩
      rcases EoVarEnv.setof_mem_of_mem hXEnv hEoMem with
        ⟨setVars', hSetEnv', hSetMem⟩
      have hSetVarsEq : setVars = setVars' :=
        EoVarEnv.vars_eq_of_same_env hSetEnv hSetEnv'
      exact List.mem_map.2
        ⟨eoKey, by simpa [hSetVarsEq] using hSetMem, hKeyEq⟩
    have hSetMemYOrDiffSmt :
        ∀ key, key ∈ setVars.map EoVarKey.toSmt ->
          key ∈ yVars.map EoVarKey.toSmt ∨
            key ∈ exceptVars.map EoVarKey.toSmt := by
      intro key hMem
      rcases List.mem_map.1 hMem with ⟨eoKey, hEoMem, hKeyEq⟩
      rcases
        eo_var_env_diff_mem_or hSetEnv hYEnv hDiffEnv eoKey hEoMem with
        hMemY | hMemDiff
      · exact Or.inl (List.mem_map.2 ⟨eoKey, hMemY, hKeyEq⟩)
      · have hExceptMem :
            eoKey ∈ exceptVars :=
          EoVarEnvPerm.mem_of_exact_env_mem
            hExceptDiff hDiffEnv hMemDiff
        exact Or.inr (List.mem_map.2 ⟨eoKey, hExceptMem, hKeyEq⟩)
    have hBodyNoFreeDiff :
        __contains_atomic_term_list_free_rec F
            (__eo_list_diff Term.__eo_List_cons
              (__eo_list_setof Term.__eo_List_cons x) y)
            (__eo_list_concat Term.__eo_List_cons y Term.__eo_List_nil) =
          Term.Boolean false := by
      cases hYEnv with
      | nil =>
          exfalso
          rcases hQ with hForall | hExists
          · subst Q
            exact hGTrans (by
              change __smtx_typeof SmtTerm.None = SmtType.None
              exact TranslationProofs.smtx_typeof_none)
          · subst Q
            exact hGTrans (by
              change __smtx_typeof SmtTerm.None = SmtType.None
              exact TranslationProofs.smtx_typeof_none)
      | cons hTail =>
          rename_i s T env tailVars
          simpa [qterm] using
            contains_atomic_term_list_free_rec_list_branch_false_body
              (q := Q) (x := Term.Var (Term.String s) T)
              (ys := env) (body := F)
              (except :=
                __eo_list_diff Term.__eo_List_cons
                  (__eo_list_setof Term.__eo_List_cons x)
                  (Term.Apply
                    (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String s) T)) env))
              (bound := Term.__eo_List_nil)
              hNoFreeDiff
    have hBoundY :
        EoVarEnvPerm
          (__eo_list_concat Term.__eo_List_cons y Term.__eo_List_nil)
          yVars := by
      simpa using
        EoVarEnvPerm.of_exact
          (EoVarEnv.concat hYEnv EoVarEnv.nil)
    have hRightInvariant :
        ∀ {N : SmtModel},
          model_wf N ->
            model_agrees_except_on_env
                (setVars.map EoVarKey.toSmt) [] N M ->
              __smtx_model_eval N (__eo_to_smt (qterm Q y F)) =
                __smtx_model_eval M (__eo_to_smt (qterm Q y F)) := by
      intro N _hN hAgreeSet
      refine
        smtx_model_eval_qterm_eq_of_body_eval_eq_bound
          hQ hYEnv ?_ hAgreeSet
      intro M' N' hAgreeSetBound
      have hAgreeDiffBound :
          model_agrees_except_on_env
              (exceptVars.map EoVarKey.toSmt)
              (yVars.map EoVarKey.toSmt) M' N' := by
        refine ⟨hAgreeSetBound.globals, ?_⟩
        intro s T hAllowed
        apply hAgreeSetBound.vars_eq
        rcases hAllowed with hBound | hNotDiff
        · exact Or.inl hBound
        · by_cases hSetMem :
              (s, T) ∈ setVars.map EoVarKey.toSmt
          · rcases hSetMemYOrDiffSmt (s, T) hSetMem with
              hMemY | hMemDiff
            · exact Or.inl hMemY
            · exact False.elim (hNotDiff hMemDiff)
          · exact Or.inr hSetMem
      exact
        smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
          hExceptDiff hBoundY hFTrans hBodyNoFreeDiff hAgreeDiffBound
    have hXNonNil : x ≠ Term.__eo_List_nil := by
      intro hx
      subst x
      rcases hQ with hForall | hExists
      · subst Q
        exact hLeftTrans (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none)
      · subst Q
        exact hLeftTrans (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none)
    have hYNonNil : y ≠ Term.__eo_List_nil := by
      intro hy
      subst y
      rcases hQ with hForall | hExists
      · subst Q
        exact hGTrans (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none)
      · subst Q
        exact hGTrans (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none)
    have hFBodyTy :
        __smtx_typeof (__eo_to_smt F) = SmtType.Bool :=
      quant_body_has_bool_type hQ hLeftTrans
    have hNestedBodyTy :
        __smtx_typeof (__eo_to_smt (qterm Q y F)) = SmtType.Bool :=
      quant_qterm_has_bool_type hQ hGTrans
    have hXWf :
        ∀ s T, (s, T) ∈ xVars ->
          __smtx_type_wf (__eo_to_smt_type T) = true :=
      quant_binder_types_wf hQ hLeftTrans hXEnv
    have hYWf :
        ∀ s T, (s, T) ∈ yVars ->
          __smtx_type_wf (__eo_to_smt_type T) = true :=
      quant_binder_types_wf hQ hGTrans hYEnv
    have hXInSet :
        ∀ s T, (s, T) ∈ xVars ->
          (s, __eo_to_smt_type T) ∈ setVars.map EoVarKey.toSmt := by
      intro s T hMem
      exact
        hXSubsetSetSmt (s, __eo_to_smt_type T)
          (List.mem_map.2
            ⟨(s, T), hMem, by simp [EoVarKey.toSmt]⟩)
    have hDropOuter :
        __smtx_model_eval M
            (__eo_to_smt (qterm Q x (qterm Q y F))) =
          __smtx_model_eval M (__eo_to_smt (qterm Q y F)) :=
      smtx_model_eval_qterm_eq_body_of_body_eval_eq_typed
        hQ hXEnv hXNonNil hM hXWf hXInSet hNestedBodyTy
        hRightInvariant
        hM
        (model_agrees_except_on_env_refl
          (setVars.map EoVarKey.toSmt) [] M)
    have hNested :
        __smtx_model_eval M
            (__eo_to_smt (qterm Q x (qterm Q y F))) =
          __smtx_model_eval M (__eo_to_smt (qterm Q x F)) :=
      smtx_model_eval_qterm_nested_of_subset
        M hM hQ hXEnv hYEnv hXNonNil hYNonNil
        hYSubsetXSmt hFBodyTy hYWf
    exact hNested.symm.trans hDropOuter

public theorem cmd_step_quant_unused_vars_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_unused_vars args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.quant_unused_vars args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_unused_vars args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.quant_unused_vars args premises ≠
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
                  __eo_prog_quant_unused_vars a1 ≠ Term.Stuck := by
                change __eo_prog_quant_unused_vars a1 ≠ Term.Stuck at hProg
                simpa using hProg
              rcases quant_unused_vars_shape_of_not_stuck a1 hProgQuant with
                ⟨Q, x, F, G, ha1, hQ, hNoFree, hProgEq⟩
              have hTransFormula :
                  RuleProofs.eo_has_smt_translation (qeq (qterm Q x F) G) := by
                simpa [ha1] using hTransA1
              have hFormulaType :
                  __eo_typeof (qeq (qterm Q x F) G) = Term.Bool := by
                change __eo_typeof (__eo_prog_quant_unused_vars a1) =
                  Term.Bool at hResultTy
                rw [hProgEq] at hResultTy
                exact hResultTy
              have hFormulaBool :
                  RuleProofs.eo_has_bool_type (qeq (qterm Q x F) G) :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  (qeq (qterm Q x F) G) hTransFormula hFormulaType
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M
                  (__eo_prog_quant_unused_vars a1) true
                rw [hProgEq]
                apply RuleProofs.eo_interprets_eq_of_rel M
                  (qterm Q x F) G
                · exact hFormulaBool
                · have hEvalEq :=
                    quant_unused_vars_eval M hM Q x F G hQ hFormulaBool
                      hNoFree
                  rw [hEvalEq]
                  exact RuleProofs.smt_value_rel_refl
                    (__smtx_model_eval M (__eo_to_smt G))
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_quant_unused_vars a1)
                rw [hProgEq]
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  hFormulaBool
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
