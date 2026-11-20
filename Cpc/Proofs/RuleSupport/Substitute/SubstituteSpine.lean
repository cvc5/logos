module

public import Cpc.Proofs.RuleSupport.SubstituteTranslatabilitySupport
import all Cpc.Proofs.RuleSupport.SubstituteTranslatabilitySupport
public import Cpc.Proofs.Translation.LambdaApply
import all Cpc.Proofs.Translation.LambdaApply
import all Cpc.Logos

/-!
# Substitution into lambda spines

A lambda applied to arguments is a binder for substitution only at the lambda
itself. Substitution into such a spine is the spine of the substituted lambda
applied to the substituted arguments (`substitute_simul_rec_spine`, and
`substitute_simul_rec_spine_rename` in rename mode, which renames the
lambda's variables instead of binding them), and the EO and SMT types of a
spine depend only on those of its body and arguments.
-/

public section

open Eo
open SmtEval
open Smtm
open TranslationProofs
open SubstituteTranslatabilitySupport

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

theorem LamSpineSupport.eoVarEnv_eoVarList (vs : List (native_String × Term)) :
    EoVarEnv (LamSpineSupport.eoVarList vs) vs := by
  induction vs with
  | nil => exact EoVarEnv.nil
  | cons p vs ih => exact EoVarEnv.cons ih


namespace InstantiateRule

theorem eo_list_cons_no_smt_translation (v vs : Term) :
    ¬ eoHasSmtTranslation (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
  intro h
  apply h
  change __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt v))
    (__eo_to_smt vs)) = SmtType.None
  exact TranslationProofs.typeof_apply_apply_none_head_eq _ _

/-- A spine whose arguments and body have translations is not a binder head. -/
theorem mkSpine_not_binderHead (us body : Term) :
    ∀ (r : List Term), eoHasSmtTranslation body ->
      (∀ x ∈ r, eoHasSmtTranslation x) ->
      ¬ ∃ q v vs, LamSpineSupport.mkSpine (LamSpineSupport.lamT us body) r =
        Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
  | [], hBody, _, ⟨q, v, vs, he⟩ => by
      injection he with _ he
      subst he
      exact eo_list_cons_no_smt_translation v vs hBody
  | b :: r, _, hArgs, ⟨q, v, vs, he⟩ => by
      injection he with _ he
      subst he
      exact eo_list_cons_no_smt_translation v vs (hArgs _ List.mem_cons_self)

/-- Substitution into a spine: the spine of the lambda whose body is
substituted under its variables, applied to the substituted arguments. -/
theorem substitute_simul_rec_spine
    (xs ss bvs : Term) {bvsVars : List EoVarKey}
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck)
    (vs : List (native_String × Term)) (body : Term)
    (hBody : eoHasSmtTranslation body) :
    ∀ (r : List Term), (∀ x ∈ r, eoHasSmtTranslation x) ->
      __substitute_simul_rec (Term.Boolean false)
          (LamSpineSupport.mkSpine
            (LamSpineSupport.lamT (LamSpineSupport.eoVarList vs) body) r) xs ss bvs ≠
        Term.Stuck ->
      ∃ bvsFull,
        EoVarEnvPerm bvsFull (vs.reverse ++ bvsVars) ∧
        (vs ≠ [] ->
          __contains_atomic_term_list_free_rec ss (LamSpineSupport.eoVarList vs)
            Term.__eo_List_nil = Term.Boolean false) ∧
        __substitute_simul_rec (Term.Boolean false)
            (LamSpineSupport.mkSpine
              (LamSpineSupport.lamT (LamSpineSupport.eoVarList vs) body) r) xs ss bvs =
          LamSpineSupport.mkSpine
            (LamSpineSupport.lamT (LamSpineSupport.eoVarList vs)
              (__substitute_simul_rec (Term.Boolean false) body xs ss bvsFull))
            (r.map (fun x => __substitute_simul_rec (Term.Boolean false) x xs ss bvs))
  | [], _, hNe => by
      have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
      have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
      cases vs with
      | nil =>
          refine ⟨bvs, by simpa using hBvsEnv, fun h => absurd rfl h, ?_⟩
          change __substitute_simul_rec (Term.Boolean false)
              (Term.Apply (Term.Apply (Term.UOp UserOp.lambda) Term.__eo_List_nil) body)
              xs ss bvs = _
          change __substitute_simul_rec (Term.Boolean false)
              (Term.Apply (Term.Apply (Term.UOp UserOp.lambda) Term.__eo_List_nil) body)
              xs ss bvs ≠ _ at hNe
          have hNilSub :
              __substitute_simul_rec (Term.Boolean false) Term.__eo_List_nil xs ss bvs =
                Term.__eo_List_nil := by
            rw [SubstituteSupport.substitute_simul_rec_atom _ _ _ _ _ hisr hxs hss hbvs
              (by intro f a h; cases h) (by intro s S h; cases h) (by intro h; cases h)]
            rfl
          have hLamSub :
              __substitute_simul_rec (Term.Boolean false) (Term.UOp UserOp.lambda) xs ss bvs =
                Term.UOp UserOp.lambda := by
            rw [SubstituteSupport.substitute_simul_rec_atom _ _ _ _ _ hisr hxs hss hbvs
              (by intro f a h; cases h) (by intro s S h; cases h) (by intro h; cases h)]
            rfl
          have hHead :
              __substitute_simul_rec (Term.Boolean false)
                  (Term.Apply (Term.UOp UserOp.lambda) Term.__eo_List_nil) xs ss bvs =
                Term.Apply (Term.UOp UserOp.lambda) Term.__eo_List_nil := by
            rw [SubstituteSupport.substitute_simul_rec_apply _ _ _ xs ss bvs hisr hxs hss hbvs
                (by intro q v vs hEq; cases hEq), hLamSub, hNilSub]
            rfl
          rw [SubstituteSupport.substitute_simul_rec_apply _ _ _ xs ss bvs hisr hxs hss hbvs
              (by intro q v vs hEq; injection hEq with _ hEq; cases hEq), hHead] at hNe ⊢
          exact instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hNe
      | cons p vs =>
          obtain ⟨s, T⟩ := p
          refine ⟨__eo_list_concat Term.__eo_List_cons
              (LamSpineSupport.eoVarList ((s, T) :: vs)) bvs,
            EoVarEnvPerm.concat_rev (LamSpineSupport.eoVarEnv_eoVarList _) hBvsEnv, ?_, ?_⟩
          · intro _
            change __substitute_simul_rec (Term.Boolean false)
                (Term.Apply (Term.Apply (Term.UOp UserOp.lambda)
                  (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
                    (LamSpineSupport.eoVarList vs))) body) xs ss bvs ≠ _ at hNe
            rw [SubstituteSupport.substFalse_quant _ _ _ _ _ _ _ hxs hss hbvs] at hNe
            exact support_eo_requires_cond_eq_of_non_stuck hNe
          · change __substitute_simul_rec (Term.Boolean false)
                (Term.Apply (Term.Apply (Term.UOp UserOp.lambda)
                  (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
                    (LamSpineSupport.eoVarList vs))) body) xs ss bvs ≠ _ at hNe
            change __substitute_simul_rec (Term.Boolean false)
                (Term.Apply (Term.Apply (Term.UOp UserOp.lambda)
                  (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
                    (LamSpineSupport.eoVarList vs))) body) xs ss bvs = _
            rw [SubstituteSupport.substFalse_quant _ _ _ _ _ _ _ hxs hss hbvs] at hNe ⊢
            have hReqEq :=
              SubstituteTranslatabilitySupport.instantiate_eo_requires_result_eq_of_ne_stuck hNe
            rw [hReqEq] at hNe ⊢
            exact instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hNe
  | a :: r, hArgs, hNe => by
      have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
      have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
      have hNB := mkSpine_not_binderHead (LamSpineSupport.eoVarList vs) body r hBody
        (fun x hx => hArgs x (List.mem_cons_of_mem _ hx))
      change __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (LamSpineSupport.mkSpine
            (LamSpineSupport.lamT (LamSpineSupport.eoVarList vs) body) r) a) xs ss bvs ≠ _ at hNe
      rw [SubstituteSupport.substitute_simul_rec_apply _ _ _ xs ss bvs hisr hxs hss hbvs
          (fun q v vs' hEq => hNB ⟨q, v, vs', hEq⟩)] at hNe
      have hfNe := instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hNe
      obtain ⟨bvsFull, hEnv, hNoFree, hEq⟩ :=
        substitute_simul_rec_spine xs ss bvs hBvsEnv hxs hss vs body hBody r
          (fun x hx => hArgs x (List.mem_cons_of_mem _ hx)) hfNe
      refine ⟨bvsFull, hEnv, hNoFree, ?_⟩
      change __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (LamSpineSupport.mkSpine
            (LamSpineSupport.lamT (LamSpineSupport.eoVarList vs) body) r) a) xs ss bvs = _
      rw [SubstituteSupport.substitute_simul_rec_apply _ _ _ xs ss bvs hisr hxs hss hbvs
          (fun q v vs' hEq => hNB ⟨q, v, vs', hEq⟩)]
      rw [instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hNe, hEq]
      rfl


/-- Substitution into a spine in rename mode: the lambda's variables are
renamed and its body substituted under the same bound variables. -/
theorem substitute_simul_rec_spine_rename
    (xs ss bvs : Term) {bvsVars : List EoVarKey}
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck)
    (vs : List (native_String × Term)) (body : Term)
    (hBody : eoHasSmtTranslation body) :
    ∀ (r : List Term), (∀ x ∈ r, eoHasSmtTranslation x) ->
      __substitute_simul_rec (Term.Boolean true)
          (LamSpineSupport.mkSpine
            (LamSpineSupport.lamT (LamSpineSupport.eoVarList vs) body) r) xs ss bvs ≠
        Term.Stuck ->
      (vs ≠ [] ->
        __contains_atomic_term_list_free_rec ss (LamSpineSupport.eoVarList vs)
          Term.__eo_List_nil = Term.Boolean false) ∧
      __substitute_simul_rec (Term.Boolean true)
          (LamSpineSupport.mkSpine
            (LamSpineSupport.lamT (LamSpineSupport.eoVarList vs) body) r) xs ss bvs =
        LamSpineSupport.mkSpine
          (LamSpineSupport.lamT
            (__substitute_simul_rec (Term.Boolean true) (LamSpineSupport.eoVarList vs) xs ss bvs)
            (__substitute_simul_rec (Term.Boolean true) body xs ss bvs))
          (r.map (fun x => __substitute_simul_rec (Term.Boolean true) x xs ss bvs))
  | [], _, hNe => by
      have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
      have hisr : (Term.Boolean true : Term) ≠ Term.Stuck := by decide
      cases vs with
      | nil =>
          refine ⟨fun h => absurd rfl h, ?_⟩
          change __substitute_simul_rec (Term.Boolean true)
              (Term.Apply (Term.Apply (Term.UOp UserOp.lambda) Term.__eo_List_nil) body)
              xs ss bvs ≠ _ at hNe
          change __substitute_simul_rec (Term.Boolean true)
              (Term.Apply (Term.Apply (Term.UOp UserOp.lambda) Term.__eo_List_nil) body)
              xs ss bvs = _
          have hLamSub :
              __substitute_simul_rec (Term.Boolean true) (Term.UOp UserOp.lambda) xs ss bvs =
                Term.UOp UserOp.lambda := by
            rw [SubstituteSupport.substitute_simul_rec_atom _ _ _ _ _ hisr hxs hss hbvs
              (by intro f a h; cases h) (by intro s S h; cases h) (by intro h; cases h)]
            rfl
          rw [SubstituteSupport.substitute_simul_rec_apply _ _ _ xs ss bvs hisr hxs hss hbvs
              (by intro q v vs hEq; injection hEq with _ hEq; cases hEq)] at hNe ⊢
          rw [SubstituteSupport.substitute_simul_rec_apply _ _ _ xs ss bvs hisr hxs hss hbvs
              (by intro q v vs hEq; cases hEq), hLamSub] at hNe ⊢
          have hHeadNe := instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hNe
          rw [instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hHeadNe] at hNe ⊢
          exact instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hNe
      | cons p vs =>
          obtain ⟨s, T⟩ := p
          change __substitute_simul_rec (Term.Boolean true)
              (Term.Apply (Term.Apply (Term.UOp UserOp.lambda)
                (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
                  (LamSpineSupport.eoVarList vs))) body) xs ss bvs ≠ _ at hNe
          rw [SubstituteSupport.substTrue_quant _ _ _ _ _ _ _ hxs hss hbvs] at hNe
          have hCap := support_eo_requires_cond_eq_of_non_stuck hNe
          refine ⟨fun _ => hCap, ?_⟩
          change __substitute_simul_rec (Term.Boolean true)
              (Term.Apply (Term.Apply (Term.UOp UserOp.lambda)
                (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
                  (LamSpineSupport.eoVarList vs))) body) xs ss bvs = _
          rw [SubstituteSupport.substTrue_quant _ _ _ _ _ _ _ hxs hss hbvs]
          have hReqEq := instantiate_eo_requires_result_eq_of_ne_stuck hNe
          rw [hReqEq] at hNe ⊢
          have hInner := instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hNe
          rw [instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hNe,
            instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInner]
          rfl
  | a :: r, hArgs, hNe => by
      have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
      have hisr : (Term.Boolean true : Term) ≠ Term.Stuck := by decide
      have hNB := mkSpine_not_binderHead (LamSpineSupport.eoVarList vs) body r hBody
        (fun x hx => hArgs x (List.mem_cons_of_mem _ hx))
      change __substitute_simul_rec (Term.Boolean true)
          (Term.Apply (LamSpineSupport.mkSpine
            (LamSpineSupport.lamT (LamSpineSupport.eoVarList vs) body) r) a) xs ss bvs ≠ _ at hNe
      rw [SubstituteSupport.substitute_simul_rec_apply _ _ _ xs ss bvs hisr hxs hss hbvs
          (fun q v vs' hEq => hNB ⟨q, v, vs', hEq⟩)] at hNe
      have hfNe := instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hNe
      obtain ⟨hCap, hEq⟩ := substitute_simul_rec_spine_rename xs ss bvs hBvsEnv hxs hss vs body
        hBody r (fun x hx => hArgs x (List.mem_cons_of_mem _ hx)) hfNe
      refine ⟨hCap, ?_⟩
      change __substitute_simul_rec (Term.Boolean true)
          (Term.Apply (LamSpineSupport.mkSpine
            (LamSpineSupport.lamT (LamSpineSupport.eoVarList vs) body) r) a) xs ss bvs = _
      rw [SubstituteSupport.substitute_simul_rec_apply _ _ _ xs ss bvs hisr hxs hss hbvs
          (fun q v vs' hEq => hNB ⟨q, v, vs', hEq⟩)]
      rw [instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hNe, hEq]
      rfl

theorem eo_typeof_apply_stuck_left (Y : Term) : __eo_typeof_apply Term.Stuck Y = Term.Stuck := by
  cases Y <;> rfl

theorem eo_typeof_lambda_stuck_body (X L : Term) :
    __eo_typeof_lambda X L Term.Stuck = Term.Stuck := by
  cases L <;> rfl

/-! ## Peeling function types -/

/-- The type a function of type `G` returns, applied to one argument. -/
@[expose] def eoPeel1 : Term -> Term
  | Term.Apply (Term.Apply Term.FunType _) U => U
  | Term.DtcAppType _ U => U
  | _ => Term.Stuck

/-- The type a function of type `G` returns, applied to `n` arguments. -/
@[expose] def eoPeel (G : Term) : Nat -> Term
  | 0 => G
  | n + 1 => eoPeel1 (eoPeel G n)

theorem eoPeel_stuck : ∀ n, eoPeel Term.Stuck n = Term.Stuck
  | 0 => rfl
  | n + 1 => by simp [eoPeel, eoPeel_stuck n, eoPeel1]

theorem eoPeel_add (G : Term) (j : Nat) : ∀ d, eoPeel G (j + d) = eoPeel (eoPeel G j) d
  | 0 => rfl
  | d + 1 => by simp [eoPeel, eoPeel_add G j d]

theorem eoPeel_succ' (G : Term) : ∀ n, eoPeel G (n + 1) = eoPeel (eoPeel1 G) n := by
  intro n
  rw [Nat.add_comm, eoPeel_add G 1 n]
  rfl

theorem eoPeel_ne_stuck_of_le {G : Term} {j k : Nat} (hjk : j ≤ k)
    (h : eoPeel G k ≠ Term.Stuck) : eoPeel G j ≠ Term.Stuck := by
  intro hj
  apply h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  rw [eoPeel_add, hj, eoPeel_stuck]

theorem eo_typeof_apply_eq_peel1 {P V : Term} (h : __eo_typeof_apply P V ≠ Term.Stuck) :
    __eo_typeof_apply P V = eoPeel1 P := by
  revert h
  unfold __eo_typeof_apply
  split <;> intro h
  · exact absurd rfl h
  · exact instantiate_eo_requires_result_eq_of_ne_stuck h
  · exact instantiate_eo_requires_result_eq_of_ne_stuck h
  · exact absurd rfl h

/-- The type of an application spine is its lambda's type with an arrow peeled
off per argument. -/
theorem eo_typeof_mkSpine_eq_peel (us B : Term) :
    ∀ r : List Term,
      __eo_typeof (LamSpineSupport.mkSpine (LamSpineSupport.lamT us B) r) ≠ Term.Stuck ->
      __eo_typeof (LamSpineSupport.mkSpine (LamSpineSupport.lamT us B) r) =
        eoPeel (__eo_typeof (LamSpineSupport.lamT us B)) r.length
  | [], _ => rfl
  | a :: r, h => by
      change __eo_typeof (Term.Apply (LamSpineSupport.mkSpine (LamSpineSupport.lamT us B) r) a) ≠
        Term.Stuck at h
      change __eo_typeof (Term.Apply (LamSpineSupport.mkSpine (LamSpineSupport.lamT us B) r) a) = _
      rw [(LamSpineSupport.lamSpine_mkSpine us B r).eo_typeof_apply a] at h ⊢
      have hHead : __eo_typeof (LamSpineSupport.mkSpine (LamSpineSupport.lamT us B) r) ≠
          Term.Stuck := by
        intro hs; rw [hs, eo_typeof_apply_stuck_left] at h; exact h rfl
      rw [eo_typeof_apply_eq_peel1 h, eo_typeof_mkSpine_eq_peel us B r hHead]
      rfl

theorem eo_typeof_lambda_eq_of_ne_stuck {X L B : Term}
    (h : __eo_typeof_lambda X L B ≠ Term.Stuck) :
    __eo_typeof_lambda X L B = __get_lambda_type L B := by
  revert h
  unfold __eo_typeof_lambda
  split <;> intro h
  · exact absurd rfl h
  · exact absurd rfl h
  · rfl
  · exact absurd rfl h

/-- Renaming a list of variables whose lambda has a type gives a list of
variables of the same types. -/
theorem substitute_simul_rec_rename_vars
    (xs ss bvs : Term) {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars) (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hss : ss ≠ Term.Stuck) (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hEntryTypes : SubstituteSupport.SubstEntryPreservesTypes xs ss) (B : Term)
    (hB : B ≠ Term.Stuck) :
    ∀ (vs : List (native_String × Term)),
      eoPeel (__get_lambda_type
          (__substitute_simul_rec (Term.Boolean true) (LamSpineSupport.eoVarList vs) xs ss bvs)
          B) vs.length ≠ Term.Stuck ->
      ∃ vs' : List (native_String × Term),
        __substitute_simul_rec (Term.Boolean true) (LamSpineSupport.eoVarList vs) xs ss bvs =
          LamSpineSupport.eoVarList vs' ∧
        vs'.map Prod.snd = vs.map Prod.snd
  | [], _ => by
      have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
      have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
      refine ⟨[], ?_, rfl⟩
      change __substitute_simul_rec (Term.Boolean true) Term.__eo_List_nil xs ss bvs = _
      rw [SubstituteSupport.substitute_simul_rec_atom _ _ _ _ _ (by decide) hxs hss hbvs
        (by intro f a h; cases h) (by intro s S h; cases h) (by intro h; cases h)]
      rfl
  | (s, T) :: vs, hNe => by
      have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
      have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
      have hisr : (Term.Boolean true : Term) ≠ Term.Stuck := by decide
      have hConsSub :
          __substitute_simul_rec (Term.Boolean true) Term.__eo_List_cons xs ss bvs =
            Term.__eo_List_cons := by
        rw [SubstituteSupport.substitute_simul_rec_atom _ _ _ _ _ hisr hxs hss hbvs
          (by intro f a h; cases h) (by intro s S h; cases h) (by intro h; cases h)]
        rfl
      have hUnfold :
          __substitute_simul_rec (Term.Boolean true)
              (LamSpineSupport.eoVarList ((s, T) :: vs)) xs ss bvs =
            __eo_mk_apply
              (__eo_mk_apply Term.__eo_List_cons
                (__substitute_simul_rec (Term.Boolean true) (Term.Var (Term.String s) T) xs ss bvs))
              (__substitute_simul_rec (Term.Boolean true) (LamSpineSupport.eoVarList vs)
                xs ss bvs) := by
        change __substitute_simul_rec (Term.Boolean true)
            (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
              (LamSpineSupport.eoVarList vs)) xs ss bvs = _
        rw [SubstituteSupport.substitute_simul_rec_apply _ _ _ xs ss bvs hisr hxs hss hbvs
            (by intro q v vs hEq; injection hEq with _ hEq; cases hEq),
          SubstituteSupport.substitute_simul_rec_apply _ _ _ xs ss bvs hisr hxs hss hbvs
            (by intro q v vs hEq; cases hEq), hConsSub]
      rw [hUnfold] at hNe ⊢
      have hOuterNe : __eo_mk_apply
          (__eo_mk_apply Term.__eo_List_cons
            (__substitute_simul_rec (Term.Boolean true) (Term.Var (Term.String s) T) xs ss bvs))
          (__substitute_simul_rec (Term.Boolean true) (LamSpineSupport.eoVarList vs)
            xs ss bvs) ≠ Term.Stuck := by
        intro h; rw [h] at hNe; exact hNe (by
          rw [show __get_lambda_type Term.Stuck B = Term.Stuck by cases B <;> rfl]
          exact eoPeel_stuck _)
      have hInnerNe := instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNe
      rw [instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hOuterNe,
        instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNe] at hNe ⊢
      -- the renamed head is a variable of the same type
      have hVar : ∃ s', __substitute_simul_rec (Term.Boolean true)
          (Term.Var (Term.String s) T) xs ss bvs = Term.Var (Term.String s') T := by
        by_cases hBound : (s, T) ∈ bvsVars
        · exact ⟨s, SubstituteSupport.substitute_simul_rec_var_bound _ _ _ xs ss bvs hisr hxs hss
            hbvs (hBvsEnv.find_neg_false_of_mem hBound)⟩
        · have hFree := hBvsEnv.find_neg_true_of_not_mem hBound
          by_cases hMapped : (s, T) ∈ xsVars
          · have hFind := hXsEnv.find_neg_false_of_mem hMapped
            rw [SubstituteSupport.substitute_simul_rec_var_mapped _ _ _ xs ss bvs hisr hxs hss
              hbvs hFree hFind] at hNe ⊢
            have hTy := hEntryTypes s T hFind
            have hETrans := SubstituteSupport.assoc_nil_nth_has_smt_translation_of_list_all_and_ne_stuck
              ss (__eo_list_find Term.__eo_List_cons xs (Term.Var (Term.String s) T)) hSsTrans
              (by
                intro h; rw [h] at hNe; exact hNe (by
                  rw [show __get_lambda_type _ B = Term.Stuck by cases B <;> rfl]
                  exact eoPeel_stuck _))
            generalize __assoc_nil_nth Term.__eo_List_cons ss
              (__eo_list_find Term.__eo_List_cons xs (Term.Var (Term.String s) T)) = e at hNe hTy hETrans ⊢
            cases e with
            | Var nm T' =>
                cases nm with
                | String s' =>
                    have : T' = T := by simpa [__eo_typeof] using hTy
                    subst this
                    exact ⟨s', rfl⟩
                | _ =>
                    exact false_of_non_string_var_has_smt_translation
                      (by intro s h; cases h) hETrans
            | _ =>
                exact absurd (by
                  rw [show __get_lambda_type _ B = Term.Stuck by cases B <;> rfl]
                  exact eoPeel_stuck _) hNe
          · exact ⟨s, SubstituteSupport.substitute_simul_rec_var_unmapped _ _ _ xs ss bvs hisr hxs
              hss hbvs hFree (hXsEnv.find_neg_true_of_not_mem hMapped)⟩
      obtain ⟨s', hs'⟩ := hVar
      rw [hs'] at hNe ⊢
      rw [__get_lambda_type.eq_2 B _ _ _ hB, List.length_cons, eoPeel_succ'] at hNe
      have hRestNe := hNe
      obtain ⟨vs', hEq, hTys⟩ :=
        substitute_simul_rec_rename_vars xs ss bvs hXsEnv hBvsEnv hss hSsTrans hEntryTypes B hB vs hRestNe
      refine ⟨(s', T) :: vs', ?_, by simp [hTys]⟩
      rw [hEq]
      rfl

/-! ## Types of spines -/

theorem eo_typeof_lamT (us B : Term) :
    __eo_typeof (LamSpineSupport.lamT us B) =
      __eo_typeof_lambda (__eo_typeof us) us (__eo_typeof B) := by
  change __eo_typeof_lambda (__eo_typeof us) us (__eo_typeof B) = _
  rfl

/-- A spine with a type has a body and arguments with types. -/
theorem eo_typeof_mkSpine_ne_stuck (us B : Term) :
    ∀ r : List Term,
      __eo_typeof (LamSpineSupport.mkSpine (LamSpineSupport.lamT us B) r) ≠ Term.Stuck ->
      __eo_typeof (LamSpineSupport.lamT us B) ≠ Term.Stuck ∧
        ∀ x ∈ r, __eo_typeof x ≠ Term.Stuck
  | [], h => ⟨h, by simp⟩
  | a :: r, h => by
      change __eo_typeof (Term.Apply (LamSpineSupport.mkSpine (LamSpineSupport.lamT us B) r) a) ≠
        Term.Stuck at h
      rw [(LamSpineSupport.lamSpine_mkSpine us B r).eo_typeof_apply a] at h
      have hHead : __eo_typeof (LamSpineSupport.mkSpine (LamSpineSupport.lamT us B) r) ≠
          Term.Stuck := by
        intro hs; rw [hs, eo_typeof_apply_stuck_left] at h; exact h rfl
      have hArg : __eo_typeof a ≠ Term.Stuck := by
        intro hs; rw [hs] at h; exact h (__eo_typeof_apply.eq_1 _)
      obtain ⟨h1, h2⟩ := eo_typeof_mkSpine_ne_stuck us B r hHead
      refine ⟨h1, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hArg
      · exact h2 x hx

/-- The EO type of a spine depends only on the types of its lambda and
arguments. -/
theorem eo_typeof_mkSpine_congr (us B us' B' : Term) (σ : Term -> Term)
    (hLam : __eo_typeof (LamSpineSupport.lamT us' B') = __eo_typeof (LamSpineSupport.lamT us B)) :
    ∀ r : List Term, (∀ x ∈ r, __eo_typeof (σ x) = __eo_typeof x) ->
      __eo_typeof (LamSpineSupport.mkSpine (LamSpineSupport.lamT us' B') (r.map σ)) =
        __eo_typeof (LamSpineSupport.mkSpine (LamSpineSupport.lamT us B) r)
  | [], _ => hLam
  | a :: r, h => by
      change __eo_typeof (Term.Apply
          (LamSpineSupport.mkSpine (LamSpineSupport.lamT us' B') (r.map σ)) (σ a)) =
        __eo_typeof (Term.Apply (LamSpineSupport.mkSpine (LamSpineSupport.lamT us B) r) a)
      rw [(LamSpineSupport.lamSpine_mkSpine us' B' (r.map σ)).eo_typeof_apply (σ a),
        (LamSpineSupport.lamSpine_mkSpine us B r).eo_typeof_apply a,
        eo_typeof_mkSpine_congr us B us' B' σ hLam r (fun x hx => h x (List.mem_cons_of_mem _ hx)),
        h a List.mem_cons_self]

theorem get_lambda_type_eoVarList_congr (B : Term) (hB : B ≠ Term.Stuck) :
    ∀ (vs vs' : List (native_String × Term)), vs'.map Prod.snd = vs.map Prod.snd ->
      __get_lambda_type (LamSpineSupport.eoVarList vs') B =
        __get_lambda_type (LamSpineSupport.eoVarList vs) B
  | [], [], _ => rfl
  | (s, T) :: vs, (s', T') :: vs', h => by
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      change __get_lambda_type (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s') T')) (LamSpineSupport.eoVarList vs')) B =
        __get_lambda_type (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T')) (LamSpineSupport.eoVarList vs)) B
      rw [get_lambda_type_cons hB, get_lambda_type_cons hB,
        get_lambda_type_eoVarList_congr B hB vs vs' h]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem smtx_typeof_bindings_bindsApp_congr (U : SmtType) :
    ∀ (vs vs' : List (native_String × Term)) (l : List Term) (σ : Term -> Term),
      vs'.map (fun p => __eo_to_smt_type p.2) = vs.map (fun p => __eo_to_smt_type p.2) ->
      (∀ x ∈ l, __smtx_typeof (__eo_to_smt (σ x)) = __smtx_typeof (__eo_to_smt x)) ->
      __smtx_typeof_bindings (LamSpineSupport.bindsApp (vs'.zip (l.map σ)) SmtBindings.nil) U =
        __smtx_typeof_bindings (LamSpineSupport.bindsApp (vs.zip l) SmtBindings.nil) U
  | [], [], l, σ, _, _ => by cases l <;> rfl
  | (s, T) :: vs, (s', T') :: vs', [], σ, _, _ => rfl
  | (s, T) :: vs, (s', T') :: vs', a :: l, σ, hT, hl => by
      simp only [List.map_cons, List.cons.injEq] at hT
      obtain ⟨hT1, hT⟩ := hT
      simp only [List.map_cons, List.zip_cons_cons, LamSpineSupport.bindsApp,
        __smtx_typeof_bindings]
      rw [hT1, hl a List.mem_cons_self,
        smtx_typeof_bindings_bindsApp_congr U vs vs' l σ hT
          (fun x hx => hl x (List.mem_cons_of_mem _ hx))]
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h

/-- The SMT type of a spine depends only on those of the types of its lambda's
variables, its body and its arguments. -/
theorem smtx_typeof_mkSpine_congr (vs vs' : List (native_String × Term)) (B B' : Term)
    (σ : Term -> Term)
    (hlen : vs'.length = vs.length)
    (hTys : vs'.map (fun p => __eo_to_smt_type p.2) = vs.map (fun p => __eo_to_smt_type p.2))
    (hB : __smtx_typeof (__eo_to_smt B') = __smtx_typeof (__eo_to_smt B)) :
    ∀ r : List Term, vs.length ≤ r.length ->
      (∀ x ∈ r, __smtx_typeof (__eo_to_smt (σ x)) = __smtx_typeof (__eo_to_smt x)) ->
      __smtx_typeof (__eo_to_smt (LamSpineSupport.mkSpine
          (LamSpineSupport.lamT (LamSpineSupport.eoVarList vs') B') (r.map σ))) =
        __smtx_typeof (__eo_to_smt (LamSpineSupport.mkSpine
          (LamSpineSupport.lamT (LamSpineSupport.eoVarList vs) B) r))
  | r, hm, hArgs => by
      have hv := LamSpineSupport.lamVars_eoVarList vs
      have hv' : lamVars (LamSpineSupport.eoVarList vs') vs.length = true := by
        rw [← hlen]; exact LamSpineSupport.lamVars_eoVarList vs'
      by_cases hmr : vs.length = r.length
      · rw [(LamSpineSupport.lamSpine_mkSpine _ B r).eo_to_smt_full (hmr ▸ hv),
          (LamSpineSupport.lamSpine_mkSpine _ B' (r.map σ)).eo_to_smt_full
            (by simpa [hmr] using hv'),
          smtx_typeof_bind_eq, smtx_typeof_bind_eq,
          LamSpineSupport.lamBindings_eoVarList vs r SmtBindings.nil (by omega),
          LamSpineSupport.lamBindings_eoVarList vs' (r.map σ) SmtBindings.nil (by simp; omega),
          show vs.take r.length = vs by rw [← hmr, List.take_length],
          show vs'.take (r.map σ).length = vs' by rw [List.length_map, ← hmr, ← hlen, List.take_length],
          ← List.map_reverse, hB]
        exact smtx_typeof_bindings_bindsApp_congr _ vs vs' r.reverse σ hTys
          (fun x hx => hArgs x (List.mem_reverse.1 hx))
      · cases r with
        | nil => exact absurd (Nat.le_zero.1 hm) hmr
        | cons a r =>
            simp only [List.length_cons] at hm hmr
            change __smtx_typeof (__eo_to_smt (LamSpineSupport.mkSpine
                (LamSpineSupport.lamT (LamSpineSupport.eoVarList vs') B') (σ a :: r.map σ))) = _
            rw [LamSpineSupport.eo_to_smt_mkSpine_apply_of_lamVars_lt hv a r (by omega),
              LamSpineSupport.eo_to_smt_mkSpine_apply_of_lamVars_lt hv' (σ a) (r.map σ)
                (by simp; omega),
              LamSpineSupport.smtx_typeof_mkSpine_apply, LamSpineSupport.smtx_typeof_mkSpine_apply,
              smtx_typeof_mkSpine_congr vs vs' B B' σ hlen hTys hB r (by omega)
                (fun x hx => hArgs x (List.mem_cons_of_mem _ hx)),
              hArgs a List.mem_cons_self]
termination_by r => r.length

end InstantiateRule
