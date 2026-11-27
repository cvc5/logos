module

public import Cpc.Proofs.Translation.EoTypeofCore
import all Cpc.Proofs.Translation.EoTypeofCore
public import Cpc.Proofs.TypePreservation.Base
import all Cpc.Proofs.TypePreservation.Base
import all Cpc.Spec
public import Cpc.Proofs.ModelEvalBindings
import all Cpc.Proofs.ModelEvalBindings

/-!
# Lambdas and their applications

A lambda is a stub: `(lambda (x1 ... xn) t)` translates to the curried chain
`lam x1 T1 ... (lam xn Tn t)`, which has no type, or to no term when it binds
no variables. An application of a lambda is translated generically, as the SMT
application of that chain, and has no type either.

This file establishes:

* no term translates to a `let`, so none to a lambda waiting for an argument
  (`eo_to_smt_ne_bind`, `eo_to_smt_not_pending`);
* no lambda spine (`LamSpine`) has an SMT type (`LamSpine.smtx_typeof_none`);
* the EO type of a spine, and facts about the variables a lambda binds, which
  the substitution engine uses.
-/

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false

namespace TranslationProofs

/-! ## The SMT side -/

/-- Whether an SMT term is headed by `bind` or `lam`. -/
@[expose] def smtHeadBL : SmtTerm -> Bool
  | SmtTerm.bind _ _ => true
  | SmtTerm.lam _ _ _ => true
  | _ => false

/-- A lambda still waiting for an argument. -/
@[expose] def SmtPendingLam (t : SmtTerm) : Prop :=
  ∃ c s T F, t = SmtTerm.bind c (SmtTerm.lam s T F)

theorem smtx_typeof_lam (s : native_String) (T : SmtType) (F : SmtTerm) :
    __smtx_typeof (SmtTerm.lam s T F) = SmtType.None := by
  rfl

theorem smtx_typeof_bindings_none :
    ∀ bs : SmtBindings, __smtx_typeof_bindings bs SmtType.None = SmtType.None
  | SmtBindings.nil => rfl
  | SmtBindings.cons s T t bs => by
      change native_ite (native_Teq (__smtx_typeof t) T)
          (__smtx_typeof_guard_wf T (__smtx_typeof_bindings bs SmtType.None)) SmtType.None = _
      rw [smtx_typeof_bindings_none bs]
      cases native_Teq (__smtx_typeof t) T <;>
        simp [native_ite, __smtx_typeof_guard_wf]

/-- A lambda still waiting for an argument has no type. -/
theorem smtx_typeof_pending {g : SmtTerm} (h : SmtPendingLam g) :
    __smtx_typeof g = SmtType.None := by
  obtain ⟨c, s, T, F, rfl⟩ := h
  change __smtx_typeof_bindings c (__smtx_typeof (SmtTerm.lam s T F)) = _
  rw [smtx_typeof_lam]
  exact smtx_typeof_bindings_none c

/-! ## Which translations are headed by `bind` or `lam` -/

private theorem smtHeadBL_ite (c : Bool) (a b : SmtTerm) :
    smtHeadBL (native_ite c a b) = native_ite c (smtHeadBL a) (smtHeadBL b) := by
  cases c <;> rfl

private theorem smtHeadBL_re_unfold (n : native_Nat) :
    ∀ s r, smtHeadBL (__eo_to_smt_re_unfold_pos_component s r n) = false := by
  induction n with
  | zero =>
      intro s r; unfold __eo_to_smt_re_unfold_pos_component
      split <;> first | rfl | (exfalso; simp_all; done)
  | succ n ih =>
      intro s r; unfold __eo_to_smt_re_unfold_pos_component
      split <;> first | rfl | (exfalso; simp_all; done) |
        (simp only [Nat.succ.injEq] at *; subst_vars; exact ih _ _)

private theorem smtHeadBL_skolemize (n : native_Nat) :
    ∀ vs G, smtHeadBL (__eo_to_smt_quantifiers_skolemize vs G n) = false := by
  induction n with
  | zero =>
      intro vs G; unfold __eo_to_smt_quantifiers_skolemize
      split <;> first | rfl | (exfalso; simp_all; done)
  | succ n ih =>
      intro vs G; unfold __eo_to_smt_quantifiers_skolemize
      split <;> first | rfl | (exfalso; simp_all; done) |
        (simp only [Nat.succ.injEq] at *; subst_vars; exact ih _ _)

private theorem smtHeadBL_exists (vs : Term) (F : SmtTerm) (h : vs ≠ Term.__eo_List_nil) :
    smtHeadBL (__eo_to_smt_exists vs F) = false := by
  unfold __eo_to_smt_exists
  split
  · exact absurd rfl h
  · rfl
  · rfl

private theorem smtHeadBL_updater (a b c : SmtTerm) :
    smtHeadBL (__eo_to_smt_updater a b c) = false := by
  unfold __eo_to_smt_updater
  split
  · simp only [smtHeadBL_ite]; cases native_zlt _ _ <;> rfl
  · rfl

private theorem smtHeadBL_prepend_rec (dd d tail) : ∀ n acc,
    smtHeadBL acc = false -> smtHeadBL (__eo_to_smt_tuple_prepend_rec dd d tail n acc) = false
  | 0, _, h => h
  | _ + 1, _, _ => rfl

private theorem smtHeadBL_tuple_prepend (h : SmtTerm) (hT : SmtType) (tail : SmtTerm) :
    smtHeadBL (__eo_to_smt_tuple_prepend h hT tail) = false := by
  unfold __eo_to_smt_tuple_prepend __eo_to_smt_tuple_prepend_of_type
  split
  · simp only [smtHeadBL_ite]
    cases native_and _ _ <;> first | rfl | (apply smtHeadBL_prepend_rec; rfl)
  · rfl

private theorem smtHeadBL_tuple_select (T a b) :
    smtHeadBL (__eo_to_smt_tuple_select T a b) = false := by
  unfold __eo_to_smt_tuple_select
  split
  · simp only [smtHeadBL_ite]; cases native_and _ _ <;> rfl
  · rfl

private theorem smtHeadBL_tuple_update (T a b c) :
    smtHeadBL (__eo_to_smt_tuple_update T a b c) = false := by
  unfold __eo_to_smt_tuple_update
  split
  · simp only [smtHeadBL_ite, smtHeadBL_updater]; cases native_and _ _ <;> rfl
  · rfl

private theorem smtHeadBL_distinct (t) : smtHeadBL (__eo_to_smt_distinct t) = false := by
  unfold __eo_to_smt_distinct; split <;> rfl

private theorem smtHeadBL_array_deq_diff (a T b U) :
    smtHeadBL (__eo_to_smt_array_deq_diff a T b U) = false := by
  unfold __eo_to_smt_array_deq_diff; split <;> rfl

private theorem smtHeadBL_sets_deq_diff (a T b U) :
    smtHeadBL (__eo_to_smt_sets_deq_diff a T b U) = false := by
  unfold __eo_to_smt_sets_deq_diff; split <;> rfl

private theorem smtHeadBL_seq_empty (T) : smtHeadBL (__eo_to_smt_seq_empty T) = false := by
  unfold __eo_to_smt_seq_empty; split <;> rfl

private theorem smtHeadBL_set_empty (T) : smtHeadBL (__eo_to_smt_set_empty T) = false := by
  unfold __eo_to_smt_set_empty; split <;> rfl

/-- Only a lambda translates to a term headed by `bind` or `lam`. -/
theorem eo_to_smt_headBL_cases (t : Term) (h : smtHeadBL (__eo_to_smt t) = true) :
    ∃ us body, t = Term.Apply (Term.Apply (Term.UOp UserOp.lambda) us) body := by
  generalize hr : __eo_to_smt t = r at h ⊢
  rw [__eo_to_smt.eq_def] at hr
  split at hr <;> subst hr
  all_goals first
    | exact ⟨_, _, rfl⟩
    | (exfalso; revert h
       try simp only [smtHeadBL_ite, smtHeadBL_re_unfold, smtHeadBL_skolemize,
         smtHeadBL_updater, smtHeadBL_tuple_prepend, smtHeadBL_tuple_select,
         smtHeadBL_tuple_update, smtHeadBL_distinct, smtHeadBL_array_deq_diff,
         smtHeadBL_sets_deq_diff, smtHeadBL_seq_empty, smtHeadBL_set_empty]
       simp [smtHeadBL, native_ite]; done)
    | (exfalso; rename_i hne; rw [smtHeadBL_exists _ _ hne] at h; cases h)

/-! ## Lambda spines -/

/-- `t` is the lambda `(lambda us body)` applied to the arguments `rargs`,
listed last argument first. -/
inductive LamSpine : Term -> Term -> Term -> List Term -> Prop
  | lam (us body : Term) :
      LamSpine (Term.Apply (Term.Apply (Term.UOp UserOp.lambda) us) body) us body []
  | app {f us body : Term} {rargs : List Term} (a : Term) :
      LamSpine f us body rargs -> LamSpine (Term.Apply f a) us body (a :: rargs)

/-- Whether `t` is an application spine headed by a lambda. -/
@[expose] def IsLamSpine (t : Term) : Prop := ∃ us body rargs, LamSpine t us body rargs

/-- The leftmost leaf of an application spine. -/
@[expose] def eoSpineHead : Term -> Term
  | Term.Apply f _ => eoSpineHead f
  | t => t

/-- The list `vs` without its first `k` elements. -/
@[expose] def eoListDrop : Nat -> Term -> Term
  | 0, vs => vs
  | k + 1, Term.Apply (Term.Apply Term.__eo_List_cons _) vs => eoListDrop k vs
  | _ + 1, _ => Term.Stuck

/-- Whether a lambda may bind a variable of type `T`: its translation is a type
a function can take (`__eo_to_smt_lambda_curry` checks the same). -/
@[expose] def lamVarWf (T : Term) : Bool :=
  __smtx_type_wf_component (__eo_to_smt_type T)

/-- Whether `vs` is a list of exactly `n` variables a lambda may bind. -/
@[expose] def lamVars : Term -> Nat -> Bool
  | Term.__eo_List_nil, 0 => true
  | Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String _) T)) vs, n + 1 =>
      lamVarWf T && lamVars vs n
  | _, _ => false

/-- Whether `vs` begins with `n` variables a lambda may bind. -/
@[expose] def lamVarsPrefix : Term -> Nat -> Bool
  | _, 0 => true
  | us, n + 1 =>
      match us with
      | Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String _) T)) vs =>
          lamVarWf T && lamVarsPrefix vs n
      | _ => false
termination_by structural _ n => n

/-- The `n`-th element of the list `vs`. -/
@[expose] def lamNth : Term -> Nat -> Term
  | Term.Apply (Term.Apply Term.__eo_List_cons v) _, 0 => v
  | Term.Apply (Term.Apply Term.__eo_List_cons _) vs, n + 1 => lamNth vs n
  | _, _ => Term.Stuck

/-- The binding of the variable `v` to `a`, in front of `bs`. -/
@[expose] def lamBinding : Term -> SmtTerm -> SmtBindings -> SmtBindings
  | Term.Var (Term.String s) T, a, bs => SmtBindings.cons s (__eo_to_smt_type T) a bs
  | _, _, bs => bs

/-- The bindings of the arguments `rargs` (last first) to the variables of `vs`,
in front of `bs`. -/
@[expose] def lamBindings (vs : Term) : List Term -> SmtBindings -> SmtBindings
  | [], bs => bs
  | a :: r, bs => lamBindings vs r (lamBinding (lamNth vs r.length) (__eo_to_smt a) bs)

/-- The arguments are typed as the variables they are bound to. -/
@[expose] def LamArgsTyped (us : Term) : List Term -> Prop
  | [] => True
  | a :: r =>
      (∀ s T, lamNth us r.length = Term.Var (Term.String s) T ->
        __eo_typeof a = T ∧ T ≠ Term.Stuck) ∧
      LamArgsTyped us r

namespace LamSpine

theorem shape {t us body : Term} {r : List Term} (h : LamSpine t us body r) :
    ∃ g c b, t = Term.Apply (Term.Apply g c) b := by
  induction h with
  | lam => exact ⟨_, _, _, rfl⟩
  | app a hf ih =>
      obtain ⟨g, c, b, rfl⟩ := ih
      exact ⟨_, _, _, rfl⟩

/-- A spine is its lambda, or an application of a spine (one level deeper than
`shape`, so that translation equations reduce). -/
theorem deep_shape {t us body : Term} {r : List Term} (h : LamSpine t us body r) :
    t = Term.Apply (Term.Apply (Term.UOp UserOp.lambda) us) body ∨
      ∃ g c b a, t = Term.Apply (Term.Apply (Term.Apply g c) b) a := by
  cases h with
  | lam => exact Or.inl rfl
  | app a hf =>
      obtain ⟨g, c, b, rfl⟩ := hf.shape
      exact Or.inr ⟨_, _, _, _, rfl⟩

theorem head {t us body : Term} {r : List Term} (h : LamSpine t us body r) :
    eoSpineHead t = Term.UOp UserOp.lambda := by
  induction h with
  | lam => rfl
  | app a _ ih => exact ih

theorem sizeOf_lt {t us body : Term} {r : List Term} (h : LamSpine t us body r) :
    sizeOf body < sizeOf t ∧ ∀ a ∈ r, sizeOf a < sizeOf t := by
  induction h with
  | lam => exact ⟨by simp <;> omega, by simp⟩
  | app a hf ih =>
      refine ⟨by have := ih.1; simp <;> omega, ?_⟩
      intro a' ha'
      simp only [List.mem_cons] at ha'
      rcases ha' with rfl | ha'
      · simp <;> omega
      · have := ih.2 a' ha'
        simp <;> omega

/-- An application of a spine is translated generically. -/
theorem eo_to_smt_app {f us body : Term} {r : List Term} (h : LamSpine f us body r)
    (a : Term) :
    __eo_to_smt (Term.Apply f a) = SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a) := by
  cases h with
  | lam => rfl
  | app b hf =>
      rcases hf.deep_shape with hfe | ⟨g, c, b', a', hfe⟩ <;> subst hfe <;> rfl

/-- A spine translates to no term, a `lam`, or an SMT application. -/
theorem eo_to_smt_shape {t us body : Term} {r : List Term} (h : LamSpine t us body r) :
    __eo_to_smt t = SmtTerm.None ∨ (∃ s T G, __eo_to_smt t = SmtTerm.lam s T G) ∨
      ∃ g x, __eo_to_smt t = SmtTerm.Apply g x := by
  cases h with
  | lam us body =>
      rcases eo_to_smt_lambda_shape us body with hc | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inl hc)
  | app a hf => exact Or.inr (Or.inr ⟨_, _, hf.eo_to_smt_app a⟩)

/-- A lambda is a stub: no spine has a type. -/
theorem smtx_typeof_none {t us body : Term} {r : List Term} (h : LamSpine t us body r) :
    __smtx_typeof (__eo_to_smt t) = SmtType.None := by
  induction h with
  | lam us body =>
      rcases eo_to_smt_lambda_shape us body with hc | ⟨_, _, _, hc⟩ <;> rw [hc]
      · exact TranslationProofs.smtx_typeof_none
      · rfl
  | @app f us body r a hf ih =>
      rw [hf.eo_to_smt_app a]
      have h2 : __smtx_typeof (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a)) =
          __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f)) (__smtx_typeof (__eo_to_smt a)) := by
        rcases hf.eo_to_smt_shape with hc | ⟨_, _, _, hc⟩ | ⟨_, _, hc⟩ <;> rw [hc] <;> rfl
      rw [h2, ih]
      rfl

/-- The EO type of an application of a spine is the generic one. -/
theorem eo_typeof_apply {f us body : Term} {r : List Term} (h : LamSpine f us body r)
    (a : Term) :
    __eo_typeof (Term.Apply f a) = __eo_typeof_apply (__eo_typeof f) (__eo_typeof a) := by
  cases h with
  | lam => rfl
  | app b hf =>
      rcases hf.deep_shape with hfe | ⟨g, c, b', a', hfe⟩ <;> subst hfe <;> rfl

end LamSpine

theorem isLamSpine_apply {f : Term} (h : IsLamSpine f) (a : Term) :
    IsLamSpine (Term.Apply f a) := by
  obtain ⟨us, body, r, h⟩ := h
  exact ⟨us, body, a :: r, LamSpine.app a h⟩

theorem not_isLamSpine_of_head {t : Term}
    (h : eoSpineHead t ≠ Term.UOp UserOp.lambda) : ¬ IsLamSpine t := by
  rintro ⟨us, body, r, hs⟩
  exact h hs.head

/-! ## Pending lambdas come from lambda spines -/

/-- No term translates to a `let`. -/
theorem eo_to_smt_ne_bind (t : Term) (bs : SmtBindings) (F : SmtTerm) :
    __eo_to_smt t ≠ SmtTerm.bind bs F := by
  intro h
  obtain ⟨us, body, rfl⟩ := eo_to_smt_headBL_cases t (by rw [h]; rfl)
  rcases eo_to_smt_lambda_shape us body with hc | ⟨_, _, _, hc⟩ <;> rw [hc] at h <;> cases h

/-- No term translates to a lambda waiting for an argument. -/
theorem eo_to_smt_not_pending (t : Term) : ¬ SmtPendingLam (__eo_to_smt t) := by
  rintro ⟨c, s, T, F, h⟩
  exact eo_to_smt_ne_bind t c _ h

/-- Only a lambda spine translates to a lambda still waiting for an argument
(vacuously: none does). -/
theorem eo_to_smt_pending_spine (t : Term) (hp : SmtPendingLam (__eo_to_smt t)) :
    IsLamSpine t :=
  absurd hp (eo_to_smt_not_pending t)

/-! ## Variable lists -/

theorem lambda_vars_zero_inv {us : Term}
    (h : lamVars us 0 = true) : us = Term.__eo_List_nil := by
  by_contra hne
  rw [lamVars.eq_3 us 0 (fun h1 _ => hne h1)
    (fun _ _ _ _ _ h2 => Nat.noConfusion h2)] at h
  cases h

theorem lambda_vars_succ_inv {us : Term} {n : Nat}
    (h : lamVars us (n + 1) = true) :
    ∃ s T vs,
      us = Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) vs ∧
        lamVars vs n = true := by
  by_contra hne
  rw [lamVars.eq_3 us (n + 1) (fun _ h2 => Nat.noConfusion h2)
    (fun s T vs n' h1 h2 => hne ⟨s, T, vs, h1, by
      subst h1
      have hn := Nat.succ.inj h2
      subst hn
      simp only [lamVars, Bool.and_eq_true] at h
      exact h.2⟩)] at h
  cases h

theorem lambda_vars_succ_wf {s : native_String} {T vs : Term} {n : Nat}
    (h : lamVars (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) vs)
      (n + 1) = true) : lamVarWf T = true := by
  simp only [lamVars, Bool.and_eq_true] at h
  exact h.1

theorem lambda_vars_split :
    ∀ (k : Nat) {us : Term} {m : Nat},
      lamVars us m = true -> k < m ->
      ∃ s T,
        lamNth us k = Term.Var (Term.String s) T ∧
          eoListDrop k us =
            Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
              (eoListDrop (k + 1) us)
  | k, us, 0, _, hk => absurd hk (Nat.not_lt_zero _)
  | 0, us, m + 1, h, _ => by
      obtain ⟨s, T, vs, rfl, _⟩ := lambda_vars_succ_inv h
      exact ⟨s, T, rfl, rfl⟩
  | k + 1, us, m + 1, h, hk => by
      obtain ⟨s, T, vs, rfl, hvs⟩ := lambda_vars_succ_inv h
      obtain ⟨s', T', hn, hd⟩ := lambda_vars_split k hvs (by omega)
      exact ⟨s', T', hn, hd⟩

theorem lambda_vars_drop_all :
    ∀ (m : Nat) {us : Term}, lamVars us m = true ->
      eoListDrop m us = Term.__eo_List_nil
  | 0, us, h => lambda_vars_zero_inv h
  | m + 1, us, h => by
      obtain ⟨s, T, vs, rfl, hvs⟩ := lambda_vars_succ_inv h
      exact lambda_vars_drop_all m hvs

theorem lamVarsPrefix_succ_inv {us : Term} {k : Nat}
    (h : lamVarsPrefix us (k + 1) = true) :
    ∃ s T vs,
      us = Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) vs ∧
        lamVarsPrefix vs k = true := by
  unfold lamVarsPrefix at h
  split at h
  · simp only [Bool.and_eq_true] at h
    exact ⟨_, _, _, rfl, h.2⟩
  · cases h

theorem lamVarsPrefix_succ_wf {s : native_String} {T vs : Term} {k : Nat}
    (h : lamVarsPrefix
      (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) vs) (k + 1) =
        true) : lamVarWf T = true := by
  simp only [lamVarsPrefix, Bool.and_eq_true] at h
  exact h.1

theorem lamVarsPrefix_pred :
    ∀ (k : Nat) {us : Term}, lamVarsPrefix us (k + 1) = true -> lamVarsPrefix us k = true
  | 0, us, _ => rfl
  | k + 1, us, h => by
      obtain ⟨s, T, vs, rfl, hvs⟩ := lamVarsPrefix_succ_inv h
      have hw := lamVarsPrefix_succ_wf h
      show (lamVarWf T && lamVarsPrefix vs k) = true
      rw [hw, lamVarsPrefix_pred k hvs]
      rfl

/-- Where the first `k + 1` elements of `us` are variables, the list without
its first `k` begins with one. -/
theorem lamVarsPrefix_drop :
    ∀ (k : Nat) {us : Term}, lamVarsPrefix us (k + 1) = true ->
      ∃ s T vs, eoListDrop k us =
        Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) vs
  | 0, us, h => by
      obtain ⟨s, T, vs, rfl, _⟩ := lamVarsPrefix_succ_inv h
      exact ⟨s, T, vs, rfl⟩
  | k + 1, us, h => by
      obtain ⟨s, T, vs, rfl, hvs⟩ := lamVarsPrefix_succ_inv h
      exact lamVarsPrefix_drop k hvs

/-- Where the list `us` has a variable after its first `k` elements, its first
`k + 1` elements are variables when its first `k` are, and that variable is its
`k`-th element. -/
theorem lamVarsPrefix_succ :
    ∀ (k : Nat) (us : Term) {s : native_String} {T vs : Term},
      lamVarsPrefix us k = true ->
      eoListDrop k us =
        Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) vs ->
      lamVarWf T = true ->
      lamVarsPrefix us (k + 1) = true ∧ eoListDrop (k + 1) us = vs ∧
        lamNth us k = Term.Var (Term.String s) T
  | 0, us, s, T, vs, _, hd, hwf => by
      change us = _ at hd
      subst hd
      refine ⟨?_, rfl, rfl⟩
      show (lamVarWf T && lamVarsPrefix vs 0) = true
      rw [hwf]
      rfl
  | k + 1, us, s, T, vs, hp, hd, hwf => by
      obtain ⟨s', T', us', rfl, hp'⟩ := lamVarsPrefix_succ_inv hp
      have hw' := lamVarsPrefix_succ_wf hp
      obtain ⟨h1, h2, h3⟩ := lamVarsPrefix_succ k us' hp' hd hwf
      refine ⟨?_, h2, h3⟩
      show (lamVarWf T' && lamVarsPrefix us' (k + 1)) = true
      rw [hw', h1]
      rfl

/-- Where the list `us` has, after its first `k` elements, a variable a lambda
may not bind, its first `k + 1` elements are not variables a lambda may bind. -/
theorem lamVarsPrefix_succ_false_of_not_wf :
    ∀ (k : Nat) (us : Term) {s : native_String} {T vs : Term},
      eoListDrop k us =
        Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) vs ->
      lamVarWf T = false ->
      lamVarsPrefix us (k + 1) = false
  | 0, us, s, T, vs, hd, hwf => by
      change us = _ at hd
      subst hd
      simp [lamVarsPrefix, hwf]
  | k + 1, us, s, T, vs, hd, hwf => by
      unfold lamVarsPrefix
      split
      · rename_i s' T' us'
        simp only [Bool.and_eq_false_iff]
        exact Or.inr (lamVarsPrefix_succ_false_of_not_wf k us' hd hwf)
      · rfl

/-- A list that begins with `k` variables and has nothing after them is a list
of exactly `k` variables. -/
theorem lamVars_of_prefix :
    ∀ (k : Nat) (us : Term), lamVarsPrefix us k = true ->
      eoListDrop k us = Term.__eo_List_nil -> lamVars us k = true
  | 0, us, _, hd => by
      change us = Term.__eo_List_nil at hd
      subst hd
      rfl
  | k + 1, us, hp, hd => by
      obtain ⟨s, T, vs, rfl, hvs⟩ := lamVarsPrefix_succ_inv hp
      have hw := lamVarsPrefix_succ_wf hp
      show (lamVarWf T && lamVars vs (k + 1 - 1)) = true
      rw [hw, show k + 1 - 1 = k from rfl, lamVars_of_prefix k vs hvs hd]
      rfl

theorem lamVarsPrefix_of_lamVars :
    ∀ (m : Nat) {us : Term}, lamVars us m = true -> lamVarsPrefix us m = true
  | 0, us, _ => rfl
  | m + 1, us, h => by
      obtain ⟨s, T, vs, rfl, hvs⟩ := lambda_vars_succ_inv h
      have hw := lambda_vars_succ_wf h
      show (lamVarWf T && lamVarsPrefix vs m) = true
      rw [hw, lamVarsPrefix_of_lamVars m hvs]
      rfl

/-! ## The curried chain of a lambda -/

theorem curry_cons (s : native_String) (T vs : Term) (F : SmtTerm) :
    __eo_to_smt_lambda_curry
        (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) vs) F =
      native_ite (lamVarWf T)
        (SmtTerm.lam s (__eo_to_smt_type T) (__eo_to_smt_lambda_curry vs F)) SmtTerm.None := rfl

theorem curry_cons_of_wf (s : native_String) (T vs : Term) (F : SmtTerm)
    (h : lamVarWf T = true) :
    __eo_to_smt_lambda_curry
        (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) vs) F =
      SmtTerm.lam s (__eo_to_smt_type T) (__eo_to_smt_lambda_curry vs F) := by
  rw [curry_cons, h]
  rfl

theorem curry_cons_of_not_wf (s : native_String) (T vs : Term) (F : SmtTerm)
    (h : lamVarWf T = false) :
    __eo_to_smt_lambda_curry
        (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) vs) F =
      SmtTerm.None := by
  rw [curry_cons, h]
  rfl

/-! ## The translation of a spine -/

/-- A typed application of a lambda waiting for an argument applies the lambda
to as many arguments as it binds variables (vacuously: no lambda is waiting). -/
theorem lamVars_of_pending_app {f us body : Term} {r : List Term} (y : Term)
    (hs : LamSpine f us body r) (hp : SmtPendingLam (__eo_to_smt f))
    (hNN : term_has_non_none_type (__eo_to_smt (Term.Apply f y))) :
    lamVars us (y :: r).length = true :=
  absurd hp (eo_to_smt_not_pending f)

/-! ## Typing applications of lambdas -/

theorem eo_typeof_apply_fun_self {T U : Term} (hT : T ≠ Term.Stuck) :
    __eo_typeof_apply (Term.Apply (Term.Apply Term.FunType T) U) T = U := by
  rw [__eo_typeof_apply.eq_def]
  by_cases hStuck : T = Term.Stuck
  · exact False.elim (hT hStuck)
  · simp [hStuck, __eo_requires.eq_def, native_teq, native_ite, native_not]

theorem eo_typeof_lambda_vars :
    ∀ (m : Nat) {us : Term}, lamVars us m = true ->
      __eo_typeof us = Term.__eo_List
  | 0, us, h => by
      rw [lambda_vars_zero_inv h]
      rfl
  | m + 1, us, h => by
      obtain ⟨s, T, vs, rfl, hvs⟩ := lambda_vars_succ_inv h
      change __eo_typeof_apply
          (Term.Apply (Term.Apply Term.FunType Term.__eo_List) Term.__eo_List)
          (__eo_typeof vs) = _
      rw [eo_typeof_lambda_vars m hvs]
      exact eo_typeof_apply_fun_self (by decide)

theorem get_lambda_type_cons {s T vs B : Term} (hB : B ≠ Term.Stuck) :
    __get_lambda_type
        (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var s T)) vs) B =
      __eo_mk_apply (__eo_mk_apply Term.FunType T) (__get_lambda_type vs B) :=
  __get_lambda_type.eq_2 B s T vs hB

/-- The function type `__get_lambda_type` builds with `__eo_mk_apply` is the
plain one when neither component is stuck. -/
theorem eo_mk_apply_fun_type_eq {T U : Term} (hT : T ≠ Term.Stuck)
    (hU : U ≠ Term.Stuck) :
    __eo_mk_apply (__eo_mk_apply Term.FunType T) U =
      Term.Apply (Term.Apply Term.FunType T) U := by
  have hInner : __eo_mk_apply Term.FunType T = Term.Apply Term.FunType T := by
    cases T <;> first | rfl | exact absurd rfl hT
  rw [hInner]
  cases U <;> first | rfl | exact absurd rfl hU

theorem lamBindings_mem (vs : Term) :
    ∀ (r : List Term) (bs : SmtBindings) {s : native_String} {T : SmtType} {v : SmtTerm},
      SmtBindings.Mem bs s T v -> SmtBindings.Mem (lamBindings vs r bs) s T v
  | [], bs, s, T, v, hm => hm
  | a :: r, bs, s, T, v, hm => by
      apply lamBindings_mem vs r
      unfold lamBinding
      split
      · exact SmtBindings.Mem.tail _ _ _ hm
      · exact hm

/-- A binding of `lamBindings` binds an argument, or comes from the accumulator. -/
theorem lamBindings_mem_inv (vs : Term) :
    ∀ (r : List Term) (bs : SmtBindings) {s : native_String} {T : SmtType} {v : SmtTerm},
      SmtBindings.Mem (lamBindings vs r bs) s T v ->
        SmtBindings.Mem bs s T v ∨ ∃ a ∈ r, v = __eo_to_smt a
  | [], bs, s, T, v, hm => Or.inl hm
  | a :: r, bs, s, T, v, hm => by
      rcases lamBindings_mem_inv vs r _ hm with hm | ⟨a', ha', rfl⟩
      · revert hm
        unfold lamBinding
        split
        · intro hm
          cases hm with
          | head => exact Or.inr ⟨a, List.mem_cons_self, rfl⟩
          | tail _ _ _ hm => exact Or.inl hm
        · intro hm
          exact Or.inl hm
      · exact Or.inr ⟨a', List.mem_cons_of_mem a ha', rfl⟩

/-- Every argument of a well-formed spine is bound to a variable. -/
theorem lamBindings_mem_arg {us : Term} {m : Nat}
    (hvars : lamVars us m = true) :
    ∀ (r : List Term) (bs : SmtBindings), r.length ≤ m ->
      ∀ a ∈ r, ∃ s T, SmtBindings.Mem (lamBindings us r bs) s T (__eo_to_smt a)
  | [], bs, _, a, ha => absurd ha List.not_mem_nil
  | a :: r, bs, hlen, a', ha' => by
      simp only [List.length_cons] at hlen
      rcases List.mem_cons.1 ha' with rfl | ha'
      · obtain ⟨s, T, hn, _⟩ := lambda_vars_split r.length hvars (by omega)
        refine ⟨s, __eo_to_smt_type T, ?_⟩
        change SmtBindings.Mem (lamBindings us r
          (lamBinding (lamNth us r.length) (__eo_to_smt a') bs)) _ _ _
        rw [hn]
        exact lamBindings_mem us r _ (SmtBindings.Mem.head _ _ _ _)
      · exact lamBindings_mem_arg hvars r _ (by omega) a' ha'

private theorem smtx_type_wf_none_false : __smtx_type_wf SmtType.None = false := by
  decide +kernel

theorem lamArgsTyped_of_bindings (vs : Term) :
    ∀ (r : List Term) (bs : SmtBindings),
      (∀ s T v, SmtBindings.Mem (lamBindings vs r bs) s T v ->
        __smtx_typeof v = T ∧ __smtx_type_wf T = true) ->
      (∀ a ∈ r, __smtx_typeof (__eo_to_smt a) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) ∧
          eo_type_valid (__eo_typeof a)) ->
      LamArgsTyped vs r
  | [], bs, _, _ => trivial
  | a :: r, bs, hb, ih => by
      refine ⟨?_, lamArgsTyped_of_bindings vs r _ hb
        (fun a' ha' => ih a' (List.mem_cons_of_mem a ha'))⟩
      intro s T hn
      have hm :
          SmtBindings.Mem (lamBindings vs (a :: r) bs) s (__eo_to_smt_type T) (__eo_to_smt a) := by
        change SmtBindings.Mem (lamBindings vs r
          (lamBinding (lamNth vs r.length) (__eo_to_smt a) bs)) _ _ _
        rw [hn]
        exact lamBindings_mem vs r _ (SmtBindings.Mem.head _ _ _ _)
      obtain ⟨hTy, hWf⟩ := hb _ _ _ hm
      have hNN : __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
        rw [hTy]
        intro hNone
        rw [hNone, smtx_type_wf_none_false] at hWf
        cases hWf
      obtain ⟨hA, hValid⟩ := ih a (List.mem_cons_self) hNN
      have hEq : __eo_typeof a = T :=
        eo_to_smt_type_eq_of_valid hValid (by rw [← hA, hTy])
      exact ⟨hEq, hEq ▸ eo_type_valid_not_stuck hValid⟩

/-- A typed spine that applies its lambda to as many arguments as it binds
variables has, as its SMT type, the translation of its EO type (vacuously: no
spine is typed). -/
theorem eo_to_smt_typeof_matches_translation_lam_spine
    {t us body : Term} {r : List Term} (h : LamSpine t us body r)
    (hv : lamVars us r.length = true)
    (ih :
      ∀ u, sizeOf u < sizeOf t ->
        __smtx_typeof (__eo_to_smt u) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt u) = __eo_to_smt_type (__eo_typeof u) ∧
          eo_type_valid (__eo_typeof u))
    (hNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t) ∧
      eo_type_valid (__eo_typeof t) :=
  absurd h.smtx_typeof_none hNN

/-- A typed lambda has, as its SMT type, the translation of its EO type
(vacuously: no lambda is typed). -/
theorem eo_to_smt_typeof_matches_translation_lambda (us body : Term)
    (ih :
      ∀ u, sizeOf u < sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.lambda) us) body) ->
        __smtx_typeof (__eo_to_smt u) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt u) = __eo_to_smt_type (__eo_typeof u) ∧
          eo_type_valid (__eo_typeof u))
    (hNN :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.lambda) us) body)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.lambda) us) body)) =
        __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lambda) us) body)) ∧
      eo_type_valid
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lambda) us) body)) :=
  absurd (LamSpine.lam us body).smtx_typeof_none hNN

/-- A typed spine binds a list of variables, and its body and arguments are
typed (vacuously: no spine is typed). -/
theorem LamSpine.parts_typed_any {t us body : Term} {r : List Term}
    (h : LamSpine t us body r)
    (hNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None) :
    (∃ m, lamVars us m = true) ∧
      __smtx_typeof (__eo_to_smt body) ≠ SmtType.None ∧
      ∀ a ∈ r, __smtx_typeof (__eo_to_smt a) ≠ SmtType.None :=
  absurd h.smtx_typeof_none hNN

/-- Typing of a generically translated application `(f y)`, by `hGeneric` from
the SMT application it translates to. -/
theorem eo_to_smt_typeof_matches_translation_generic_or_spine
    (f y : Term)
    (ih :
      ∀ u, sizeOf u < sizeOf (Term.Apply f y) ->
        __smtx_typeof (__eo_to_smt u) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt u) = __eo_to_smt_type (__eo_typeof u) ∧
          eo_type_valid (__eo_typeof u))
    (hgen :
      __eo_to_smt (Term.Apply f y) = SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt y))
    (hGeneric :
      __eo_to_smt (Term.Apply f y) = SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt y) ->
      __smtx_typeof (__eo_to_smt (Term.Apply f y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply f y)))
    (hNN : __smtx_typeof (__eo_to_smt (Term.Apply f y)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply f y)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply f y)) :=
  hGeneric hgen

end TranslationProofs
