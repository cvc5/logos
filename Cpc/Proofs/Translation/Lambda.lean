module

public import Cpc.Proofs.Translation.EoTypeofCore
import all Cpc.Proofs.Translation.EoTypeofCore
public import Cpc.Proofs.TypePreservation.Base
import all Cpc.Proofs.TypePreservation.Base
import all Cpc.Spec

/-!
# Beta redexes

An application spine headed by a lambda, `(_ (lambda us body) a1 ... an)`,
translates to the (parallel) `let` of `body` binding each variable of `us` to
its argument, when `us` is a list of exactly `n` variables, and to no term
otherwise. This file gives that translation a structural form (`LamSpine`,
`lamBindings`) and proves that, when it is typed, its SMT type is the
translation of the EO type of the redex.
-/

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false

namespace TranslationProofs

/-- `t` is the lambda `(lambda us body)` applied to the arguments `rargs`,
listed last argument first. -/
inductive LamSpine : Term -> Term -> Term -> List Term -> Prop
  | lam (us body : Term) :
      LamSpine (Term.Apply (Term.Apply (Term.UOp UserOp.lambda) us) body) us body []
  | app {f us body : Term} {rargs : List Term} (a : Term) :
      LamSpine f us body rargs -> LamSpine (Term.Apply f a) us body (a :: rargs)

/-- Whether `t` is an application spine headed by a lambda. -/
@[expose] def IsLamSpine (t : Term) : Prop := ∃ us body rargs, LamSpine t us body rargs

/-- The bindings of the arguments `rargs` (last first) to the variables of `vs`,
in front of `bs`, as the translation builds them. -/
@[expose] def lamBindings (vs : Term) : List Term -> SmtBindings -> SmtBindings
  | [], bs => bs
  | a :: r, bs =>
      lamBindings vs r
        (__eo_to_smt_lambda_binding (__eo_to_smt_lambda_nth vs r.length) (__eo_to_smt a) bs)

/-- The leftmost leaf of an application spine. -/
@[expose] def eoSpineHead : Term -> Term
  | Term.Apply f _ => eoSpineHead f
  | t => t

/-- The list `vs` without its first `k` elements. -/
@[expose] def eoListDrop : Nat -> Term -> Term
  | 0, vs => vs
  | k + 1, Term.Apply (Term.Apply Term.__eo_List_cons _) vs => eoListDrop k vs
  | _ + 1, _ => Term.Stuck

/-- The arguments are typed as the variables they are bound to. -/
@[expose] def LamArgsTyped (us : Term) : List Term -> Prop
  | [] => True
  | a :: r =>
      (∀ s T, __eo_to_smt_lambda_nth us r.length = Term.Var (Term.String s) T ->
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

theorem arity {t us body : Term} {r : List Term} (h : LamSpine t us body r) :
    __eo_to_smt_lambda_arity t = r.length := by
  induction h with
  | lam => rfl
  | app a hf ih =>
      obtain ⟨g, c, b, rfl⟩ := hf.shape
      change Nat.succ (__eo_to_smt_lambda_arity (Term.Apply (Term.Apply g c) b)) = _
      rw [ih]
      rfl

theorem vs {t us body : Term} {r : List Term} (h : LamSpine t us body r) :
    __eo_to_smt_lambda_vs t = us := by
  induction h with
  | lam => rfl
  | app a hf ih =>
      obtain ⟨g, c, b, rfl⟩ := hf.shape
      exact ih

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

theorem lambda_app {t us body : Term} {r : List Term} (h : LamSpine t us body r)
    (vs : Term) :
    ∀ (bs : SmtBindings) (n : native_Nat) (d : SmtTerm),
      __eo_to_smt_lambda_app vs t bs n d =
        native_ite (__eo_to_smt_lambda_vars us (n + r.length))
          (SmtTerm.bind (lamBindings vs r bs) (__eo_to_smt body)) SmtTerm.None := by
  induction h with
  | lam => intro bs n d; rfl
  | @app f us' body' rargs a hf ih =>
      intro bs n d
      obtain ⟨g, c, b, hfe⟩ := hf.shape
      have hStep :
          __eo_to_smt_lambda_app vs (Term.Apply f a) bs n d =
            __eo_to_smt_lambda_app vs f
              (__eo_to_smt_lambda_binding
                (__eo_to_smt_lambda_nth vs (__eo_to_smt_lambda_arity f))
                (__eo_to_smt a) bs) (Nat.succ n) d := by
        subst hfe
        rfl
      rw [hStep, ih, hf.arity, Nat.succ_add]
      rfl

/-- The translation of a beta redex. -/
theorem eo_to_smt {t us body : Term} {r : List Term} (h : LamSpine t us body r)
    (hr : r ≠ []) :
    __eo_to_smt t =
      native_ite (__eo_to_smt_lambda_vars us r.length)
        (SmtTerm.bind (lamBindings us r SmtBindings.nil) (__eo_to_smt body))
        SmtTerm.None := by
  cases h with
  | lam => exact absurd rfl hr
  | app y hf =>
      cases hf with
      | lam => rfl
      | app x2 hf' =>
          rename_i f' r'
          have hStep :
              __eo_to_smt (Term.Apply (Term.Apply f' x2) y) =
                __eo_to_smt_lambda_app (__eo_to_smt_lambda_vs f') f'
                  (__eo_to_smt_lambda_binding
                    (__eo_to_smt_lambda_nth (__eo_to_smt_lambda_vs f')
                      (__eo_to_smt_lambda_arity f'))
                    (__eo_to_smt x2)
                    (__eo_to_smt_lambda_binding
                      (__eo_to_smt_lambda_nth (__eo_to_smt_lambda_vs f')
                        (Nat.succ (__eo_to_smt_lambda_arity f')))
                      (__eo_to_smt y) SmtBindings.nil))
                  (Nat.succ (Nat.succ Nat.zero))
                  (SmtTerm.Apply (__eo_to_smt (Term.Apply f' x2)) (__eo_to_smt y)) := by
            rcases hf'.deep_shape with hfe | ⟨g, c, b, a, hfe⟩ <;> subst hfe <;> rfl
          rw [hStep, hf'.vs, hf'.arity, hf'.lambda_app]
          have hLen : Nat.succ (Nat.succ Nat.zero) + r'.length = (y :: x2 :: r').length := by
            show 2 + r'.length = r'.length + 1 + 1
            omega
          rw [hLen]
          rfl

/-- The EO type of a beta-redex application is the generic one. -/
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

/-! ## Applications that are not beta redexes -/

theorem eo_to_smt_lambda_app_of_not_spine :
    ∀ (t : Term), ¬ IsLamSpine t ->
      ∀ (vs : Term) (bs : SmtBindings) (n : native_Nat) (d : SmtTerm),
        __eo_to_smt_lambda_app vs t bs n d = d
  | t, hns, vs, bs, n, d => by
      rw [__eo_to_smt_lambda_app.eq_def]
      split
      · rename_i us body
        exact absurd ⟨us, body, [], LamSpine.lam us body⟩ hns
      · rename_i f a _
        exact eo_to_smt_lambda_app_of_not_spine f
          (fun hf => hns (isLamSpine_apply hf a)) vs _ _ d
      · rfl
termination_by t => sizeOf t

theorem eo_to_smt_apply_of_not_spine (arg app : SmtTerm) (f : Term)
    (hns : ¬ IsLamSpine f) :
    __eo_to_smt_lambda_spine f arg app = app := by
  rw [__eo_to_smt_lambda_spine.eq_def]
  split
  · rename_i us body
    exact absurd ⟨us, body, [], LamSpine.lam us body⟩ hns
  · rename_i x1 x2 _
    exact eo_to_smt_lambda_app_of_not_spine x1
      (fun hx => hns (isLamSpine_apply hx x2)) _ _ _ _
  · rfl

/-- A generically translated application whose head is not a beta redex is the
SMT application. -/
theorem eo_to_smt_apply_eq_of_not_spine {f y : Term}
    (hgen :
      __eo_to_smt (Term.Apply f y) =
        __eo_to_smt_lambda_spine f (__eo_to_smt y)
          (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt y)))
    (hns : ¬ IsLamSpine f) :
    __eo_to_smt (Term.Apply f y) = SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt y) := by
  rw [hgen, eo_to_smt_apply_of_not_spine _ _ f hns]

/-! ## Variable lists -/

theorem lambda_vars_zero_inv {us : Term}
    (h : __eo_to_smt_lambda_vars us 0 = true) : us = Term.__eo_List_nil := by
  by_contra hne
  rw [__eo_to_smt_lambda_vars.eq_3 us 0 (fun h1 _ => hne h1)
    (fun _ _ _ _ _ h2 => Nat.noConfusion h2)] at h
  cases h

theorem lambda_vars_succ_inv {us : Term} {n : Nat}
    (h : __eo_to_smt_lambda_vars us (n + 1) = true) :
    ∃ s T vs,
      us = Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) vs ∧
        __eo_to_smt_lambda_vars vs n = true := by
  by_contra hne
  rw [__eo_to_smt_lambda_vars.eq_3 us (n + 1) (fun _ h2 => Nat.noConfusion h2)
    (fun s T vs n' h1 h2 => hne ⟨s, T, vs, h1, by
      subst h1
      have hn := Nat.succ.inj h2
      subst hn
      exact h⟩)] at h
  cases h

theorem lambda_vars_split :
    ∀ (k : Nat) {us : Term} {m : Nat},
      __eo_to_smt_lambda_vars us m = true -> k < m ->
      ∃ s T,
        __eo_to_smt_lambda_nth us k = Term.Var (Term.String s) T ∧
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
    ∀ (m : Nat) {us : Term}, __eo_to_smt_lambda_vars us m = true ->
      eoListDrop m us = Term.__eo_List_nil
  | 0, us, h => lambda_vars_zero_inv h
  | m + 1, us, h => by
      obtain ⟨s, T, vs, rfl, hvs⟩ := lambda_vars_succ_inv h
      exact lambda_vars_drop_all m hvs

theorem eo_typeof_apply_fun_self {T U : Term} (hT : T ≠ Term.Stuck) :
    __eo_typeof_apply (Term.Apply (Term.Apply Term.FunType T) U) T = U := by
  rw [__eo_typeof_apply.eq_def]
  by_cases hStuck : T = Term.Stuck
  · exact False.elim (hT hStuck)
  · simp [hStuck, __eo_requires.eq_def, native_teq, native_ite, native_not]

theorem eo_typeof_lambda_vars :
    ∀ (m : Nat) {us : Term}, __eo_to_smt_lambda_vars us m = true ->
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

theorem get_lambda_type_nil {B : Term} (hB : B ≠ Term.Stuck) :
    __get_lambda_type Term.__eo_List_nil B = B :=
  __get_lambda_type.eq_3 B hB

theorem get_lambda_type_cons {s T vs B : Term} (hB : B ≠ Term.Stuck) :
    __get_lambda_type
        (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var s T)) vs) B =
      Term.Apply (Term.Apply Term.FunType T) (__get_lambda_type vs B) :=
  __get_lambda_type.eq_2 B s T vs hB

/-! ## Typing beta redexes -/

theorem LamSpine.eo_typeof_eq {t us body : Term} {r : List Term} (h : LamSpine t us body r)
    {m : Nat} (hvars : __eo_to_smt_lambda_vars us m = true) (hlen : r.length ≤ m)
    (hB : __eo_typeof body ≠ Term.Stuck) (hArgs : LamArgsTyped us r) :
    __eo_typeof t = __get_lambda_type (eoListDrop r.length us) (__eo_typeof body) := by
  induction h with
  | lam us body =>
      change __eo_typeof_lambda (__eo_typeof us) us (__eo_typeof body) = _
      rw [eo_typeof_lambda_vars m hvars]
      have hus : us ≠ Term.Stuck := by
        intro hs
        subst hs
        cases m with
        | zero => cases lambda_vars_zero_inv hvars
        | succ m =>
            obtain ⟨_, _, _, h, _⟩ := lambda_vars_succ_inv hvars
            cases h
      exact __eo_typeof_lambda.eq_3 us (__eo_typeof body) hus hB
  | app a hf ih =>
      rename_i f rf
      obtain ⟨hHead, hRest⟩ := hArgs
      simp only [List.length_cons] at hlen
      rw [hf.eo_typeof_apply a, ih hvars (by omega) hB hRest]
      obtain ⟨s, T, hn, hd⟩ := lambda_vars_split rf.length hvars (by omega)
      obtain ⟨haT, hT⟩ := hHead s T hn
      rw [hd, get_lambda_type_cons hB, haT, eo_typeof_apply_fun_self hT]
      rfl

theorem lamBindings_mem (vs : Term) :
    ∀ (r : List Term) (bs : SmtBindings) {s : native_String} {T : SmtType} {v : SmtTerm},
      SmtBindings.Mem bs s T v -> SmtBindings.Mem (lamBindings vs r bs) s T v
  | [], bs, s, T, v, hm => hm
  | a :: r, bs, s, T, v, hm => by
      apply lamBindings_mem vs r
      unfold __eo_to_smt_lambda_binding
      split
      · exact SmtBindings.Mem.tail _ _ _ hm
      · exact hm

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
          (__eo_to_smt_lambda_binding (__eo_to_smt_lambda_nth vs r.length) (__eo_to_smt a) bs))
          _ _ _
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

/-- A typed beta redex has, as its SMT type, the translation of its EO type. -/
theorem eo_to_smt_typeof_matches_translation_lam_spine
    {t us body : Term} {r : List Term} (h : LamSpine t us body r) (hr : r ≠ [])
    (ih :
      ∀ u, sizeOf u < sizeOf t ->
        __smtx_typeof (__eo_to_smt u) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt u) = __eo_to_smt_type (__eo_typeof u) ∧
          eo_type_valid (__eo_typeof u))
    (hNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t) ∧
      eo_type_valid (__eo_typeof t) := by
  rw [h.eo_to_smt hr] at hNN ⊢
  cases hv : __eo_to_smt_lambda_vars us r.length
  · rw [hv] at hNN
    exact absurd smtx_typeof_none hNN
  · rw [hv] at hNN
    simp only [native_ite, ite_true] at hNN ⊢
    have hTyB :
        term_has_non_none_type
          (SmtTerm.bind (lamBindings us r SmtBindings.nil) (__eo_to_smt body)) := hNN
    obtain ⟨hBodyLt, hArgsLt⟩ := h.sizeOf_lt
    obtain ⟨hBodyTy, hBodyValid⟩ :=
      ih body hBodyLt (bind_body_non_none_of_non_none hTyB)
    have hArgs : LamArgsTyped us r :=
      lamArgsTyped_of_bindings us r SmtBindings.nil
        (fun s T v hm =>
          ⟨bind_binding_type_of_non_none hTyB hm, bind_binding_type_wf_of_non_none hTyB hm⟩)
        (fun a ha => ih a (hArgsLt a ha))
    have hBStuck : __eo_typeof body ≠ Term.Stuck := eo_type_valid_not_stuck hBodyValid
    have hTyT : __eo_typeof t = __eo_typeof body := by
      rw [h.eo_typeof_eq hv (Nat.le_refl _) hBStuck hArgs, lambda_vars_drop_all _ hv,
        get_lambda_type_nil hBStuck]
    rw [hTyT, bind_term_typeof_of_non_none hTyB]
    exact ⟨hBodyTy, hBodyValid⟩

/-- Typing of a generically translated application `(f y)`: a beta redex is
typed by `eo_to_smt_typeof_matches_translation_lam_spine`, and any other
application by `hGeneric` from the SMT application it translates to. -/
theorem eo_to_smt_typeof_matches_translation_generic_or_spine
    (f y : Term)
    (ih :
      ∀ u, sizeOf u < sizeOf (Term.Apply f y) ->
        __smtx_typeof (__eo_to_smt u) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt u) = __eo_to_smt_type (__eo_typeof u) ∧
          eo_type_valid (__eo_typeof u))
    (hgen :
      __eo_to_smt (Term.Apply f y) =
        __eo_to_smt_lambda_spine f (__eo_to_smt y)
          (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt y)))
    (hGeneric :
      __eo_to_smt (Term.Apply f y) = SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt y) ->
      __smtx_typeof (__eo_to_smt (Term.Apply f y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply f y)))
    (hNN : __smtx_typeof (__eo_to_smt (Term.Apply f y)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply f y)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply f y)) := by
  by_cases hs : IsLamSpine f
  · obtain ⟨us, body, r, hs⟩ := hs
    exact (eo_to_smt_typeof_matches_translation_lam_spine (LamSpine.app y hs)
      (List.cons_ne_nil _ _) ih hNN).1
  · exact hGeneric (eo_to_smt_apply_eq_of_not_spine hgen hs)

end TranslationProofs
