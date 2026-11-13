module

public import Cpc.Proofs.Closed.ContainsAtomicTermListFree
import all Cpc.Proofs.Closed.ContainsAtomicTermListFree

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-!
# Substitution utilities — `__substitute_simul_rec`

`__substitute_simul_rec isr t xs ss bvs` (`Cpc/Logos.lean:2298`) performs a
simultaneous substitution `[xs ↦ ss]` into `t`, with `bvs` the accumulator of
locally bound variables. The leading flag `isr` ("is rename") selects between two
genuinely different operations, and **only the quantifier case depends on it**:

* **`isr = false` — capture-avoiding substitution** (used by `instantiate`,
  `skolemize`). At a binder `(q (v::vs) a)` the binder list is kept verbatim and
  its variables are pushed onto `bvs`, so they *shadow* the substitution inside
  the body `a`.

* **`isr = true` — uniform renaming** (used by `alpha_equiv`). At a binder the
  substitution is applied to the binder list *itself*, and the bound variables
  are **not** added to `bvs`. Soundness here is alpha-equivalence (`t = subst t`),
  a different statement from the substitution semantics.

The variable / application / atom / `Stuck` cases thread `isr` through unchanged,
so their unfolding lemmas are shared. This file establishes the definitional
unfolding lemmas; semantic (model-evaluation) lemmas build on top in sibling
files, split by mode.

Naming: `substitute_simul_rec_*` for shared structural lemmas;
`substFalse_*` / `substTrue_*` for the mode-specific quantifier lemmas.
-/

/-! ## `EoVarEnvPerm` helpers (reusable)

Permutation-level companions of the `EoVarEnv` find lemmas, plus a cons builder,
used by the binder-push reasoning below. -/

/-- Membership in the reflected list forces a non-negative `find` index. -/
theorem EoVarEnvPerm.find_neg_false_of_mem
    {env : Term} {vars : List EoVarKey}
    (h : EoVarEnvPerm env vars)
    {s : native_String} {T : Term}
    (hMem : (s, T) ∈ vars) :
    __eo_is_neg (__eo_list_find Term.__eo_List_cons env (Term.Var (Term.String s) T)) =
      Term.Boolean false := by
  rcases h with ⟨exact, hExact, hEquiv⟩
  exact hExact.find_neg_false_of_mem ((hEquiv (s, T)).2 hMem)

/-- Non-membership in the reflected list forces a negative `find` index. -/
theorem EoVarEnvPerm.find_neg_true_of_not_mem
    {env : Term} {vars : List EoVarKey}
    (h : EoVarEnvPerm env vars)
    {s : native_String} {T : Term}
    (hNotMem : (s, T) ∉ vars) :
    __eo_is_neg (__eo_list_find Term.__eo_List_cons env (Term.Var (Term.String s) T)) =
      Term.Boolean true := by
  rcases h with ⟨exact, hExact, hEquiv⟩
  exact hExact.find_neg_true_of_not_mem (fun hc => hNotMem ((hEquiv (s, T)).1 hc))

/-- Prepending a binder variable to a reflected environment. -/
theorem EoVarEnvPerm.cons
    {s : native_String} {T env : Term} {vars : List EoVarKey}
    (h : EoVarEnvPerm env vars) :
    EoVarEnvPerm
      (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) env)
      ((s, T) :: vars) := by
  rcases h with ⟨exact, hExact, hEquiv⟩
  refine ⟨(s, T) :: exact, EoVarEnv.cons hExact, ?_⟩
  intro key
  simp only [List.mem_cons]
  rw [hEquiv key]

namespace SubstituteSupport

/-! ## `Stuck` propagation (mode-independent)

Only the `isr = Stuck` case is definitional; the others require the earlier
arguments to be resolved first, so they are not stated here (the structural
lemmas below take `≠ Stuck` hypotheses directly). -/

@[simp] theorem substitute_simul_rec_stuck_isr (t xs ss bvs : Term) :
    __substitute_simul_rec Term.Stuck t xs ss bvs = Term.Stuck := by
  simp [__substitute_simul_rec]

/-! ## Variable case (mode-independent)

A variable is kept if it is locally bound (`bvs`); otherwise it is looked up in
`xs` and replaced by the associated `ss` entry, or kept if absent. -/
theorem substitute_simul_rec_var
    (isr s S xs ss bvs : Term)
    (hisr : isr ≠ Term.Stuck) (hxs : xs ≠ Term.Stuck)
    (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck) :
    __substitute_simul_rec isr (Term.Var s S) xs ss bvs =
      __eo_ite (__eo_is_neg (__eo_list_find Term.__eo_List_cons bvs (Term.Var s S)))
        (__eo_ite (__eo_is_neg (__eo_list_find Term.__eo_List_cons xs (Term.Var s S)))
          (Term.Var s S)
          (__assoc_nil_nth Term.__eo_List_cons ss
            (__eo_list_find Term.__eo_List_cons xs (Term.Var s S))))
        (Term.Var s S) := by
  simp [__substitute_simul_rec]

/-! ### Variable outcomes

`substitute_simul_rec_var` exposes the raw nested `__eo_ite`. The three lemmas
below resolve it into the three semantic outcomes, keyed on whether the variable
is locally bound (`bvs`) and whether it is mapped by `xs`. These are what the
model-evaluation variable case consumes.

`__eo_is_neg (__eo_list_find _ l x)` is `Boolean true` exactly when `x ∉ l`
(`__eo_list_find` returns `-1` when absent, a non-negative index otherwise). -/

/-- Variable locally bound (`x ∈ bvs`): kept verbatim. -/
theorem substitute_simul_rec_var_bound
    (isr s S xs ss bvs : Term)
    (hisr : isr ≠ Term.Stuck) (hxs : xs ≠ Term.Stuck)
    (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hBound :
      __eo_is_neg (__eo_list_find Term.__eo_List_cons bvs (Term.Var s S)) =
        Term.Boolean false) :
    __substitute_simul_rec isr (Term.Var s S) xs ss bvs = Term.Var s S := by
  rw [substitute_simul_rec_var isr s S xs ss bvs hisr hxs hss hbvs, hBound]
  simp [__eo_ite, native_ite, native_teq]

/-- Variable free (`x ∉ bvs`) and unmapped (`x ∉ xs`): kept verbatim. -/
theorem substitute_simul_rec_var_unmapped
    (isr s S xs ss bvs : Term)
    (hisr : isr ≠ Term.Stuck) (hxs : xs ≠ Term.Stuck)
    (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hFree :
      __eo_is_neg (__eo_list_find Term.__eo_List_cons bvs (Term.Var s S)) =
        Term.Boolean true)
    (hUnmapped :
      __eo_is_neg (__eo_list_find Term.__eo_List_cons xs (Term.Var s S)) =
        Term.Boolean true) :
    __substitute_simul_rec isr (Term.Var s S) xs ss bvs = Term.Var s S := by
  rw [substitute_simul_rec_var isr s S xs ss bvs hisr hxs hss hbvs, hFree, hUnmapped]
  simp [__eo_ite, native_ite, native_teq]

/-- Variable free (`x ∉ bvs`) and mapped (`x ∈ xs`): replaced by the associated
`ss` entry at the found index. -/
theorem substitute_simul_rec_var_mapped
    (isr s S xs ss bvs : Term)
    (hisr : isr ≠ Term.Stuck) (hxs : xs ≠ Term.Stuck)
    (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hFree :
      __eo_is_neg (__eo_list_find Term.__eo_List_cons bvs (Term.Var s S)) =
        Term.Boolean true)
    (hMapped :
      __eo_is_neg (__eo_list_find Term.__eo_List_cons xs (Term.Var s S)) =
        Term.Boolean false) :
    __substitute_simul_rec isr (Term.Var s S) xs ss bvs =
      __assoc_nil_nth Term.__eo_List_cons ss
        (__eo_list_find Term.__eo_List_cons xs (Term.Var s S)) := by
  rw [substitute_simul_rec_var isr s S xs ss bvs hisr hxs hss hbvs, hFree, hMapped]
  simp [__eo_ite, native_ite, native_teq]

/-! ## Application case, non-binder (mode-independent)

Reached for `Apply f a` whose head `f` is *not* of binder shape
`Apply q (v :: vs)`. The substitution distributes over the application. -/
theorem substitute_simul_rec_apply
    (isr f a xs ss bvs : Term)
    (hisr : isr ≠ Term.Stuck) (hxs : xs ≠ Term.Stuck)
    (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotBinder : ∀ q v vs,
      f ≠ Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) :
    __substitute_simul_rec isr (Term.Apply f a) xs ss bvs =
      __eo_mk_apply
        (__substitute_simul_rec isr f xs ss bvs)
        (__substitute_simul_rec isr a xs ss bvs) := by
  simp [__substitute_simul_rec]

/-! ## Atom case (mode-independent)

A non-`Apply`, non-`Var`, non-`Stuck` term (constants, `UOp`, …) must be ground:
the result requires `__is_closed_rec` and returns the term unchanged. -/
theorem substitute_simul_rec_atom
    (isr x xs ss bvs : Term)
    (hisr : isr ≠ Term.Stuck) (hxs : xs ≠ Term.Stuck)
    (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotApply : ∀ f a, x ≠ Term.Apply f a)
    (hNotVar : ∀ s S, x ≠ Term.Var s S)
    (hNotStuck : x ≠ Term.Stuck) :
    __substitute_simul_rec isr x xs ss bvs =
      __eo_requires (__is_closed_rec x Term.__eo_List_nil) (Term.Boolean true) x := by
  cases x <;>
    simp_all [__substitute_simul_rec]

/-! ## Quantifier case — mode-specific

At a binder `(q (v::vs) a)` the capture-avoidance side condition
`__contains_atomic_term_list_free_rec ss (v::vs) nil = false` is required; then
the two modes diverge. -/

/-- **Substitution mode** (`isr = false`): binder list kept, bound vars pushed
onto `bvs`, body substituted under the extended `bvs`. -/
theorem substFalse_quant
    (q v vs a xs ss bvs : Term)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck) :
    __substitute_simul_rec (Term.Boolean false)
        (Term.Apply (Term.Apply q
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a) xs ss bvs =
      __eo_requires
        (__contains_atomic_term_list_free_rec ss
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) Term.__eo_List_nil)
        (Term.Boolean false)
        (__eo_mk_apply
          (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss
            (__eo_list_concat Term.__eo_List_cons
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs))) := by
  simp [__substitute_simul_rec, __eo_ite, native_ite, native_teq]

/-- **Rename mode** (`isr = true`): substitution applied to the binder list too,
bound vars *not* pushed, body substituted under the unchanged `bvs`. -/
theorem substTrue_quant
    (q v vs a xs ss bvs : Term)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck) :
    __substitute_simul_rec (Term.Boolean true)
        (Term.Apply (Term.Apply q
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a) xs ss bvs =
      __eo_requires
        (__contains_atomic_term_list_free_rec ss
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) Term.__eo_List_nil)
        (Term.Boolean false)
        (__eo_mk_apply
          (__eo_mk_apply q
            (__substitute_simul_rec (Term.Boolean true)
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) xs ss bvs))
          (__substitute_simul_rec (Term.Boolean true) a xs ss bvs)) := by
  simp [__substitute_simul_rec, __eo_ite, native_ite, native_teq]

/-! ## Substitution-mode semantics (`isr = false`)

The model-evaluation lemma: evaluating the translation of `subst false F xs ss bvs`
in `M` equals evaluating `toSmt F` in a model `N` that realises the substitution
`[xs ↦ ss]` (off the bound `bvs`). The relation `SubstFalseRel` packages exactly
the per-variable obligations the variable case needs; the induction on `F`
threads it through, re-establishing it under each binder via the
capture-avoidance side condition. -/

/-- Evaluating an EO variable reduces to the model's variable lookup. -/
theorem eval_eo_var (M : SmtModel) (s : native_String) (T : Term) :
    __smtx_model_eval M (__eo_to_smt (Term.Var (Term.String s) T)) =
      native_model_var_lookup M s (__eo_to_smt_type T) := by
  rw [__smtx_model_eval.eq_def]
  rfl

/--
Model relation realising a simultaneous substitution `[xs ↦ ss]` off the bound
variables `bvs`, in substitution mode.

* `agree` — variables that are bound (`is_neg (find bvs x) = false`) or unmapped
  (`is_neg (find xs x) = true`) are interpreted identically by `M` and `N`.
* `mapped` — a free, mapped variable `x` is assigned by `N` the value of its
  substitute `ss[find xs x]` evaluated in the ambient model `M`.

This is the substitution analogue of `model_agrees_except_on_eo_env`. -/
structure SubstFalseRel (M N : SmtModel) (xs ss bvs : Term) : Prop where
  globals : model_agrees_on_globals M N
  agree :
    ∀ (s : native_String) (T : Term),
      __eo_is_neg (__eo_list_find Term.__eo_List_cons bvs (Term.Var (Term.String s) T)) =
          Term.Boolean false ∨
        __eo_is_neg (__eo_list_find Term.__eo_List_cons xs (Term.Var (Term.String s) T)) =
          Term.Boolean true ->
      native_model_var_lookup M s (__eo_to_smt_type T) =
        native_model_var_lookup N s (__eo_to_smt_type T)
  mapped :
    ∀ (s : native_String) (T : Term),
      __eo_is_neg (__eo_list_find Term.__eo_List_cons bvs (Term.Var (Term.String s) T)) =
          Term.Boolean true ->
      __eo_is_neg (__eo_list_find Term.__eo_List_cons xs (Term.Var (Term.String s) T)) =
          Term.Boolean false ->
      native_model_var_lookup N s (__eo_to_smt_type T) =
        __smtx_model_eval M
          (__eo_to_smt
            (__assoc_nil_nth Term.__eo_List_cons ss
              (__eo_list_find Term.__eo_List_cons xs (Term.Var (Term.String s) T))))

/--
**Variable case** of the substitution-mode evaluation lemma.

Given proper var-list reflections for `xs` and `bvs`, the substituted variable
evaluated in `M` matches the variable evaluated in the substitution model `N`.
Splits on membership (bound / mapped / unmapped) and discharges each via the
corresponding variable-outcome lemma and a field of `SubstFalseRel`. -/
theorem substFalse_eval_var
    (M N : SmtModel) (s : native_String) (T xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars) (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hss : ss ≠ Term.Stuck)
    (hRel : SubstFalseRel M N xs ss bvs) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean false) (Term.Var (Term.String s) T) xs ss bvs)) =
      __smtx_model_eval N (__eo_to_smt (Term.Var (Term.String s) T)) := by
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  rw [eval_eo_var N s T]
  rcases hBvsEnv with ⟨bvExact, hBvExact, hBvEquiv⟩
  by_cases hBound : (s, T) ∈ bvExact
  · -- bound: kept; M and N agree
    have hb : __eo_is_neg
        (__eo_list_find Term.__eo_List_cons bvs (Term.Var (Term.String s) T)) =
        Term.Boolean false := hBvExact.find_neg_false_of_mem hBound
    rw [substitute_simul_rec_var_bound (Term.Boolean false) (Term.String s) T xs ss bvs
      hisr hxs hss hbvs hb, eval_eo_var M s T]
    exact hRel.agree s T (Or.inl hb)
  · have hbTrue : __eo_is_neg
        (__eo_list_find Term.__eo_List_cons bvs (Term.Var (Term.String s) T)) =
        Term.Boolean true := hBvExact.find_neg_true_of_not_mem hBound
    rcases hXsEnv with ⟨xsExact, hXsExact, hXsEquiv⟩
    by_cases hMapped : (s, T) ∈ xsExact
    · -- free and mapped: replaced by ss entry
      have hx : __eo_is_neg
          (__eo_list_find Term.__eo_List_cons xs (Term.Var (Term.String s) T)) =
          Term.Boolean false := hXsExact.find_neg_false_of_mem hMapped
      rw [substitute_simul_rec_var_mapped (Term.Boolean false) (Term.String s) T xs ss bvs
        hisr hxs hss hbvs hbTrue hx]
      exact (hRel.mapped s T hbTrue hx).symm
    · -- free and unmapped: kept; M and N agree
      have hx : __eo_is_neg
          (__eo_list_find Term.__eo_List_cons xs (Term.Var (Term.String s) T)) =
          Term.Boolean true := hXsExact.find_neg_true_of_not_mem hMapped
      rw [substitute_simul_rec_var_unmapped (Term.Boolean false) (Term.String s) T xs ss bvs
        hisr hxs hss hbvs hbTrue hx, eval_eo_var M s T]
      exact hRel.agree s T (Or.inr hx)

/-! ### Atom case

A non-`Apply`, non-`Var`, non-`Stuck` term must be ground for the substitution to
succeed (`substitute_simul_rec_atom` wraps it in `__eo_requires (closed …) …`). If
the substituted term translates (is non-`None`, hence non-`Stuck`) the closedness
guard fired, so the term is unchanged and closed, and a closed term evaluates the
same under any two models agreeing on globals. -/
theorem substitute_simul_eval_atom
    {isRename : Bool}
    (M N : SmtModel) (F xs ss bvs : Term)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotApply : ∀ f a, F ≠ Term.Apply f a)
    (hNotVar : ∀ s S, F ≠ Term.Var s S)
    (hNotStuck : F ≠ Term.Stuck)
    (hF : eoHasSmtTranslation F)
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename) F xs ss bvs))
    (hGlobals : model_agrees_on_globals M N) :
    __smtx_model_eval M
        (__eo_to_smt (__substitute_simul_rec (Term.Boolean isRename) F xs ss bvs)) =
      __smtx_model_eval N (__eo_to_smt F) := by
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by
    cases isRename <;> decide
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename) F xs ss bvs =
        __eo_requires (__is_closed_rec F Term.__eo_List_nil) (Term.Boolean true) F :=
    substitute_simul_rec_atom (Term.Boolean isRename) F xs ss bvs
      hisr hxs hss hbvs hNotApply hNotVar hNotStuck
  -- The substitution translates, so the `requires` did not collapse to `Stuck`.
  rw [hSubstEq] at hSubstTrans ⊢
  by_cases hck :
      native_teq (__is_closed_rec F Term.__eo_List_nil) (Term.Boolean true) = true
  · have hcTrue : __is_closed_rec F Term.__eo_List_nil = Term.Boolean true := by
      have := hck
      simp only [native_teq, decide_eq_true_eq] at this
      exact this
    have hReq :
        __eo_requires (__is_closed_rec F Term.__eo_List_nil) (Term.Boolean true) F = F := by
      simp [__eo_requires, hcTrue, native_ite, native_teq, native_not, SmtEval.native_not]
    rw [hReq]
    have hClosed : __eo_is_closed F = Term.Boolean true := by
      rw [← is_closed_rec_eq_eo_is_closed_of_has_smt_translation hF]
      exact hcTrue
    exact smt_model_eval_eq_of_eo_closed F hClosed M N hGlobals
  · exfalso
    have hReq :
        __eo_requires (__is_closed_rec F Term.__eo_List_nil) (Term.Boolean true) F =
          Term.Stuck := by
      simp [__eo_requires, native_ite, hck]
    rw [hReq] at hSubstTrans
    unfold eoHasSmtTranslation at hSubstTrans
    change __smtx_typeof SmtTerm.None ≠ SmtType.None at hSubstTrans
    exact hSubstTrans TranslationProofs.smtx_typeof_none

/-- Backwards-compatible substitution-mode specialization. -/
theorem substFalse_eval_atom
    (M N : SmtModel) (F xs ss bvs : Term)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotApply : ∀ f a, F ≠ Term.Apply f a)
    (hNotVar : ∀ s S, F ≠ Term.Var s S)
    (hNotStuck : F ≠ Term.Stuck)
    (hF : eoHasSmtTranslation F)
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean false) F xs ss bvs))
    (hGlobals : model_agrees_on_globals M N) :
    __smtx_model_eval M
        (__eo_to_smt (__substitute_simul_rec (Term.Boolean false) F xs ss bvs)) =
      __smtx_model_eval N (__eo_to_smt F) :=
  substitute_simul_eval_atom (isRename := false) M N F xs ss bvs
    hxs hss hbvs hNotApply hNotVar hNotStuck hF hSubstTrans hGlobals

/-! ### Capture avoidance: substitute values are push-invariant

Going under a binder pushes the binder's variables. The capture-avoidance side
condition `contains ss (binderList) nil = false` guarantees those variables do
not occur free in the substitution values `ss`, so each substitute's evaluation
is unchanged by the push. This is the key fact that makes `SubstFalseRel`
survive a binder. -/

private theorem assoc_nil_nth_index_stuck (f xs : Term) :
    __assoc_nil_nth f xs Term.Stuck = Term.Stuck := by
  cases f <;> cases xs <;>
    simp [__assoc_nil_nth]

private theorem assoc_nil_nth_nil_stuck (f n : Term) :
    __assoc_nil_nth f Term.__eo_List_nil n = Term.Stuck := by
  cases f <;> cases n <;>
    simp [__assoc_nil_nth, __eo_l_1___assoc_nil_nth]

private theorem eo_typeof_stuck :
    __eo_typeof Term.Stuck = Term.Stuck := by
  rfl

/--
An entry extracted from a translated EO value list inherits "no free occurrence
of `except`". The SMT-translation hypotheses rule out the `Stuck` and
binder-shaped edge cases where `__assoc_nil_nth` / `contains` would otherwise
make the statement false.
-/
theorem contains_assoc_nil_nth_false_lt
    (n : Nat) (ss except idx : Term)
    {exceptVars : List EoVarKey}
    (hLt : sizeOf ss < n)
    (hExceptEnv : EoVarEnvPerm except exceptVars)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hTrans : eoHasSmtTranslation (__assoc_nil_nth Term.__eo_List_cons ss idx))
    (hNoFree :
      __contains_atomic_term_list_free_rec ss except Term.__eo_List_nil =
        Term.Boolean false) :
    __contains_atomic_term_list_free_rec
        (__assoc_nil_nth Term.__eo_List_cons ss idx) except Term.__eo_List_nil =
      Term.Boolean false := by
  cases n with
  | zero => omega
  | succ n =>
      have hBoundEnv : EoVarEnvPerm Term.__eo_List_nil ([] : List EoVarKey) :=
        EoVarEnvPerm.of_exact EoVarEnv.nil
      let hRec :
          ∀ {ss' except' idx' : Term} {exceptVars' : List EoVarKey},
            sizeOf ss' < sizeOf ss ->
              EoVarEnvPerm except' exceptVars' ->
              EoListAllHaveSmtTranslation ss' ->
              eoHasSmtTranslation (__assoc_nil_nth Term.__eo_List_cons ss' idx') ->
              __contains_atomic_term_list_free_rec ss' except' Term.__eo_List_nil =
                Term.Boolean false ->
              __contains_atomic_term_list_free_rec
                  (__assoc_nil_nth Term.__eo_List_cons ss' idx') except'
                  Term.__eo_List_nil =
                Term.Boolean false :=
        fun {ss' except' idx' exceptVars'} hLt' hExcept' hSsTrans' hTrans' hNoFree' =>
          contains_assoc_nil_nth_false_lt n ss' except' idx'
            (by omega) hExcept' hSsTrans' hTrans' hNoFree'
      cases ss with
      | __eo_List_nil =>
          exfalso
          cases idx <;>
            unfold eoHasSmtTranslation at hTrans <;>
            simp [__assoc_nil_nth, __eo_l_1___assoc_nil_nth] at hTrans <;>
            exact hTrans TranslationProofs.smtx_typeof_none
      | Apply f tail =>
          cases f with
          | Apply g head =>
              by_cases hg : g = Term.__eo_List_cons
              · subst g
                rcases hSsTrans with ⟨hHeadTrans, hTailTrans⟩
                rcases
                  contains_atomic_term_list_free_rec_apply_false_cases
                    hExceptEnv hBoundEnv
                    (by
                      intro q x ys hEq
                      cases hEq
                      exact
                        term_not_eo_list_cons_of_has_smt_translation
                          hHeadTrans x ys rfl)
                    hNoFree with
                  ⟨hHeadApplyNoFree, hTailNoFree⟩
                rcases
                  contains_atomic_term_list_free_rec_apply_false_cases
                    hExceptEnv hBoundEnv
                    (by intro q x ys hEq; cases hEq)
                    hHeadApplyNoFree with
                  ⟨_hConsNoFree, hHeadNoFree⟩
                by_cases hIdxZero : idx = Term.Numeral 0
                · subst idx
                  simpa [__assoc_nil_nth, __eo_ite, __eo_eq, native_ite,
                    native_teq] using hHeadNoFree
                · have hAssocTail :
                      __assoc_nil_nth Term.__eo_List_cons
                          ((Term.Apply (Term.Apply Term.__eo_List_cons head) tail))
                          idx =
                        __assoc_nil_nth Term.__eo_List_cons tail
                          (__eo_add idx (Term.Numeral (-1 : native_Int))) := by
                    cases idx with
                    | Numeral k =>
                        by_cases hk : k = 0
                        · exfalso
                          apply hIdxZero
                          simp [hk]
                        · simp [__assoc_nil_nth, __eo_l_1___assoc_nil_nth,
                            __eo_requires, __eo_eq, native_ite, native_teq,
                            native_not, SmtEval.native_not, __eo_add, hk]
                    | Stuck =>
                        have hAdd :
                            __eo_add Term.Stuck (Term.Numeral (-1 : native_Int)) =
                              Term.Stuck := by
                          rfl
                        rw [assoc_nil_nth_index_stuck, hAdd,
                          assoc_nil_nth_index_stuck]
                    | _ =>
                        simp [__assoc_nil_nth, __eo_l_1___assoc_nil_nth,
                          __eo_requires, __eo_eq, native_ite, native_teq,
                          native_not, SmtEval.native_not, __eo_add] at hIdxZero ⊢
                  have hTailTrans' :
                      eoHasSmtTranslation
                        (__assoc_nil_nth Term.__eo_List_cons tail
                          (__eo_add idx (Term.Numeral (-1 : native_Int)))) := by
                    simpa [hAssocTail] using hTrans
                  have hTailResult :
                      __contains_atomic_term_list_free_rec
                          (__assoc_nil_nth Term.__eo_List_cons tail
                            (__eo_add idx (Term.Numeral (-1 : native_Int))))
                          except Term.__eo_List_nil =
                        Term.Boolean false :=
                    hRec
                      (ss' := tail)
                      (idx' := __eo_add idx (Term.Numeral (-1 : native_Int)))
                      (by simp)
                      hExceptEnv
                      hTailTrans
                      hTailTrans'
                      hTailNoFree
                  simpa [hAssocTail] using hTailResult
              · exfalso
                cases g <;> simp [EoListAllHaveSmtTranslation] at hSsTrans hg
          | _ =>
              cases hSsTrans
      | _ =>
          cases hSsTrans
termination_by n
decreasing_by
  all_goals omega

theorem contains_assoc_nil_nth_false
    (ss except idx : Term)
    {exceptVars : List EoVarKey}
    (hExceptEnv : EoVarEnvPerm except exceptVars)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hTrans : eoHasSmtTranslation (__assoc_nil_nth Term.__eo_List_cons ss idx))
    (hNoFree :
      __contains_atomic_term_list_free_rec ss except Term.__eo_List_nil =
        Term.Boolean false) :
    __contains_atomic_term_list_free_rec
        (__assoc_nil_nth Term.__eo_List_cons ss idx) except Term.__eo_List_nil =
      Term.Boolean false := by
  exact contains_assoc_nil_nth_false_lt (sizeOf ss + 1) ss except idx
    (by omega) hExceptEnv hSsTrans hTrans hNoFree

theorem assoc_nil_nth_has_smt_translation_of_list_all_and_typeof_bool_lt
    (n : Nat) (ss idx : Term)
    (hLt : sizeOf ss < n)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hTy :
      __eo_typeof (__assoc_nil_nth Term.__eo_List_cons ss idx) =
        Term.Bool) :
    eoHasSmtTranslation (__assoc_nil_nth Term.__eo_List_cons ss idx) := by
  cases n with
  | zero => omega
  | succ n =>
      let hRec :
          ∀ {ss' idx' : Term},
            sizeOf ss' < sizeOf ss ->
              EoListAllHaveSmtTranslation ss' ->
              __eo_typeof (__assoc_nil_nth Term.__eo_List_cons ss' idx') =
                Term.Bool ->
              eoHasSmtTranslation
                (__assoc_nil_nth Term.__eo_List_cons ss' idx') :=
        fun {ss' idx'} hLt' hSsTrans' hTy' =>
          assoc_nil_nth_has_smt_translation_of_list_all_and_typeof_bool_lt
            n ss' idx' (by omega) hSsTrans' hTy'
      cases ss with
      | __eo_List_nil =>
          exfalso
          rw [assoc_nil_nth_nil_stuck, eo_typeof_stuck] at hTy
          cases hTy
      | Apply f tail =>
          cases f with
          | Apply g head =>
              by_cases hg : g = Term.__eo_List_cons
              · subst g
                rcases hSsTrans with ⟨hHeadTrans, hTailTrans⟩
                by_cases hIdxZero : idx = Term.Numeral 0
                · subst idx
                  simpa [__assoc_nil_nth, __eo_ite, __eo_eq, native_ite,
                    native_teq] using hHeadTrans
                · have hAssocTail :
                      __assoc_nil_nth Term.__eo_List_cons
                          ((Term.Apply (Term.Apply Term.__eo_List_cons head) tail))
                          idx =
                        __assoc_nil_nth Term.__eo_List_cons tail
                          (__eo_add idx (Term.Numeral (-1 : native_Int))) := by
                    cases idx with
                    | Numeral k =>
                        by_cases hk : k = 0
                        · exfalso
                          apply hIdxZero
                          simp [hk]
                        · simp [__assoc_nil_nth, __eo_l_1___assoc_nil_nth,
                            __eo_requires, __eo_eq, native_ite, native_teq,
                            native_not, SmtEval.native_not, __eo_add, hk]
                    | Stuck =>
                        have hAdd :
                            __eo_add Term.Stuck (Term.Numeral (-1 : native_Int)) =
                              Term.Stuck := by
                          rfl
                        rw [assoc_nil_nth_index_stuck, hAdd,
                          assoc_nil_nth_index_stuck]
                    | _ =>
                        simp [__assoc_nil_nth, __eo_l_1___assoc_nil_nth,
                          __eo_requires, __eo_eq, native_ite, native_teq,
                          native_not, SmtEval.native_not, __eo_add] at hIdxZero ⊢
                  have hTailTy :
                      __eo_typeof
                          (__assoc_nil_nth Term.__eo_List_cons tail
                            (__eo_add idx (Term.Numeral (-1 : native_Int)))) =
                        Term.Bool := by
                    simpa [hAssocTail] using hTy
                  have hTailTransResult :
                      eoHasSmtTranslation
                        (__assoc_nil_nth Term.__eo_List_cons tail
                          (__eo_add idx (Term.Numeral (-1 : native_Int)))) :=
                    hRec
                      (ss' := tail)
                      (idx' := __eo_add idx (Term.Numeral (-1 : native_Int)))
                      (by simp)
                      hTailTrans
                      hTailTy
                  simpa [hAssocTail] using hTailTransResult
              · exfalso
                cases g <;> simp [EoListAllHaveSmtTranslation] at hSsTrans hg
          | _ =>
              cases hSsTrans
      | _ =>
          cases hSsTrans
termination_by n
decreasing_by
  all_goals omega

theorem assoc_nil_nth_has_smt_translation_of_list_all_and_typeof_bool
    (ss idx : Term)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hTy :
      __eo_typeof (__assoc_nil_nth Term.__eo_List_cons ss idx) =
        Term.Bool) :
    eoHasSmtTranslation (__assoc_nil_nth Term.__eo_List_cons ss idx) := by
  exact assoc_nil_nth_has_smt_translation_of_list_all_and_typeof_bool_lt
    (sizeOf ss + 1) ss idx (by omega) hSsTrans hTy

theorem assoc_nil_nth_has_smt_translation_of_list_all_and_typeof_ne_stuck_lt
    (n : Nat) (ss idx : Term)
    (hLt : sizeOf ss < n)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hTy :
      __eo_typeof (__assoc_nil_nth Term.__eo_List_cons ss idx) ≠
        Term.Stuck) :
    eoHasSmtTranslation (__assoc_nil_nth Term.__eo_List_cons ss idx) := by
  cases n with
  | zero => omega
  | succ n =>
      let hRec :
          ∀ {ss' idx' : Term},
            sizeOf ss' < sizeOf ss ->
              EoListAllHaveSmtTranslation ss' ->
              __eo_typeof (__assoc_nil_nth Term.__eo_List_cons ss' idx') ≠
                Term.Stuck ->
              eoHasSmtTranslation
                (__assoc_nil_nth Term.__eo_List_cons ss' idx') :=
        fun {ss' idx'} hLt' hSsTrans' hTy' =>
          assoc_nil_nth_has_smt_translation_of_list_all_and_typeof_ne_stuck_lt
            n ss' idx' (by omega) hSsTrans' hTy'
      cases ss with
      | __eo_List_nil =>
          exfalso
          rw [assoc_nil_nth_nil_stuck, eo_typeof_stuck] at hTy
          exact hTy rfl
      | Apply f tail =>
          cases f with
          | Apply g head =>
              by_cases hg : g = Term.__eo_List_cons
              · subst g
                rcases hSsTrans with ⟨hHeadTrans, hTailTrans⟩
                by_cases hIdxZero : idx = Term.Numeral 0
                · subst idx
                  simpa [__assoc_nil_nth, __eo_ite, __eo_eq, native_ite,
                    native_teq] using hHeadTrans
                · have hAssocTail :
                      __assoc_nil_nth Term.__eo_List_cons
                          ((Term.Apply (Term.Apply Term.__eo_List_cons head) tail))
                          idx =
                        __assoc_nil_nth Term.__eo_List_cons tail
                          (__eo_add idx (Term.Numeral (-1 : native_Int))) := by
                    cases idx with
                    | Numeral k =>
                        by_cases hk : k = 0
                        · exfalso
                          apply hIdxZero
                          simp [hk]
                        · simp [__assoc_nil_nth, __eo_l_1___assoc_nil_nth,
                            __eo_requires, __eo_eq, native_ite, native_teq,
                            native_not, SmtEval.native_not, __eo_add, hk]
                    | Stuck =>
                        have hAdd :
                            __eo_add Term.Stuck (Term.Numeral (-1 : native_Int)) =
                              Term.Stuck := by
                          rfl
                        rw [assoc_nil_nth_index_stuck, hAdd,
                          assoc_nil_nth_index_stuck]
                    | _ =>
                        simp [__assoc_nil_nth, __eo_l_1___assoc_nil_nth,
                          __eo_requires, __eo_eq, native_ite, native_teq,
                          native_not, SmtEval.native_not, __eo_add] at hIdxZero ⊢
                  have hTailTy :
                      __eo_typeof
                          (__assoc_nil_nth Term.__eo_List_cons tail
                            (__eo_add idx (Term.Numeral (-1 : native_Int)))) ≠
                        Term.Stuck := by
                    intro hTail
                    apply hTy
                    simpa [hAssocTail] using hTail
                  have hTailTransResult :
                      eoHasSmtTranslation
                        (__assoc_nil_nth Term.__eo_List_cons tail
                          (__eo_add idx (Term.Numeral (-1 : native_Int)))) :=
                    hRec
                      (ss' := tail)
                      (idx' := __eo_add idx (Term.Numeral (-1 : native_Int)))
                      (by simp)
                      hTailTrans
                      hTailTy
                  simpa [hAssocTail] using hTailTransResult
              · exfalso
                cases g <;> simp [EoListAllHaveSmtTranslation] at hSsTrans hg
          | _ =>
              cases hSsTrans
      | _ =>
          cases hSsTrans
termination_by n
decreasing_by
  all_goals omega

theorem assoc_nil_nth_has_smt_translation_of_list_all_and_typeof_ne_stuck
    (ss idx : Term)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hTy :
      __eo_typeof (__assoc_nil_nth Term.__eo_List_cons ss idx) ≠
        Term.Stuck) :
    eoHasSmtTranslation (__assoc_nil_nth Term.__eo_List_cons ss idx) := by
  exact
    assoc_nil_nth_has_smt_translation_of_list_all_and_typeof_ne_stuck_lt
      (sizeOf ss + 1) ss idx (by omega) hSsTrans hTy

/-- Selecting a non-`Stuck` entry from an EO list whose entries all have SMT
translations yields a translated entry. -/
theorem assoc_nil_nth_has_smt_translation_of_list_all_and_ne_stuck_lt
    (n : Nat) (ss idx : Term)
    (hLt : sizeOf ss < n)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hNe :
      __assoc_nil_nth Term.__eo_List_cons ss idx ≠ Term.Stuck) :
    eoHasSmtTranslation (__assoc_nil_nth Term.__eo_List_cons ss idx) := by
  cases n with
  | zero => omega
  | succ n =>
      let hRec :
          ∀ {ss' idx' : Term},
            sizeOf ss' < sizeOf ss ->
              EoListAllHaveSmtTranslation ss' ->
              __assoc_nil_nth Term.__eo_List_cons ss' idx' ≠ Term.Stuck ->
              eoHasSmtTranslation
                (__assoc_nil_nth Term.__eo_List_cons ss' idx') :=
        fun {ss' idx'} hLt' hSsTrans' hNe' =>
          assoc_nil_nth_has_smt_translation_of_list_all_and_ne_stuck_lt
            n ss' idx' (by omega) hSsTrans' hNe'
      cases ss with
      | __eo_List_nil =>
          exfalso
          rw [assoc_nil_nth_nil_stuck] at hNe
          exact hNe rfl
      | Apply f tail =>
          cases f with
          | Apply g head =>
              by_cases hg : g = Term.__eo_List_cons
              · subst g
                rcases hSsTrans with ⟨hHeadTrans, hTailTrans⟩
                by_cases hIdxZero : idx = Term.Numeral 0
                · subst idx
                  simpa [__assoc_nil_nth, __eo_ite, __eo_eq, native_ite,
                    native_teq] using hHeadTrans
                · have hAssocTail :
                      __assoc_nil_nth Term.__eo_List_cons
                          ((Term.Apply (Term.Apply Term.__eo_List_cons head) tail))
                          idx =
                        __assoc_nil_nth Term.__eo_List_cons tail
                          (__eo_add idx (Term.Numeral (-1 : native_Int))) := by
                    cases idx with
                    | Numeral k =>
                        by_cases hk : k = 0
                        · exfalso
                          apply hIdxZero
                          simp [hk]
                        · simp [__assoc_nil_nth, __eo_l_1___assoc_nil_nth,
                            __eo_requires, __eo_eq, native_ite, native_teq,
                            native_not, SmtEval.native_not, __eo_add, hk]
                    | Stuck =>
                        have hAdd :
                            __eo_add Term.Stuck (Term.Numeral (-1 : native_Int)) =
                              Term.Stuck := by
                          rfl
                        rw [assoc_nil_nth_index_stuck, hAdd,
                          assoc_nil_nth_index_stuck]
                    | _ =>
                        simp [__assoc_nil_nth, __eo_l_1___assoc_nil_nth,
                          __eo_requires, __eo_eq, native_ite, native_teq,
                          native_not, SmtEval.native_not, __eo_add] at hIdxZero ⊢
                  have hTailNe :
                      __assoc_nil_nth Term.__eo_List_cons tail
                          (__eo_add idx (Term.Numeral (-1 : native_Int))) ≠
                        Term.Stuck := by
                    intro hTail
                    apply hNe
                    simpa [hAssocTail] using hTail
                  have hTailTransResult :
                      eoHasSmtTranslation
                        (__assoc_nil_nth Term.__eo_List_cons tail
                          (__eo_add idx (Term.Numeral (-1 : native_Int)))) :=
                    hRec
                      (ss' := tail)
                      (idx' := __eo_add idx (Term.Numeral (-1 : native_Int)))
                      (by simp)
                      hTailTrans
                      hTailNe
                  simpa [hAssocTail] using hTailTransResult
              · exfalso
                cases g <;> simp [EoListAllHaveSmtTranslation] at hSsTrans hg
          | _ =>
              cases hSsTrans
      | _ =>
          cases hSsTrans
termination_by n
decreasing_by
  all_goals omega

theorem assoc_nil_nth_has_smt_translation_of_list_all_and_ne_stuck
    (ss idx : Term)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hNe :
      __assoc_nil_nth Term.__eo_List_cons ss idx ≠ Term.Stuck) :
    eoHasSmtTranslation (__assoc_nil_nth Term.__eo_List_cons ss idx) := by
  exact
    assoc_nil_nth_has_smt_translation_of_list_all_and_ne_stuck_lt
      (sizeOf ss + 1) ss idx (by omega) hSsTrans hNe

/--
A substitute entry's evaluation is invariant under pushing a binder variable that
is excluded by the capture-avoidance condition. Proved via the master coincidence
theorem `smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped`. -/
theorem subst_entry_eval_push_invariant
    (M : SmtModel) (ss except idx : Term)
    {exceptVars : List EoVarKey}
    (hExceptEnv : EoVarEnvPerm except exceptVars)
    (s : native_String) (T : Term) (v : SmtValue)
    (hMem : (s, T) ∈ exceptVars)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hTrans : eoHasSmtTranslation (__assoc_nil_nth Term.__eo_List_cons ss idx))
    (hNoFree :
      __contains_atomic_term_list_free_rec ss except Term.__eo_List_nil =
        Term.Boolean false) :
    __smtx_model_eval M
        (__eo_to_smt (__assoc_nil_nth Term.__eo_List_cons ss idx)) =
      __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
        (__eo_to_smt (__assoc_nil_nth Term.__eo_List_cons ss idx)) := by
  have hEntryNoFree :=
    contains_assoc_nil_nth_false ss except idx hExceptEnv hSsTrans hTrans hNoFree
  have hBoundEnv : EoVarEnvPerm Term.__eo_List_nil ([] : List EoVarKey) :=
    EoVarEnvPerm.of_exact EoVarEnv.nil
  have hMemSmt :
      (s, __eo_to_smt_type T) ∈ exceptVars.map EoVarKey.toSmt :=
    List.mem_map.2 ⟨(s, T), hMem, rfl⟩
  have hAgree :
      model_agrees_except_on_env (exceptVars.map EoVarKey.toSmt)
        (([] : List EoVarKey).map EoVarKey.toSmt)
        (native_model_push M s (__eo_to_smt_type T) v) M :=
    model_agrees_except_on_env_push_left_of_mem_except hMemSmt (by simp)
  exact
    (smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
      hExceptEnv hBoundEnv hTrans hEntryNoFree hAgree).symm

/-! ### Binder-push preservation

`SubstFalseRel` survives descending under a binder: pushing the binder variable
`(s, T)` to value `v` in both `M` and `N`, and prepending it to `bvs`,
re-establishes the relation. The `agree` fields follow from the push lemmas; the
`mapped` field uses `subst_entry_eval_push_invariant` (capture avoidance).

Design note: `SubstFalseRel` mixes EO-keyed checker conditions (`is_neg (find …)`)
with SMT-keyed model lookups. The `mapped` field's asymmetry means it can fail if
a free-mapped variable shares an SMT key with the pushed binder while differing as
an EO variable (distinct EO types collapsing under `__eo_to_smt_type`). This
genuine semantic case (an SMT-level capture the EO checker doesn't see) is
excluded by the explicit `hNoCollide` hypothesis, to be discharged from the
substitution's well-formedness when wiring into the rule. -/
theorem substFalseRel_push
    (M N : SmtModel) (xs ss bvs except : Term)
    {bvsVars exceptVars : List EoVarKey}
    (s : native_String) (T : Term) (v : SmtValue)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hExceptEnv : EoVarEnvPerm except exceptVars)
    (hMemExcept : (s, T) ∈ exceptVars)
    (hNoFreeSs :
      __contains_atomic_term_list_free_rec ss except Term.__eo_List_nil =
        Term.Boolean false)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hEntryTrans :
      ∀ (s' : native_String) (T' : Term),
        __eo_is_neg (__eo_list_find Term.__eo_List_cons bvs (Term.Var (Term.String s') T')) =
            Term.Boolean true ->
        __eo_is_neg (__eo_list_find Term.__eo_List_cons xs (Term.Var (Term.String s') T')) =
            Term.Boolean false ->
        eoHasSmtTranslation
          (__assoc_nil_nth Term.__eo_List_cons ss
            (__eo_list_find Term.__eo_List_cons xs (Term.Var (Term.String s') T'))))
    (hNoCollide :
      ∀ (s' : native_String) (T' : Term),
        __eo_is_neg
            (__eo_list_find Term.__eo_List_cons
              (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) bvs)
              (Term.Var (Term.String s') T')) = Term.Boolean true ->
        __eo_is_neg (__eo_list_find Term.__eo_List_cons xs (Term.Var (Term.String s') T')) =
            Term.Boolean false ->
        ({ isVar := true, name := s', ty := __eo_to_smt_type T' } : SmtModelKey) ≠
          { isVar := true, name := s, ty := __eo_to_smt_type T })
    (hRel : SubstFalseRel M N xs ss bvs) :
    SubstFalseRel (native_model_push M s (__eo_to_smt_type T) v)
      (native_model_push N s (__eo_to_smt_type T) v) xs ss
      (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) bvs) := by
  have hBvs'Env :
      EoVarEnvPerm
        (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) bvs)
        ((s, T) :: bvsVars) := hBvsEnv.cons
  refine ⟨model_agrees_on_globals_push₂ hRel.globals, ?_, ?_⟩
  · -- agree
    intro s' T' H
    by_cases hKey :
        ({ isVar := true, name := s', ty := __eo_to_smt_type T' } : SmtModelKey) =
          { isVar := true, name := s, ty := __eo_to_smt_type T }
    · simp [native_model_var_lookup, native_model_push, hKey]
    · have hML :
          native_model_var_lookup (native_model_push M s (__eo_to_smt_type T) v) s'
              (__eo_to_smt_type T') =
            native_model_var_lookup M s' (__eo_to_smt_type T') := by
        simp [native_model_var_lookup, native_model_push, hKey]
      have hNL :
          native_model_var_lookup (native_model_push N s (__eo_to_smt_type T) v) s'
              (__eo_to_smt_type T') =
            native_model_var_lookup N s' (__eo_to_smt_type T') := by
        simp [native_model_var_lookup, native_model_push, hKey]
      rw [hML, hNL]
      apply hRel.agree s' T'
      rcases H with hb' | hx'
      · left
        have hMem' : (s', T') ∈ (s, T) :: bvsVars := hBvs'Env.mem_of_find_neg_false hb'
        have hNeKey : (s', T') ≠ (s, T) := by
          intro hEq
          simp only [Prod.mk.injEq] at hEq
          obtain ⟨rfl, rfl⟩ := hEq
          exact hKey rfl
        have hMemBvs : (s', T') ∈ bvsVars := by
          rcases List.mem_cons.1 hMem' with hh | hh
          · exact absurd hh hNeKey
          · exact hh
        exact hBvsEnv.find_neg_false_of_mem hMemBvs
      · right; exact hx'
  · -- mapped
    intro s' T' hFree hMapped
    have hNotMem' : (s', T') ∉ (s, T) :: bvsVars :=
      hBvs'Env.not_mem_of_find_neg_true hFree
    have hNotMemBvs : (s', T') ∉ bvsVars :=
      fun hc => hNotMem' (List.mem_cons_of_mem _ hc)
    have hbTrueBvs :
        __eo_is_neg (__eo_list_find Term.__eo_List_cons bvs (Term.Var (Term.String s') T')) =
          Term.Boolean true := hBvsEnv.find_neg_true_of_not_mem hNotMemBvs
    have hKeyNe := hNoCollide s' T' hFree hMapped
    have hNL :
        native_model_var_lookup (native_model_push N s (__eo_to_smt_type T) v) s'
            (__eo_to_smt_type T') =
          native_model_var_lookup N s' (__eo_to_smt_type T') := by
      simp [native_model_var_lookup, native_model_push, hKeyNe]
    rw [hNL, hRel.mapped s' T' hbTrueBvs hMapped]
    exact
      subst_entry_eval_push_invariant M ss except
        (__eo_list_find Term.__eo_List_cons xs (Term.Var (Term.String s') T'))
        hExceptEnv s T v hMemExcept
        hSsTrans (hEntryTrans s' T' hbTrueBvs hMapped) hNoFreeSs

end SubstituteSupport
