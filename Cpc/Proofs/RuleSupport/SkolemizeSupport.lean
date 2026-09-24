module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.SubstitutePreservationSupport
import all Cpc.Proofs.RuleSupport.SubstitutePreservationSupport
public import Cpc.Proofs.RuleSupport.SubstituteSimulEvalSupport
import all Cpc.Proofs.RuleSupport.SubstituteSimulEvalSupport
public import Cpc.Proofs.Closed.ContainsAtomicTermListFree
import all Cpc.Proofs.Closed.ContainsAtomicTermListFree
public import Cpc.Proofs.Closed.IsClosedRec
import all Cpc.Proofs.Closed.IsClosedRec

open Eo
open SmtEval
open Smtm
open SubstituteTranslatabilitySupport
open SubstitutePreservationSupport

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

/-!
# CPC rule `skolemize`

The `skolemize` rule has one premise, a negated universally quantified formula:

```
premise:  (not (forall (x1 T1) ... (xn Tn) G))
conclude: (not G)[x1 ↦ sk1, ..., xn ↦ skn]
```

where `ski = (@quantifiers_skolemize (forall xs G) (i-1))` (see
`__eo_prog_skolemize`, `Cpc/Logos.lean`).  The checker guards the rule by
`__is_closed_rec (forall xs G) nil = true` (the premise quantifier is closed)
and `__eo_list_setof cons xs = xs` (the binder list is duplicate-free).

The SMT translation of the skolem for index `i` is the nested Hilbert-choice
term produced by `__eo_to_smt_quantifiers_skolemize xs (not ⟦G⟧) i`
(`Cpc/Spec.lean`): writing `H := SmtTerm.not ⟦G⟧`,

```
sk₀ = choice x1 (∃ x2 ... xn. H)
skᵢ = choice x(i+1) (∃ x(i+2) ... xn. bind-chain(H))
```

where `bind-chain` re-binds `x1 ... xi` to their own choice terms.

Proof plan (mirrors `Instantiate.lean` where possible):

1. **Mirrors** — reflect `__eo_to_smt_exists`, `__eo_to_smt_quantifiers_skolemize`
   and `__mk_skolems` into list-level functions `smtExistsList`, `qskolTerm`,
   `mkSkolemList` over the reflected binder environment (`EoVarEnv`).
2. **Guards** — reflect the `setof` guard into key distinctness
   (`DistinctList (smtKeys vars)`) and the closedness guard into
   `SmtTermClosedIn (smtKeys vars) ⟦G⟧`.
3. **Typing** — `qskolTerm vars H n` has SMT type `⟦Tₙ⟧`, giving
   `SubstActualsHaveSmtTypes` and `EoListAllHaveSmtTranslation` for the
   skolem list.
4. **Semantics** — the sequential witness chain `chainModel`/`chainValue`
   realises the choices left-to-right; `Classical.choose_spec` gives that the
   final chain model satisfies `H` (`chainModel_body_true`).  The stability
   theorem `qskol_eval_eq_chainValue` shows each skolem's translation
   evaluates (in any globals-agreeing model) to the corresponding chain
   value: the `bind`-chains replay the earlier pushes, and closedness makes
   every choice body model-independent up to globals and the tracked pins.
5. **Assembly** — `InstantiateRule.pushSubstModel M xs ts` then agrees with
   the chain model on the binder keys, closed-term coincidence transfers
   truth of `H`, and `InstantiateRule.substitute_simul_eval` (with
   `F := not G`) yields the conclusion.  Translatability comes from the
   generic preservation engine.
-/

namespace SkolemizeRule

/-- SMT-level keys of a reflected binder environment. -/
abbrev smtKeys (vars : List EoVarKey) : List SmtVarKey :=
  vars.map EoVarKey.toSmt

/-- Shorthand for the EO `forall` application. -/
abbrev forallTerm (x G : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.forall) x) G

/-- Shorthand for the EO `not` application. -/
abbrev notTerm (G : Term) : Term :=
  Term.Apply (Term.UOp UserOp.not) G

/-- The EO skolem term for binder index `i` of the quantifier `F`. -/
def skolemEoTerm (F : Term) (i : native_Int) : Term :=
  Term.UOp2 UserOp2._at_quantifiers_skolemize F (Term.Numeral i)

/-- List-level mirror of `__eo_to_smt_exists`. -/
def smtExistsList : List EoVarKey -> SmtTerm -> SmtTerm
  | [], B => B
  | (s, T) :: vs, B =>
      SmtTerm.exists s (__eo_to_smt_type T) (smtExistsList vs B)

/-- List-level mirror of `__eo_to_smt_quantifiers_skolemize`. -/
def qskolTerm : List EoVarKey -> SmtTerm -> Nat -> SmtTerm
  | (s, T) :: vs, B, 0 =>
      SmtTerm.choice s (__eo_to_smt_type T) (smtExistsList vs B)
  | (s, T) :: vs, B, Nat.succ n =>
      qskolTerm vs
        (SmtTerm.bind s (__eo_to_smt_type T)
          (SmtTerm.choice s (__eo_to_smt_type T) (smtExistsList vs B)) B)
        n
  | [], _B, _n => SmtTerm.None

/-- List-level mirror of `__mk_skolems`. -/
def mkSkolemList (F : Term) : List EoVarKey -> native_Int -> Term
  | [], _i => Term.__eo_List_nil
  | _p :: vs, i =>
      Term.Apply (Term.Apply Term.__eo_List_cons (skolemEoTerm F i))
        (mkSkolemList F vs (i + 1))

/-- Pairwise distinctness of a list (self-contained; the project has no
external list library). -/
public inductive DistinctList {α : Type} : List α -> Prop
  | nil : DistinctList []
  | cons {a : α} {l : List α} :
      a ∉ l -> DistinctList l -> DistinctList (a :: l)

/-- Removes every occurrence of a key (mirror of `__eo_list_erase_all_rec`). -/
def eraseKey (p : EoVarKey) : List EoVarKey -> List EoVarKey
  | [] => []
  | q :: qs => if q = p then eraseKey p qs else q :: eraseKey p qs

/-- Keep-first deduplication (mirror of `__eo_list_setof_rec`). -/
def ddfKeys : List EoVarKey -> List EoVarKey
  | [] => []
  | p :: ps => p :: eraseKey p (ddfKeys ps)

/-! ## Basic reduction helpers -/

private theorem eo_mk_apply_eq {a b : Term}
    (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    __eo_mk_apply a b = Term.Apply a b := by
  unfold __eo_mk_apply
  split
  · exact absurd rfl ha
  · exact absurd rfl hb
  · rfl

private theorem eo_to_smt_not_eq (t : Term) :
    __eo_to_smt (notTerm t) = SmtTerm.not (__eo_to_smt t) := rfl

private theorem typeof_exists_eq (s : native_String) (T : SmtType) (b : SmtTerm) :
    __smtx_typeof (SmtTerm.exists s T b) =
      native_ite (native_Teq (__smtx_typeof b) SmtType.Bool)
        (__smtx_typeof_guard_wf T SmtType.Bool) SmtType.None := rfl

private theorem typeof_choice_eq (s : native_String) (T : SmtType) (b : SmtTerm) :
    __smtx_typeof (SmtTerm.choice s T b) =
      native_ite (native_Teq (__smtx_typeof b) SmtType.Bool)
        (__smtx_typeof_guard_wf T T) SmtType.None := rfl

private theorem typeof_bind_eq (s : native_String) (T : SmtType) (v b : SmtTerm) :
    __smtx_typeof (SmtTerm.bind s T v b) =
      native_ite (native_Teq (__smtx_typeof v) T)
        (__smtx_typeof_guard_wf T (__smtx_typeof b)) SmtType.None := rfl

private theorem guard_wf_eq_of_wf {T : SmtType} (U : SmtType)
    (hWf : __smtx_type_wf T = true) :
    __smtx_typeof_guard_wf T U = U := by
  simp [__smtx_typeof_guard_wf, hWf, native_ite]

private theorem type_wf_none_false : __smtx_type_wf SmtType.None = false := by
  native_decide

private theorem ne_none_of_wf {T : SmtType} (hWf : __smtx_type_wf T = true) :
    T ≠ SmtType.None := by
  intro h
  rw [h, type_wf_none_false] at hWf
  cases hWf

/-! ## Mirror equations -/

theorem eo_to_smt_exists_eq_smtExistsList
    {env : Term} {vars : List EoVarKey} (hEnv : EoVarEnv env vars) :
    ∀ B : SmtTerm, __eo_to_smt_exists env B = smtExistsList vars B := by
  induction hEnv with
  | nil => intro B; rfl
  | cons hTail ih =>
      intro B
      rename_i s T env vars
      show SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt_exists env B) = _
      rw [ih B]
      rfl

theorem eo_to_smt_qskol_eq_qskolTerm
    {env : Term} {vars : List EoVarKey} (hEnv : EoVarEnv env vars) :
    ∀ (B : SmtTerm) (n : Nat),
      __eo_to_smt_quantifiers_skolemize env B n = qskolTerm vars B n := by
  induction hEnv with
  | nil =>
      intro B n
      cases n <;> rfl
  | cons hTail ih =>
      intro B n
      rename_i s T env vars
      cases n with
      | zero =>
          show SmtTerm.choice s (__eo_to_smt_type T) (__eo_to_smt_exists env B) = _
          rw [eo_to_smt_exists_eq_smtExistsList hTail B]
          rfl
      | succ n =>
          show __eo_to_smt_quantifiers_skolemize env
              (SmtTerm.bind s (__eo_to_smt_type T)
                (SmtTerm.choice s (__eo_to_smt_type T) (__eo_to_smt_exists env B)) B)
              n = _
          rw [eo_to_smt_exists_eq_smtExistsList hTail B, ih]
          rfl

theorem eo_to_smt_skolem_eq (x G : Term) (i : native_Int) (hi : (0 : Int) ≤ i) :
    __eo_to_smt (skolemEoTerm (forallTerm x G) i) =
      __eo_to_smt_quantifiers_skolemize x (SmtTerm.not (__eo_to_smt G))
        (Int.toNat i) := by
  show native_ite (__eo_to_smt_nat_is_valid (Term.Numeral i))
      (__eo_to_smt_quantifiers_skolemize x (SmtTerm.not (__eo_to_smt G))
        (__eo_to_smt_nat (Term.Numeral i)))
      SmtTerm.None = _
  have hValid : __eo_to_smt_nat_is_valid (Term.Numeral i) = true := by
    simpa [__eo_to_smt_nat_is_valid, native_zleq] using hi
  simp [hValid, native_ite, __eo_to_smt_nat, native_int_to_nat]

private theorem mkSkolemList_ne_stuck (F : Term) (vars : List EoVarKey)
    (i : native_Int) : mkSkolemList F vars i ≠ Term.Stuck := by
  cases vars <;> simp [mkSkolemList]

theorem mk_skolems_eq_mkSkolemList
    (x G : Term) {env : Term} {vars : List EoVarKey} (hEnv : EoVarEnv env vars) :
    ∀ i : native_Int,
      __mk_skolems env (forallTerm x G) (Term.Numeral i) =
        mkSkolemList (forallTerm x G) vars i := by
  induction hEnv with
  | nil => intro i; rfl
  | cons hTail ih =>
      intro i
      rename_i s T env vars
      show __eo_mk_apply
          (Term.Apply Term.__eo_List_cons
            (Term.UOp2 UserOp2._at_quantifiers_skolemize (forallTerm x G)
              (Term.Numeral i)))
          (__mk_skolems env (forallTerm x G)
            (__eo_add (Term.Numeral i) (Term.Numeral 1))) = _
  -- `__eo_add` on numerals is native addition.
      have hAdd : __eo_add (Term.Numeral i) (Term.Numeral 1) =
          Term.Numeral (i + 1) := rfl
      rw [hAdd, ih (i + 1),
        eo_mk_apply_eq (by simp)
          (mkSkolemList_ne_stuck (forallTerm x G) vars (i + 1))]
      rfl

/-! ## Distinctness from the `setof` guard -/

private theorem eraseKey_length_le (p : EoVarKey) :
    ∀ l : List EoVarKey, (eraseKey p l).length ≤ l.length := by
  intro l
  induction l with
  | nil => simp [eraseKey]
  | cons q qs ih =>
      by_cases h : q = p <;> simp [eraseKey, h] <;> omega

private theorem ddfKeys_length_le :
    ∀ l : List EoVarKey, (ddfKeys l).length ≤ l.length := by
  intro l
  induction l with
  | nil => simp [ddfKeys]
  | cons p ps ih =>
      have h1 := eraseKey_length_le p (ddfKeys ps)
      simp [ddfKeys]
      omega

private theorem not_mem_eraseKey_self (p : EoVarKey) :
    ∀ l : List EoVarKey, p ∉ eraseKey p l := by
  intro l
  induction l with
  | nil => simp [eraseKey]
  | cons q qs ih =>
      by_cases h : q = p
      · simpa [eraseKey, h] using ih
      · intro hMem
        rcases (by simpa [eraseKey, h] using hMem : p = q ∨ p ∈ eraseKey p qs) with
          hEq | hTail
        · exact h hEq.symm
        · exact ih hTail

private theorem eraseKey_eq_self_of_length (p : EoVarKey) :
    ∀ l : List EoVarKey, (eraseKey p l).length = l.length -> eraseKey p l = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons q qs ih =>
      intro hLen
      by_cases h : q = p
      · exfalso
        have h1 := eraseKey_length_le p qs
        simp [eraseKey, h] at hLen
        omega
      · simp [eraseKey, h] at hLen ⊢
        exact ih hLen

private theorem ddfKeys_eq_self_distinct :
    ∀ l : List EoVarKey, ddfKeys l = l -> DistinctList l := by
  intro l
  induction l with
  | nil => intro _; exact DistinctList.nil
  | cons p ps ih =>
      intro hEq
      have hTailEq : eraseKey p (ddfKeys ps) = ps := by
        simpa [ddfKeys] using hEq
      have hNotMem : p ∉ ps := by
        rw [← hTailEq]
        exact not_mem_eraseKey_self p (ddfKeys ps)
      have hLenTail : (eraseKey p (ddfKeys ps)).length = ps.length := by
        rw [hTailEq]
      have hLe1 := eraseKey_length_le p (ddfKeys ps)
      have hLe2 := ddfKeys_length_le ps
      have hDdfLen : (ddfKeys ps).length = ps.length := by omega
      have hEraseEq : eraseKey p (ddfKeys ps) = ddfKeys ps :=
        eraseKey_eq_self_of_length p (ddfKeys ps) (by omega)
      have hDdfEq : ddfKeys ps = ps := by
        rw [← hEraseEq]
        exact hTailEq
      exact DistinctList.cons hNotMem (ih hDdfEq)

private theorem var_term_eq_iff (s s' : native_String) (T T' : Term) :
    Term.Var (Term.String s) T = Term.Var (Term.String s') T' ↔
      ((s, T) : EoVarKey) = (s', T') := by
  constructor
  · intro h
    injection h with h1 h2
    injection h1 with h1
    subst h1
    subst h2
    rfl
  · intro h
    cases h
    rfl

private theorem skol_prepend_if_true_eq
    {f x res : Term}
    (hF : f ≠ Term.Stuck) (hX : x ≠ Term.Stuck) (hRes : res ≠ Term.Stuck) :
    __eo_prepend_if (Term.Boolean true) f x res =
      Term.Apply (Term.Apply f x) res := by
  cases f <;> cases x <;> cases res <;>
    simp [__eo_prepend_if] at hF hX hRes ⊢

private theorem skol_prepend_if_false_eq
    {f x res : Term}
    (hF : f ≠ Term.Stuck) (hX : x ≠ Term.Stuck) (hRes : res ≠ Term.Stuck) :
    __eo_prepend_if (Term.Boolean false) f x res = res := by
  cases f <;> cases x <;> cases res <;>
    simp [__eo_prepend_if] at hF hX hRes ⊢

/-- `__eo_list_erase_all_rec` on a reflected environment computes `eraseKey`. -/
theorem erase_all_rec_env
    {env : Term} {vars : List EoVarKey} (hEnv : EoVarEnv env vars)
    (s : native_String) (T : Term) :
    EoVarEnv (__eo_list_erase_all_rec env (Term.Var (Term.String s) T))
      (eraseKey (s, T) vars) := by
  induction hEnv with
  | nil =>
      simpa [__eo_list_erase_all_rec, eraseKey] using EoVarEnv.nil
  | cons hTail ih =>
      rename_i s' T' env vars
      have hTailNe := ih.ne_stuck
      by_cases hKey : ((s', T') : EoVarKey) = (s, T)
      · have hVarEq : Term.Var (Term.String s) T = Term.Var (Term.String s') T' :=
          (var_term_eq_iff s s' T T').mpr hKey.symm
        have hPrep :
            __eo_prepend_if (Term.Boolean false) Term.__eo_List_cons
                (Term.Var (Term.String s') T')
                (__eo_list_erase_all_rec env (Term.Var (Term.String s) T)) =
              __eo_list_erase_all_rec env (Term.Var (Term.String s) T) :=
          skol_prepend_if_false_eq (by intro h; cases h) (by intro h; cases h)
            hTailNe
        show EoVarEnv
            (__eo_prepend_if
              (__eo_not (__eo_eq (Term.Var (Term.String s) T)
                (Term.Var (Term.String s') T')))
              Term.__eo_List_cons (Term.Var (Term.String s') T')
              (__eo_list_erase_all_rec env (Term.Var (Term.String s) T))) _
        have hEqTrue :
            __eo_eq (Term.Var (Term.String s) T) (Term.Var (Term.String s') T') =
              Term.Boolean true := by
          simp [__eo_eq, native_teq, hVarEq.symm]
        rw [hEqTrue]
        show EoVarEnv
            (__eo_prepend_if (Term.Boolean false) Term.__eo_List_cons
              (Term.Var (Term.String s') T')
              (__eo_list_erase_all_rec env (Term.Var (Term.String s) T))) _
        rw [hPrep]
        simpa [eraseKey, hKey] using ih
      · have hVarNe :
            Term.Var (Term.String s') T' ≠ Term.Var (Term.String s) T := by
          intro h
          exact hKey ((var_term_eq_iff s' s T' T).mp h)
        have hPrep :
            __eo_prepend_if (Term.Boolean true) Term.__eo_List_cons
                (Term.Var (Term.String s') T')
                (__eo_list_erase_all_rec env (Term.Var (Term.String s) T)) =
              Term.Apply
                (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s') T'))
                (__eo_list_erase_all_rec env (Term.Var (Term.String s) T)) :=
          skol_prepend_if_true_eq (by intro h; cases h) (by intro h; cases h)
            hTailNe
        show EoVarEnv
            (__eo_prepend_if
              (__eo_not (__eo_eq (Term.Var (Term.String s) T)
                (Term.Var (Term.String s') T')))
              Term.__eo_List_cons (Term.Var (Term.String s') T')
              (__eo_list_erase_all_rec env (Term.Var (Term.String s) T))) _
        have hEqFalse :
            __eo_eq (Term.Var (Term.String s) T) (Term.Var (Term.String s') T') =
              Term.Boolean false := by
          simp [__eo_eq, native_teq, hVarNe]
        rw [hEqFalse]
        show EoVarEnv
            (__eo_prepend_if (Term.Boolean true) Term.__eo_List_cons
              (Term.Var (Term.String s') T')
              (__eo_list_erase_all_rec env (Term.Var (Term.String s) T))) _
        rw [hPrep]
        simpa [eraseKey, hKey] using EoVarEnv.cons (s := s') (T := T') ih

/-- `__eo_list_setof_rec` on a reflected environment computes `ddfKeys`. -/
theorem setof_rec_env :
    ∀ {env : Term} {vars : List EoVarKey}, EoVarEnv env vars ->
      EoVarEnv (__eo_list_setof_rec env) (ddfKeys vars)
  | _, _, EoVarEnv.nil => by
      simpa [__eo_list_setof_rec, ddfKeys] using EoVarEnv.nil
  | _, _, EoVarEnv.cons (s := s) (T := T) hTail => by
      have hSet := setof_rec_env hTail
      have hErase := erase_all_rec_env hSet s T
      show EoVarEnv
          (__eo_mk_apply
            (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
            (__eo_list_erase_all_rec (__eo_list_setof_rec _)
              (Term.Var (Term.String s) T)))
          (ddfKeys ((s, T) :: _))
      rw [eo_mk_apply_eq (by simp) hErase.ne_stuck]
      simpa [ddfKeys] using EoVarEnv.cons (s := s) (T := T) hErase

/-- The `setof` guard forces the reflected binder keys to be distinct. -/
public theorem distinct_of_setof_guard
    {env : Term} {vars : List EoVarKey} (hEnv : EoVarEnv env vars)
    (hGuard : __eo_list_setof Term.__eo_List_cons env = env) :
    DistinctList vars := by
  have hList := hEnv.is_list
  have hRecEq : __eo_list_setof_rec env = env := by
    have : __eo_list_setof Term.__eo_List_cons env = __eo_list_setof_rec env := by
      simp [__eo_list_setof, __eo_requires, hList, native_ite, native_teq,
        native_not]
    rw [← this, hGuard]
  have hSetEnv := setof_rec_env hEnv
  rw [hRecEq] at hSetEnv
  have hVarsEq : ddfKeys vars = vars :=
    EoVarEnv.vars_eq_of_same_env hSetEnv hEnv
  exact ddfKeys_eq_self_distinct vars hVarsEq

/-- Distinct EO binder keys with well-formed translated types have distinct
SMT keys. -/
theorem distinct_smtKeys
    {vars : List EoVarKey}
    (hWfAll : ∀ p ∈ vars, __smtx_type_wf (__eo_to_smt_type p.2) = true)
    (hD : DistinctList vars) :
    DistinctList (smtKeys vars) := by
  induction hD with
  | nil => exact DistinctList.nil
  | cons hNotMem hTail ih =>
      rename_i p l
      refine DistinctList.cons ?_ (ih (fun q hq => hWfAll q (List.Mem.tail _ hq)))
      intro hMem
      have hWfHead : __smtx_type_wf (__eo_to_smt_type p.2) = true :=
        hWfAll p (List.Mem.head _)
      have hEo : (p.1, p.2) ∈ l := by
        refine EoVarKey.mem_of_toSmt_mem_map_of_type_wf hWfHead ?_
        simpa [EoVarKey.toSmt] using hMem
      exact hNotMem (by simpa using hEo)

/-! ## Closedness from the `is_closed` guard -/

private theorem concat_rec_nil
    {env : Term} {vars : List EoVarKey} (hEnv : EoVarEnv env vars) :
    __eo_list_concat_rec env Term.__eo_List_nil = env := by
  induction hEnv with
  | nil => rfl
  | cons hTail ih =>
      rename_i s T env vars
      show __eo_mk_apply
          (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
          (__eo_list_concat_rec env Term.__eo_List_nil) = _
      rw [ih, eo_mk_apply_eq (by simp) hTail.ne_stuck]

private theorem is_list_nil :
    __eo_is_list Term.__eo_List_cons Term.__eo_List_nil = Term.Boolean true := by
  native_decide

private theorem concat_var_list_nil
    {env : Term} {vars : List EoVarKey} (hEnv : EoVarEnv env vars) :
    __eo_list_concat Term.__eo_List_cons env Term.__eo_List_nil = env := by
  have hList := hEnv.is_list
  show __eo_requires (__eo_is_list Term.__eo_List_cons env) (Term.Boolean true)
      (__eo_requires (__eo_is_list Term.__eo_List_cons Term.__eo_List_nil)
        (Term.Boolean true)
        (__eo_list_concat_rec env Term.__eo_List_nil)) = env
  rw [hList, is_list_nil, concat_rec_nil hEnv]
  simp [__eo_requires, native_ite, native_teq, native_not]

/-- The closedness guard yields SMT closedness of the quantifier body in the
binder-key environment. -/
theorem body_closedIn_of_guard
    {x G : Term} {vars : List EoVarKey} (hEnv : EoVarEnv x vars)
    (hTrans : eoHasSmtTranslation (forallTerm x G))
    (hGuard : __is_closed_rec (forallTerm x G) Term.__eo_List_nil =
      Term.Boolean true) :
    SmtTermClosedIn (smtKeys vars) (__eo_to_smt G) := by
  -- Bridge the checker's closedness function to the library's under
  -- translatability, then take the library's `forall` recursion step.
  have hBridge :
      __is_closed_rec (forallTerm x G) Term.__eo_List_nil =
        __eo_is_closed_rec (forallTerm x G) Term.__eo_List_nil :=
    is_closed_rec_eq_eo_is_closed_rec_of_has_smt_translation
      EoSmtVarEnv.nil hTrans
  have hEo : __eo_is_closed_rec (forallTerm x G) Term.__eo_List_nil =
      Term.Boolean true := by
    rw [← hBridge]
    exact hGuard
  have hRow : __eo_is_closed_rec (forallTerm x G) Term.__eo_List_nil =
      __eo_is_closed_rec G
        (__eo_list_concat Term.__eo_List_cons x Term.__eo_List_nil) := by
    simp only [__eo_is_closed_rec]
  rw [hRow, concat_var_list_nil hEnv] at hEo
  exact smtTermClosedIn_of_eo_is_closed_rec_perm
    (EoSmtVarEnvPerm.of_exact hEnv.to_smt) hEo

/-! ## Typing of skolem terms -/

theorem smtExistsList_typeof_bool :
    ∀ (vs : List EoVarKey) (B : SmtTerm),
      (∀ p ∈ vs, __smtx_type_wf (__eo_to_smt_type p.2) = true) ->
      __smtx_typeof B = SmtType.Bool ->
      __smtx_typeof (smtExistsList vs B) = SmtType.Bool := by
  intro vs
  induction vs with
  | nil => intro B _ hB; simpa [smtExistsList] using hB
  | cons p vs ih =>
      intro B hWf hB
      obtain ⟨s, T⟩ := p
      have hTail := ih B (fun q hq => hWf q (List.Mem.tail _ hq)) hB
      have hWfHead : __smtx_type_wf (__eo_to_smt_type T) = true :=
        hWf (s, T) (List.Mem.head _)
      show __smtx_typeof
          (SmtTerm.exists s (__eo_to_smt_type T) (smtExistsList vs B)) = _
      rw [typeof_exists_eq, hTail]
      simp [native_Teq, native_ite, guard_wf_eq_of_wf SmtType.Bool hWfHead]

private theorem typeof_choice_head
    (s : native_String) (T : Term) (vs : List EoVarKey) (B : SmtTerm)
    (hWfHead : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hWfTail : ∀ p ∈ vs, __smtx_type_wf (__eo_to_smt_type p.2) = true)
    (hB : __smtx_typeof B = SmtType.Bool) :
    __smtx_typeof
        (SmtTerm.choice s (__eo_to_smt_type T) (smtExistsList vs B)) =
      __eo_to_smt_type T := by
  rw [typeof_choice_eq, smtExistsList_typeof_bool vs B hWfTail hB]
  simp [native_Teq, native_ite, guard_wf_eq_of_wf _ hWfHead]

theorem qskolTerm_typeof :
    ∀ (n : Nat) (vs : List EoVarKey) (B : SmtTerm) (hn : n < vs.length),
      (∀ p ∈ vs, __smtx_type_wf (__eo_to_smt_type p.2) = true) ->
      __smtx_typeof B = SmtType.Bool ->
      __smtx_typeof (qskolTerm vs B n) = __eo_to_smt_type (vs[n]'hn).2 := by
  intro n
  induction n with
  | zero =>
      intro vs B hn hWf hB
      cases vs with
      | nil => simp at hn
      | cons p vs =>
          obtain ⟨s, T⟩ := p
          show __smtx_typeof
              (SmtTerm.choice s (__eo_to_smt_type T) (smtExistsList vs B)) = _
          simpa using
            typeof_choice_head s T vs B ((by exact hWf (s, T) (List.Mem.head _)))
              (fun q hq => hWf q (List.Mem.tail _ hq)) hB
  | succ n ih =>
      intro vs B hn hWf hB
      cases vs with
      | nil => simp at hn
      | cons p vs =>
          obtain ⟨s, T⟩ := p
          have hWfHead : __smtx_type_wf (__eo_to_smt_type T) = true :=
            hWf (s, T) (List.Mem.head _)
          have hWfTail : ∀ q ∈ vs, __smtx_type_wf (__eo_to_smt_type q.2) = true :=
            fun q hq => hWf q (List.Mem.tail _ hq)
          have hBindBool :
              __smtx_typeof
                  (SmtTerm.bind s (__eo_to_smt_type T)
                    (SmtTerm.choice s (__eo_to_smt_type T) (smtExistsList vs B))
                    B) = SmtType.Bool := by
            rw [typeof_bind_eq, typeof_choice_head s T vs B hWfHead hWfTail hB, hB]
            simp [native_Teq, native_ite, guard_wf_eq_of_wf _ hWfHead]
          have hLt : n < vs.length := by
            simpa using Nat.lt_of_succ_lt_succ hn
          show __smtx_typeof (qskolTerm vs
              (SmtTerm.bind s (__eo_to_smt_type T)
                (SmtTerm.choice s (__eo_to_smt_type T) (smtExistsList vs B)) B)
              n) = _
          rw [ih vs _ hLt hWfTail hBindBool]
          simp

/-! ## The actuals record for the skolem list -/

private theorem int_ofNat_shift (i : native_Int) (j : Nat) :
    i + Int.ofNat (j + 1) = (i + 1) + Int.ofNat j := by
  have h1 : Int.ofNat (j + 1) = Int.ofNat j + 1 := rfl
  rw [h1, Int.add_comm (Int.ofNat j) 1, ← Int.add_assoc]

/-- Packaged typing facts for the skolem at absolute index `i`. -/
def SkolemEntryFacts (F : Term) (i : native_Int) (T : Term) : Prop :=
  __smtx_type_wf (__eo_to_smt_type T) = true ∧
  RuleProofs.eo_has_smt_translation (skolemEoTerm F i) ∧
  __smtx_typeof (__eo_to_smt (skolemEoTerm F i)) = __eo_to_smt_type T

theorem substActuals_skolems (F : Term) :
    ∀ {envS : Term} {varsS : List EoVarKey}, EoVarEnv envS varsS ->
    ∀ i : native_Int,
      (∀ (j : Nat) (hj : j < varsS.length),
        SkolemEntryFacts F (i + Int.ofNat j) (varsS[j]'hj).2) ->
      SubstActualsHaveSmtTypes envS (mkSkolemList F varsS i) := by
  intro envS varsS hEnv
  induction hEnv with
  | nil =>
      intro i _
      exact SubstActualsHaveSmtTypes.nil _
  | cons hTail ih =>
      rename_i s T env vars
      intro i hFacts
      -- `((s, T) :: vars)[0].2` reduces to `T` by iota, but `simp` no longer
      -- rewrites it here, so hand the gap to `exact`'s defeq check instead.
      have hHead : SkolemEntryFacts F (i + Int.ofNat 0) T :=
        hFacts 0 (by simp)
      rw [show i + Int.ofNat 0 = i by simp] at hHead
      have hTailFacts :
          ∀ (j : Nat) (hj : j < vars.length),
            SkolemEntryFacts F ((i + 1) + Int.ofNat j) (vars[j]'hj).2 := by
        intro j hj
        have := hFacts (j + 1) (by simpa using Nat.succ_lt_succ hj)
        rw [int_ofNat_shift i j] at this
        simpa using this
      show SubstActualsHaveSmtTypes _
          (Term.Apply (Term.Apply Term.__eo_List_cons (skolemEoTerm F i))
            (mkSkolemList F vars (i + 1)))
      exact SubstActualsHaveSmtTypes.cons hHead.1 hHead.2.1 hHead.2.2
        (ih (i + 1) hTailFacts)

theorem eoListAll_skolems (F : Term) :
    ∀ (varsS : List EoVarKey) (i : native_Int),
      (∀ (j : Nat), j < varsS.length ->
        RuleProofs.eo_has_smt_translation (skolemEoTerm F (i + Int.ofNat j))) ->
      EoListAllHaveSmtTranslation (mkSkolemList F varsS i) := by
  intro varsS
  induction varsS with
  | nil =>
      intro i _
      simp [mkSkolemList, EoListAllHaveSmtTranslation]
  | cons p vs ih =>
      intro i hTrans
      have hHead : RuleProofs.eo_has_smt_translation (skolemEoTerm F i) := by
        have := hTrans 0 (by simp)
        simpa using this
      have hTail : EoListAllHaveSmtTranslation (mkSkolemList F vs (i + 1)) := by
        refine ih (i + 1) ?_
        intro j hj
        have := hTrans (j + 1) (by simpa using Nat.succ_lt_succ hj)
        rw [int_ofNat_shift i j] at this
        exact this
      show EoListAllHaveSmtTranslation
          (Term.Apply (Term.Apply Term.__eo_List_cons (skolemEoTerm F i))
            (mkSkolemList F vs (i + 1)))
      refine ⟨?_, hTail⟩
      simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hHead

/-! ## Evaluation helpers -/

private theorem eval_exists_eq (M : SmtModel) (s : native_String) (T : SmtType)
    (b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.exists s T b) = native_eval_exists M s T b := rfl

private theorem eval_choice_eq (M : SmtModel) (s : native_String) (T : SmtType)
    (b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.choice s T b) = native_eval_choice M s T b := rfl

private theorem eval_bind_eq (M : SmtModel) (s : native_String) (T : SmtType)
    (v b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bind s T v b) =
      __smtx_model_eval (native_model_push M s T (__smtx_model_eval M v)) b := rfl

private theorem canonical_of_canonical_bool {v : SmtValue}
    (h : __smtx_value_canonical v = true) : value_canonical v := by
  simpa [value_canonical] using h

private theorem canonical_bool_of_canonical {v : SmtValue}
    (h : value_canonical v) : __smtx_value_canonical v = true := by
  simpa [value_canonical] using h

/-- If an encoded existential is true, pushing its choice value makes the body
true (`Classical.choose_spec`). -/
theorem texists_true_push_tchoice
    (N : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm)
    (hEx : native_eval_exists N s T body = SmtValue.Boolean true) :
    __smtx_model_eval (native_model_push N s T (native_eval_choice N s T body))
        body = SmtValue.Boolean true := by
  classical
  by_cases hSat :
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical v = true ∧
          __smtx_model_eval (native_model_push N s T v) body =
            SmtValue.Boolean true
  · have hChoice :
        native_eval_choice N s T body = Classical.choose hSat := by
      rw [dif_pos hSat]
    rw [hChoice]
    exact (Classical.choose_spec hSat).2.2
  · rw [dif_neg hSat] at hEx
    cases hEx

/-- The choice value at a well-formed type is always typed and canonical. -/
theorem tchoice_typed_canonical_of_wf
    (N : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm)
    (hWf : __smtx_type_wf T = true) :
    __smtx_typeof_value (native_eval_choice N s T body) = T ∧
      __smtx_value_canonical (native_eval_choice N s T body) = true := by
  classical
  by_cases hSat :
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical v = true ∧
          __smtx_model_eval (native_model_push N s T v) body =
            SmtValue.Boolean true
  · rw [dif_pos hSat]
    exact ⟨(Classical.choose_spec hSat).1, (Classical.choose_spec hSat).2.1⟩
  · have hTy : ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧ __smtx_value_canonical v := by
      rcases canonical_type_inhabited_of_type_wf T hWf with ⟨v, hvTy, hvCan⟩
      exact ⟨v, hvTy, by simpa using canonical_bool_of_canonical hvCan⟩
    rw [dif_neg hSat, dif_pos hTy]
    refine ⟨(Classical.choose_spec hTy).1, ?_⟩
    simpa using (Classical.choose_spec hTy).2

/-- Different-body congruence for the choice evaluator, needing body agreement
only at values passing the evaluator's guards. -/
theorem native_eval_tchoice_eq_of_body_eval_eq_diff_typed
    {M N : SmtModel} {s : native_String} {T : SmtType} {bodyM bodyN : SmtTerm}
    (hBody : ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
      __smtx_value_canonical v = true ->
      __smtx_model_eval (native_model_push M s T v) bodyM =
        __smtx_model_eval (native_model_push N s T v) bodyN) :
    native_eval_choice M s T bodyM = native_eval_choice N s T bodyN := by
  classical
  have hPredEq :
      (fun v : SmtValue =>
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical v = true ∧
          __smtx_model_eval (native_model_push M s T v) bodyM =
            SmtValue.Boolean true) =
      (fun v : SmtValue =>
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical v = true ∧
          __smtx_model_eval (native_model_push N s T v) bodyN =
            SmtValue.Boolean true) := by
    funext v
    apply propext
    constructor
    · intro h
      exact ⟨h.1, h.2.1, by rw [← hBody v h.1 h.2.1]; exact h.2.2⟩
    · intro h
      exact ⟨h.1, h.2.1, by rw [hBody v h.1 h.2.1]; exact h.2.2⟩
  rw [hPredEq]

/-! ## The sequential witness chain -/

/-- The model obtained by realising the choices left-to-right. -/
noncomputable def chainModel (H : SmtTerm) : SmtModel -> List EoVarKey -> SmtModel
  | M, [] => M
  | M, (s, T) :: vs =>
      chainModel H
        (native_model_push M s (__eo_to_smt_type T)
          (native_eval_choice M s (__eo_to_smt_type T) (smtExistsList vs H)))
        vs

/-- The value the chain assigns to the `n`-th binder. -/
noncomputable def chainValue (H : SmtTerm) : SmtModel -> List EoVarKey -> Nat -> SmtValue
  | M, (s, T) :: vs, 0 =>
      native_eval_choice M s (__eo_to_smt_type T) (smtExistsList vs H)
  | M, (s, T) :: vs, Nat.succ n =>
      chainValue H
        (native_model_push M s (__eo_to_smt_type T)
          (native_eval_choice M s (__eo_to_smt_type T) (smtExistsList vs H)))
        vs n
  | _M, [], _n => SmtValue.NotValue

/-- A true encoded existential list makes the body true in the chain model. -/
theorem chainModel_body_true (H : SmtTerm) :
    ∀ (vs : List EoVarKey) (M : SmtModel),
      __smtx_model_eval M (smtExistsList vs H) = SmtValue.Boolean true ->
      __smtx_model_eval (chainModel H M vs) H = SmtValue.Boolean true := by
  intro vs
  induction vs with
  | nil =>
      intro M h
      simpa [smtExistsList, chainModel] using h
  | cons p vs ih =>
      obtain ⟨s, T⟩ := p
      intro M h
      have hEx : native_eval_exists M s (__eo_to_smt_type T)
          (smtExistsList vs H) = SmtValue.Boolean true := h
      have hPush := texists_true_push_tchoice M s (__eo_to_smt_type T)
        (smtExistsList vs H) hEx
      show __smtx_model_eval (chainModel H _ vs) H = SmtValue.Boolean true
      exact ih _ hPush

theorem chainModel_globals (H : SmtTerm) :
    ∀ (vs : List EoVarKey) (M : SmtModel),
      model_agrees_on_globals M (chainModel H M vs) := by
  intro vs
  induction vs with
  | nil =>
      intro M
      exact model_agrees_on_globals_refl M
  | cons p vs ih =>
      obtain ⟨s, T⟩ := p
      intro M
      exact model_agrees_on_globals_trans
        (model_agrees_on_globals_push M s (__eo_to_smt_type T) _) (ih _)

theorem chainModel_total_typed (H : SmtTerm) :
    ∀ (vs : List EoVarKey) (M : SmtModel),
      model_wf M ->
      (∀ p ∈ vs, __smtx_type_wf (__eo_to_smt_type p.2) = true) ->
      model_wf (chainModel H M vs) := by
  intro vs
  induction vs with
  | nil => intro M hM _; exact hM
  | cons p vs ih =>
      obtain ⟨s, T⟩ := p
      intro M hM hWf
      have hWfHead : __smtx_type_wf (__eo_to_smt_type T) = true :=
        hWf (s, T) (List.Mem.head _)
      obtain ⟨hTy, hCan⟩ := tchoice_typed_canonical_of_wf M s (__eo_to_smt_type T)
        (smtExistsList vs H) hWfHead
      exact ih _
        (model_total_typed_push hM s (__eo_to_smt_type T) _ hWfHead hTy
          (canonical_of_canonical_bool hCan))
        (fun q hq => hWf q (List.Mem.tail _ hq))

private theorem var_lookup_push_self (M : SmtModel) (s : native_String)
    (T : SmtType) (v : SmtValue) :
    native_model_var_lookup (native_model_push M s T v) s T = v := by
  simp [native_model_var_lookup, native_model_push]

private theorem var_lookup_push_ne {s' : native_String} {T' : SmtType}
    (M : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue)
    (hNe : ((s', T') : SmtVarKey) ≠ (s, T)) :
    native_model_var_lookup (native_model_push M s T v) s' T' =
      native_model_var_lookup M s' T' := by
  have hKey : ({ isVar := true, name := s', ty := T' } : SmtModelKey) ≠
      { isVar := true, name := s, ty := T } := by
    intro h
    injection h with _ h1 h2
    exact hNe (by rw [h1, h2])
  simp [native_model_var_lookup, native_model_push, hKey]

/-- Keys outside the chain's binder list keep their base-model assignment. -/
theorem chainModel_lookup_not_mem (H : SmtTerm) :
    ∀ (vs : List EoVarKey) (M : SmtModel) (s : native_String) (T : SmtType),
      ((s, T) : SmtVarKey) ∉ smtKeys vs ->
      native_model_var_lookup (chainModel H M vs) s T =
        native_model_var_lookup M s T := by
  intro vs
  induction vs with
  | nil => intro M s T _; rfl
  | cons p vs ih =>
      obtain ⟨s0, T0⟩ := p
      intro M s T hNotMem
      have hNeHead : ((s, T) : SmtVarKey) ≠ (s0, __eo_to_smt_type T0) := by
        intro h
        exact hNotMem (by rw [h]; exact List.Mem.head _)
      have hNotTail : ((s, T) : SmtVarKey) ∉ smtKeys vs := by
        intro h
        exact hNotMem (List.Mem.tail _ h)
      show native_model_var_lookup (chainModel H _ vs) s T = _
      rw [ih _ s T hNotTail, var_lookup_push_ne _ _ _ _ hNeHead]

/-- With distinct keys, the chain model assigns the `n`-th binder its chain
value. -/
theorem chainModel_lookup (H : SmtTerm) :
    ∀ (vs : List EoVarKey) (M : SmtModel) (n : Nat) (hn : n < vs.length),
      DistinctList (smtKeys vs) ->
      native_model_var_lookup (chainModel H M vs) (vs[n]'hn).1
          (__eo_to_smt_type (vs[n]'hn).2) =
        chainValue H M vs n := by
  intro vs
  induction vs with
  | nil => intro M n hn _; simp at hn
  | cons p vs ih =>
      obtain ⟨s0, T0⟩ := p
      intro M n hn hD
      cases hD with
      | cons hNotMem hTail =>
        cases n with
        | zero =>
            show native_model_var_lookup (chainModel H _ vs) s0
                (__eo_to_smt_type T0) = _
            rw [chainModel_lookup_not_mem H vs _ s0 (__eo_to_smt_type T0)
              (by simpa [EoVarKey.toSmt] using hNotMem)]
            rw [var_lookup_push_self]
            rfl
        | succ n =>
            have hLt : n < vs.length := by simpa using Nat.lt_of_succ_lt_succ hn
            show native_model_var_lookup (chainModel H _ vs) (vs[n]'hLt).1
                (__eo_to_smt_type (vs[n]'hLt).2) = _
            rw [ih _ n hLt hTail]
            rfl

/-! ## Congruence and stability -/

/-- Pins: variable assignments the right-hand model is known to carry. -/
def pinsHold (Q : SmtModel) (pins : List (SmtVarKey × SmtValue)) : Prop :=
  ∀ pv ∈ pins, native_model_var_lookup Q pv.1.1 pv.1.2 = pv.2

private theorem pinsHold_nil (Q : SmtModel) : pinsHold Q [] := by
  intro pv hpv
  cases hpv

private theorem pinsHold_push_of_fresh {Q : SmtModel}
    {pins : List (SmtVarKey × SmtValue)} {s : native_String} {T : SmtType}
    (v : SmtValue) (h : pinsHold Q pins)
    (hFresh : ((s, T) : SmtVarKey) ∉ pins.map Prod.fst) :
    pinsHold (native_model_push Q s T v) pins := by
  intro pv hpv
  obtain ⟨⟨ps, pT⟩, pval⟩ := pv
  have hNe : ((ps, pT) : SmtVarKey) ≠ (s, T) := by
    intro hEq
    exact hFresh (hEq ▸ List.mem_map_of_mem hpv)
  rw [var_lookup_push_ne _ _ _ _ hNe]
  exact h _ hpv

private theorem agrees_on_vars_mono {vars vars' : List SmtVarKey}
    {M N : SmtModel} (hSub : ∀ k ∈ vars', k ∈ vars)
    (h : model_agrees_on_vars vars M N) :
    model_agrees_on_vars vars' M N := by
  intro s T hMem
  exact h s T (hSub (s, T) hMem)

private theorem agrees_on_vars_push_same {vars : List SmtVarKey} {M N : SmtModel}
    {s : native_String} {T : SmtType} (v : SmtValue)
    (h : model_agrees_on_vars vars M N) :
    model_agrees_on_vars ((s, T) :: vars)
      (native_model_push M s T v) (native_model_push N s T v) := by
  intro s' T' hMem
  by_cases hKey : ((s', T') : SmtVarKey) = (s, T)
  · injection hKey with h1 h2
    subst h1
    subst h2
    rw [var_lookup_push_self, var_lookup_push_self]
  · rw [var_lookup_push_ne _ _ _ _ hKey, var_lookup_push_ne _ _ _ _ hKey]
    cases hMem with
    | head => exact absurd rfl hKey
    | tail _ hTail => exact h s' T' hTail

private theorem mem_append_of_mem_left {α : Type} {a : α} :
    ∀ {l1 : List α} (l2 : List α), a ∈ l1 -> a ∈ l1 ++ l2 := by
  intro l1 l2 h
  induction h with
  | head => exact List.Mem.head _
  | tail _ _ ih => exact List.Mem.tail _ ih

private theorem mem_append_of_mem_right {α : Type} {a : α} :
    ∀ (l1 : List α) {l2 : List α}, a ∈ l2 -> a ∈ l1 ++ l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 h; exact h
  | cons b l1 ih => intro l2 h; exact List.Mem.tail _ (ih h)

private theorem mem_append_split {α : Type} {a : α} :
    ∀ (l1 : List α) {l2 : List α}, a ∈ l1 ++ l2 -> a ∈ l1 ∨ a ∈ l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 h; exact Or.inr h
  | cons b l1 ih =>
      intro l2 h
      cases h with
      | head => exact Or.inl (List.Mem.head _)
      | tail _ hTail =>
          rcases ih hTail with h1 | h2
          · exact Or.inl (List.Mem.tail _ h1)
          · exact Or.inr h2

private theorem distinctList_append_disjoint {α : Type} :
    ∀ {l1 l2 : List α}, DistinctList (l1 ++ l2) -> ∀ a ∈ l1, a ∉ l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 _ a ha; cases ha
  | cons b l1 ih =>
      intro l2 hD a ha hMem
      cases hD with
      | cons hNotMem hTail =>
        cases ha with
        | head => exact hNotMem (mem_append_of_mem_right l1 hMem)
        | tail _ hTailMem => exact ih hTail a hTailMem hMem

private theorem distinctList_middle {α : Type} :
    ∀ {l1 : List α} {a : α} {l2 : List α},
      DistinctList (l1 ++ a :: l2) -> DistinctList (a :: (l1 ++ l2)) := by
  intro l1
  induction l1 with
  | nil => intro a l2 h; exact h
  | cons b l1 ih =>
      intro a l2 hD
      cases hD with
      | cons hbNotMem hTail =>
        have hIH := ih hTail
        cases hIH with
        | cons haNotMem haTail =>
          have hab : a ≠ b := by
            intro hEq
            apply hbNotMem
            rw [hEq]
            exact mem_append_of_mem_right l1 (List.Mem.head _)
          refine DistinctList.cons ?_ (DistinctList.cons ?_ haTail)
          · intro hMem
            cases hMem with
            | head => exact hab rfl
            | tail _ hIn => exact haNotMem hIn
          · intro hMem
            rcases mem_append_split l1 hMem with h1 | h2
            · exact hbNotMem (mem_append_of_mem_left _ h1)
            · exact hbNotMem
                (mem_append_of_mem_right l1 (List.Mem.tail _ h2))

/-- Different-body congruence for encoded existential lists.

`B1` (in `P`) and `B2` (in `Q`) need only agree, as leaf bodies, on models that
agree on the pushed binder keys plus the ambient environment `E`, with the pin
assignments still visible on the `Q` side. -/
theorem existsList_eval_congr
    (M : SmtModel) (pins : List (SmtVarKey × SmtValue)) (B1 B2 : SmtTerm) :
    ∀ (vs : List EoVarKey) (E : List SmtVarKey) (P Q : SmtModel),
      model_wf P -> model_wf Q ->
      model_agrees_on_globals M P -> model_agrees_on_globals M Q ->
      (∀ p ∈ vs, __smtx_type_wf (__eo_to_smt_type p.2) = true) ->
      model_agrees_on_vars E P Q ->
      pinsHold Q pins ->
      (∀ pv ∈ pins, pv.1 ∉ smtKeys vs) ->
      (∀ P' Q' : SmtModel,
        model_wf P' -> model_wf Q' ->
        model_agrees_on_globals M P' -> model_agrees_on_globals M Q' ->
        model_agrees_on_vars (smtKeys vs ++ E) P' Q' ->
        pinsHold Q' pins ->
        __smtx_model_eval P' B1 = __smtx_model_eval Q' B2) ->
      __smtx_model_eval P (smtExistsList vs B1) =
        __smtx_model_eval Q (smtExistsList vs B2) := by
  intro vs
  induction vs with
  | nil =>
      intro E P Q hP hQ hMP hMQ _hWf hAgreeE hPins _hDisj hRel
      exact hRel P Q hP hQ hMP hMQ (by simpa using hAgreeE) hPins
  | cons p vs ih =>
      obtain ⟨s, T⟩ := p
      intro E P Q hP hQ hMP hMQ hWf hAgreeE hPins hDisj hRel
      have hWfHead : __smtx_type_wf (__eo_to_smt_type T) = true :=
        hWf (s, T) (List.Mem.head _)
      show __smtx_model_eval P
          (SmtTerm.exists s (__eo_to_smt_type T) (smtExistsList vs B1)) =
        __smtx_model_eval Q
          (SmtTerm.exists s (__eo_to_smt_type T) (smtExistsList vs B2))
      rw [eval_exists_eq P s (__eo_to_smt_type T) (smtExistsList vs B1),
        eval_exists_eq Q s (__eo_to_smt_type T) (smtExistsList vs B2)]
      apply InstantiateRule.native_eval_texists_eq_of_body_eval_eq_diff_typed
      intro w hwTy hwCan
      have hPushP : model_wf
          (native_model_push P s (__eo_to_smt_type T) w) :=
        model_total_typed_push hP s _ w hWfHead hwTy
          (canonical_of_canonical_bool hwCan)
      have hPushQ : model_wf
          (native_model_push Q s (__eo_to_smt_type T) w) :=
        model_total_typed_push hQ s _ w hWfHead hwTy
          (canonical_of_canonical_bool hwCan)
      refine ih ((s, __eo_to_smt_type T) :: E)
        (native_model_push P s (__eo_to_smt_type T) w)
        (native_model_push Q s (__eo_to_smt_type T) w)
        hPushP hPushQ
        (model_agrees_on_globals_trans hMP
          (model_agrees_on_globals_push P s _ w))
        (model_agrees_on_globals_trans hMQ
          (model_agrees_on_globals_push Q s _ w))
        (fun q hq => hWf q (List.Mem.tail _ hq))
        (agrees_on_vars_push_same w hAgreeE)
        (pinsHold_push_of_fresh w hPins ?_)
        (fun pv hpv => ?_)
        (fun P' Q' hP' hQ' hMP' hMQ' hAgree' hPins' => ?_)
      · intro hMem
        rcases List.mem_map.1 hMem with ⟨pv, hpv, hEq⟩
        refine hDisj pv hpv ?_
        rw [hEq]
        show ((s, __eo_to_smt_type T) : SmtVarKey) ∈
          ((s, __eo_to_smt_type T) :: smtKeys vs)
        exact List.Mem.head _
      · intro hMem
        exact hDisj pv hpv (List.Mem.tail _ hMem)
      · refine hRel P' Q' hP' hQ' hMP' hMQ' ?_ hPins'
        refine agrees_on_vars_mono ?_ hAgree'
        intro k hk
        simp only [smtKeys, List.map_cons, List.cons_append, List.mem_cons,
          List.mem_append] at hk ⊢
        rcases hk with h1 | h2
        · exact Or.inr (Or.inl h1)
        · rcases h2 with h2a | h2b
          · exact Or.inl h2a
          · exact Or.inr (Or.inr h2b)

/-! ## Stability: skolem translations evaluate to the chain values -/

private theorem globals_symm {M N : SmtModel}
    (h : model_agrees_on_globals M N) : model_agrees_on_globals N M :=
  ⟨fun s T => (h.1 s T).symm, fun f T U => (h.2 f T U).symm⟩

/-- The head choice of a skolem agrees between any pin-respecting model pair. -/
private theorem qskol_head_choice_eq
    (M : SmtModel) (pins : List (SmtVarKey × SmtValue)) (B H : SmtTerm)
    (s : native_String) (T : Term) (vs : List EoVarKey)
    (P L : SmtModel)
    (hP : model_wf P) (hL : model_wf L)
    (hMP : model_agrees_on_globals M P) (hML : model_agrees_on_globals M L)
    (hWfHead : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hWfTail : ∀ p ∈ vs, __smtx_type_wf (__eo_to_smt_type p.2) = true)
    (hPinsL : pinsHold L pins)
    (hFresh : ((s, __eo_to_smt_type T) : SmtVarKey) ∉ pins.map Prod.fst)
    (hDisjTail : ∀ pv ∈ pins, pv.1 ∉ smtKeys vs)
    (hBodyRel : ∀ P' Q' : SmtModel,
      model_wf P' -> model_wf Q' ->
      model_agrees_on_globals M P' -> model_agrees_on_globals M Q' ->
      model_agrees_on_vars (smtKeys ((s, T) :: vs)) P' Q' ->
      pinsHold Q' pins ->
      __smtx_model_eval P' B = __smtx_model_eval Q' H) :
    native_eval_choice P s (__eo_to_smt_type T) (smtExistsList vs B) =
      native_eval_choice L s (__eo_to_smt_type T) (smtExistsList vs H) := by
  apply native_eval_tchoice_eq_of_body_eval_eq_diff_typed
  intro w hwTy hwCan
  refine existsList_eval_congr M pins B H vs [(s, __eo_to_smt_type T)]
    (native_model_push P s (__eo_to_smt_type T) w)
    (native_model_push L s (__eo_to_smt_type T) w)
    (model_total_typed_push hP s _ w hWfHead hwTy
      (canonical_of_canonical_bool hwCan))
    (model_total_typed_push hL s _ w hWfHead hwTy
      (canonical_of_canonical_bool hwCan))
    (model_agrees_on_globals_trans hMP
      (model_agrees_on_globals_push P s _ w))
    (model_agrees_on_globals_trans hML
      (model_agrees_on_globals_push L s _ w))
    hWfTail
    ?_ (pinsHold_push_of_fresh w hPinsL hFresh) hDisjTail
    (fun P' Q' hP' hQ' hMP' hMQ' hAgree' hPins' => ?_)
  · intro s' T' hMem
    cases hMem with
    | head => rw [var_lookup_push_self, var_lookup_push_self]
    | tail _ h => cases h
  · refine hBodyRel P' Q' hP' hQ' hMP' hMQ' ?_ hPins'
    intro s' T' hMem
    apply hAgree'
    cases hMem with
    | head => exact mem_append_of_mem_right _ (List.Mem.head _)
    | tail _ h => exact mem_append_of_mem_left _ h

/--
Core stability: in any total, globals-agreeing model `K`, the skolem term
`qskolTerm vs B n` evaluates to the sequential chain value taken from `L`,
provided `B` and `H` are evaluation-equivalent relative to the binder keys
and the pinned earlier choices (which `L` carries).
-/
theorem qskol_eval_eq_chainValue (M : SmtModel) (H : SmtTerm) :
    ∀ (n : Nat) (vs : List EoVarKey) (B : SmtTerm)
      (K L : SmtModel) (pins : List (SmtVarKey × SmtValue)),
      n < vs.length ->
      model_wf K -> model_wf L ->
      model_agrees_on_globals M K -> model_agrees_on_globals M L ->
      (∀ p ∈ vs, __smtx_type_wf (__eo_to_smt_type p.2) = true) ->
      DistinctList (pins.map Prod.fst ++ smtKeys vs) ->
      pinsHold L pins ->
      (∀ P Q : SmtModel,
        model_wf P -> model_wf Q ->
        model_agrees_on_globals M P -> model_agrees_on_globals M Q ->
        model_agrees_on_vars (smtKeys vs) P Q ->
        pinsHold Q pins ->
        __smtx_model_eval P B = __smtx_model_eval Q H) ->
      __smtx_model_eval K (qskolTerm vs B n) = chainValue H L vs n := by
  intro n
  induction n with
  | zero =>
      intro vs B K L pins hn hK hL hMK hML hWf hD hPins hBodyRel
      cases vs with
      | nil => simp at hn
      | cons p vs =>
          obtain ⟨s, T⟩ := p
          have hFresh : ((s, __eo_to_smt_type T) : SmtVarKey) ∉
              pins.map Prod.fst := by
            intro hMem
            exact distinctList_append_disjoint hD _ hMem (List.Mem.head _)
          have hDisjTail : ∀ pv ∈ pins, pv.1 ∉ smtKeys vs := by
            intro pv hpv hMem
            exact distinctList_append_disjoint hD _ (List.mem_map_of_mem hpv)
              (List.Mem.tail _ hMem)
          show __smtx_model_eval K
              (SmtTerm.choice s (__eo_to_smt_type T) (smtExistsList vs B)) =
            chainValue H L ((s, T) :: vs) 0
          rw [eval_choice_eq]
          exact qskol_head_choice_eq M pins B H s T vs K L hK hL hMK hML
            (hWf (s, T) (List.Mem.head _))
            (fun q hq => hWf q (List.Mem.tail _ hq))
            hPins hFresh hDisjTail hBodyRel
  | succ n ih =>
      intro vs B K L pins hn hK hL hMK hML hWf hD hPins hBodyRel
      cases vs with
      | nil => simp at hn
      | cons p vs =>
          obtain ⟨s, T⟩ := p
          have hWfHead : __smtx_type_wf (__eo_to_smt_type T) = true :=
            hWf (s, T) (List.Mem.head _)
          have hWfTail : ∀ q ∈ vs, __smtx_type_wf (__eo_to_smt_type q.2) = true :=
            fun q hq => hWf q (List.Mem.tail _ hq)
          have hDMid : DistinctList
              (((s, __eo_to_smt_type T) : SmtVarKey) ::
                (pins.map Prod.fst ++ smtKeys vs)) :=
            distinctList_middle hD
          have hHeadNotMem : ((s, __eo_to_smt_type T) : SmtVarKey) ∉
              pins.map Prod.fst ++ smtKeys vs := by
            cases hDMid with
            | cons h _ => exact h
          have hFresh : ((s, __eo_to_smt_type T) : SmtVarKey) ∉
              pins.map Prod.fst :=
            fun h => hHeadNotMem (mem_append_of_mem_left _ h)
          have hNotInTail : ((s, __eo_to_smt_type T) : SmtVarKey) ∉
              smtKeys vs :=
            fun h => hHeadNotMem (mem_append_of_mem_right _ h)
          have hDisjTail : ∀ pv ∈ pins, pv.1 ∉ smtKeys vs := by
            intro pv hpv hMem
            exact distinctList_append_disjoint hD _ (List.mem_map_of_mem hpv)
              (List.Mem.tail _ hMem)
          obtain ⟨hCTy, hCCan⟩ := tchoice_typed_canonical_of_wf L s
            (__eo_to_smt_type T) (smtExistsList vs H) hWfHead
          have hL' : model_wf
              (native_model_push L s (__eo_to_smt_type T)
                (native_eval_choice L s (__eo_to_smt_type T)
                  (smtExistsList vs H))) :=
            model_total_typed_push hL s _ _ hWfHead hCTy
              (canonical_of_canonical_bool hCCan)
          have hML' : model_agrees_on_globals M
              (native_model_push L s (__eo_to_smt_type T)
                (native_eval_choice L s (__eo_to_smt_type T)
                  (smtExistsList vs H))) :=
            model_agrees_on_globals_trans hML
              (model_agrees_on_globals_push L s _ _)
          have hPins' : pinsHold
              (native_model_push L s (__eo_to_smt_type T)
                (native_eval_choice L s (__eo_to_smt_type T)
                  (smtExistsList vs H)))
              (((s, __eo_to_smt_type T),
                  native_eval_choice L s (__eo_to_smt_type T)
                    (smtExistsList vs H)) :: pins) := by
            intro pv hpv
            cases hpv with
            | head => exact var_lookup_push_self _ _ _ _
            | tail _ h =>
                obtain ⟨⟨ps, pT⟩, pval⟩ := pv
                have hNe : ((ps, pT) : SmtVarKey) ≠ (s, __eo_to_smt_type T) := by
                  intro hEq
                  exact hFresh (hEq ▸ List.mem_map_of_mem h)
                rw [var_lookup_push_ne _ _ _ _ hNe]
                exact hPins _ h
          have hD' : DistinctList
              ((((s, __eo_to_smt_type T),
                  native_eval_choice L s (__eo_to_smt_type T)
                    (smtExistsList vs H)) :: pins).map Prod.fst ++
                smtKeys vs) := hDMid
          have hBodyRel' : ∀ P Q : SmtModel,
              model_wf P -> model_wf Q ->
              model_agrees_on_globals M P -> model_agrees_on_globals M Q ->
              model_agrees_on_vars (smtKeys vs) P Q ->
              pinsHold Q
                (((s, __eo_to_smt_type T),
                    native_eval_choice L s (__eo_to_smt_type T)
                      (smtExistsList vs H)) :: pins) ->
              __smtx_model_eval P
                  (SmtTerm.bind s (__eo_to_smt_type T)
                    (SmtTerm.choice s (__eo_to_smt_type T)
                      (smtExistsList vs B)) B) =
                __smtx_model_eval Q H := by
            intro P Q hP hQ hMP hMQ hAgreeVs hPinsQ'
            have hPinsQ : pinsHold Q pins :=
              fun pv hpv => hPinsQ' pv (List.Mem.tail _ hpv)
            have hQHead : native_model_var_lookup Q s (__eo_to_smt_type T) =
                native_eval_choice L s (__eo_to_smt_type T)
                  (smtExistsList vs H) :=
              hPinsQ' _ (List.Mem.head _)
            rw [eval_bind_eq, eval_choice_eq]
            have hdc : native_eval_choice P s (__eo_to_smt_type T)
                (smtExistsList vs B) =
                native_eval_choice L s (__eo_to_smt_type T)
                  (smtExistsList vs H) :=
              qskol_head_choice_eq M pins B H s T vs P L hP hL hMP hML
                hWfHead hWfTail hPins hFresh hDisjTail hBodyRel
            rw [hdc]
            refine hBodyRel
              (native_model_push P s (__eo_to_smt_type T)
                (native_eval_choice L s (__eo_to_smt_type T)
                  (smtExistsList vs H)))
              Q
              (model_total_typed_push hP s _ _ hWfHead hCTy
                (canonical_of_canonical_bool hCCan))
              hQ
              (model_agrees_on_globals_trans hMP
                (model_agrees_on_globals_push P s _ _))
              hMQ ?_ hPinsQ
            intro s' T' hMem
            cases hMem with
            | head =>
                rw [var_lookup_push_self, hQHead]
            | tail _ h =>
                have hNe : ((s', T') : SmtVarKey) ≠
                    (s, __eo_to_smt_type T) := by
                  intro hEq
                  exact hNotInTail (hEq ▸ h)
                rw [var_lookup_push_ne _ _ _ _ hNe]
                exact hAgreeVs s' T' h
          have hn' : n < vs.length := by
            simpa using Nat.lt_of_succ_lt_succ hn
          show __smtx_model_eval K
              (qskolTerm vs
                (SmtTerm.bind s (__eo_to_smt_type T)
                  (SmtTerm.choice s (__eo_to_smt_type T)
                    (smtExistsList vs B)) B) n) =
            chainValue H
              (native_model_push L s (__eo_to_smt_type T)
                (native_eval_choice L s (__eo_to_smt_type T)
                  (smtExistsList vs H)))
              vs n
          exact ih vs
            (SmtTerm.bind s (__eo_to_smt_type T)
              (SmtTerm.choice s (__eo_to_smt_type T) (smtExistsList vs B)) B)
            K
            (native_model_push L s (__eo_to_smt_type T)
              (native_eval_choice L s (__eo_to_smt_type T)
                (smtExistsList vs H)))
            (((s, __eo_to_smt_type T),
                native_eval_choice L s (__eo_to_smt_type T)
                  (smtExistsList vs H)) :: pins)
            hn' hK hL' hMK hML' hWfTail hD' hPins' hBodyRel'

/-- Base-model corollary: each skolem's translation evaluates to its chain
value in the ambient model, given closedness of the body. -/
theorem qskolTerm_eval_eq_chainValue_base
    (M : SmtModel) (hM : model_wf M) (H : SmtTerm)
    (vars : List EoVarKey)
    (hWfAll : ∀ p ∈ vars, __smtx_type_wf (__eo_to_smt_type p.2) = true)
    (hD : DistinctList (smtKeys vars))
    (hClosed : SmtTermClosedIn (smtKeys vars) H)
    (n : Nat) (hn : n < vars.length) :
    __smtx_model_eval M (qskolTerm vars H n) = chainValue H M vars n := by
  refine qskol_eval_eq_chainValue M H n vars H M M [] hn hM hM
    (model_agrees_on_globals_refl M) (model_agrees_on_globals_refl M)
    hWfAll hD (pinsHold_nil M) ?_
  intro P Q hP hQ hMP hMQ hAgree _
  exact smt_model_eval_eq_of_closedIn H (smtKeys vars) P Q hClosed
    ⟨model_agrees_on_globals_trans (globals_symm hMP) hMQ, hAgree⟩

/-! ## The substitution model realises the chain -/

private theorem getElem_mem' {α : Type} :
    ∀ (l : List α) (n : Nat) (hn : n < l.length), l[n]'hn ∈ l := by
  intro l
  induction l with
  | nil => intro n hn; simp at hn
  | cons a l ih =>
      intro n hn
      cases n with
      | zero => exact List.Mem.head _
      | succ n =>
          exact List.Mem.tail _ (ih n (by simpa using Nat.lt_of_succ_lt_succ hn))

private theorem mem_index' {α : Type} :
    ∀ {l : List α} {a : α}, a ∈ l ->
      ∃ (n : Nat) (hn : n < l.length), l[n]'hn = a := by
  intro l a h
  induction h with
  | head => exact ⟨0, by simp, rfl⟩
  | tail b hTail ih =>
      obtain ⟨n, hn, hEq⟩ := ih
      exact ⟨n + 1, by simpa using Nat.succ_lt_succ hn, by simpa using hEq⟩

/-- The skolem translation at a natural index, as a `qskolTerm`. -/
private theorem skolem_transl_eq (x G : Term) {vars : List EoVarKey}
    (hEnv : EoVarEnv x vars) (j : Nat) :
    __eo_to_smt (skolemEoTerm (forallTerm x G) (Int.ofNat j)) =
      qskolTerm vars (SmtTerm.not (__eo_to_smt G)) j := by
  rw [eo_to_smt_skolem_eq x G (Int.ofNat j) (Int.ofNat_le.mpr (Nat.zero_le j)),
    eo_to_smt_qskol_eq_qskolTerm hEnv]
  rfl

/-- With distinct keys, `pushSubstModel` over the skolem list assigns the
`n`-th binder the base-model value of the `n`-th skolem. -/
theorem pushSubstModel_lookup_mkSkolems
    (M : SmtModel) (F : Term) :
    ∀ {env : Term} {vars : List EoVarKey}, EoVarEnv env vars ->
      DistinctList (smtKeys vars) ->
      ∀ (i : native_Int) (n : Nat) (hn : n < vars.length),
        native_model_var_lookup
            (InstantiateRule.pushSubstModel M env (mkSkolemList F vars i))
            (vars[n]'hn).1 (__eo_to_smt_type (vars[n]'hn).2) =
          __smtx_model_eval M
            (__eo_to_smt (skolemEoTerm F (i + Int.ofNat n))) := by
  intro env vars hEnv
  induction hEnv with
  | nil =>
      intro _ i n hn
      simp at hn
  | cons hTail ih =>
      rename_i s T env vars
      intro hD i n hn
      cases hD with
      | cons hNotMem hDTail =>
        cases n with
        | zero =>
            show native_model_var_lookup
                (InstantiateRule.pushSubstModel M
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) env)
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (skolemEoTerm F i)) (mkSkolemList F vars (i + 1))))
                s (__eo_to_smt_type T) =
              __smtx_model_eval M
                (__eo_to_smt (skolemEoTerm F (i + Int.ofNat 0)))
            rw [InstantiateRule.pushSubstModel_cons_var, var_lookup_push_self,
              show i + Int.ofNat 0 = i from Int.add_zero i]
        | succ n =>
            have hLt : n < vars.length := by
              simpa using Nat.lt_of_succ_lt_succ hn
            have hKeyNe : (((vars[n]'hLt).1,
                __eo_to_smt_type (vars[n]'hLt).2) : SmtVarKey) ≠
                (s, __eo_to_smt_type T) := by
              intro hEq
              apply hNotMem
              have hMem : EoVarKey.toSmt (vars[n]'hLt) ∈ smtKeys vars :=
                List.mem_map_of_mem (getElem_mem' vars n hLt)
              rw [show EoVarKey.toSmt (vars[n]'hLt) =
                  ((vars[n]'hLt).1, __eo_to_smt_type (vars[n]'hLt).2) from rfl,
                hEq] at hMem
              exact hMem
            show native_model_var_lookup
                (InstantiateRule.pushSubstModel M
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) env)
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (skolemEoTerm F i)) (mkSkolemList F vars (i + 1))))
                (vars[n]'hLt).1 (__eo_to_smt_type (vars[n]'hLt).2) =
              __smtx_model_eval M
                (__eo_to_smt (skolemEoTerm F (i + Int.ofNat (n + 1))))
            rw [InstantiateRule.pushSubstModel_cons_var,
              var_lookup_push_ne _ _ _ _ hKeyNe, int_ofNat_shift i n]
            exact ih hDTail (i + 1) n hLt

/-- Truth of the body under the substitution model that maps each binder to
its skolem. -/
theorem skolemize_pushSubst_body_true
    (M : SmtModel) (hM : model_wf M)
    (x G : Term) (vars : List EoVarKey) (hEnv : EoVarEnv x vars)
    (hWfAll : ∀ p ∈ vars, __smtx_type_wf (__eo_to_smt_type p.2) = true)
    (hD : DistinctList (smtKeys vars))
    (hClosed : SmtTermClosedIn (smtKeys vars) (SmtTerm.not (__eo_to_smt G)))
    (hExTrue : __smtx_model_eval M
      (smtExistsList vars (SmtTerm.not (__eo_to_smt G))) =
        SmtValue.Boolean true) :
    __smtx_model_eval
        (InstantiateRule.pushSubstModel M x
          (mkSkolemList (forallTerm x G) vars 0))
        (SmtTerm.not (__eo_to_smt G)) = SmtValue.Boolean true := by
  have hChainTrue :=
    chainModel_body_true (SmtTerm.not (__eo_to_smt G)) vars M hExTrue
  have hAgree : model_agrees_on_env (smtKeys vars)
      (InstantiateRule.pushSubstModel M x
        (mkSkolemList (forallTerm x G) vars 0))
      (chainModel (SmtTerm.not (__eo_to_smt G)) M vars) := by
    refine ⟨?_, ?_⟩
    · exact model_agrees_on_globals_trans
        (globals_symm (InstantiateRule.pushSubstModel_globals M x _))
        (chainModel_globals _ vars M)
    · intro s' T' hMem
      obtain ⟨n, hn, hGet⟩ := mem_index' hMem
      have hn' : n < vars.length := by
        simpa [smtKeys] using hn
      have hKey : ((s', T') : SmtVarKey) =
          ((vars[n]'hn').1, __eo_to_smt_type (vars[n]'hn').2) := by
        rw [← hGet]
        simp [smtKeys, EoVarKey.toSmt]
      cases hKey
      rw [pushSubstModel_lookup_mkSkolems M (forallTerm x G) hEnv hD 0 n hn',
        chainModel_lookup (SmtTerm.not (__eo_to_smt G)) vars M n hn' hD,
        show (0 : native_Int) + Int.ofNat n = Int.ofNat n from Int.zero_add _,
        skolem_transl_eq x G hEnv n]
      exact qskolTerm_eval_eq_chainValue_base M hM _ vars hWfAll hD hClosed n hn'
  have hEvalEq := smt_model_eval_eq_of_closedIn
    (SmtTerm.not (__eo_to_smt G)) (smtKeys vars)
    (InstantiateRule.pushSubstModel M x (mkSkolemList (forallTerm x G) vars 0))
    (chainModel (SmtTerm.not (__eo_to_smt G)) M vars) hClosed hAgree
  rw [hEvalEq]
  exact hChainTrue

/-! ## Soundness core -/

private theorem exists_true_of_premise
    (M : SmtModel) (x G : Term) {vars : List EoVarKey}
    (hEnv : EoVarEnv x vars)
    (hxNonNil : x ≠ Term.__eo_List_nil)
    (hPrem : eo_interprets M (notTerm (forallTerm x G)) true) :
    __smtx_model_eval M (smtExistsList vars (SmtTerm.not (__eo_to_smt G))) =
      SmtValue.Boolean true := by
  cases hPrem with
  | intro_true hTy hEval =>
      rw [eo_to_smt_not_eq, eo_to_smt_forall_eq_of_non_nil x G hxNonNil]
        at hEval
      rw [← eo_to_smt_exists_eq_smtExistsList hEnv]
      exact (InstantiateRule.smtx_model_eval_not_not_true_iff
        (__smtx_model_eval M
          (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt G))))).1
        (by exact hEval)

theorem skolemize_sound
    (M : SmtModel) (hM : model_wf M)
    (x G : Term) (vars : List EoVarKey) (hEnv : EoVarEnv x vars)
    (hxNonNil : x ≠ Term.__eo_List_nil)
    (hWfAll : ∀ p ∈ vars, __smtx_type_wf (__eo_to_smt_type p.2) = true)
    (hD : DistinctList (smtKeys vars))
    (hClosed : SmtTermClosedIn (smtKeys vars) (SmtTerm.not (__eo_to_smt G)))
    (hPrem : eo_interprets M (notTerm (forallTerm x G)) true)
    (hFTrans : RuleProofs.eo_has_smt_translation (notTerm G))
    (hTs : EoListAllHaveSmtTranslation (mkSkolemList (forallTerm x G) vars 0))
    (hActuals : SubstActualsHaveSmtTypes x
      (mkSkolemList (forallTerm x G) vars 0))
    (hResBool : RuleProofs.eo_has_bool_type
      (__substitute_simul_rec (Term.Boolean false) (notTerm G) x
        (mkSkolemList (forallTerm x G) vars 0) Term.__eo_List_nil)) :
    eo_interprets M
      (__substitute_simul_rec (Term.Boolean false) (notTerm G) x
        (mkSkolemList (forallTerm x G) vars 0) Term.__eo_List_nil) true := by
  have hSubstTrans : RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false) (notTerm G) x
        (mkSkolemList (forallTerm x G) vars 0) Term.__eo_List_nil) :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type _ hResBool
  have hEvalEq := InstantiateRule.substitute_simul_eval M hM (notTerm G) x
    (mkSkolemList (forallTerm x G) vars 0) hFTrans hTs hActuals hSubstTrans
  have hExTrue := exists_true_of_premise M x G hEnv hxNonNil hPrem
  have hBodyTrue := skolemize_pushSubst_body_true M hM x G vars hEnv hWfAll
    hD hClosed hExTrue
  refine smt_interprets.intro_true M _ hResBool ?_
  rw [hEvalEq]
  exact hBodyTrue

/-- The typing facts for every skolem entry, from the quantifier's own
translation facts. -/
theorem skolem_entry_facts
    (x G : Term) (vars : List EoVarKey) (hEnv : EoVarEnv x vars)
    (hWfAll : ∀ p ∈ vars, __smtx_type_wf (__eo_to_smt_type p.2) = true)
    (hHBool : __smtx_typeof (SmtTerm.not (__eo_to_smt G)) = SmtType.Bool) :
    ∀ (j : Nat) (hj : j < vars.length),
      SkolemEntryFacts (forallTerm x G) ((0 : native_Int) + Int.ofNat j)
        (vars[j]'hj).2 := by
  intro j hj
  rw [show (0 : native_Int) + Int.ofNat j = Int.ofNat j from Int.zero_add _]
  have hWfj : __smtx_type_wf (__eo_to_smt_type (vars[j]'hj).2) = true :=
    hWfAll _ (getElem_mem' vars j hj)
  have hTy : __smtx_typeof
      (__eo_to_smt (skolemEoTerm (forallTerm x G) (Int.ofNat j))) =
      __eo_to_smt_type (vars[j]'hj).2 := by
    rw [skolem_transl_eq x G hEnv j]
    exact qskolTerm_typeof j vars _ hj hWfAll hHBool
  refine ⟨hWfj, ?_, hTy⟩
  show __smtx_typeof
      (__eo_to_smt (skolemEoTerm (forallTerm x G) (Int.ofNat j))) ≠
    SmtType.None
  rw [hTy]
  exact ne_none_of_wf hWfj

/-! ## Shape of the checker program -/

theorem prog_skolemize_shape (prem : Term)
    (hNe : __eo_prog_skolemize (Proof.pf prem) ≠ Term.Stuck) :
    ∃ x G,
      prem = notTerm (forallTerm x G) ∧
      __is_closed_rec (forallTerm x G) Term.__eo_List_nil = Term.Boolean true ∧
      __eo_list_setof Term.__eo_List_cons x = x ∧
      __eo_prog_skolemize (Proof.pf prem) =
        __substitute_simul_rec (Term.Boolean false) (notTerm G) x
          (__mk_skolems x (forallTerm x G) (Term.Numeral 0))
          Term.__eo_List_nil := by
  cases prem with
  | Apply f inner =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases inner with
              | Apply g G =>
                  cases g with
                  | Apply h x =>
                      cases h with
                      | UOp op2 =>
                          cases op2 with
                          | «forall» =>
                              refine ⟨x, G, rfl, ?_⟩
                              have hProgEq :
                                  __eo_prog_skolemize
                                      (Proof.pf (notTerm (forallTerm x G))) =
                                    __eo_requires
                                      (__is_closed_rec (forallTerm x G)
                                        Term.__eo_List_nil)
                                      (Term.Boolean true)
                                      (__eo_requires
                                        (__eo_list_setof Term.__eo_List_cons x) x
                                        (__substitute_simul_rec
                                          (Term.Boolean false) (notTerm G) x
                                          (__mk_skolems x (forallTerm x G)
                                            (Term.Numeral 0))
                                          Term.__eo_List_nil)) := rfl
                              rw [hProgEq] at hNe ⊢
                              have hClosed :=
                                instantiate_eo_requires_arg_eq_of_ne_stuck hNe
                              have hOuter :=
                                instantiate_eo_requires_result_eq_of_ne_stuck hNe
                              rw [hOuter] at hNe ⊢
                              have hSetof :=
                                instantiate_eo_requires_arg_eq_of_ne_stuck hNe
                              have hInner :=
                                instantiate_eo_requires_result_eq_of_ne_stuck hNe
                              exact ⟨hClosed, hSetof, hInner⟩
                          | _ => exact absurd rfl hNe
                      | _ => exact absurd rfl hNe
                  | _ => exact absurd rfl hNe
              | _ => exact absurd rfl hNe
          | _ => exact absurd rfl hNe
      | _ => exact absurd rfl hNe
  | _ => exact absurd rfl hNe

end SkolemizeRule
