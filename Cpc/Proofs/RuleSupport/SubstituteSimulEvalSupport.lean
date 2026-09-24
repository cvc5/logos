module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.SubstitutePreservationSupport
import all Cpc.Proofs.RuleSupport.SubstitutePreservationSupport
public import Cpc.Proofs.Canonical
import all Cpc.Proofs.Canonical
public import Cpc.Proofs.Closed.ContainsAtomicTermListFree
import all Cpc.Proofs.Closed.ContainsAtomicTermListFree
public import Cpc.Proofs.Closed.Substitute
import all Cpc.Proofs.Closed.Substitute

public section

open Eo
open SmtEval
open Smtm
open SubstituteTranslatabilitySupport
open SubstitutePreservationSupport

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

/-!
# Simultaneous-substitution evaluation engine

The semantic core shared by substitution-based rules (`instantiate`,
`skolemize`): the substitution model `pushSubstModel`, the capture-avoiding
substitution/coincidence engine `substFalse_eval_gen_lt`, and its packaging
`substitute_simul_eval`, together with the quantifier-evaluator congruence
lemmas (`native_eval_exists/tforall_eq_of_body_eval_eq_diff(_typed)`).

This file was split out of `Cpc/Proofs/Rules/Instantiate.lean` so that other
rules can use the engine without depending on the `instantiate` rule module.
The `InstantiateRule` namespace is kept for the moved declarations; see the
docstring of `Cpc/Proofs/Rules/Instantiate.lean` for the engine's design
notes and case breakdown.
-/

namespace InstantiateRule

/-! ### Recursive-argument provenance -/

/-- The application head shape on which substitution and the free-variable
walker take their quantifier/binder branch. -/
def IsBinderHead (f : Term) : Prop :=
  ∃ q v vs,
    f = Term.Apply q
      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)

@[simp] theorem not_isBinderHead_uop (op : UserOp) :
    ¬ IsBinderHead (Term.UOp op) := by
  simp [IsBinderHead]

@[simp] theorem not_isBinderHead_uop1 (op : UserOp1) (i : Term) :
    ¬ IsBinderHead (Term.UOp1 op i) := by
  simp [IsBinderHead]

@[simp] theorem not_isBinderHead_uop2 (op : UserOp2) (i j : Term) :
    ¬ IsBinderHead (Term.UOp2 op i j) := by
  simp [IsBinderHead]

@[simp] theorem not_isBinderHead_uop3 (op : UserOp3) (i j k : Term) :
    ¬ IsBinderHead (Term.UOp3 op i j k) := by
  simp [IsBinderHead]

@[simp] theorem not_isBinderHead_var (name T : Term) :
    ¬ IsBinderHead (Term.Var name T) := by
  simp [IsBinderHead]

/-- `b` occurs below `root` by following only application nodes at which the
substitution/free-variable walkers take their ordinary (non-binder) branch.

The reflexive case is intentional: clients combine this predicate with the
strict `sizeOf` inequality already required by the evaluation induction.  The
predicate is exposed by the shared dispatcher so clients carrying additional
hereditary invariants (alpha-renaming's no-capture facts, in particular) can
recover those facts for the exact recursive argument requested by the
operator-specific machinery. -/
def IsNonbinderSubterm (b : Term) : Term -> Prop
  | Term.Apply f a =>
      b = Term.Apply f a ∨
        ((¬ IsBinderHead f) ∧
          (IsNonbinderSubterm b f ∨ IsNonbinderSubterm b a))
  | t => b = t

@[simp] theorem isNonbinderSubterm_refl (t : Term) :
    IsNonbinderSubterm t t := by
  cases t <;> simp [IsNonbinderSubterm]

theorem isNonbinderSubterm_trans {b c root : Term}
    (hbc : IsNonbinderSubterm b c)
    (hcr : IsNonbinderSubterm c root) :
    IsNonbinderSubterm b root := by
  let rec go (root : Term) (hcr : IsNonbinderSubterm c root) :
      IsNonbinderSubterm b root := by
    cases root with
    | Apply f a =>
        simp only [IsNonbinderSubterm] at hcr ⊢
        rcases hcr with rfl | ⟨hNotBinder, hcf | hca⟩
        · exact hbc
        · exact Or.inr ⟨hNotBinder, Or.inl (go f hcf)⟩
        · exact Or.inr ⟨hNotBinder, Or.inr (go a hca)⟩
    | _ =>
        simp only [IsNonbinderSubterm] at hcr
        subst c
        simpa only [IsNonbinderSubterm] using hbc
  termination_by sizeOf root
  exact go root hcr

theorem not_isBinderHead_apply_of_arg_translation
    (f a : Term) (hTrans : eoHasSmtTranslation a) :
    ¬ IsBinderHead (Term.Apply f a) := by
  rintro ⟨q, v, vs, hEq⟩
  injection hEq with _ hArg
  exact term_not_eo_list_cons_of_has_smt_translation hTrans v vs hArg

/-- Model extension realising a simultaneous substitution `[xs ↦ ts]`.

Recurses over the parallel EO cons-lists `xs` (binders `Var (String s) T`) and
`ts` (instantiation terms), pushing `s : __eo_to_smt_type T` to the value of the
corresponding term **evaluated in the original `M`**. Ill-formed / mismatched
lists fall through to `M` unchanged.

Note: for distinct binder variables the push order is irrelevant. The `nil`-`bvs`
case of the substitution is exactly substitution into this model. -/
noncomputable def pushSubstModel (M : SmtModel) : Term -> Term -> SmtModel
  | (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs),
    (Term.Apply (Term.Apply Term.__eo_List_cons t) ts) =>
      native_model_push (pushSubstModel M xs ts) s (__eo_to_smt_type T)
        (__smtx_model_eval M (__eo_to_smt t))
  | _, _ => M

@[simp] theorem pushSubstModel_nil_left (M : SmtModel) (ts : Term) :
    pushSubstModel M Term.__eo_List_nil ts = M := by
  cases ts <;> rfl

@[simp] theorem pushSubstModel_nil_right (M : SmtModel) (xs : Term) :
    pushSubstModel M xs Term.__eo_List_nil = M := by
  cases xs with
  | Apply f a =>
      cases f with
      | Apply g x =>
          cases g <;> cases x <;> try rfl
          case Var name T =>
            cases name <;> rfl
      | _ => rfl
  | _ => rfl

@[simp] theorem pushSubstModel_cons_var
    (M : SmtModel) (s : native_String) (T xs t ts : Term) :
    pushSubstModel M
        (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs)
        (Term.Apply (Term.Apply Term.__eo_List_cons t) ts) =
      native_model_push (pushSubstModel M xs ts) s (__eo_to_smt_type T)
        (__smtx_model_eval M (__eo_to_smt t)) := by
  rfl

/-- One `pushSubstModel` cons step preserves globals whenever the tail does. -/
theorem pushSubstModel_cons_var_globals
    (M : SmtModel) (s : native_String) (T xs t ts : Term)
    (hTail : model_agrees_on_globals M (pushSubstModel M xs ts)) :
    model_agrees_on_globals M
      (pushSubstModel M
        (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs)
        (Term.Apply (Term.Apply Term.__eo_List_cons t) ts)) := by
  rw [pushSubstModel_cons_var]
  exact model_agrees_on_globals_trans hTail
    (model_agrees_on_globals_push (pushSubstModel M xs ts) s
      (__eo_to_smt_type T) (__smtx_model_eval M (__eo_to_smt t)))

/-- The substitution model only changes variable assignments, never globals. -/
theorem pushSubstModel_globals
    (M : SmtModel) : ∀ xs ts : Term,
    model_agrees_on_globals M (pushSubstModel M xs ts)
  | xs, ts => by
      cases xs with
      | Apply f xsTail =>
          cases f with
          | Apply g x =>
              cases g <;> try exact model_agrees_on_globals_refl M
              case __eo_List_cons =>
                cases x <;> try exact model_agrees_on_globals_refl M
                case Var name T =>
                  cases name <;> try exact model_agrees_on_globals_refl M
                  case String s =>
                    cases ts with
                    | Apply ft tsTail =>
                        cases ft with
                        | Apply gt t =>
                            cases gt <;> try exact model_agrees_on_globals_refl M
                            case __eo_List_cons =>
                              exact
                                pushSubstModel_cons_var_globals M s T xsTail t tsTail
                                  (pushSubstModel_globals M xsTail tsTail)
                        | _ => exact model_agrees_on_globals_refl M
                    | _ => exact model_agrees_on_globals_refl M
          | _ => exact model_agrees_on_globals_refl M
      | _ => exact model_agrees_on_globals_refl M
termination_by xs ts => xs

theorem model_agrees_except_on_env_weaken_except
    {except except' bound : List SmtVarKey} {M N : SmtModel}
    (hSub : ∀ key, key ∈ except -> key ∈ except')
    (hAgree : model_agrees_except_on_env except bound M N) :
    model_agrees_except_on_env except' bound M N := by
  refine ⟨hAgree.globals, ?_⟩
  intro s T hAllowed
  apply hAgree.vars_eq
  rcases hAllowed with hBound | hNotExcept'
  · exact Or.inl hBound
  · exact Or.inr (by
      intro hMem
      exact hNotExcept' (hSub (s, T) hMem))

theorem smtVar_mem_cons_map_tail
    {s : native_String} {T : Term} {vars : List EoVarKey} {key : SmtVarKey}
    (hMem : key ∈ vars.map EoVarKey.toSmt) :
    key ∈ ((s, T) :: vars).map EoVarKey.toSmt := by
  exact List.Mem.tail _ hMem

theorem model_agrees_except_on_env_weaken_cons
    {s : native_String} {T : Term} {vars : List EoVarKey}
    {bound : List SmtVarKey} {M N : SmtModel}
    (hAgree : model_agrees_except_on_env (vars.map EoVarKey.toSmt) bound M N) :
    model_agrees_except_on_env (((s, T) :: vars).map EoVarKey.toSmt) bound M N :=
  model_agrees_except_on_env_weaken_except
    (fun key hMem => smtVar_mem_cons_map_tail hMem) hAgree

theorem model_agrees_on_env_of_agrees_except_empty
    {vars bound : List SmtVarKey} {M N : SmtModel}
    (hAgree : model_agrees_except_on_env [] bound M N) :
    model_agrees_on_env vars M N := by
  refine ⟨hAgree.globals, ?_⟩
  intro s T _hMem
  exact hAgree.vars_eq s T (Or.inr (by simp))

theorem model_agrees_on_env_of_agrees_everywhere
    {vars : List SmtVarKey} {M N : SmtModel}
    (hAgree : model_agrees_except_on_env [] [] M N) :
    model_agrees_on_env vars M N := by
  exact model_agrees_on_env_of_agrees_except_empty hAgree

/-- `pushSubstModel` agrees with the original model outside the binder keys. -/
theorem pushSubstModel_agrees_except
    (M : SmtModel) :
    ∀ {xs : Term} {vars : List EoVarKey} (ts : Term),
      EoVarEnv xs vars ->
        model_agrees_except_on_env (vars.map EoVarKey.toSmt) []
          (pushSubstModel M xs ts) M
  | _, _, ts, EoVarEnv.nil => by
      simp [pushSubstModel]
      exact model_agrees_except_on_env_refl [] [] M
  | _, _, ts, EoVarEnv.cons (s := s) (T := T) (env := env) (vars := vars) hTail => by
      have hBase :
          model_agrees_except_on_env (((s, T) :: vars).map EoVarKey.toSmt) [] M M :=
        model_agrees_except_on_env_weaken_cons
          (s := s) (T := T) (vars := vars) (bound := [])
          (M := M) (N := M)
          (model_agrees_except_on_env_refl (vars.map EoVarKey.toSmt) [] M)
      cases ts with
      | Apply ft tsTail =>
          cases ft with
          | Apply gt t =>
              cases gt <;> try simpa [pushSubstModel] using hBase
              case __eo_List_cons =>
                have hTailAgree :
                    model_agrees_except_on_env (vars.map EoVarKey.toSmt) []
                      (pushSubstModel M env tsTail) M :=
                  pushSubstModel_agrees_except M tsTail hTail
                have hTailAgreeWeak :
                    model_agrees_except_on_env (((s, T) :: vars).map EoVarKey.toSmt) []
                      (pushSubstModel M env tsTail) M :=
                  model_agrees_except_on_env_weaken_cons
                    (s := s) (T := T) (vars := vars) (bound := [])
                    (M := pushSubstModel M env tsTail) (N := M)
                    hTailAgree
                have hHeadMem :
                    (s, __eo_to_smt_type T) ∈ ((s, T) :: vars).map EoVarKey.toSmt :=
                  List.mem_map.2 ⟨(s, T), List.Mem.head _, rfl⟩
                simpa [pushSubstModel, EoVarKey.toSmt] using
                  model_agrees_except_on_env_push_left hTailAgreeWeak
                    hHeadMem (by simp)
          | _ =>
              simpa [pushSubstModel] using hBase
      | _ =>
          simpa [pushSubstModel] using hBase

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

theorem smtx_typeof_eo_to_smt_eq_of_eval_eq
    {M N : SmtModel} (hM : model_wf M) (hN : model_wf N)
    (x y : Term)
    (hX : eoHasSmtTranslation x) (hY : eoHasSmtTranslation y)
    (hEval :
      __smtx_model_eval M (__eo_to_smt x) =
        __smtx_model_eval N (__eo_to_smt y)) :
    __smtx_typeof (__eo_to_smt x) =
      __smtx_typeof (__eo_to_smt y) := by
  have hXNN : term_has_non_none_type (__eo_to_smt x) := by
    simpa [eoHasSmtTranslation, term_has_non_none_type] using hX
  have hYNN : term_has_non_none_type (__eo_to_smt y) := by
    simpa [eoHasSmtTranslation, term_has_non_none_type] using hY
  have hXTy :=
    smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) hXNN
  have hYTy :=
    smt_model_eval_preserves_type_of_non_none N hN (__eo_to_smt y) hYNN
  calc
    __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) := hXTy.symm
    _ = __smtx_typeof_value (__smtx_model_eval N (__eo_to_smt y)) := by
      rw [hEval]
    _ = __smtx_typeof (__eo_to_smt y) := hYTy

/-- The semantic shape of a model obtained by instantiating an EO binder list. -/
inductive ForallInstantiationModel : SmtModel -> Term -> SmtModel -> Prop where
  | nil (M : SmtModel) :
      ForallInstantiationModel M Term.__eo_List_nil M
  | cons {M N : SmtModel} {s : native_String} {T env : Term} {v : SmtValue} :
      __smtx_type_wf (__eo_to_smt_type T) = true ->
      __smtx_typeof_value v = __eo_to_smt_type T ->
      __smtx_value_canonical v = true ->
      ForallInstantiationModel
        (native_model_push M s (__eo_to_smt_type T) v) env N ->
      ForallInstantiationModel M
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) env) N

/--
Builds the quantifier-assignment model obtained by reading each binder value
from `Source` and pushing it, in binder order, onto the base model `M`.
-/
noncomputable def forallAssignmentModel (Source : SmtModel) :
    SmtModel -> Term -> SmtModel
  | M,
    (Term.Apply (Term.Apply Term.__eo_List_cons
      (Term.Var (Term.String s) T)) env) =>
      forallAssignmentModel Source
        (native_model_push M s (__eo_to_smt_type T)
          (native_model_var_lookup Source s (__eo_to_smt_type T)))
        env
  | M, _ => M

@[simp] theorem forallAssignmentModel_nil
    (Source M : SmtModel) :
    forallAssignmentModel Source M Term.__eo_List_nil = M := by
  rfl

@[simp] theorem forallAssignmentModel_cons_var
    (Source M : SmtModel) (s : native_String) (T env : Term) :
    forallAssignmentModel Source M
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) env) =
      forallAssignmentModel Source
        (native_model_push M s (__eo_to_smt_type T)
          (native_model_var_lookup Source s (__eo_to_smt_type T)))
        env := by
  rfl

/-- Well-typed canonical instantiation preserves total typedness of models. -/
theorem ForallInstantiationModel.total_typed
    {M N : SmtModel} {xs : Term}
    (hInst : ForallInstantiationModel M xs N)
    (hM : model_wf M) :
    model_wf N := by
  induction hInst with
  | nil M =>
      exact hM
  | cons hWf hValTy hValCan _hTail ih =>
      rename_i M N s T env v
      exact ih
        (model_total_typed_push hM s (__eo_to_smt_type T) v
          hWf hValTy
          (by simpa [value_canonical] using hValCan))

/--
An instantiation model agrees with its base model outside the quantified binder
keys. The instantiated values may differ exactly on those keys.
-/
theorem ForallInstantiationModel.agrees_except
    {M N : SmtModel} {xs : Term} {vars : List EoVarKey}
    (hInst : ForallInstantiationModel M xs N)
    (hEnv : EoVarEnv xs vars) :
    model_agrees_except_on_env (vars.map EoVarKey.toSmt) [] N M := by
  induction hInst generalizing vars with
  | nil M =>
      cases hEnv
      exact model_agrees_except_on_env_refl [] [] M
  | cons hWf hValTy hValCan hTail ih =>
      rename_i M N s T env v
      cases hEnv with
      | cons hEnvTail =>
          rename_i tailVars
          have hTailAgree :
              model_agrees_except_on_env
                (tailVars.map EoVarKey.toSmt) [] N
                (native_model_push M s (__eo_to_smt_type T) v) :=
            ih hEnvTail
          have hPushGlobals :
              model_agrees_on_globals
                (native_model_push M s (__eo_to_smt_type T) v) M :=
            ⟨by
                intro s' T'
                exact
                  ((model_agrees_on_globals_push M s (__eo_to_smt_type T) v).1
                    s' T').symm,
              by
                intro fid T' U'
                exact
                  ((model_agrees_on_globals_push M s (__eo_to_smt_type T) v).2
                    fid T' U').symm⟩
          refine
            ⟨model_agrees_on_globals_trans hTailAgree.globals hPushGlobals, ?_⟩
          intro s' T' hAllowed
          rcases hAllowed with hBound | hNotExcept
          · cases hBound
          · have hNotTail :
                (s', T') ∉ tailVars.map EoVarKey.toSmt := by
              intro hMem
              exact hNotExcept (List.Mem.tail _ hMem)
            have hKeyNe :
                ({ isVar := true, name := s', ty := T' } : SmtModelKey) ≠
                  { isVar := true, name := s, ty := __eo_to_smt_type T } := by
              intro hKey
              apply hNotExcept
              cases hKey
              simp [EoVarKey.toSmt]
            have hTailEq :
                native_model_var_lookup N s' T' =
                  native_model_var_lookup
                    (native_model_push M s (__eo_to_smt_type T) v) s' T' :=
              hTailAgree.vars_eq s' T' (Or.inr hNotTail)
            have hPushEq :
                native_model_var_lookup
                    (native_model_push M s (__eo_to_smt_type T) v) s' T' =
                  native_model_var_lookup M s' T' := by
              simp [native_model_var_lookup, native_model_push, hKeyNe]
            exact hTailEq.trans hPushEq

/--
Values read from a total model produce a legal instantiation model for any
well-formed binder environment.
-/
theorem forallAssignmentModel_instantiation
    (Source : SmtModel) (hSource : model_wf Source)
    {xs : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv xs vars)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (M : SmtModel) :
    ForallInstantiationModel M xs
      (forallAssignmentModel Source M xs) := by
  induction hEnv generalizing M with
  | nil =>
      simp [forallAssignmentModel]
      exact ForallInstantiationModel.nil M
  | cons hTail ih =>
      rename_i s T env tailVars
      rw [forallAssignmentModel_cons_var]
      let ST := __eo_to_smt_type T
      have hHeadWf : __smtx_type_wf ST = true :=
        hWf s T (List.Mem.head _)
      refine ForallInstantiationModel.cons (M := M)
        (N := forallAssignmentModel Source
          (native_model_push M s ST
            (native_model_var_lookup Source s ST)) env)
        (s := s) (T := T) (env := env)
        (v := native_model_var_lookup Source s ST)
        (by simpa [ST] using hHeadWf)
        (by
          simpa [ST] using
            model_total_typed_var_lookup hSource s ST hHeadWf)
        (by
          simpa [ST, value_canonical] using
            model_total_typed_var_lookup_canonical hSource s ST hHeadWf)
        ?_
      exact ih
        (by
          intro s' T' hMem
          exact hWf s' T' (List.Mem.tail _ hMem))
        (native_model_push M s ST
          (native_model_var_lookup Source s ST))

theorem forallAssignmentModel_total_typed
    (Source M : SmtModel)
    (hSource : model_wf Source) (hM : model_wf M)
    {xs : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv xs vars)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true) :
    model_wf (forallAssignmentModel Source M xs) :=
  (forallAssignmentModel_instantiation Source hSource hEnv hWf M).total_typed hM

theorem forallAssignmentModel_agrees_except_base
    (Source M : SmtModel)
    {xs : Term} {vars : List EoVarKey}
    (hSource : model_wf Source)
    (hEnv : EoVarEnv xs vars)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true) :
    model_agrees_except_on_env (vars.map EoVarKey.toSmt) []
      (forallAssignmentModel Source M xs) M :=
  (forallAssignmentModel_instantiation Source hSource hEnv hWf M).agrees_except hEnv

/--
If `M` and `Source` already agree outside the binder keys, assigning the binder
keys from `Source` makes the resulting model agree with `Source` everywhere.
-/
theorem forallAssignmentModel_agrees_source
    (Source M : SmtModel)
    {xs : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv xs vars)
    (hBase :
      model_agrees_except_on_env (vars.map EoVarKey.toSmt) [] M Source) :
    model_agrees_except_on_env [] []
      (forallAssignmentModel Source M xs) Source := by
  induction hEnv generalizing M with
  | nil =>
      simpa [forallAssignmentModel] using hBase
  | cons hTail ih =>
      rename_i s T env tailVars
      rw [forallAssignmentModel_cons_var]
      let ST := __eo_to_smt_type T
      let v := native_model_var_lookup Source s ST
      have hPushGlobals :
          model_agrees_on_globals (native_model_push M s ST v) Source := by
        have hPushToBase :
            model_agrees_on_globals (native_model_push M s ST v) M :=
          ⟨by
              intro s' T'
              exact ((model_agrees_on_globals_push M s ST v).1 s' T').symm,
            by
              intro fid T' U'
              exact
                ((model_agrees_on_globals_push M s ST v).2 fid T' U').symm⟩
        exact model_agrees_on_globals_trans hPushToBase hBase.globals
      have hPushBase :
          model_agrees_except_on_env (tailVars.map EoVarKey.toSmt) []
            (native_model_push M s ST v) Source := by
        refine ⟨hPushGlobals, ?_⟩
        intro s' T' hAllowed
        rcases hAllowed with hBound | hNotTail
        · cases hBound
        · by_cases hPair : (s', T') = (s, ST)
          · cases hPair
            simp [native_model_var_lookup, native_model_push, v]
          · have hKeyNe :
                ({ isVar := true, name := s', ty := T' } : SmtModelKey) ≠
                  { isVar := true, name := s, ty := ST } := by
              intro hKey
              apply hPair
              cases hKey
              rfl
            have hNotFull :
                (s', T') ∉ ((s, T) :: tailVars).map EoVarKey.toSmt := by
              intro hMem
              cases hMem with
              | head =>
                  exact hPair rfl
              | tail _ hTailMem =>
                  exact hNotTail hTailMem
            have hPushEq :
                native_model_var_lookup
                    (native_model_push M s ST v) s' T' =
                  native_model_var_lookup M s' T' := by
              simp [native_model_var_lookup, native_model_push, hKeyNe]
            exact hPushEq.trans (hBase.vars_eq s' T' (Or.inr hNotFull))
      exact ih (native_model_push M s ST v) hPushBase


theorem substActualsHaveSmtTypes_pushSubstModel_lookup_mapped
    (M : SmtModel) :
    ∀ {xs ts : Term},
      SubstActualsHaveSmtTypes xs ts ->
        ∀ (s : native_String) (T : Term),
          __eo_is_neg (__eo_list_find Term.__eo_List_cons xs
            (Term.Var (Term.String s) T)) = Term.Boolean false ->
          native_model_var_lookup (pushSubstModel M xs ts)
              s (__eo_to_smt_type T) =
            __smtx_model_eval M
              (__eo_to_smt
                (__assoc_nil_nth Term.__eo_List_cons ts
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T))))
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
  | _, _, SubstActualsHaveSmtTypes.cons hWf hTrans hTy hTail =>
      by
        rename_i s0 T0 env t ts
        intro s T hFind
        rcases SubstActualsHaveSmtTypes.env hTail with ⟨vars, hEnv⟩
        by_cases hHead :
            Term.Var (Term.String s0) T0 =
              Term.Var (Term.String s) T
        · cases hHead
          have hConsList :
              __eo_is_list Term.__eo_List_cons
                (Term.Apply (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s0) T0)) env) =
                Term.Boolean true := by
            simpa using (EoVarEnv.cons (s := s0) (T := T0) hEnv).is_list
          simp [pushSubstModel_cons_var, __eo_list_find, __eo_requires,
            hConsList, __eo_list_find_rec, __assoc_nil_nth,
            __eo_l_1___assoc_nil_nth, __eo_eq, native_model_var_lookup,
            native_model_push, native_ite, native_teq, native_not,
            SmtEval.native_not]
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
          have hTargetWf :
              __smtx_type_wf (__eo_to_smt_type T) = true :=
            SubstActualsHaveSmtTypes.wf_of_find_neg_false
              (SubstActualsHaveSmtTypes.cons hWf hTrans hTy hTail)
              s T hFind
          have hKeyNe :
              ({ isVar := true, name := s, ty := __eo_to_smt_type T } :
                  SmtModelKey) ≠
                { isVar := true, name := s0, ty := __eo_to_smt_type T0 } := by
            intro hKey
            have hSmtMem :
                (s, __eo_to_smt_type T) ∈
                  ([(s0, T0)] : List EoVarKey).map EoVarKey.toSmt := by
              have hPair :
                  (s, __eo_to_smt_type T) =
                    (s0, __eo_to_smt_type T0) := by
                injection hKey with _ hName hTySmt
                exact Prod.ext hName hTySmt
              rw [hPair]
              simp [EoVarKey.toSmt]
            have hExact : (s, T) ∈ ([(s0, T0)] : List EoVarKey) :=
              EoVarKey.mem_of_toSmt_mem_map_of_type_wf hTargetWf hSmtMem
            simp at hExact
            exact hHeadKeyNe (Prod.ext hExact.1 hExact.2)
          have hPushEq :
              native_model_var_lookup
                  (native_model_push (pushSubstModel M env ts)
                    s0 (__eo_to_smt_type T0)
                    (__smtx_model_eval M (__eo_to_smt t)))
                  s (__eo_to_smt_type T) =
                native_model_var_lookup (pushSubstModel M env ts)
                  s (__eo_to_smt_type T) := by
            simp [native_model_var_lookup, native_model_push, hKeyNe]
          have hAssoc :=
            assoc_nil_nth_cons_find_tail_eq (ts := ts)
              hEnv s0 T0 t hHead hTailMem
          rw [pushSubstModel_cons_var, hPushEq, hAssoc]
          exact
            substActualsHaveSmtTypes_pushSubstModel_lookup_mapped M
              hTail s T hTailFind

theorem pushSubstModel_total_typed_of_actuals
    (M : SmtModel) (hM : model_wf M)
    {xs ts : Term}
    (hActuals : SubstActualsTyped M xs ts) :
    model_wf (pushSubstModel M xs ts) := by
  induction hActuals with
  | nil ts =>
      simp [pushSubstModel]
      exact hM
  | cons hWf hValTy hValCan _hTail ih =>
      rename_i s T env t ts
      rw [pushSubstModel_cons_var]
      exact model_total_typed_push ih s (__eo_to_smt_type T)
        (__smtx_model_eval M (__eo_to_smt t)) hWf hValTy
        (by simpa [value_canonical] using hValCan)

theorem pushSubstModel_total_typed_of_smt_typed_actuals
    (M : SmtModel) (hM : model_wf M)
    {xs ts : Term}
    (hActuals : SubstActualsHaveSmtTypes xs ts) :
    model_wf (pushSubstModel M xs ts) :=
  pushSubstModel_total_typed_of_actuals M hM
    (SubstActualsHaveSmtTypes.to_typed M hM hActuals)

theorem substFalseRel_pushSubstModel
    (M : SmtModel) (hM : model_wf M)
    {xs ts : Term}
    (hActuals : SubstActualsHaveSmtTypes xs ts) :
    SubstituteSupport.SubstFalseRel M (pushSubstModel M xs ts)
      xs ts Term.__eo_List_nil := by
  rcases SubstActualsHaveSmtTypes.env_wf hActuals with
    ⟨vars, hEnv, hVarsWf⟩
  refine ⟨pushSubstModel_globals M xs ts, ?_, ?_⟩
  · intro s T hAllowed
    rcases hAllowed with hBound | hUnmapped
    · have hNil :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons Term.__eo_List_nil
                (Term.Var (Term.String s) T)) =
            Term.Boolean true :=
        EoVarEnv.nil.find_neg_true_of_not_mem (by simp)
      rw [hNil] at hBound
      cases hBound
    · by_cases hWf :
          __smtx_type_wf (__eo_to_smt_type T) = true
      · have hNotMem :
            (s, __eo_to_smt_type T) ∉ vars.map EoVarKey.toSmt :=
          EoVarEnvPerm.toSmt_not_mem_of_find_neg_true
            (EoVarEnvPerm.of_exact hEnv) hWf hUnmapped
        have hAgree :
            native_model_var_lookup (pushSubstModel M xs ts)
                s (__eo_to_smt_type T) =
              native_model_var_lookup M s (__eo_to_smt_type T) :=
          (pushSubstModel_agrees_except M ts hEnv).vars_eq
            s (__eo_to_smt_type T) (Or.inr hNotMem)
        exact hAgree.symm
      · have hWfFalse :
            __smtx_type_wf (__eo_to_smt_type T) = false := by
          cases hWfBool : __smtx_type_wf (__eo_to_smt_type T) <;>
            simp [hWfBool] at hWf ⊢
        have hNotMem :
            (s, __eo_to_smt_type T) ∉ vars.map EoVarKey.toSmt := by
          intro hMem
          rcases List.mem_map.1 hMem with ⟨⟨s', T'⟩, hKeyMem, hKeyEq⟩
          have hKeyWf := hVarsWf s' T' hKeyMem
          simp [EoVarKey.toSmt] at hKeyEq
          rw [hKeyEq.2, hWfFalse] at hKeyWf
          cases hKeyWf
        have hAgree :=
          (pushSubstModel_agrees_except M ts hEnv).vars_eq
            s (__eo_to_smt_type T) (Or.inr hNotMem)
        exact hAgree.symm
  · intro s T _hFree hMapped
    exact
      substActualsHaveSmtTypes_pushSubstModel_lookup_mapped
        M hActuals s T hMapped

theorem smtx_model_eval_not_true_iff (v : SmtValue) :
    __smtx_model_eval_not v = SmtValue.Boolean true ↔
      v = SmtValue.Boolean false := by
  cases v <;> simp [__smtx_model_eval_not, SmtEval.native_not]

theorem smtx_model_eval_not_not_true_iff (v : SmtValue) :
    __smtx_model_eval_not (__smtx_model_eval_not v) =
        SmtValue.Boolean true ↔
      v = SmtValue.Boolean true := by
  cases v <;> simp [__smtx_model_eval_not, SmtEval.native_not]

theorem forall_instantiation_exists_type_bool
    {M N : SmtModel} {xs : Term}
    (hInst : ForallInstantiationModel M xs N)
    (body : SmtTerm)
    (hBodyTy : __smtx_typeof body = SmtType.Bool) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool := by
  induction hInst generalizing body with
  | nil M =>
      simpa [__eo_to_smt_exists] using hBodyTy
  | cons hWf _hValTy _hValCan _hTail ih =>
      rename_i M N s T env v
      exact
        closed_smtx_typeof_eo_to_smt_exists_cons_bool_of_tail_bool
          s T env body hWf (ih body hBodyTy)

/--
If an encoded universal quantifier is true, its body is true in any model that
is obtained by a well-typed canonical instantiation of its binder list.
-/
theorem forall_instantiation_body_true
    {M N : SmtModel} {xs : Term} {body : SmtTerm}
    (hInst : ForallInstantiationModel M xs N)
    (hM : model_wf M)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hEval :
      __smtx_model_eval M
        (SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not body))) =
        SmtValue.Boolean true) :
    __smtx_model_eval N body = SmtValue.Boolean true := by
  induction hInst generalizing body with
  | nil M =>
      exact
        (smtx_model_eval_not_not_true_iff
          (__smtx_model_eval M body)).1
          (by simpa [__eo_to_smt_exists, __smtx_model_eval] using hEval)
  | cons hWf hValTy hValCan hTail ih =>
      rename_i M N s T env v
      let ST := __eo_to_smt_type T
      let tail := __eo_to_smt_exists env (SmtTerm.not body)
      have hOuterNot :
          __smtx_model_eval_not
              (__smtx_model_eval M (SmtTerm.exists s ST tail)) =
            SmtValue.Boolean true := by
        simpa [ST, tail, __eo_to_smt_exists, __smtx_model_eval] using hEval
      have hExistsFalse :
          __smtx_model_eval M (SmtTerm.exists s ST tail) =
            SmtValue.Boolean false :=
        (smtx_model_eval_not_true_iff
          (__smtx_model_eval M (SmtTerm.exists s ST tail))).1 hOuterNot
      have hNoSat :
          ¬ ∃ w : SmtValue,
            __smtx_typeof_value w = ST ∧
              __smtx_value_canonical w = true ∧
              __smtx_model_eval (native_model_push M s ST w) tail =
                SmtValue.Boolean true := by
        intro hSat
        have hExistsTrue :
            __smtx_model_eval M (SmtTerm.exists s ST tail) =
              SmtValue.Boolean true := by
          simp [__smtx_model_eval, hSat]
        rw [hExistsFalse] at hExistsTrue
        cases hExistsTrue
      have hNotBodyTy :
          __smtx_typeof (SmtTerm.not body) = SmtType.Bool :=
        smtx_typeof_not_eq_bool_of_non_none body
          (by
            rw [typeof_not_eq, hBodyTy]
            simp [native_ite, native_Teq])
      have hTailTy :
          __smtx_typeof tail = SmtType.Bool := by
        simpa [tail] using
          forall_instantiation_exists_type_bool hTail
            (SmtTerm.not body) hNotBodyTy
      have hPushTotal :
          model_wf (native_model_push M s ST v) :=
        model_total_typed_push hM s ST v
          (by simpa [ST] using hWf)
          (by simpa [ST] using hValTy)
          (by simpa [value_canonical] using hValCan)
      have hTailNotTrue :
          __smtx_model_eval (native_model_push M s ST v) tail ≠
            SmtValue.Boolean true := by
        intro hTailTrue
        exact hNoSat ⟨v, by simpa [ST] using hValTy, hValCan, hTailTrue⟩
      rcases smt_model_eval_bool_is_boolean
          (native_model_push M s ST v) hPushTotal tail hTailTy with
        ⟨b, hTailEval⟩
      cases b
      · have hEvalTail :
            __smtx_model_eval (native_model_push M s ST v)
                (SmtTerm.not tail) =
              SmtValue.Boolean true := by
          simp [__smtx_model_eval, hTailEval, __smtx_model_eval_not,
            SmtEval.native_not]
        exact ih hPushTotal hBodyTy (by simpa [tail] using hEvalTail)
      · exact False.elim (hTailNotTrue hTailEval)

/--
Pure universal instantiation using binder values read from an arbitrary total
source model.
-/
theorem forall_assignment_body_true
    {M Source : SmtModel} {xs : Term} {vars : List EoVarKey}
    {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hSource : model_wf Source)
    (hM : model_wf M)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hEval :
      __smtx_model_eval M
        (SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not body))) =
        SmtValue.Boolean true) :
    __smtx_model_eval (forallAssignmentModel Source M xs) body =
      SmtValue.Boolean true :=
  forall_instantiation_body_true
    (forallAssignmentModel_instantiation Source hSource hEnv hWf M)
    hM hBodyTy hEval

/--
Bridge from pure universal instantiation to the substitution model.

The two remaining facts needed by the full instantiate proof are kept explicit:
`pushSubstModel` must be total-typed, and the translated body must be closed in
some finite SMT-variable environment. The assignment model then agrees with the
substitution model everywhere, so closed-term evaluation coincidence transfers
the truth of the body.
-/
theorem instantiate_body_true_of_push_total_and_closedIn
    (M : SmtModel) (hM : model_wf M)
    (xs F ts : Term)
    (hPrem : eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) true)
    (hWf : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hPushTotal : model_wf (pushSubstModel M xs ts))
    (hBodyClosed :
      ∃ bodyVars : List SmtVarKey,
        SmtTermClosedIn bodyVars (__eo_to_smt F)) :
    __smtx_model_eval (pushSubstModel M xs ts) (__eo_to_smt F) =
      SmtValue.Boolean true := by
  have hXsNonNil : xs ≠ Term.__eo_List_nil :=
    forall_binders_non_nil_of_has_smt_translation xs F hWf
  have hBodyBool : RuleProofs.eo_has_bool_type F :=
    forall_body_has_bool_type_of_has_smt_translation xs F hWf
  rcases forall_binders_env_of_has_smt_translation xs F hWf with
    ⟨binderVars, hXsEnv⟩
  cases hPrem with
  | intro_true hForallTy hForallEval =>
      rw [eo_to_smt_forall_eq_of_non_nil xs F hXsNonNil] at hForallTy hForallEval
      let Source := pushSubstModel M xs ts
      have hBinderWf :
          ∀ s T, (s, T) ∈ binderVars ->
            __smtx_type_wf (__eo_to_smt_type T) = true :=
        forall_binder_types_wf_of_has_smt_translation hWf hXsEnv
      have hAssignTrue :
          __smtx_model_eval (forallAssignmentModel Source M xs)
              (__eo_to_smt F) =
            SmtValue.Boolean true :=
        forall_assignment_body_true
          (M := M) (Source := Source) (xs := xs) (vars := binderVars)
          (body := __eo_to_smt F)
          hXsEnv
          (by simpa [Source] using hPushTotal)
          hM hBinderWf hBodyBool hForallEval
      have hBase :
          model_agrees_except_on_env (binderVars.map EoVarKey.toSmt) []
            M Source :=
        model_agrees_except_on_env_symm
          (by
            simpa [Source] using
              pushSubstModel_agrees_except M ts hXsEnv)
      have hAgreeAll :
          model_agrees_except_on_env [] []
            (forallAssignmentModel Source M xs) Source :=
        forallAssignmentModel_agrees_source Source M hXsEnv hBase
      rcases hBodyClosed with ⟨bodyVars, hClosed⟩
      have hEvalEq :
          __smtx_model_eval (forallAssignmentModel Source M xs)
              (__eo_to_smt F) =
            __smtx_model_eval Source (__eo_to_smt F) :=
        smt_model_eval_eq_of_closedIn (__eo_to_smt F) bodyVars
          (forallAssignmentModel Source M xs) Source hClosed
          (model_agrees_on_env_of_agrees_everywhere hAgreeAll)
      simpa [Source, ← hEvalEq] using hAssignTrue

/-- Different-body congruence for the existential evaluator: if for every
witness value the two (distinct) bodies evaluate equally in the pushed models,
then the existentials evaluate equally. Generalises
`native_eval_texists_eq_of_body_eval_eq` (same body) and is what the
substitution case needs (`toSmt (subst a)` vs `toSmt a`). -/
theorem native_eval_texists_eq_of_body_eval_eq_diff
    {M N : SmtModel} {s : native_String} {T : SmtType} {bodyM bodyN : SmtTerm}
    (hBody : ∀ v : SmtValue,
      __smtx_model_eval (native_model_push M s T v) bodyM =
        __smtx_model_eval (native_model_push N s T v) bodyN) :
    (native_eval_exists M s T bodyM : SmtValue) =
      (native_eval_exists N s T bodyN : SmtValue) := by
  classical
  let PM : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push M s T v) bodyM = SmtValue.Boolean true
  let PN : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push N s T v) bodyN = SmtValue.Boolean true
  change (if _ : PM then SmtValue.Boolean true else SmtValue.Boolean false) =
    (if _ : PN then SmtValue.Boolean true else SmtValue.Boolean false)
  have hIff : PM ↔ PN := by
    constructor
    · intro h
      rcases h with ⟨v, hTy, hCanon, hEval⟩
      exact ⟨v, hTy, hCanon, by simpa [hBody v] using hEval⟩
    · intro h
      rcases h with ⟨v, hTy, hCanon, hEval⟩
      exact ⟨v, hTy, hCanon, by simpa [← hBody v] using hEval⟩
  by_cases hM : PM
  · have hN : PN := hIff.mp hM
    simp [hM, hN]
  · have hN : ¬ PN := fun h => hM (hIff.mpr h)
    simp [hM, hN]

/-- Different-body existential congruence where the body equality is only
needed for values that pass the evaluator's type/canonical guards. -/
theorem native_eval_texists_eq_of_body_eval_eq_diff_typed
    {M N : SmtModel} {s : native_String} {T : SmtType} {bodyM bodyN : SmtTerm}
    (hBody : ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
      __smtx_value_canonical v = true ->
      __smtx_model_eval (native_model_push M s T v) bodyM =
        __smtx_model_eval (native_model_push N s T v) bodyN) :
    (native_eval_exists M s T bodyM : SmtValue) =
      (native_eval_exists N s T bodyN : SmtValue) := by
  classical
  let PM : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push M s T v) bodyM = SmtValue.Boolean true
  let PN : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push N s T v) bodyN = SmtValue.Boolean true
  change (if _ : PM then SmtValue.Boolean true else SmtValue.Boolean false) =
    (if _ : PN then SmtValue.Boolean true else SmtValue.Boolean false)
  have hIff : PM ↔ PN := by
    constructor
    · intro h
      rcases h with ⟨v, hTy, hCanon, hEval⟩
      exact ⟨v, hTy, hCanon, by simpa [hBody v hTy hCanon] using hEval⟩
    · intro h
      rcases h with ⟨v, hTy, hCanon, hEval⟩
      exact ⟨v, hTy, hCanon, by simpa [← hBody v hTy hCanon] using hEval⟩
  by_cases hM : PM
  · have hN : PN := hIff.mp hM
    simp [hM, hN]
  · have hN : ¬ PN := fun h => hM (hIff.mpr h)
    simp [hM, hN]

/-- Different-body congruence for the universal evaluator. -/
theorem native_eval_tforall_eq_of_body_eval_eq_diff
    {M N : SmtModel} {s : native_String} {T : SmtType} {bodyM bodyN : SmtTerm}
    (hBody : ∀ v : SmtValue,
      __smtx_model_eval (native_model_push M s T v) bodyM =
        __smtx_model_eval (native_model_push N s T v) bodyN) :
    (native_eval_forall M s T bodyM : SmtValue) =
      (native_eval_forall N s T bodyN : SmtValue) := by
  classical
  let PM : Prop :=
    ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
        __smtx_value_canonical v = true ->
        __smtx_model_eval (native_model_push M s T v) bodyM = SmtValue.Boolean true
  let PN : Prop :=
    ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
        __smtx_value_canonical v = true ->
        __smtx_model_eval (native_model_push N s T v) bodyN = SmtValue.Boolean true
  change (if _ : PM then SmtValue.Boolean true else SmtValue.Boolean false) =
    (if _ : PN then SmtValue.Boolean true else SmtValue.Boolean false)
  have hIff : PM ↔ PN := by
    constructor
    · intro h v hTy hCanon
      simpa [← hBody v] using h v hTy hCanon
    · intro h v hTy hCanon
      simpa [hBody v] using h v hTy hCanon
  by_cases hM : PM
  · have hN : PN := hIff.mp hM
    simp [hM, hN]
  · have hN : ¬ PN := fun h => hM (hIff.mpr h)
    simp [hM, hN]

/-- Different-body universal congruence where the body equality is only needed
for values that pass the evaluator's type/canonical guards. -/
theorem native_eval_tforall_eq_of_body_eval_eq_diff_typed
    {M N : SmtModel} {s : native_String} {T : SmtType} {bodyM bodyN : SmtTerm}
    (hBody : ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
      __smtx_value_canonical v = true ->
      __smtx_model_eval (native_model_push M s T v) bodyM =
        __smtx_model_eval (native_model_push N s T v) bodyN) :
    (native_eval_forall M s T bodyM : SmtValue) =
      (native_eval_forall N s T bodyN : SmtValue) := by
  classical
  let PM : Prop :=
    ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
        __smtx_value_canonical v = true ->
        __smtx_model_eval (native_model_push M s T v) bodyM = SmtValue.Boolean true
  let PN : Prop :=
    ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
        __smtx_value_canonical v = true ->
        __smtx_model_eval (native_model_push N s T v) bodyN = SmtValue.Boolean true
  change (if _ : PM then SmtValue.Boolean true else SmtValue.Boolean false) =
    (if _ : PN then SmtValue.Boolean true else SmtValue.Boolean false)
  have hIff : PM ↔ PN := by
    constructor
    · intro h v hTy hCanon
      simpa [← hBody v hTy hCanon] using h v hTy hCanon
    · intro h v hTy hCanon
      simpa [hBody v hTy hCanon] using h v hTy hCanon
  by_cases hM : PM
  · have hN : PN := hIff.mp hM
    simp [hM, hN]
  · have hN : ¬ PN := fun h => hM (hIff.mpr h)
    simp [hM, hN]

theorem substFalseRel_of_bvs_perm
    {M N : SmtModel} {xs ss bvsOld bvsNew : Term}
    {bvsVars : List EoVarKey}
    (hOld : EoVarEnvPerm bvsOld bvsVars)
    (hNew : EoVarEnvPerm bvsNew bvsVars)
    (hRel : SubstituteSupport.SubstFalseRel M N xs ss bvsOld) :
    SubstituteSupport.SubstFalseRel M N xs ss bvsNew := by
  refine ⟨hRel.globals, ?_, ?_⟩
  · intro s T hAllowed
    apply hRel.agree s T
    rcases hAllowed with hBound | hMapped
    · left
      have hMem : (s, T) ∈ bvsVars :=
        EoVarEnvPerm.mem_of_find_neg_false hNew hBound
      exact EoVarEnvPerm.find_neg_false_of_mem hOld hMem
    · exact Or.inr hMapped
  · intro s T hFree hMapped
    have hNotMem : (s, T) ∉ bvsVars :=
      EoVarEnvPerm.not_mem_of_find_neg_true hNew hFree
    have hFreeOld :
      __eo_is_neg
            (__eo_list_find Term.__eo_List_cons bvsOld
              (Term.Var (Term.String s) T)) =
          Term.Boolean true :=
      EoVarEnvPerm.find_neg_true_of_not_mem hOld hNotMem
    exact hRel.mapped s T hFreeOld hMapped

theorem substFalse_eval_eo_to_smt_exists_diff_rel
    (vs xs ss bvs fullBvs except : Term)
    {binderVars xsVars bvsVars exceptVars : List EoVarKey}
    {M N : SmtModel} {bodyM bodyN : SmtTerm}
    (hEnv : EoVarEnv vs binderVars)
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hFullBvsEnv : EoVarEnvPerm fullBvs (binderVars.reverse ++ bvsVars))
    (hExceptEnv : EoVarEnvPerm except exceptVars)
    (hVsSub : ∀ key, key ∈ binderVars -> key ∈ exceptVars)
    (hExceptWf :
      ∀ s T, (s, T) ∈ exceptVars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hNoFreeSs :
      __contains_atomic_term_list_free_rec ss except Term.__eo_List_nil =
        Term.Boolean false)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hEntryTrans :
      ∀ (s : native_String) (T : Term),
        __eo_is_neg (__eo_list_find Term.__eo_List_cons xs
          (Term.Var (Term.String s) T)) = Term.Boolean false ->
        eoHasSmtTranslation
          (__assoc_nil_nth Term.__eo_List_cons ss
            (__eo_list_find Term.__eo_List_cons xs
              (Term.Var (Term.String s) T))))
    (hMappedWf :
      ∀ (s : native_String) (T : Term),
        __eo_is_neg (__eo_list_find Term.__eo_List_cons xs
          (Term.Var (Term.String s) T)) = Term.Boolean false ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hM : model_wf M) (hN : model_wf N)
    (hRel : SubstituteSupport.SubstFalseRel M N xs ss bvs)
    (hBase :
      ∀ {M' N' : SmtModel},
        model_wf M' ->
        model_wf N' ->
        SubstituteSupport.SubstFalseRel M' N' xs ss fullBvs ->
        __smtx_model_eval M' bodyM =
          __smtx_model_eval N' bodyN) :
    __smtx_model_eval M (__eo_to_smt_exists vs bodyM) =
      __smtx_model_eval N (__eo_to_smt_exists vs bodyN) := by
  induction hEnv generalizing bvs bvsVars M N with
  | nil =>
      have hRelFull :
          SubstituteSupport.SubstFalseRel M N xs ss fullBvs :=
        substFalseRel_of_bvs_perm hBvsEnv (by simpa using hFullBvsEnv) hRel
      simpa [__eo_to_smt_exists] using hBase hM hN hRelFull
  | cons hTail ih =>
      rename_i s T tail tailVars
      have hMemExcept : (s, T) ∈ exceptVars :=
        hVsSub (s, T) (List.Mem.head _)
      have hHeadWf : __smtx_type_wf (__eo_to_smt_type T) = true :=
        hExceptWf s T hMemExcept
      change
        __smtx_model_eval M
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists tail bodyM)) =
          __smtx_model_eval N
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists tail bodyN))
      simpa [__smtx_model_eval] using
        native_eval_texists_eq_of_body_eval_eq_diff_typed
          (fun v hValTy hValCanon => by
            have hBvsConsEnv :
                EoVarEnvPerm
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) bvs)
                  ((s, T) :: bvsVars) :=
              EoVarEnvPerm.cons hBvsEnv
            have hRelPush :
                SubstituteSupport.SubstFalseRel
                  (native_model_push M s (__eo_to_smt_type T) v)
                  (native_model_push N s (__eo_to_smt_type T) v)
                  xs ss
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) bvs) :=
              SubstituteSupport.substFalseRel_push
                M N xs ss bvs except s T v
                hBvsEnv hExceptEnv hMemExcept hNoFreeSs hSsTrans
                (fun s' T' _hFree hMapped => hEntryTrans s' T' hMapped)
                (fun s' T' hFree hMapped hKey => by
                  have hNotMem :
                      (s', T') ∉ (s, T) :: bvsVars :=
                    EoVarEnvPerm.not_mem_of_find_neg_true hBvsConsEnv hFree
                  apply hNotMem
                  apply EoVarKey.mem_of_toSmt_mem_map_of_type_wf
                    (hMappedWf s' T' hMapped)
                  have hSmtMem :
                      (s', __eo_to_smt_type T') ∈
                        ((s, T) :: bvsVars).map EoVarKey.toSmt := by
                    have hPair :
                        (s', __eo_to_smt_type T') =
                          (s, __eo_to_smt_type T) := by
                      injection hKey with _ hName hTy
                      exact Prod.ext hName hTy
                    rw [hPair]
                    exact List.mem_map.2 ⟨(s, T), List.Mem.head _, rfl⟩
                  exact hSmtMem)
                hRel
            have hM' :
                model_wf
                  (native_model_push M s (__eo_to_smt_type T) v) :=
              model_total_typed_push hM s (__eo_to_smt_type T) v
                hHeadWf hValTy (by
                  simpa [value_canonical] using hValCanon)
            have hN' :
                model_wf
                  (native_model_push N s (__eo_to_smt_type T) v) :=
              model_total_typed_push hN s (__eo_to_smt_type T) v
                hHeadWf hValTy (by
                  simpa [value_canonical] using hValCanon)
            exact
              ih
                (bvs :=
                  Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) bvs)
                (bvsVars := (s, T) :: bvsVars)
                (M := native_model_push M s (__eo_to_smt_type T) v)
                (N := native_model_push N s (__eo_to_smt_type T) v)
                hBvsConsEnv
                (by
                  simpa [List.reverse_cons, List.append_assoc] using
                    hFullBvsEnv)
                (fun key hMem => hVsSub key (List.Mem.tail _ hMem))
                hM' hN' hRelPush)

variable {isRename : Bool}

/-- Reusable reduction for a **unary special-head application** in the
substitution-evaluation induction. Given that the head's substitution is the
bare operator (`hHeadSub`, from `substitute_simul_rec_uop_eq_self`), argument
translatability extraction (`hArgExtract`), the SMT constructor's evaluation
congruence (`hCong`), and the argument IH provider (`hRecArg`), the whole
application reduces to the argument IH. Each concrete unary head (`not`,
`to_real`, …) instantiates this with its constructor and arg-extraction lemma. -/
theorem substFalse_eval_unary_op
    (op : UserOp) (a xs ss bvs : Term) {M N : SmtModel}
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hFTrans : eoHasSmtTranslation (Term.Apply (Term.UOp op) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) a) xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename) (Term.UOp op) xs ss bvs =
        Term.UOp op)
    (hArgExtract :
      ∀ {t : Term},
        eoHasSmtTranslation (Term.Apply (Term.UOp op) t) → eoHasSmtTranslation t)
    (hCong :
      ∀ X Y : Term,
        __smtx_model_eval M (__eo_to_smt X) = __smtx_model_eval N (__eo_to_smt Y) →
          __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp op) X)) =
            __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp op) Y)))
    (hRecArg :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.UOp op) a) xs ss bvs)) =
      __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp op) a)) := by
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) a) xs ss bvs =
        __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.UOp op) a xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [hHeadSub] using hApplyEq
  have hMkNeStuck :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) ≠ Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hMk :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) =
        Term.Apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNeStuck
  have hATrans : eoHasSmtTranslation a := hArgExtract hFTrans
  have hSubstApplyTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) := by
    rw [← hMk, ← hSubstEq]; exact hSubstTrans
  have hSubstATrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    hArgExtract hSubstApplyTrans
  rw [hSubstEq, hMk]
  exact hCong _ _ (hRecArg hATrans hSubstATrans)

/-- Variant of `substFalse_eval_unary_op` for unary heads whose SMT translation
also mentions the SMT type of the argument. -/
theorem substFalse_eval_unary_op_type_dependent
    (op : UserOp) (a xs ss bvs : Term) {M N : SmtModel}
    (hM : model_wf M) (hN : model_wf N)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hFTrans : eoHasSmtTranslation (Term.Apply (Term.UOp op) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) a) xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename) (Term.UOp op) xs ss bvs =
        Term.UOp op)
    (hArgExtract :
      ∀ {t : Term},
        eoHasSmtTranslation (Term.Apply (Term.UOp op) t) → eoHasSmtTranslation t)
    (hCong :
      ∀ X Y : Term,
        __smtx_typeof (__eo_to_smt X) =
          __smtx_typeof (__eo_to_smt Y) →
        __smtx_model_eval M (__eo_to_smt X) =
          __smtx_model_eval N (__eo_to_smt Y) →
          __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp op) X)) =
            __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp op) Y)))
    (hRecArg :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.UOp op) a) xs ss bvs)) =
      __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp op) a)) := by
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) a) xs ss bvs =
        __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.UOp op) a xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [hHeadSub] using hApplyEq
  have hMkNeStuck :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) ≠ Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hMk :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) =
        Term.Apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNeStuck
  have hATrans : eoHasSmtTranslation a := hArgExtract hFTrans
  have hSubstApplyTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) := by
    rw [← hMk, ← hSubstEq]
    exact hSubstTrans
  have hSubstATrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    hArgExtract hSubstApplyTrans
  have hArgEval := hRecArg hATrans hSubstATrans
  have hArgTy :
      __smtx_typeof
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
        __smtx_typeof (__eo_to_smt a) :=
    smtx_typeof_eo_to_smt_eq_of_eval_eq hM hN
      (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) a
      hSubstATrans hATrans hArgEval
  rw [hSubstEq, hMk]
  exact hCong _ _ hArgTy hArgEval

theorem substFalse_eval_eo_to_smt_distinct_pairs_cross
    (root : Term) (sSub sOrig : SmtTerm)
    (tl xs ss bvs : Term) {M N : SmtModel}
    {xsVars bvsVars : List EoVarKey}
    (hLt : sizeOf tl < sizeOf root)
    (hTlSubterm : IsNonbinderSubterm tl root)
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hElemNN : __eo_to_smt_typed_list_elem_type tl ≠ SmtType.None)
    (hSubstElemNN :
      __eo_to_smt_typed_list_elem_type
          (__substitute_simul_rec (Term.Boolean isRename) tl xs ss bvs) ≠
        SmtType.None)
    (hS :
      __smtx_model_eval M sSub =
        __smtx_model_eval N sOrig)
    (hRec :
      ∀ {b : Term},
        IsNonbinderSubterm b root ->
        sizeOf b < sizeOf root ->
        eoHasSmtTranslation b ->
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs) ->
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt b)) :
    __smtx_model_eval M
        (__eo_to_smt_distinct_pairs sSub
          (__substitute_simul_rec (Term.Boolean isRename) tl xs ss bvs)) =
      __smtx_model_eval N (__eo_to_smt_distinct_pairs sOrig tl) := by
  cases tl with
  | Apply f tail =>
      cases f with
      | UOp op =>
          cases op with
          | _at__at_TypedList_nil =>
              let TSub :=
                __substitute_simul_rec (Term.Boolean isRename) tail xs ss bvs
              have hHeadSub :
                  __substitute_simul_rec (Term.Boolean isRename)
                      (Term.UOp UserOp._at__at_TypedList_nil) xs ss bvs =
                    Term.UOp UserOp._at__at_TypedList_nil :=
                substitute_simul_rec_uop_eq_self
                  UserOp._at__at_TypedList_nil xs ss bvs hXsEnv hBvsEnv hSsTrans
              have hSubstEq :
                  __substitute_simul_rec (Term.Boolean isRename)
                      (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) tail)
                      xs ss bvs =
                    __eo_mk_apply (Term.UOp UserOp._at__at_TypedList_nil) TSub := by
                have hApplyEq :=
                  SubstituteSupport.substitute_simul_rec_apply
                    (Term.Boolean isRename)
                    (Term.UOp UserOp._at__at_TypedList_nil) tail xs ss bvs
                    hisr hxs hss hbvs
                    (by intro q v vs hEq; cases hEq)
                simpa [TSub, hHeadSub] using hApplyEq
              have hMk :
                  __eo_mk_apply (Term.UOp UserOp._at__at_TypedList_nil) TSub =
                    Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) TSub :=
                instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
                  rw [← hSubstEq]
                  exact TypedListSubstitutionSupport.typed_list_elem_type_non_none_not_stuck
                    hSubstElemNN)
              rw [hSubstEq, hMk]
              change
                __smtx_model_eval M (SmtTerm.Boolean true) =
                  __smtx_model_eval N (SmtTerm.Boolean true)
              simp [__smtx_model_eval]
          | _ =>
              exact False.elim
                (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | Apply g head =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_TypedList_cons =>
                  let headSub :=
                    __substitute_simul_rec (Term.Boolean isRename) head xs ss bvs
                  let tailSub :=
                    __substitute_simul_rec (Term.Boolean isRename) tail xs ss bvs
                  rcases TypedListSubstitutionSupport.typed_list_cons_elem_type_parts head tail hElemNN with
                    ⟨_hHeadTail, hHeadNN, hTailNN, _hConsEq⟩
                  have hHeadTrans : eoHasSmtTranslation head := by
                    unfold eoHasSmtTranslation
                    simpa using hHeadNN
                  have hConsNonbinder :
                      ¬ IsBinderHead
                        (Term.Apply
                          (Term.UOp UserOp._at__at_TypedList_cons) head) :=
                    not_isBinderHead_apply_of_arg_translation _ _ hHeadTrans
                  have hHeadSubterm : IsNonbinderSubterm head root :=
                    isNonbinderSubterm_trans
                      (by
                        simp [IsNonbinderSubterm, hConsNonbinder])
                      hTlSubterm
                  have hTailSubterm : IsNonbinderSubterm tail root :=
                    isNonbinderSubterm_trans
                      (by
                        simp [IsNonbinderSubterm, hConsNonbinder])
                      hTlSubterm
                  have hInnerSub :
                      __substitute_simul_rec (Term.Boolean isRename)
                          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
                          xs ss bvs =
                        __eo_mk_apply
                          (Term.UOp UserOp._at__at_TypedList_cons) headSub := by
                    have hHeadSub :
                        __substitute_simul_rec (Term.Boolean isRename)
                            (Term.UOp UserOp._at__at_TypedList_cons) xs ss bvs =
                          Term.UOp UserOp._at__at_TypedList_cons :=
                      substitute_simul_rec_uop_eq_self
                        UserOp._at__at_TypedList_cons xs ss bvs
                        hXsEnv hBvsEnv hSsTrans
                    have hApplyEq :=
                      SubstituteSupport.substitute_simul_rec_apply
                        (Term.Boolean isRename)
                        (Term.UOp UserOp._at__at_TypedList_cons) head xs ss bvs
                        hisr hxs hss hbvs
                        (by intro q v vs hEq; cases hEq)
                    simpa [headSub, hHeadSub] using hApplyEq
                  have hOuterSub :
                      __substitute_simul_rec (Term.Boolean isRename)
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
                            tail) xs ss bvs =
                        __eo_mk_apply
                          (__substitute_simul_rec (Term.Boolean isRename)
                            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                              head) xs ss bvs)
                          tailSub := by
                    have hApplyEq :=
                      SubstituteSupport.substitute_simul_rec_apply
                        (Term.Boolean isRename)
                        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
                        tail xs ss bvs hisr hxs hss hbvs
                        (by
                          intro q v vs hEq
                          cases hEq
                          exact term_not_eo_list_cons_of_has_smt_translation
                            hHeadTrans v vs rfl)
                    simpa [tailSub] using hApplyEq
                  have hOuterNe :
                      __eo_mk_apply
                          (__substitute_simul_rec (Term.Boolean isRename)
                            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                              head) xs ss bvs)
                          tailSub ≠ Term.Stuck := by
                    rw [← hOuterSub]
                    exact TypedListSubstitutionSupport.typed_list_elem_type_non_none_not_stuck
                      hSubstElemNN
                  have hOuterNe' :
                      __eo_mk_apply
                          (__eo_mk_apply
                            (Term.UOp UserOp._at__at_TypedList_cons) headSub)
                          tailSub ≠ Term.Stuck := by
                    simpa [hInnerSub] using hOuterNe
                  have hInnerNe :
                      __eo_mk_apply
                          (Term.UOp UserOp._at__at_TypedList_cons) headSub ≠
                        Term.Stuck := by
                    rw [← hInnerSub]
                    exact instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNe
                  have hInnerMk :
                      __eo_mk_apply
                          (Term.UOp UserOp._at__at_TypedList_cons) headSub =
                        Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                          headSub :=
                    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNe
                  have hOuterMk :
                      __eo_mk_apply
                          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                            headSub)
                          tailSub =
                        Term.Apply
                          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                            headSub)
                          tailSub :=
                    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
                      rw [← hInnerMk]
                      exact hOuterNe')
                  have hResultEq :
                      __substitute_simul_rec (Term.Boolean isRename)
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
                            tail) xs ss bvs =
                        Term.Apply
                          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                            headSub)
                          tailSub := by
                    rw [hOuterSub, hInnerSub, hInnerMk, hOuterMk]
                  rcases
                    TypedListSubstitutionSupport.typed_list_cons_elem_type_parts headSub tailSub
                      (by simpa [headSub, tailSub, hResultEq] using hSubstElemNN) with
                    ⟨_hSubHeadTail, hSubHeadNN, hSubTailNN, _hSubConsEq⟩
                  have hHeadSubTrans : eoHasSmtTranslation headSub := by
                    unfold eoHasSmtTranslation
                    simpa [headSub] using hSubHeadNN
                  have hHeadEval :
                      __smtx_model_eval M (__eo_to_smt headSub) =
                        __smtx_model_eval N (__eo_to_smt head) :=
                    hRec hHeadSubterm (by simp at hLt ⊢; omega)
                      hHeadTrans hHeadSubTrans
                  have hTailPairsEval :
                      __smtx_model_eval M
                          (__eo_to_smt_distinct_pairs sSub tailSub) =
                        __smtx_model_eval N
                          (__eo_to_smt_distinct_pairs sOrig tail) :=
                    substFalse_eval_eo_to_smt_distinct_pairs_cross
                      root sSub sOrig tail xs ss bvs
                      (by simp at hLt ⊢; omega)
                      hTailSubterm
                      hXsEnv hBvsEnv hSsTrans hisr hxs hss hbvs
                      hTailNN
                      (by simpa [tailSub] using hSubTailNN)
                      hS hRec
                  rw [hResultEq]
                  change
                    __smtx_model_eval M
                        (SmtTerm.and
                          (SmtTerm.not (SmtTerm.eq sSub (__eo_to_smt headSub)))
                          (__eo_to_smt_distinct_pairs sSub tailSub)) =
                      __smtx_model_eval N
                        (SmtTerm.and
                          (SmtTerm.not (SmtTerm.eq sOrig (__eo_to_smt head)))
                          (__eo_to_smt_distinct_pairs sOrig tail))
                  simp only [__smtx_model_eval]
                  rw [hS, hHeadEval, hTailPairsEval]
              | _ =>
                  exact False.elim
                    (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
          | _ =>
              exact False.elim
                (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | _ =>
          exact False.elim
            (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
  | _ =>
      exact False.elim
        (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
termination_by tl

theorem substFalse_eval_eo_to_smt_distinct_cross
    (root : Term) (tl xs ss bvs : Term) {M N : SmtModel}
    {xsVars bvsVars : List EoVarKey}
    (hLt : sizeOf tl < sizeOf root)
    (hTlSubterm : IsNonbinderSubterm tl root)
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hElemNN : __eo_to_smt_typed_list_elem_type tl ≠ SmtType.None)
    (hSubstElemNN :
      __eo_to_smt_typed_list_elem_type
          (__substitute_simul_rec (Term.Boolean isRename) tl xs ss bvs) ≠
        SmtType.None)
    (hRec :
      ∀ {b : Term},
        IsNonbinderSubterm b root ->
        sizeOf b < sizeOf root ->
        eoHasSmtTranslation b ->
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs) ->
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt b)) :
    __smtx_model_eval M
        (__eo_to_smt_distinct
          (__substitute_simul_rec (Term.Boolean isRename) tl xs ss bvs)) =
      __smtx_model_eval N (__eo_to_smt_distinct tl) := by
  cases tl with
  | Apply f tail =>
      cases f with
      | UOp op =>
          cases op with
          | _at__at_TypedList_nil =>
              let TSub :=
                __substitute_simul_rec (Term.Boolean isRename) tail xs ss bvs
              have hHeadSub :
                  __substitute_simul_rec (Term.Boolean isRename)
                      (Term.UOp UserOp._at__at_TypedList_nil) xs ss bvs =
                    Term.UOp UserOp._at__at_TypedList_nil :=
                substitute_simul_rec_uop_eq_self
                  UserOp._at__at_TypedList_nil xs ss bvs hXsEnv hBvsEnv hSsTrans
              have hSubstEq :
                  __substitute_simul_rec (Term.Boolean isRename)
                      (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) tail)
                      xs ss bvs =
                    __eo_mk_apply (Term.UOp UserOp._at__at_TypedList_nil) TSub := by
                have hApplyEq :=
                  SubstituteSupport.substitute_simul_rec_apply
                    (Term.Boolean isRename)
                    (Term.UOp UserOp._at__at_TypedList_nil) tail xs ss bvs
                    hisr hxs hss hbvs
                    (by intro q v vs hEq; cases hEq)
                simpa [TSub, hHeadSub] using hApplyEq
              have hMk :
                  __eo_mk_apply (Term.UOp UserOp._at__at_TypedList_nil) TSub =
                    Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) TSub :=
                instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
                  rw [← hSubstEq]
                  exact TypedListSubstitutionSupport.typed_list_elem_type_non_none_not_stuck
                    hSubstElemNN)
              rw [hSubstEq, hMk]
              change
                __smtx_model_eval M (SmtTerm.Boolean true) =
                  __smtx_model_eval N (SmtTerm.Boolean true)
              simp [__smtx_model_eval]
          | _ =>
              exact False.elim
                (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | Apply g head =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_TypedList_cons =>
                  let headSub :=
                    __substitute_simul_rec (Term.Boolean isRename) head xs ss bvs
                  let tailSub :=
                    __substitute_simul_rec (Term.Boolean isRename) tail xs ss bvs
                  rcases TypedListSubstitutionSupport.typed_list_cons_elem_type_parts head tail hElemNN with
                    ⟨_hHeadTail, hHeadNN, hTailNN, _hConsEq⟩
                  have hHeadTrans : eoHasSmtTranslation head := by
                    unfold eoHasSmtTranslation
                    simpa using hHeadNN
                  have hConsNonbinder :
                      ¬ IsBinderHead
                        (Term.Apply
                          (Term.UOp UserOp._at__at_TypedList_cons) head) :=
                    not_isBinderHead_apply_of_arg_translation _ _ hHeadTrans
                  have hHeadSubterm : IsNonbinderSubterm head root :=
                    isNonbinderSubterm_trans
                      (by
                        simp [IsNonbinderSubterm, hConsNonbinder])
                      hTlSubterm
                  have hTailSubterm : IsNonbinderSubterm tail root :=
                    isNonbinderSubterm_trans
                      (by
                        simp [IsNonbinderSubterm, hConsNonbinder])
                      hTlSubterm
                  have hInnerSub :
                      __substitute_simul_rec (Term.Boolean isRename)
                          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
                          xs ss bvs =
                        __eo_mk_apply
                          (Term.UOp UserOp._at__at_TypedList_cons) headSub := by
                    have hHeadSub :
                        __substitute_simul_rec (Term.Boolean isRename)
                            (Term.UOp UserOp._at__at_TypedList_cons) xs ss bvs =
                          Term.UOp UserOp._at__at_TypedList_cons :=
                      substitute_simul_rec_uop_eq_self
                        UserOp._at__at_TypedList_cons xs ss bvs
                        hXsEnv hBvsEnv hSsTrans
                    have hApplyEq :=
                      SubstituteSupport.substitute_simul_rec_apply
                        (Term.Boolean isRename)
                        (Term.UOp UserOp._at__at_TypedList_cons) head xs ss bvs
                        hisr hxs hss hbvs
                        (by intro q v vs hEq; cases hEq)
                    simpa [headSub, hHeadSub] using hApplyEq
                  have hOuterSub :
                      __substitute_simul_rec (Term.Boolean isRename)
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
                            tail) xs ss bvs =
                        __eo_mk_apply
                          (__substitute_simul_rec (Term.Boolean isRename)
                            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                              head) xs ss bvs)
                          tailSub := by
                    have hApplyEq :=
                      SubstituteSupport.substitute_simul_rec_apply
                        (Term.Boolean isRename)
                        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
                        tail xs ss bvs hisr hxs hss hbvs
                        (by
                          intro q v vs hEq
                          cases hEq
                          exact term_not_eo_list_cons_of_has_smt_translation
                            hHeadTrans v vs rfl)
                    simpa [tailSub] using hApplyEq
                  have hOuterNe :
                      __eo_mk_apply
                          (__substitute_simul_rec (Term.Boolean isRename)
                            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                              head) xs ss bvs)
                          tailSub ≠ Term.Stuck := by
                    rw [← hOuterSub]
                    exact TypedListSubstitutionSupport.typed_list_elem_type_non_none_not_stuck
                      hSubstElemNN
                  have hOuterNe' :
                      __eo_mk_apply
                          (__eo_mk_apply
                            (Term.UOp UserOp._at__at_TypedList_cons) headSub)
                          tailSub ≠ Term.Stuck := by
                    simpa [hInnerSub] using hOuterNe
                  have hInnerNe :
                      __eo_mk_apply
                          (Term.UOp UserOp._at__at_TypedList_cons) headSub ≠
                        Term.Stuck := by
                    rw [← hInnerSub]
                    exact instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNe
                  have hInnerMk :
                      __eo_mk_apply
                          (Term.UOp UserOp._at__at_TypedList_cons) headSub =
                        Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                          headSub :=
                    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNe
                  have hOuterMk :
                      __eo_mk_apply
                          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                            headSub)
                          tailSub =
                        Term.Apply
                          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                            headSub)
                          tailSub :=
                    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
                      rw [← hInnerMk]
                      exact hOuterNe')
                  have hResultEq :
                      __substitute_simul_rec (Term.Boolean isRename)
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
                            tail) xs ss bvs =
                        Term.Apply
                          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                            headSub)
                          tailSub := by
                    rw [hOuterSub, hInnerSub, hInnerMk, hOuterMk]
                  rcases
                    TypedListSubstitutionSupport.typed_list_cons_elem_type_parts headSub tailSub
                      (by simpa [headSub, tailSub, hResultEq] using hSubstElemNN) with
                    ⟨_hSubHeadTail, hSubHeadNN, hSubTailNN, _hSubConsEq⟩
                  have hHeadSubTrans : eoHasSmtTranslation headSub := by
                    unfold eoHasSmtTranslation
                    simpa [headSub] using hSubHeadNN
                  have hHeadEval :
                      __smtx_model_eval M (__eo_to_smt headSub) =
                        __smtx_model_eval N (__eo_to_smt head) :=
                    hRec hHeadSubterm (by simp at hLt ⊢; omega)
                      hHeadTrans hHeadSubTrans
                  have hPairsEval :
                      __smtx_model_eval M
                          (__eo_to_smt_distinct_pairs (__eo_to_smt headSub)
                            tailSub) =
                        __smtx_model_eval N
                          (__eo_to_smt_distinct_pairs (__eo_to_smt head)
                            tail) :=
                    substFalse_eval_eo_to_smt_distinct_pairs_cross
                      root (__eo_to_smt headSub) (__eo_to_smt head) tail xs ss bvs
                      (by simp at hLt ⊢; omega)
                      hTailSubterm
                      hXsEnv hBvsEnv hSsTrans hisr hxs hss hbvs
                      hTailNN
                      (by simpa [tailSub] using hSubTailNN)
                      hHeadEval hRec
                  have hTailEval :
                      __smtx_model_eval M (__eo_to_smt_distinct tailSub) =
                        __smtx_model_eval N (__eo_to_smt_distinct tail) :=
                    substFalse_eval_eo_to_smt_distinct_cross
                      root tail xs ss bvs
                      (by simp at hLt ⊢; omega)
                      hTailSubterm
                      hXsEnv hBvsEnv hSsTrans hisr hxs hss hbvs
                      hTailNN
                      (by simpa [tailSub] using hSubTailNN)
                      hRec
                  rw [hResultEq]
                  change
                    __smtx_model_eval M
                        (SmtTerm.and
                          (__eo_to_smt_distinct_pairs (__eo_to_smt headSub)
                            tailSub)
                          (__eo_to_smt_distinct tailSub)) =
                      __smtx_model_eval N
                        (SmtTerm.and
                          (__eo_to_smt_distinct_pairs (__eo_to_smt head)
                            tail)
                          (__eo_to_smt_distinct tail))
                  simp only [__smtx_model_eval]
                  rw [hPairsEval, hTailEval]
              | _ =>
                  exact False.elim
                    (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
          | _ =>
              exact False.elim
                (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | _ =>
          exact False.elim
            (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
  | _ =>
      exact False.elim
        (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
termination_by tl

theorem substFalse_eval_distinct
    (a xs ss bvs : Term) {M N : SmtModel}
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hFTrans : eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.distinct) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp UserOp.distinct) a) xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename) (Term.UOp UserOp.distinct)
          xs ss bvs =
        Term.UOp UserOp.distinct)
    (hRecArg :
      ∀ {b : Term},
        IsNonbinderSubterm b (Term.Apply (Term.UOp UserOp.distinct) a) ->
        sizeOf b < sizeOf (Term.Apply (Term.UOp UserOp.distinct) a) ->
        eoHasSmtTranslation b ->
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs) ->
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt b)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.UOp UserOp.distinct) a) xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) a)) := by
  let aSub := __substitute_simul_rec (Term.Boolean isRename) a xs ss bvs
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp UserOp.distinct) a) xs ss bvs =
        __eo_mk_apply (Term.UOp UserOp.distinct) aSub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.UOp UserOp.distinct) a xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [aSub, hHeadSub] using hApplyEq
  have hMkNe :
      __eo_mk_apply (Term.UOp UserOp.distinct) aSub ≠ Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hMk :
      __eo_mk_apply (Term.UOp UserOp.distinct) aSub =
        Term.Apply (Term.UOp UserOp.distinct) aSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe
  have hResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp UserOp.distinct) a) xs ss bvs =
        Term.Apply (Term.UOp UserOp.distinct) aSub := by
    rw [hSubstEq, hMk]
  have hElemNN :
      __eo_to_smt_typed_list_elem_type a ≠ SmtType.None :=
    typed_list_elem_type_non_none_of_distinct_has_smt_translation hFTrans
  have hSubstDistinctTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.distinct) aSub) := by
    rw [← hResultEq]
    exact hSubstTrans
  have hSubstElemNN :
      __eo_to_smt_typed_list_elem_type aSub ≠ SmtType.None :=
    typed_list_elem_type_non_none_of_distinct_has_smt_translation hSubstDistinctTrans
  rw [hResultEq,
    TypedListSubstitutionSupport.eo_to_smt_distinct_eq_of_elem_type_non_none aSub hSubstElemNN,
    TypedListSubstitutionSupport.eo_to_smt_distinct_eq_of_elem_type_non_none a hElemNN]
  exact
    substFalse_eval_eo_to_smt_distinct_cross
      (Term.Apply (Term.UOp UserOp.distinct) a) a xs ss bvs
      (by simp)
      (by simp [IsNonbinderSubterm])
      hXsEnv hBvsEnv hSsTrans hisr hxs hss hbvs
      hElemNN (by simpa [aSub] using hSubstElemNN)
      hRecArg

theorem substFalse_eval_eo_to_smt_set_insert_cross
    (root : Term) (baseSub baseOrig : SmtTerm)
    (tl xs ss bvs : Term) {M N : SmtModel}
    {xsVars bvsVars : List EoVarKey}
    (hLt : sizeOf tl < sizeOf root)
    (hTlSubterm : IsNonbinderSubterm tl root)
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hElemNN : __eo_to_smt_typed_list_elem_type tl ≠ SmtType.None)
    (hSubstElemNN :
      __eo_to_smt_typed_list_elem_type
          (__substitute_simul_rec (Term.Boolean isRename) tl xs ss bvs) ≠
        SmtType.None)
    (hBaseSubTy :
      __smtx_typeof baseSub =
        SmtType.Set
          (__eo_to_smt_typed_list_elem_type
            (__substitute_simul_rec (Term.Boolean isRename) tl xs ss bvs)))
    (hBaseOrigTy :
      __smtx_typeof baseOrig =
        SmtType.Set (__eo_to_smt_typed_list_elem_type tl))
    (hBaseEval :
      __smtx_model_eval M baseSub =
        __smtx_model_eval N baseOrig)
    (hRec :
      ∀ {b : Term},
        IsNonbinderSubterm b root ->
        sizeOf b < sizeOf root ->
        eoHasSmtTranslation b ->
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs) ->
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt b)) :
    __smtx_model_eval M
        (__eo_to_smt_set_insert
          (__substitute_simul_rec (Term.Boolean isRename) tl xs ss bvs)
          baseSub) =
      __smtx_model_eval N (__eo_to_smt_set_insert tl baseOrig) := by
  cases tl with
  | Apply f tail =>
      cases f with
      | UOp op =>
          cases op with
          | _at__at_TypedList_nil =>
              let TSub :=
                __substitute_simul_rec (Term.Boolean isRename) tail xs ss bvs
              have hHeadSub :
                  __substitute_simul_rec (Term.Boolean isRename)
                      (Term.UOp UserOp._at__at_TypedList_nil) xs ss bvs =
                    Term.UOp UserOp._at__at_TypedList_nil :=
                substitute_simul_rec_uop_eq_self
                  UserOp._at__at_TypedList_nil xs ss bvs hXsEnv hBvsEnv hSsTrans
              have hSubstEq :
                  __substitute_simul_rec (Term.Boolean isRename)
                      (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) tail)
                      xs ss bvs =
                    __eo_mk_apply (Term.UOp UserOp._at__at_TypedList_nil) TSub := by
                have hApplyEq :=
                  SubstituteSupport.substitute_simul_rec_apply
                    (Term.Boolean isRename)
                    (Term.UOp UserOp._at__at_TypedList_nil) tail xs ss bvs
                    hisr hxs hss hbvs
                    (by intro q v vs hEq; cases hEq)
                simpa [TSub, hHeadSub] using hApplyEq
              have hMk :
                  __eo_mk_apply (Term.UOp UserOp._at__at_TypedList_nil) TSub =
                    Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) TSub :=
                instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
                  rw [← hSubstEq]
                  exact TypedListSubstitutionSupport.typed_list_elem_type_non_none_not_stuck
                    hSubstElemNN)
              have hBaseSubTy' :
                  __smtx_typeof baseSub =
                    SmtType.Set
                      (__eo_to_smt_typed_list_elem_type
                        (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
                          TSub)) := by
                simpa [TSub, hSubstEq, hMk] using hBaseSubTy
              have hSubstElemNN' :
                  __eo_to_smt_typed_list_elem_type
                      (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
                        TSub) ≠
                    SmtType.None := by
                simpa [TSub, hSubstEq, hMk] using hSubstElemNN
              have hSubElemEq :=
                TypedListSubstitutionSupport.typed_list_nil_elem_type_eq_of_non_none
                  TSub hSubstElemNN'
              have hOrigElemEq :=
                TypedListSubstitutionSupport.typed_list_nil_elem_type_eq_of_non_none
                  tail hElemNN
              have hSubGuard :
                  native_Teq (__smtx_typeof baseSub)
                      (SmtType.Set (__eo_to_smt_type TSub)) =
                    true := by
                rw [hBaseSubTy', hSubElemEq]
                simp [native_Teq]
              have hOrigGuard :
                  native_Teq (__smtx_typeof baseOrig)
                      (SmtType.Set (__eo_to_smt_type tail)) =
                    true := by
                rw [hBaseOrigTy, hOrigElemEq]
                simp [native_Teq]
              rw [hSubstEq, hMk]
              change
                __smtx_model_eval M
                    (native_ite
                      (native_Teq (__smtx_typeof baseSub)
                        (SmtType.Set (__eo_to_smt_type TSub)))
                      baseSub SmtTerm.None) =
                  __smtx_model_eval N
                    (native_ite
                      (native_Teq (__smtx_typeof baseOrig)
                        (SmtType.Set (__eo_to_smt_type tail)))
                      baseOrig SmtTerm.None)
              rw [hSubGuard, hOrigGuard]
              simpa [native_ite] using hBaseEval
          | _ =>
              exact False.elim
                (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | Apply g head =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_TypedList_cons =>
                  let headSub :=
                    __substitute_simul_rec (Term.Boolean isRename) head xs ss bvs
                  let tailSub :=
                    __substitute_simul_rec (Term.Boolean isRename) tail xs ss bvs
                  rcases TypedListSubstitutionSupport.typed_list_cons_elem_type_parts head tail hElemNN with
                    ⟨hHeadTail, hHeadNN, hTailNN, hConsEq⟩
                  have hHeadTrans : eoHasSmtTranslation head := by
                    unfold eoHasSmtTranslation
                    simpa using hHeadNN
                  have hConsNonbinder :
                      ¬ IsBinderHead
                        (Term.Apply
                          (Term.UOp UserOp._at__at_TypedList_cons) head) :=
                    not_isBinderHead_apply_of_arg_translation _ _ hHeadTrans
                  have hHeadSubterm : IsNonbinderSubterm head root :=
                    isNonbinderSubterm_trans
                      (by
                        simp [IsNonbinderSubterm, hConsNonbinder])
                      hTlSubterm
                  have hTailSubterm : IsNonbinderSubterm tail root :=
                    isNonbinderSubterm_trans
                      (by
                        simp [IsNonbinderSubterm, hConsNonbinder])
                      hTlSubterm
                  have hInnerSub :
                      __substitute_simul_rec (Term.Boolean isRename)
                          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
                          xs ss bvs =
                        __eo_mk_apply
                          (Term.UOp UserOp._at__at_TypedList_cons) headSub := by
                    have hHeadSub :
                        __substitute_simul_rec (Term.Boolean isRename)
                            (Term.UOp UserOp._at__at_TypedList_cons) xs ss bvs =
                          Term.UOp UserOp._at__at_TypedList_cons :=
                      substitute_simul_rec_uop_eq_self
                        UserOp._at__at_TypedList_cons xs ss bvs
                        hXsEnv hBvsEnv hSsTrans
                    have hApplyEq :=
                      SubstituteSupport.substitute_simul_rec_apply
                        (Term.Boolean isRename)
                        (Term.UOp UserOp._at__at_TypedList_cons) head xs ss bvs
                        hisr hxs hss hbvs
                        (by intro q v vs hEq; cases hEq)
                    simpa [headSub, hHeadSub] using hApplyEq
                  have hOuterSub :
                      __substitute_simul_rec (Term.Boolean isRename)
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
                            tail) xs ss bvs =
                        __eo_mk_apply
                          (__substitute_simul_rec (Term.Boolean isRename)
                            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                              head) xs ss bvs)
                          tailSub := by
                    have hApplyEq :=
                      SubstituteSupport.substitute_simul_rec_apply
                        (Term.Boolean isRename)
                        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
                        tail xs ss bvs hisr hxs hss hbvs
                        (by
                          intro q v vs hEq
                          cases hEq
                          exact term_not_eo_list_cons_of_has_smt_translation
                            hHeadTrans v vs rfl)
                    simpa [tailSub] using hApplyEq
                  have hOuterNe :
                      __eo_mk_apply
                          (__substitute_simul_rec (Term.Boolean isRename)
                            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                              head) xs ss bvs)
                          tailSub ≠ Term.Stuck := by
                    rw [← hOuterSub]
                    exact TypedListSubstitutionSupport.typed_list_elem_type_non_none_not_stuck
                      hSubstElemNN
                  have hOuterNe' :
                      __eo_mk_apply
                          (__eo_mk_apply
                            (Term.UOp UserOp._at__at_TypedList_cons) headSub)
                          tailSub ≠ Term.Stuck := by
                    simpa [hInnerSub] using hOuterNe
                  have hInnerNe :
                      __eo_mk_apply
                          (Term.UOp UserOp._at__at_TypedList_cons) headSub ≠
                        Term.Stuck := by
                    rw [← hInnerSub]
                    exact instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNe
                  have hInnerMk :
                      __eo_mk_apply
                          (Term.UOp UserOp._at__at_TypedList_cons) headSub =
                        Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                          headSub :=
                    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNe
                  have hOuterMk :
                      __eo_mk_apply
                          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                            headSub)
                          tailSub =
                        Term.Apply
                          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                            headSub)
                          tailSub :=
                    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
                      rw [← hInnerMk]
                      exact hOuterNe')
                  have hResultEq :
                      __substitute_simul_rec (Term.Boolean isRename)
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
                            tail) xs ss bvs =
                        Term.Apply
                          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                            headSub)
                          tailSub := by
                    rw [hOuterSub, hInnerSub, hInnerMk, hOuterMk]
                  rcases
                    TypedListSubstitutionSupport.typed_list_cons_elem_type_parts headSub tailSub
                      (by simpa [headSub, tailSub, hResultEq] using hSubstElemNN) with
                    ⟨hSubHeadTail, hSubHeadNN, hSubTailNN, hSubConsEq⟩
                  have hHeadSubTrans : eoHasSmtTranslation headSub := by
                    unfold eoHasSmtTranslation
                    simpa [headSub] using hSubHeadNN
                  have hHeadEval :
                      __smtx_model_eval M (__eo_to_smt headSub) =
                        __smtx_model_eval N (__eo_to_smt head) :=
                    hRec hHeadSubterm (by simp at hLt ⊢; omega)
                      hHeadTrans hHeadSubTrans
                  have hBaseSubTy' :
                      __smtx_typeof baseSub =
                        SmtType.Set
                          (__eo_to_smt_typed_list_elem_type
                            (Term.Apply
                              (Term.Apply
                                (Term.UOp UserOp._at__at_TypedList_cons)
                                headSub)
                              tailSub)) := by
                    simpa [headSub, tailSub, hResultEq] using hBaseSubTy
                  have hBaseSubTailTy :
                      __smtx_typeof baseSub =
                        SmtType.Set (__eo_to_smt_typed_list_elem_type tailSub) := by
                    rw [hBaseSubTy', hSubConsEq, hSubHeadTail]
                  have hBaseOrigTailTy :
                      __smtx_typeof baseOrig =
                        SmtType.Set (__eo_to_smt_typed_list_elem_type tail) := by
                    rw [hBaseOrigTy, hConsEq, hHeadTail]
                  have hTailEval :
                      __smtx_model_eval M
                          (__eo_to_smt_set_insert tailSub baseSub) =
                        __smtx_model_eval N
                          (__eo_to_smt_set_insert tail baseOrig) :=
                    substFalse_eval_eo_to_smt_set_insert_cross
                      root baseSub baseOrig tail xs ss bvs
                      (by simp at hLt ⊢; omega)
                      hTailSubterm
                      hXsEnv hBvsEnv hSsTrans hisr hxs hss hbvs
                      hTailNN
                      (by simpa [tailSub] using hSubTailNN)
                      hBaseSubTailTy hBaseOrigTailTy hBaseEval hRec
                  rw [hResultEq]
                  change
                    __smtx_model_eval M
                        (SmtTerm.set_union
                          (SmtTerm.set_singleton (__eo_to_smt headSub))
                          (__eo_to_smt_set_insert tailSub baseSub)) =
                      __smtx_model_eval N
                        (SmtTerm.set_union
                          (SmtTerm.set_singleton (__eo_to_smt head))
                          (__eo_to_smt_set_insert tail baseOrig))
                  simp only [__smtx_model_eval]
                  rw [hHeadEval, hTailEval]
              | _ =>
                  exact False.elim
                    (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
          | _ =>
              exact False.elim
                (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | _ =>
          exact False.elim
            (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
  | _ =>
      exact False.elim
        (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
termination_by tl

theorem substFalse_eval_set_insert
    (tl base xs ss bvs : Term) {M N : SmtModel}
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp.set_insert) tl ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) tl) base))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) tl) base)
          xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp UserOp.set_insert) xs ss bvs =
        Term.UOp UserOp.set_insert)
    (hRecArg :
      ∀ {b : Term},
        IsNonbinderSubterm b
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) tl) base) ->
        sizeOf b <
          sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) tl) base) ->
        eoHasSmtTranslation b ->
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs) ->
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt b)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) tl) base)
            xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) tl) base)) := by
  let tlSub := __substitute_simul_rec (Term.Boolean isRename) tl xs ss bvs
  let baseSub := __substitute_simul_rec (Term.Boolean isRename) base xs ss bvs
  have hSubstHead :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp UserOp.set_insert) tl) xs ss bvs =
        __eo_mk_apply (Term.UOp UserOp.set_insert) tlSub := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.UOp UserOp.set_insert) tl xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [tlSub, hHeadSub] using hEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) tl) base)
          xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.set_insert) tlSub)
          baseSub := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Apply (Term.UOp UserOp.set_insert) tl) base xs ss bvs
        hisr hxs hss hbvs hNotBinderOuter
    rw [hEq, hSubstHead]
  have hOuterNeStuck :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.set_insert) tlSub)
          baseSub ≠ Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hInnerNeStuck :
      __eo_mk_apply (Term.UOp UserOp.set_insert) tlSub ≠ Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  have hInnerMk :
      __eo_mk_apply (Term.UOp UserOp.set_insert) tlSub =
        Term.Apply (Term.UOp UserOp.set_insert) tlSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNeStuck
  have hOuterMk :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.set_insert) tlSub) baseSub =
        Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) tlSub) baseSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      rw [← hInnerMk]
      exact hOuterNeStuck)
  have hResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) tl) base)
          xs ss bvs =
        Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) tlSub) baseSub := by
    rw [hSubstEq, hInnerMk, hOuterMk]
  have hOrigNN :
      __smtx_typeof (__eo_to_smt_set_insert tl (__eo_to_smt base)) ≠
        SmtType.None := by
    unfold eoHasSmtTranslation at hFTrans
    change
      __smtx_typeof (__eo_to_smt_set_insert tl (__eo_to_smt base)) ≠
        SmtType.None at hFTrans
    exact hFTrans
  rcases eo_to_smt_set_insert_shape_of_non_none tl (__eo_to_smt base)
      hOrigNN with
    ⟨A, _hOrigSetTy, hBaseOrigTyA, hElemEqA, hANN⟩
  have hElemNN : __eo_to_smt_typed_list_elem_type tl ≠ SmtType.None := by
    rw [hElemEqA]
    exact hANN
  have hBaseOrigTy :
      __smtx_typeof (__eo_to_smt base) =
        SmtType.Set (__eo_to_smt_typed_list_elem_type tl) := by
    rw [hElemEqA]
    exact hBaseOrigTyA
  have hBaseTrans : eoHasSmtTranslation base := by
    unfold eoHasSmtTranslation
    rw [hBaseOrigTyA]
    simp
  have hSubstFullTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) tlSub) baseSub) := by
    rw [← hResultEq]
    exact hSubstTrans
  have hSubstNN :
      __smtx_typeof (__eo_to_smt_set_insert tlSub (__eo_to_smt baseSub)) ≠
        SmtType.None := by
    unfold eoHasSmtTranslation at hSubstFullTrans
    change
      __smtx_typeof (__eo_to_smt_set_insert tlSub (__eo_to_smt baseSub)) ≠
        SmtType.None at hSubstFullTrans
    exact hSubstFullTrans
  rcases eo_to_smt_set_insert_shape_of_non_none tlSub (__eo_to_smt baseSub)
      hSubstNN with
    ⟨B, _hSubstSetTy, hBaseSubTyB, hSubstElemEqB, hBNN⟩
  have hSubstElemNN : __eo_to_smt_typed_list_elem_type tlSub ≠ SmtType.None := by
    rw [hSubstElemEqB]
    exact hBNN
  have hBaseSubTy :
      __smtx_typeof (__eo_to_smt baseSub) =
        SmtType.Set (__eo_to_smt_typed_list_elem_type tlSub) := by
    rw [hSubstElemEqB]
    exact hBaseSubTyB
  have hBaseSubTrans : eoHasSmtTranslation baseSub := by
    unfold eoHasSmtTranslation
    rw [hBaseSubTyB]
    simp
  have hOuterNonbinder :
      ¬ IsBinderHead (Term.Apply (Term.UOp UserOp.set_insert) tl) := by
    rintro ⟨q, v, vs, hEq⟩
    exact hNotBinderOuter q v vs hEq
  have hBaseSubterm :
      IsNonbinderSubterm base
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) tl) base) := by
    simp [IsNonbinderSubterm, hOuterNonbinder]
  have hTlSubterm :
      IsNonbinderSubterm tl
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) tl) base) := by
    simp [IsNonbinderSubterm, hOuterNonbinder]
  have hBaseEval :
      __smtx_model_eval M (__eo_to_smt baseSub) =
        __smtx_model_eval N (__eo_to_smt base) :=
    hRecArg hBaseSubterm (by simp; omega) hBaseTrans
      (by simpa [baseSub] using hBaseSubTrans)
  rw [hResultEq]
  change
    __smtx_model_eval M
        (__eo_to_smt_set_insert tlSub (__eo_to_smt baseSub)) =
      __smtx_model_eval N
        (__eo_to_smt_set_insert tl (__eo_to_smt base))
  exact
    substFalse_eval_eo_to_smt_set_insert_cross
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) tl) base)
      (__eo_to_smt baseSub) (__eo_to_smt base) tl xs ss bvs
      (by simp; omega)
      hTlSubterm
      hXsEnv hBvsEnv hSsTrans hisr hxs hss hbvs
      hElemNN (by simpa [tlSub] using hSubstElemNN)
      (by simpa [tlSub] using hBaseSubTy)
      hBaseOrigTy hBaseEval
      hRecArg

/-- Reusable reduction for a unary indexed special-head application
`Apply (UOp1 op idx) a`. The indexed head is syntactically fixed by
substitution; concrete operator cases provide the index-evaluation fact and the
SMT constructor congruence. -/
theorem substFalse_eval_unary_uop1
    (op : UserOp1) (idx a xs ss bvs : Term) {M N : SmtModel}
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hFTrans : eoHasSmtTranslation (Term.Apply (Term.UOp1 op idx) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 op idx) a) xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename) (Term.UOp1 op idx) xs ss bvs =
        Term.UOp1 op idx)
    (hArgExtract :
      ∀ {t : Term},
        eoHasSmtTranslation (Term.Apply (Term.UOp1 op idx) t) →
          eoHasSmtTranslation t)
    (hIdxEval :
      __smtx_model_eval M (__eo_to_smt idx) =
        __smtx_model_eval N (__eo_to_smt idx))
    (hCong :
      ∀ X Y : Term,
        __smtx_model_eval M (__eo_to_smt idx) =
          __smtx_model_eval N (__eo_to_smt idx) →
        __smtx_model_eval M (__eo_to_smt X) =
          __smtx_model_eval N (__eo_to_smt Y) →
          __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp1 op idx) X)) =
            __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp1 op idx) Y)))
    (hRecArg :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.UOp1 op idx) a) xs ss bvs)) =
      __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp1 op idx) a)) := by
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 op idx) a) xs ss bvs =
        __eo_mk_apply (Term.UOp1 op idx)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.UOp1 op idx) a xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [hHeadSub] using hApplyEq
  have hMkNeStuck :
      __eo_mk_apply (Term.UOp1 op idx)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) ≠ Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hMk :
      __eo_mk_apply (Term.UOp1 op idx)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) =
        Term.Apply (Term.UOp1 op idx)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNeStuck
  have hATrans : eoHasSmtTranslation a := hArgExtract hFTrans
  have hSubstApplyTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 op idx)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) := by
    rw [← hMk, ← hSubstEq]
    exact hSubstTrans
  have hSubstATrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    hArgExtract hSubstApplyTrans
  rw [hSubstEq, hMk]
  exact hCong _ _ hIdxEval (hRecArg hATrans hSubstATrans)

theorem substFalse_eval_unary_uop1_nontuple_select
    (op : UserOp1) (idx a xs ss bvs : Term) {M N : SmtModel}
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hTupleSelect : op ≠ UserOp1.tuple_select)
    (hFTrans : eoHasSmtTranslation (Term.Apply (Term.UOp1 op idx) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 op idx) a) xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename) (Term.UOp1 op idx) xs ss bvs =
        Term.UOp1 op idx)
    (hRecArg :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.UOp1 op idx) a) xs ss bvs)) =
      __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp1 op idx) a)) := by
  cases op
  case «repeat» =>
    exact substFalse_eval_unary_uop1 UserOp1.repeat idx a xs ss bvs
      hisr hxs hss hbvs hFTrans hSubstTrans hHeadSub
      (fun {t} h => (repeat_index_nat_valid_and_arg_has_smt_translation h).2)
      (smt_model_eval_eq_of_eo_to_smt_nat_is_valid
        (repeat_index_nat_valid_and_arg_has_smt_translation hFTrans).1)
      (fun X Y hIdx hArg => by
        show __smtx_model_eval M (SmtTerm.repeat (__eo_to_smt idx) (__eo_to_smt X)) =
          __smtx_model_eval N (SmtTerm.repeat (__eo_to_smt idx) (__eo_to_smt Y))
        simp only [__smtx_model_eval]
        rw [hIdx, hArg])
      hRecArg
  case zero_extend =>
    exact substFalse_eval_unary_uop1 UserOp1.zero_extend idx a xs ss bvs
      hisr hxs hss hbvs hFTrans hSubstTrans hHeadSub
      (fun {t} h => (zero_extend_index_nat_valid_and_arg_has_smt_translation h).2)
      (smt_model_eval_eq_of_eo_to_smt_nat_is_valid
        (zero_extend_index_nat_valid_and_arg_has_smt_translation hFTrans).1)
      (fun X Y hIdx hArg => by
        show __smtx_model_eval M (SmtTerm.zero_extend (__eo_to_smt idx) (__eo_to_smt X)) =
          __smtx_model_eval N (SmtTerm.zero_extend (__eo_to_smt idx) (__eo_to_smt Y))
        simp only [__smtx_model_eval]
        rw [hIdx, hArg])
      hRecArg
  case sign_extend =>
    exact substFalse_eval_unary_uop1 UserOp1.sign_extend idx a xs ss bvs
      hisr hxs hss hbvs hFTrans hSubstTrans hHeadSub
      (fun {t} h => (sign_extend_index_nat_valid_and_arg_has_smt_translation h).2)
      (smt_model_eval_eq_of_eo_to_smt_nat_is_valid
        (sign_extend_index_nat_valid_and_arg_has_smt_translation hFTrans).1)
      (fun X Y hIdx hArg => by
        show __smtx_model_eval M (SmtTerm.sign_extend (__eo_to_smt idx) (__eo_to_smt X)) =
          __smtx_model_eval N (SmtTerm.sign_extend (__eo_to_smt idx) (__eo_to_smt Y))
        simp only [__smtx_model_eval]
        rw [hIdx, hArg])
      hRecArg
  case rotate_left =>
    exact substFalse_eval_unary_uop1 UserOp1.rotate_left idx a xs ss bvs
      hisr hxs hss hbvs hFTrans hSubstTrans hHeadSub
      (fun {t} h => (rotate_left_index_nat_valid_and_arg_has_smt_translation h).2)
      (smt_model_eval_eq_of_eo_to_smt_nat_is_valid
        (rotate_left_index_nat_valid_and_arg_has_smt_translation hFTrans).1)
      (fun X Y hIdx hArg => by
        show __smtx_model_eval M (SmtTerm.rotate_left (__eo_to_smt idx) (__eo_to_smt X)) =
          __smtx_model_eval N (SmtTerm.rotate_left (__eo_to_smt idx) (__eo_to_smt Y))
        simp only [__smtx_model_eval]
        rw [hIdx, hArg])
      hRecArg
  case rotate_right =>
    exact substFalse_eval_unary_uop1 UserOp1.rotate_right idx a xs ss bvs
      hisr hxs hss hbvs hFTrans hSubstTrans hHeadSub
      (fun {t} h => (rotate_right_index_nat_valid_and_arg_has_smt_translation h).2)
      (smt_model_eval_eq_of_eo_to_smt_nat_is_valid
        (rotate_right_index_nat_valid_and_arg_has_smt_translation hFTrans).1)
      (fun X Y hIdx hArg => by
        show __smtx_model_eval M (SmtTerm.rotate_right (__eo_to_smt idx) (__eo_to_smt X)) =
          __smtx_model_eval N (SmtTerm.rotate_right (__eo_to_smt idx) (__eo_to_smt Y))
        simp only [__smtx_model_eval]
        rw [hIdx, hArg])
      hRecArg
  case _at_bit =>
    exact substFalse_eval_unary_uop1 UserOp1._at_bit idx a xs ss bvs
      hisr hxs hss hbvs hFTrans hSubstTrans hHeadSub
      (fun {t} h => (at_bit_index_nat_valid_and_arg_has_smt_translation h).2)
      (smt_model_eval_eq_of_eo_to_smt_nat_is_valid
        (at_bit_index_nat_valid_and_arg_has_smt_translation hFTrans).1)
      (fun X Y hIdx hArg => by
        show __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx) (__eo_to_smt X))
              (SmtTerm.Binary 1 1)) =
          __smtx_model_eval N
            (SmtTerm.eq
              (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx) (__eo_to_smt Y))
              (SmtTerm.Binary 1 1))
        simp only [__smtx_model_eval]
        rw [hIdx, hArg])
      hRecArg
  case seq_empty =>
    exact false_of_apply_seq_empty hFTrans
  case re_exp =>
    exact substFalse_eval_unary_uop1 UserOp1.re_exp idx a xs ss bvs
      hisr hxs hss hbvs hFTrans hSubstTrans hHeadSub
      (fun {t} h => (re_exp_index_nat_valid_and_arg_has_smt_translation h).2)
      (smt_model_eval_eq_of_eo_to_smt_nat_is_valid
        (re_exp_index_nat_valid_and_arg_has_smt_translation hFTrans).1)
      (fun X Y hIdx hArg => by
        show __smtx_model_eval M (SmtTerm.re_exp (__eo_to_smt idx) (__eo_to_smt X)) =
          __smtx_model_eval N (SmtTerm.re_exp (__eo_to_smt idx) (__eo_to_smt Y))
        simp only [__smtx_model_eval]
        rw [hIdx, hArg])
      hRecArg
  case is =>
    rcases (is_index_cons_and_arg_has_smt_translation hFTrans).1 with
      ⟨s, d, i, hCons⟩
    exact substFalse_eval_unary_uop1 UserOp1.is idx a xs ss bvs
      hisr hxs hss hbvs hFTrans hSubstTrans hHeadSub
      (fun {t} h => (is_index_cons_and_arg_has_smt_translation h).2)
      (smt_model_eval_eq_of_eo_to_smt_eq_dt_cons hCons)
      (fun X Y _ hArg => by
        show __smtx_model_eval M
            (SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt idx)) (__eo_to_smt X)) =
          __smtx_model_eval N
            (SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt idx)) (__eo_to_smt Y))
        rw [hCons]
        simp only [__eo_to_smt_tester, __smtx_model_eval]
        rw [hArg])
      hRecArg
  case update =>
    exact false_of_apply_uop1_translate_apply_none hFTrans rfl
  case tuple_select =>
    exact False.elim (hTupleSelect rfl)
  case tuple_update =>
    exact false_of_apply_uop1_translate_apply_none hFTrans rfl
  case set_empty =>
    exact false_of_apply_set_empty hFTrans
  case int_to_bv =>
    exact substFalse_eval_unary_uop1 UserOp1.int_to_bv idx a xs ss bvs
      hisr hxs hss hbvs hFTrans hSubstTrans hHeadSub
      (fun {t} h => (int_to_bv_index_nat_valid_and_arg_has_smt_translation h).2)
      (smt_model_eval_eq_of_eo_to_smt_nat_is_valid
        (int_to_bv_index_nat_valid_and_arg_has_smt_translation hFTrans).1)
      (fun X Y hIdx hArg => by
        show __smtx_model_eval M (SmtTerm.int_to_bv (__eo_to_smt idx) (__eo_to_smt X)) =
          __smtx_model_eval N (SmtTerm.int_to_bv (__eo_to_smt idx) (__eo_to_smt Y))
        simp only [__smtx_model_eval]
        rw [hIdx, hArg])
      hRecArg

theorem quant_skolemize_apply_generic_eval
    (q idx x : Term) :
    generic_apply_eval (__eo_to_smt (Term._at_quantifiers_skolemize q idx))
      (__eo_to_smt x) := by
  unfold generic_apply_eval
  intro M
  cases hHead : __eo_to_smt (Term._at_quantifiers_skolemize q idx)
  <;> simp [__smtx_model_eval]
  · exact
      (eo_to_smt_quant_skolemize_top_ne_dt_sel_closed q idx _ _ _ _
        hHead).elim
  · exact
      (eo_to_smt_quant_skolemize_top_ne_dt_tester_closed q idx _ _ _
        hHead).elim

theorem at_const_apply_generic_eval
    (i j x : Term) :
    generic_apply_eval (__eo_to_smt (Term.UOp2 UserOp2._at_const i j))
      (__eo_to_smt x) := by
  unfold generic_apply_eval
  intro M
  cases hHead : __eo_to_smt (Term.UOp2 UserOp2._at_const i j)
  <;> simp [__smtx_model_eval]
  · exact
      (TranslationProofs.eo_to_smt_at_const_ne_dt_sel i j _ _ _ _ hHead).elim
  · exact
      (TranslationProofs.eo_to_smt_at_const_ne_dt_tester i j _ _ _ hHead).elim

theorem witness_string_length_apply_generic_eval
    (T len id x : Term) :
    generic_apply_eval
      (__eo_to_smt (Term.UOp3 UserOp3._at_witness_string_length T len id))
      (__eo_to_smt x) := by
  unfold generic_apply_eval
  intro M
  change
    __smtx_model_eval M
        (SmtTerm.Apply
          (native_ite (__eo_to_smt_nat_is_valid len)
            (native_ite (__eo_to_smt_nat_is_valid id)
              (SmtTerm.choice (native_string_lit "@x") (__eo_to_smt_type T)
                (SmtTerm.eq
                  (SmtTerm.str_len
                    (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type T)))
                  (__eo_to_smt len)))
              SmtTerm.None)
            SmtTerm.None)
          (__eo_to_smt x)) =
      __smtx_model_eval_apply M
        (__smtx_model_eval M
          (native_ite (__eo_to_smt_nat_is_valid len)
            (native_ite (__eo_to_smt_nat_is_valid id)
              (SmtTerm.choice (native_string_lit "@x") (__eo_to_smt_type T)
                (SmtTerm.eq
                  (SmtTerm.str_len
                    (SmtTerm.Var (native_string_lit "@x") (__eo_to_smt_type T)))
                  (__eo_to_smt len)))
              SmtTerm.None)
            SmtTerm.None))
        (__smtx_model_eval M (__eo_to_smt x))
  cases hLen : __eo_to_smt_nat_is_valid len <;>
    cases hId : __eo_to_smt_nat_is_valid id <;>
      simp [__smtx_model_eval, native_ite]

/-- Reusable reduction for a unary `UOp2` special-head application
`Apply (UOp2 op i j) a`. Concrete callers provide the index-evaluation facts
and the SMT constructor congruence. -/
theorem substFalse_eval_unary_uop2_special
    (op : UserOp2) (i j a xs ss bvs : Term) {M N : SmtModel}
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hFTrans : eoHasSmtTranslation (Term.Apply (Term.UOp2 op i j) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp2 op i j) a) xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename) (Term.UOp2 op i j) xs ss bvs =
        Term.UOp2 op i j)
    (hArgExtract :
      ∀ {t : Term},
        eoHasSmtTranslation (Term.Apply (Term.UOp2 op i j) t) →
          eoHasSmtTranslation t)
    (hIEval :
      __smtx_model_eval M (__eo_to_smt i) =
        __smtx_model_eval N (__eo_to_smt i))
    (hJEval :
      __smtx_model_eval M (__eo_to_smt j) =
        __smtx_model_eval N (__eo_to_smt j))
    (hCong :
      ∀ X Y : Term,
        __smtx_model_eval M (__eo_to_smt i) =
          __smtx_model_eval N (__eo_to_smt i) →
        __smtx_model_eval M (__eo_to_smt j) =
          __smtx_model_eval N (__eo_to_smt j) →
        __smtx_model_eval M (__eo_to_smt X) =
          __smtx_model_eval N (__eo_to_smt Y) →
        __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp2 op i j) X)) =
          __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp2 op i j) Y)))
    (hRecArg :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.UOp2 op i j) a) xs ss bvs)) =
      __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp2 op i j) a)) := by
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp2 op i j) a) xs ss bvs =
        __eo_mk_apply (Term.UOp2 op i j)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.UOp2 op i j) a xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [hHeadSub] using hApplyEq
  have hMkNeStuck :
      __eo_mk_apply (Term.UOp2 op i j)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) ≠ Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hMk :
      __eo_mk_apply (Term.UOp2 op i j)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) =
        Term.Apply (Term.UOp2 op i j)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNeStuck
  have hATrans : eoHasSmtTranslation a := hArgExtract hFTrans
  have hSubstApplyTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp2 op i j)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) := by
    rw [← hMk, ← hSubstEq]
    exact hSubstTrans
  have hSubstATrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    hArgExtract hSubstApplyTrans
  rw [hSubstEq, hMk]
  exact hCong _ _ hIEval hJEval (hRecArg hATrans hSubstATrans)

/-- Reusable reduction for a **binary special-head application**
`(Apply (Apply (UOp op) x1) a)` in the substitution-evaluation induction.
Analogous to `substFalse_eval_unary_op`, but recurses on both subterms. -/
theorem substFalse_eval_binary_op
    (op : UserOp) (x1 a xs ss bvs : Term) {M N : SmtModel}
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x1 ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x1) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x1) a) xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename) (Term.UOp op) xs ss bvs =
        Term.UOp op)
    (hArgExtract :
      ∀ {s t : Term},
        eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) s) t) →
          eoHasSmtTranslation s ∧ eoHasSmtTranslation t)
    (hCong :
      ∀ X1 Y1 X2 Y2 : Term,
        __smtx_model_eval M (__eo_to_smt X1) = __smtx_model_eval N (__eo_to_smt Y1) →
        __smtx_model_eval M (__eo_to_smt X2) = __smtx_model_eval N (__eo_to_smt Y2) →
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) X1) X2)) =
            __smtx_model_eval N
              (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) Y1) Y2)))
    (hRecArg1 :
      eoHasSmtTranslation x1 →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt x1))
    (hRecArg2 :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.UOp op) x1) a) xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x1) a)) := by
  have hSubstHead :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) x1) xs ss bvs =
        __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.UOp op) x1 xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [hHeadSub] using hEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x1) a) xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Apply (Term.UOp op) x1) a xs ss bvs hisr hxs hss hbvs
        hNotBinderOuter
    rw [hEq, hSubstHead]
  have hOuterNeStuck :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) ≠ Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hInnerNeStuck :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) ≠ Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  have hInnerMk :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) =
        Term.Apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNeStuck
  have hOuterMk :
      __eo_mk_apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) =
        Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by rw [← hInnerMk]; exact hOuterNeStuck)
  have hResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x1) a) xs ss bvs =
        Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) := by
    rw [hSubstEq, hInnerMk, hOuterMk]
  have hArgsTrans := hArgExtract hFTrans
  have hSubstAppTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) := by
    rw [← hResultEq]; exact hSubstTrans
  have hSubstArgsTrans := hArgExtract hSubstAppTrans
  rw [hResultEq]
  exact hCong _ _ _ _
    (hRecArg1 hArgsTrans.1 hSubstArgsTrans.1)
    (hRecArg2 hArgsTrans.2 hSubstArgsTrans.2)

theorem substFalse_eval_binary_op_with_app_trans
    (op : UserOp) (x1 a xs ss bvs : Term) {M N : SmtModel}
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x1 ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x1) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x1) a) xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename) (Term.UOp op) xs ss bvs =
        Term.UOp op)
    (hArgExtract :
      ∀ {s t : Term},
        eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) s) t) →
          eoHasSmtTranslation s ∧ eoHasSmtTranslation t)
    (hCong :
      ∀ X1 Y1 X2 Y2 : Term,
        eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) X1) X2) →
        eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) Y1) Y2) →
        __smtx_model_eval M (__eo_to_smt X1) = __smtx_model_eval N (__eo_to_smt Y1) →
        __smtx_model_eval M (__eo_to_smt X2) = __smtx_model_eval N (__eo_to_smt Y2) →
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) X1) X2)) =
            __smtx_model_eval N
              (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) Y1) Y2)))
    (hRecArg1 :
      eoHasSmtTranslation x1 →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt x1))
    (hRecArg2 :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.UOp op) x1) a) xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x1) a)) := by
  have hSubstHead :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) x1) xs ss bvs =
        __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.UOp op) x1 xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [hHeadSub] using hEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x1) a) xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Apply (Term.UOp op) x1) a xs ss bvs hisr hxs hss hbvs
        hNotBinderOuter
    rw [hEq, hSubstHead]
  have hOuterNeStuck :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) ≠ Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hInnerNeStuck :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) ≠ Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  have hInnerMk :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) =
        Term.Apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNeStuck
  have hOuterMk :
      __eo_mk_apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) =
        Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by rw [← hInnerMk]; exact hOuterNeStuck)
  have hResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x1) a) xs ss bvs =
        Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) := by
    rw [hSubstEq, hInnerMk, hOuterMk]
  have hArgsTrans := hArgExtract hFTrans
  have hSubstAppTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) := by
    rw [← hResultEq]; exact hSubstTrans
  have hSubstArgsTrans := hArgExtract hSubstAppTrans
  rw [hResultEq]
  exact hCong _ _ _ _ hSubstAppTrans hFTrans
    (hRecArg1 hArgsTrans.1 hSubstArgsTrans.1)
    (hRecArg2 hArgsTrans.2 hSubstArgsTrans.2)

/-- Reusable reduction for a **ternary special-head application**
`(Apply (Apply (Apply (UOp op) x1) x2) a)` in the substitution-evaluation
induction. -/
theorem substFalse_eval_ternary_op
    (op : UserOp) (x1 x2 a xs ss bvs : Term) {M N : SmtModel}
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.Apply (Term.UOp op) x1) x2 ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a)
          xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename) (Term.UOp op) xs ss bvs =
        Term.UOp op)
    (hArgExtract :
      ∀ {r s t : Term},
        eoHasSmtTranslation
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) r) s) t) →
          eoHasSmtTranslation r ∧ eoHasSmtTranslation s ∧
            eoHasSmtTranslation t)
    (hCong :
      ∀ X1 Y1 X2 Y2 X3 Y3 : Term,
        __smtx_model_eval M (__eo_to_smt X1) =
          __smtx_model_eval N (__eo_to_smt Y1) →
        __smtx_model_eval M (__eo_to_smt X2) =
          __smtx_model_eval N (__eo_to_smt Y2) →
        __smtx_model_eval M (__eo_to_smt X3) =
          __smtx_model_eval N (__eo_to_smt Y3) →
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) X1) X2) X3)) =
            __smtx_model_eval N
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) Y1) Y2) Y3)))
    (hRecArg :
      ∀ {b : Term},
        IsNonbinderSubterm b
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a) →
        sizeOf b <
            sizeOf (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a) →
        eoHasSmtTranslation b →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt b)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a)
            xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a)) := by
  have hArgsTrans := hArgExtract hFTrans
  have hSubstHead :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) x1) xs ss bvs =
        __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.UOp op) x1 xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [hHeadSub] using hEq
  have hNotBinderMiddle :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x1 ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
    intro q v vs hEq
    cases hEq
    exact term_not_eo_list_cons_of_has_smt_translation hArgsTrans.1 v vs rfl
  have hSubstMid :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x1) x2) xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Apply (Term.UOp op) x1) x2 xs ss bvs hisr hxs hss hbvs
        hNotBinderMiddle
    rw [hEq, hSubstHead]
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a)
          xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a xs ss bvs
        hisr hxs hss hbvs hNotBinderOuter
    rw [hEq, hSubstMid]
  have hOuterNeStuck :
      __eo_mk_apply
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) ≠
        Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hMidNeStuck :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs) ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  have hInnerNeStuck :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hMidNeStuck
  have hInnerMk :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) =
        Term.Apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNeStuck
  have hMidMk :
      __eo_mk_apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs) =
        Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      rw [← hInnerMk]
      exact hMidNeStuck)
  have hOuterMk :
      __eo_mk_apply
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) =
        Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      rw [← hMidMk, ← hInnerMk]
      exact hOuterNeStuck)
  have hResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a)
          xs ss bvs =
        Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) := by
    rw [hSubstEq, hInnerMk, hMidMk, hOuterMk]
  have hSubstAppTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) := by
    rw [← hResultEq]; exact hSubstTrans
  have hSubstArgsTrans := hArgExtract hSubstAppTrans
  have hOuterNonbinder :
      ¬ IsBinderHead (Term.Apply (Term.Apply (Term.UOp op) x1) x2) := by
    rintro ⟨q, v, vs, hEq⟩
    exact hNotBinderOuter q v vs hEq
  have hMiddleNonbinder :
      ¬ IsBinderHead (Term.Apply (Term.UOp op) x1) := by
    rintro ⟨q, v, vs, hEq⟩
    exact hNotBinderMiddle q v vs hEq
  rw [hResultEq]
  exact hCong _ _ _ _ _ _
    (hRecArg
      (by simp [IsNonbinderSubterm, hOuterNonbinder, hMiddleNonbinder])
      (by simp; omega) hArgsTrans.1 hSubstArgsTrans.1)
    (hRecArg
      (by simp [IsNonbinderSubterm, hOuterNonbinder, hMiddleNonbinder])
      (by simp; omega) hArgsTrans.2.1 hSubstArgsTrans.2.1)
    (hRecArg
      (by simp [IsNonbinderSubterm, hOuterNonbinder, hMiddleNonbinder])
      (by simp; omega) hArgsTrans.2.2 hSubstArgsTrans.2.2)

/-- Reusable reduction for a **quaternary special-head application**
`(Apply (Apply (Apply (Apply (UOp op) x1) x2) x3) a)` in the
substitution-evaluation induction. -/
theorem substFalse_eval_quaternary_op
    (op : UserOp) (x1 x2 x3 a xs ss bvs : Term) {M N : SmtModel}
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck)
    (hbvs : bvs ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply
            (Term.Apply (Term.Apply (Term.UOp op) x1) x2) x3 ≠
          Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp op) x1) x2) x3) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp op) x1) x2) x3) a)
          xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp op) xs ss bvs =
        Term.UOp op)
    (hArgExtract :
      ∀ {w x y z : Term},
        eoHasSmtTranslation
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp op) w) x) y) z) →
        eoHasSmtTranslation w ∧ eoHasSmtTranslation x ∧
          eoHasSmtTranslation y ∧ eoHasSmtTranslation z)
    (hCong :
      ∀ X1 Y1 X2 Y2 X3 Y3 X4 Y4 : Term,
        __smtx_model_eval M (__eo_to_smt X1) =
          __smtx_model_eval N (__eo_to_smt Y1) →
        __smtx_model_eval M (__eo_to_smt X2) =
          __smtx_model_eval N (__eo_to_smt Y2) →
        __smtx_model_eval M (__eo_to_smt X3) =
          __smtx_model_eval N (__eo_to_smt Y3) →
        __smtx_model_eval M (__eo_to_smt X4) =
          __smtx_model_eval N (__eo_to_smt Y4) →
        __smtx_model_eval M
            (__eo_to_smt
              (Term.Apply
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.UOp op) X1) X2) X3) X4)) =
          __smtx_model_eval N
            (__eo_to_smt
              (Term.Apply
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.UOp op) Y1) Y2) Y3) Y4)))
    (hRecArg :
      ∀ {b : Term},
        IsNonbinderSubterm b
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp op) x1) x2) x3) a) →
        sizeOf b <
          sizeOf
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.UOp op) x1) x2) x3) a) →
        eoHasSmtTranslation b →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec
                (Term.Boolean isRename) b xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt b)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.Apply (Term.UOp op) x1) x2) x3) a)
            xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp op) x1) x2) x3) a)) := by
  have hArgsTrans := hArgExtract hFTrans
  have hSubstInner :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) x1) xs ss bvs =
        __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec
            (Term.Boolean isRename) x1 xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.UOp op) x1 xs ss bvs
        hisr hxs hss hbvs (by intro q v vs hEq; cases hEq)
    simpa [hHeadSub] using hEq
  have hNotBinderMiddle :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x1 ≠
          Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
    intro q v vs hEq
    cases hEq
    exact term_not_eo_list_cons_of_has_smt_translation
      hArgsTrans.1 v vs rfl
  have hSubstMiddle :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x1) x2)
          xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp op)
            (__substitute_simul_rec
              (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec
            (Term.Boolean isRename) x2 xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename)
        (Term.Apply (Term.UOp op) x1) x2 xs ss bvs
        hisr hxs hss hbvs hNotBinderMiddle
    rw [hEq, hSubstInner]
  have hNotBinderThird :
      ∀ q v vs,
        Term.Apply
            (Term.Apply (Term.UOp op) x1) x2 ≠
          Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
    intro q v vs hEq
    cases hEq
    exact term_not_eo_list_cons_of_has_smt_translation
      hArgsTrans.2.1 v vs rfl
  have hSubstThird :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp op) x1) x2) x3)
          xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp op)
              (__substitute_simul_rec
                (Term.Boolean isRename) x1 xs ss bvs))
            (__substitute_simul_rec
              (Term.Boolean isRename) x2 xs ss bvs))
          (__substitute_simul_rec
            (Term.Boolean isRename) x3 xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename)
        (Term.Apply (Term.Apply (Term.UOp op) x1) x2) x3
        xs ss bvs hisr hxs hss hbvs hNotBinderThird
    rw [hEq, hSubstMiddle]
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp op) x1) x2) x3) a)
          xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp op)
                (__substitute_simul_rec
                  (Term.Boolean isRename) x1 xs ss bvs))
              (__substitute_simul_rec
                (Term.Boolean isRename) x2 xs ss bvs))
            (__substitute_simul_rec
              (Term.Boolean isRename) x3 xs ss bvs))
          (__substitute_simul_rec
            (Term.Boolean isRename) a xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename)
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp op) x1) x2) x3) a
        xs ss bvs hisr hxs hss hbvs hNotBinderOuter
    rw [hEq, hSubstThird]
  have hOuterNeStuck :
      __eo_mk_apply
          (__eo_mk_apply
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp op)
                (__substitute_simul_rec
                  (Term.Boolean isRename) x1 xs ss bvs))
              (__substitute_simul_rec
                (Term.Boolean isRename) x2 xs ss bvs))
            (__substitute_simul_rec
              (Term.Boolean isRename) x3 xs ss bvs))
          (__substitute_simul_rec
            (Term.Boolean isRename) a xs ss bvs) ≠
        Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hThirdNeStuck :
      __eo_mk_apply
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp op)
              (__substitute_simul_rec
                (Term.Boolean isRename) x1 xs ss bvs))
            (__substitute_simul_rec
              (Term.Boolean isRename) x2 xs ss bvs))
          (__substitute_simul_rec
            (Term.Boolean isRename) x3 xs ss bvs) ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  have hMiddleNeStuck :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp op)
            (__substitute_simul_rec
              (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec
            (Term.Boolean isRename) x2 xs ss bvs) ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hThirdNeStuck
  have hInnerNeStuck :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec
            (Term.Boolean isRename) x1 xs ss bvs) ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hMiddleNeStuck
  have hInnerMk :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec
            (Term.Boolean isRename) x1 xs ss bvs) =
        Term.Apply (Term.UOp op)
          (__substitute_simul_rec
            (Term.Boolean isRename) x1 xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNeStuck
  have hMiddleMk :
      __eo_mk_apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec
              (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec
            (Term.Boolean isRename) x2 xs ss bvs) =
        Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec
              (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec
            (Term.Boolean isRename) x2 xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      rw [← hInnerMk]
      exact hMiddleNeStuck)
  have hThirdMk :
      __eo_mk_apply
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec
                (Term.Boolean isRename) x1 xs ss bvs))
            (__substitute_simul_rec
              (Term.Boolean isRename) x2 xs ss bvs))
          (__substitute_simul_rec
            (Term.Boolean isRename) x3 xs ss bvs) =
        Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec
                (Term.Boolean isRename) x1 xs ss bvs))
            (__substitute_simul_rec
              (Term.Boolean isRename) x2 xs ss bvs))
          (__substitute_simul_rec
            (Term.Boolean isRename) x3 xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      rw [← hMiddleMk, ← hInnerMk]
      exact hThirdNeStuck)
  have hOuterMk :
      __eo_mk_apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp op)
                (__substitute_simul_rec
                  (Term.Boolean isRename) x1 xs ss bvs))
              (__substitute_simul_rec
                (Term.Boolean isRename) x2 xs ss bvs))
            (__substitute_simul_rec
              (Term.Boolean isRename) x3 xs ss bvs))
          (__substitute_simul_rec
            (Term.Boolean isRename) a xs ss bvs) =
        Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp op)
                (__substitute_simul_rec
                  (Term.Boolean isRename) x1 xs ss bvs))
              (__substitute_simul_rec
                (Term.Boolean isRename) x2 xs ss bvs))
            (__substitute_simul_rec
              (Term.Boolean isRename) x3 xs ss bvs))
          (__substitute_simul_rec
            (Term.Boolean isRename) a xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      rw [← hThirdMk, ← hMiddleMk, ← hInnerMk]
      exact hOuterNeStuck)
  have hResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp op) x1) x2) x3) a)
          xs ss bvs =
        Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp op)
                (__substitute_simul_rec
                  (Term.Boolean isRename) x1 xs ss bvs))
              (__substitute_simul_rec
                (Term.Boolean isRename) x2 xs ss bvs))
            (__substitute_simul_rec
              (Term.Boolean isRename) x3 xs ss bvs))
          (__substitute_simul_rec
            (Term.Boolean isRename) a xs ss bvs) := by
    rw [hSubstEq, hInnerMk, hMiddleMk, hThirdMk, hOuterMk]
  have hSubstAppTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp op)
                (__substitute_simul_rec
                  (Term.Boolean isRename) x1 xs ss bvs))
              (__substitute_simul_rec
                (Term.Boolean isRename) x2 xs ss bvs))
            (__substitute_simul_rec
              (Term.Boolean isRename) x3 xs ss bvs))
          (__substitute_simul_rec
            (Term.Boolean isRename) a xs ss bvs)) := by
    rw [← hResultEq]
    exact hSubstTrans
  have hSubstArgsTrans := hArgExtract hSubstAppTrans
  have hOuterNonbinder :
      ¬ IsBinderHead
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp op) x1) x2) x3) := by
    rintro ⟨q, v, vs, hEq⟩
    exact hNotBinderOuter q v vs hEq
  have hThirdNonbinder :
      ¬ IsBinderHead
        (Term.Apply (Term.Apply (Term.UOp op) x1) x2) := by
    rintro ⟨q, v, vs, hEq⟩
    exact hNotBinderThird q v vs hEq
  have hMiddleNonbinder :
      ¬ IsBinderHead (Term.Apply (Term.UOp op) x1) := by
    rintro ⟨q, v, vs, hEq⟩
    exact hNotBinderMiddle q v vs hEq
  rw [hResultEq]
  exact hCong _ _ _ _ _ _ _ _
    (hRecArg
      (by
        simp [IsNonbinderSubterm, hOuterNonbinder, hThirdNonbinder,
          hMiddleNonbinder])
      (by simp; omega) hArgsTrans.1 hSubstArgsTrans.1)
    (hRecArg
      (by
        simp [IsNonbinderSubterm, hOuterNonbinder, hThirdNonbinder,
          hMiddleNonbinder])
      (by simp; omega) hArgsTrans.2.1 hSubstArgsTrans.2.1)
    (hRecArg
      (by
        simp [IsNonbinderSubterm, hOuterNonbinder, hThirdNonbinder,
          hMiddleNonbinder])
      (by simp; omega) hArgsTrans.2.2.1 hSubstArgsTrans.2.2.1)
    (hRecArg
      (by
        simp [IsNonbinderSubterm, hOuterNonbinder, hThirdNonbinder,
          hMiddleNonbinder])
      (by simp; omega) hArgsTrans.2.2.2 hSubstArgsTrans.2.2.2)

theorem smtx_model_eval_apply_cross_eq_of_eval_eq
    {M N : SmtModel} (hGlobals : model_agrees_on_globals M N)
    {F F' X X' : SmtTerm}
    (hEvalF : generic_apply_eval F X)
    (hEvalF' : generic_apply_eval F' X')
    (hF :
      __smtx_model_eval M F =
        __smtx_model_eval N F')
    (hX :
      __smtx_model_eval M X =
        __smtx_model_eval N X') :
    __smtx_model_eval M (SmtTerm.Apply F X) =
      __smtx_model_eval N (SmtTerm.Apply F' X') := by
  unfold generic_apply_eval at hEvalF hEvalF'
  rw [hEvalF M, hEvalF' N, hF, hX]
  exact smtx_model_eval_apply_eq_of_globals hGlobals _ _

theorem smtx_model_eval_ite_cross_eq_of_eval_eq
    {M N : SmtModel} {c c' x x' y y' : SmtTerm}
    (hc :
      __smtx_model_eval M c =
        __smtx_model_eval N c')
    (hx :
      __smtx_model_eval M x =
        __smtx_model_eval N x')
    (hy :
      __smtx_model_eval M y =
        __smtx_model_eval N y') :
    __smtx_model_eval M (SmtTerm.ite c x y) =
      __smtx_model_eval N (SmtTerm.ite c' x' y') := by
  simp [__smtx_model_eval, hc, hx, hy]

theorem smtx_model_eval_apply_same_head_cross_eq_of_eval_eq
    {M N : SmtModel} (hGlobals : model_agrees_on_globals M N)
    (f x x' : SmtTerm)
    (hf :
      __smtx_model_eval M f =
        __smtx_model_eval N f)
    (hx :
      __smtx_model_eval M x =
        __smtx_model_eval N x') :
    __smtx_model_eval M (SmtTerm.Apply f x) =
      __smtx_model_eval N (SmtTerm.Apply f x') := by
  by_cases hSel : ∃ s d i j, f = SmtTerm.DtSel s d i j
  · rcases hSel with ⟨s, d, i, j, rfl⟩
    simp [__smtx_model_eval, hx, smtx_model_eval_dt_sel_eq_of_globals hGlobals]
  · by_cases hTester : ∃ s d i, f = SmtTerm.DtTester s d i
    · rcases hTester with ⟨s, d, i, rfl⟩
      simp [__smtx_model_eval, hx]
    · have hSel' : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j := fun s d i j h => hSel ⟨s, d, i, j, h⟩
      have hTester' : ∀ s d i, f ≠ SmtTerm.DtTester s d i := fun s d i h => hTester ⟨s, d, i, h⟩
      have hGenM := generic_apply_eval_of_non_datatype_head (x := x) hSel' hTester'
      have hGenN := generic_apply_eval_of_non_datatype_head (x := x') hSel' hTester'
      unfold generic_apply_eval at hGenM hGenN
      rw [hGenM M, hGenN N, hf, hx]
      exact smtx_model_eval_apply_eq_of_globals hGlobals _ _

theorem smtx_model_eval_eo_to_smt_updater_rec_cross_eq_of_eval_eq
    {M N : SmtModel} (hGlobals : model_agrees_on_globals M N)
    (sel : SmtTerm) (n : native_Nat) (t t' u u' acc : SmtTerm)
    (ht :
      __smtx_model_eval M t =
        __smtx_model_eval N t')
    (hu :
      __smtx_model_eval M u =
        __smtx_model_eval N u')
    (hAcc :
      __smtx_model_eval M acc =
        __smtx_model_eval N acc) :
    __smtx_model_eval M (__eo_to_smt_updater_rec sel n t u acc) =
      __smtx_model_eval N (__eo_to_smt_updater_rec sel n t' u' acc) := by
  induction n generalizing acc with
  | zero =>
      cases sel <;>
        simp [__eo_to_smt_updater_rec, __smtx_model_eval, hAcc]
  | succ k ih =>
      cases sel <;>
        try simp [__eo_to_smt_updater_rec, __smtx_model_eval]
      case DtSel s d i j =>
        have hArg :
            __smtx_model_eval M
                (native_ite (native_nateq j k) u
                  (SmtTerm.Apply (SmtTerm.DtSel s d i k) t)) =
              __smtx_model_eval N
                (native_ite (native_nateq j k) u'
                  (SmtTerm.Apply (SmtTerm.DtSel s d i k) t')) := by
          cases hEq : native_nateq j k <;>
            simp [native_ite, hu, ht, __smtx_model_eval,
              smtx_model_eval_dt_sel_eq_of_globals hGlobals]
        cases k with
        | zero =>
            simpa [__eo_to_smt_updater_rec] using
              smtx_model_eval_apply_same_head_cross_eq_of_eval_eq
                hGlobals acc
                (native_ite (native_nateq j 0) u
                  (SmtTerm.Apply (SmtTerm.DtSel s d i 0) t))
                (native_ite (native_nateq j 0) u'
                  (SmtTerm.Apply (SmtTerm.DtSel s d i 0) t'))
                hAcc hArg
        | succ k' =>
            have hHead :
                __smtx_model_eval M
                    (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                      (Nat.succ k') t u acc) =
                  __smtx_model_eval N
                    (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                      (Nat.succ k') t' u' acc) :=
              ih acc hAcc
            have hGeneric :
                generic_apply_eval
                  (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                    (Nat.succ k') t u acc)
                  (native_ite (native_nateq j (Nat.succ k')) u
                    (SmtTerm.Apply (SmtTerm.DtSel s d i (Nat.succ k')) t)) :=
              generic_apply_eval_of_non_datatype_head
                (by intro s0 d0 i0 j0 h; cases h)
                (by intro s0 d0 i0 h; cases h)
            have hGeneric' :
                generic_apply_eval
                  (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                    (Nat.succ k') t' u' acc)
                  (native_ite (native_nateq j (Nat.succ k')) u'
                    (SmtTerm.Apply (SmtTerm.DtSel s d i (Nat.succ k')) t')) :=
              generic_apply_eval_of_non_datatype_head
                (by intro s0 d0 i0 j0 h; cases h)
                (by intro s0 d0 i0 h; cases h)
            exact
              smtx_model_eval_apply_cross_eq_of_eval_eq hGlobals
                hGeneric hGeneric' hHead hArg

theorem smtx_model_eval_eo_to_smt_updater_cross_eq_of_eval_eq
    {M N : SmtModel} (hGlobals : model_agrees_on_globals M N)
    (sel t t' u u' : SmtTerm)
    (ht :
      __smtx_model_eval M t =
        __smtx_model_eval N t')
    (hu :
      __smtx_model_eval M u =
        __smtx_model_eval N u') :
    __smtx_model_eval M (__eo_to_smt_updater sel t u) =
      __smtx_model_eval N (__eo_to_smt_updater sel t' u') := by
  cases sel
  case DtSel s d i j =>
    cases hGuard :
        native_zlt (native_nat_to_int j)
          (native_nat_to_int (__smtx_dt_num_sels (__smtx_dd_lookup s d) i))
    · have hUpdaterM :
          __eo_to_smt_updater (SmtTerm.DtSel s d i j) t u =
            SmtTerm.None := by
        simp [__eo_to_smt_updater, native_ite, hGuard]
      have hUpdaterN :
          __eo_to_smt_updater (SmtTerm.DtSel s d i j) t' u' =
            SmtTerm.None := by
        simp [__eo_to_smt_updater, native_ite, hGuard]
      rw [hUpdaterM, hUpdaterN]
      simp [__smtx_model_eval]
    · have hUpdaterM :
          __eo_to_smt_updater (SmtTerm.DtSel s d i j) t u =
            SmtTerm.ite
              (SmtTerm.Apply (SmtTerm.DtTester s d i) t)
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)
                t u (SmtTerm.DtCons s d i))
              t := by
        simp [__eo_to_smt_updater, native_ite, hGuard]
      have hUpdaterN :
          __eo_to_smt_updater (SmtTerm.DtSel s d i j) t' u' =
            SmtTerm.ite
              (SmtTerm.Apply (SmtTerm.DtTester s d i) t')
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)
                t' u' (SmtTerm.DtCons s d i))
              t' := by
        simp [__eo_to_smt_updater, native_ite, hGuard]
      rw [hUpdaterM, hUpdaterN]
      have hCond :
          __smtx_model_eval M
              (SmtTerm.Apply (SmtTerm.DtTester s d i) t) =
            __smtx_model_eval N
              (SmtTerm.Apply (SmtTerm.DtTester s d i) t') := by
        simp [__smtx_model_eval, ht]
      have hThen :
          __smtx_model_eval M
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)
                t u (SmtTerm.DtCons s d i)) =
            __smtx_model_eval N
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
                (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)
                t' u' (SmtTerm.DtCons s d i)) :=
        smtx_model_eval_eo_to_smt_updater_rec_cross_eq_of_eval_eq
          hGlobals (SmtTerm.DtSel s d i j)
          (__smtx_dt_num_sels (__smtx_dd_lookup s d) i)
          t t' u u' (SmtTerm.DtCons s d i) ht hu
          (by simp [__smtx_model_eval])
      exact smtx_model_eval_ite_cross_eq_of_eval_eq hCond hThen ht
  all_goals
    simp [__eo_to_smt_updater, __smtx_model_eval]

theorem smtx_model_eval_eo_to_smt_tuple_select_cross_eq_of_eval_eq
    {M N : SmtModel} (hGlobals : model_agrees_on_globals M N)
    (T : SmtType) (idx x x' : SmtTerm)
    (hx :
      __smtx_model_eval M x =
        __smtx_model_eval N x') :
    __smtx_model_eval M (__eo_to_smt_tuple_select T idx x) =
      __smtx_model_eval N (__eo_to_smt_tuple_select T idx x') := by
  cases T <;> try simp [__eo_to_smt_tuple_select, __smtx_model_eval]
  case Datatype s dd =>
    cases dd with
    | nil =>
        simp [__smtx_model_eval]
    | cons s2 d rest =>
        cases rest with
        | cons s3 d3 rest3 =>
            simp [__smtx_model_eval]
        | nil =>
            cases idx <;>
              try simp [__smtx_model_eval]
            rename_i n
            cases hCond :
                native_and
                  (native_and
                    (native_streq s (native_string_lit "@Tuple"))
                    (native_streq s2 (native_string_lit "@Tuple")))
                  (native_zleq 0 n)
            · simp [native_ite, __smtx_model_eval]
            · simp [native_ite, __smtx_model_eval, hx,
                smtx_model_eval_dt_sel_eq_of_globals hGlobals]

theorem smtx_model_eval_eo_to_smt_tuple_update_cross_eq_of_eval_eq
    {M N : SmtModel} (hGlobals : model_agrees_on_globals M N)
    (T : SmtType) (idx t t' u u' : SmtTerm)
    (ht :
      __smtx_model_eval M t =
        __smtx_model_eval N t')
    (hu :
      __smtx_model_eval M u =
        __smtx_model_eval N u') :
    __smtx_model_eval M (__eo_to_smt_tuple_update T idx t u) =
      __smtx_model_eval N (__eo_to_smt_tuple_update T idx t' u') := by
  -- `__eo_to_smt_tuple_update` only inspects `idx` under a `@Tuple` datatype
  -- type, so split `T` first and reach for `idx` only in that one branch: the
  -- flat `cases T <;> cases idx` produced 15 * 151 goals, each re-unfolding the
  -- 151-arm `__smtx_model_eval` match, which exhausts `isDefEq`'s heartbeats.
  have hNone : ∀ {A B : SmtTerm}, A = SmtTerm.None → B = SmtTerm.None →
      __smtx_model_eval M A = __smtx_model_eval N B := by
    rintro _ _ rfl rfl
    simp [__smtx_model_eval]
  cases T
  case Datatype s dd =>
    cases dd with
    | nil => exact hNone rfl rfl
    | cons s2 d rest =>
        cases rest with
        | cons s3 d3 rest3 => exact hNone rfl rfl
        | nil =>
            cases idx
            case Numeral n =>
              cases hCond :
                  native_and
                    (native_and
                      (native_streq s (native_string_lit "@Tuple"))
                      (native_streq s2 (native_string_lit "@Tuple")))
                    (native_zleq 0 n)
              · simp [__eo_to_smt_tuple_update, hCond, native_ite,
                  __smtx_model_eval]
              · simp [__eo_to_smt_tuple_update, hCond, native_ite]
                exact
                  smtx_model_eval_eo_to_smt_updater_cross_eq_of_eval_eq hGlobals
                    (SmtTerm.DtSel (native_string_lit "@Tuple")
                      (__eo_to_smt_tuple_decl d) native_nat_zero
                      (native_int_to_nat n))
                    t t' u u' ht hu
            all_goals exact hNone rfl rfl
  all_goals exact hNone rfl rfl

theorem substFalse_eval_unary_uop1_tuple_select
    (idx a xs ss bvs : Term) {M N : SmtModel}
    (hM : model_wf M) (hN : model_wf N)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hFTrans : eoHasSmtTranslation (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) a) xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp1 UserOp1.tuple_select idx) xs ss bvs =
        Term.UOp1 UserOp1.tuple_select idx)
    (hGlobals : model_agrees_on_globals M N)
    (hRecArg :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) a) xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) a)) := by
  let aSub := __substitute_simul_rec (Term.Boolean isRename) a xs ss bvs
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) a) xs ss bvs =
        __eo_mk_apply (Term.UOp1 UserOp1.tuple_select idx) aSub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.UOp1 UserOp1.tuple_select idx) a xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [aSub, hHeadSub] using hApplyEq
  have hMkNeStuck :
      __eo_mk_apply (Term.UOp1 UserOp1.tuple_select idx) aSub ≠ Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hMk :
      __eo_mk_apply (Term.UOp1 UserOp1.tuple_select idx) aSub =
        Term.Apply (Term.UOp1 UserOp1.tuple_select idx) aSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNeStuck
  have hATrans : eoHasSmtTranslation a :=
    (tuple_select_index_nat_valid_and_arg_has_smt_translation hFTrans).2
  have hSubstApplyTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) aSub) := by
    rw [← hMk, ← hSubstEq]
    exact hSubstTrans
  have hSubstATrans : eoHasSmtTranslation aSub :=
    (tuple_select_index_nat_valid_and_arg_has_smt_translation hSubstApplyTrans).2
  have hArgEval := hRecArg hATrans hSubstATrans
  have hArgTy :
      __smtx_typeof (__eo_to_smt aSub) =
        __smtx_typeof (__eo_to_smt a) :=
    smtx_typeof_eo_to_smt_eq_of_eval_eq hM hN aSub a
      hSubstATrans hATrans hArgEval
  rw [hSubstEq, hMk]
  change
    __smtx_model_eval M
        (__eo_to_smt_tuple_select (__smtx_typeof (__eo_to_smt aSub))
          (__eo_to_smt idx) (__eo_to_smt aSub)) =
      __smtx_model_eval N
        (__eo_to_smt_tuple_select (__smtx_typeof (__eo_to_smt a))
          (__eo_to_smt idx) (__eo_to_smt a))
  rw [hArgTy]
  exact
    smtx_model_eval_eo_to_smt_tuple_select_cross_eq_of_eval_eq
      hGlobals (__smtx_typeof (__eo_to_smt a)) (__eo_to_smt idx)
      (__eo_to_smt aSub) (__eo_to_smt a) hArgEval

private theorem instantiate_eo_to_smt_tuple_prepend_rec_ne_dt_sel
    (tailDD : SmtDatatypeDecl) (tailD : SmtDatatype) (tail : SmtTerm) :
    ∀ (k : native_Nat) (acc : SmtTerm),
      (∀ s d i j, acc ≠ SmtTerm.DtSel s d i j) ->
        ∀ s d i j,
          __eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc ≠
            SmtTerm.DtSel s d i j
  | native_nat_zero, acc, hAcc, s, d, i, j => by
      simpa [__eo_to_smt_tuple_prepend_rec] using hAcc s d i j
  | native_nat_succ _k, _acc, _hAcc, _s, _d, _i, _j => by
      intro h
      cases h

private theorem instantiate_eo_to_smt_tuple_prepend_rec_ne_dt_tester
    (tailDD : SmtDatatypeDecl) (tailD : SmtDatatype) (tail : SmtTerm) :
    ∀ (k : native_Nat) (acc : SmtTerm),
      (∀ s d i, acc ≠ SmtTerm.DtTester s d i) ->
        ∀ s d i,
          __eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc ≠
            SmtTerm.DtTester s d i
  | native_nat_zero, acc, hAcc, s, d, i => by
      simpa [__eo_to_smt_tuple_prepend_rec] using hAcc s d i
  | native_nat_succ _k, _acc, _hAcc, _s, _d, _i => by
      intro h
      cases h

theorem smtx_model_eval_eo_to_smt_tuple_prepend_rec_cross_eq_of_eval_eq
    {M N : SmtModel} (hGlobals : model_agrees_on_globals M N)
    (tailDD : SmtDatatypeDecl) (tailD : SmtDatatype)
    (tail tail' acc acc' : SmtTerm)
    (hTail :
      __smtx_model_eval M tail =
        __smtx_model_eval N tail')
    (hAccSel : ∀ s d i j, acc ≠ SmtTerm.DtSel s d i j)
    (hAccTester : ∀ s d i, acc ≠ SmtTerm.DtTester s d i)
    (hAcc'Sel : ∀ s d i j, acc' ≠ SmtTerm.DtSel s d i j)
    (hAcc'Tester : ∀ s d i, acc' ≠ SmtTerm.DtTester s d i)
    (hAcc :
      __smtx_model_eval M acc =
        __smtx_model_eval N acc') :
    ∀ k,
      __smtx_model_eval M
          (__eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc) =
        __smtx_model_eval N
          (__eo_to_smt_tuple_prepend_rec tailDD tailD tail' k acc')
  | native_nat_zero => by
      simpa [__eo_to_smt_tuple_prepend_rec] using hAcc
  | native_nat_succ k => by
      let recTerm := __eo_to_smt_tuple_prepend_rec tailDD tailD tail k acc
      let recTerm' := __eo_to_smt_tuple_prepend_rec tailDD tailD tail' k acc'
      let argTerm :=
        SmtTerm.Apply
          (SmtTerm.DtSel (native_string_lit "@Tuple") tailDD native_nat_zero k)
          tail
      let argTerm' :=
        SmtTerm.Apply
          (SmtTerm.DtSel (native_string_lit "@Tuple") tailDD native_nat_zero k)
          tail'
      have hRecEval :
          __smtx_model_eval M recTerm =
            __smtx_model_eval N recTerm' := by
        simpa [recTerm, recTerm'] using
          smtx_model_eval_eo_to_smt_tuple_prepend_rec_cross_eq_of_eval_eq
            hGlobals tailDD tailD tail tail' acc acc' hTail
            hAccSel hAccTester hAcc'Sel hAcc'Tester hAcc k
      have hArgEval :
          __smtx_model_eval M argTerm =
            __smtx_model_eval N argTerm' := by
        simp [argTerm, argTerm', __smtx_model_eval, hTail,
          smtx_model_eval_dt_sel_eq_of_globals hGlobals]
      have hGen : generic_apply_eval recTerm argTerm :=
        generic_apply_eval_of_non_datatype_head
          (by
            intro s d i j h
            exact
              instantiate_eo_to_smt_tuple_prepend_rec_ne_dt_sel
                tailDD tailD tail k acc
                hAccSel s d i j (by simpa [recTerm] using h))
          (by
            intro s d i h
            exact
              instantiate_eo_to_smt_tuple_prepend_rec_ne_dt_tester
                tailDD tailD tail k acc
                hAccTester s d i (by simpa [recTerm] using h))
      have hGen' : generic_apply_eval recTerm' argTerm' :=
        generic_apply_eval_of_non_datatype_head
          (by
            intro s d i j h
            exact
              instantiate_eo_to_smt_tuple_prepend_rec_ne_dt_sel
                tailDD tailD tail' k acc'
                hAcc'Sel s d i j (by simpa [recTerm'] using h))
          (by
            intro s d i h
            exact
              instantiate_eo_to_smt_tuple_prepend_rec_ne_dt_tester
                tailDD tailD tail' k acc'
                hAcc'Tester s d i (by simpa [recTerm'] using h))
      exact
        smtx_model_eval_apply_cross_eq_of_eval_eq hGlobals
          hGen hGen' hRecEval hArgEval

theorem smtx_model_eval_eo_to_smt_tuple_prepend_cross_eq_of_eval_eq
    {M N : SmtModel} (hGlobals : model_agrees_on_globals M N)
    (head head' tail tail' : SmtTerm)
    (headTy headTy' : SmtType)
    (hHeadTy : headTy = headTy')
    (hTailTy : __smtx_typeof tail = __smtx_typeof tail')
    (hHead :
      __smtx_model_eval M head =
        __smtx_model_eval N head')
    (hTail :
      __smtx_model_eval M tail =
        __smtx_model_eval N tail') :
    __smtx_model_eval M (__eo_to_smt_tuple_prepend head headTy tail) =
      __smtx_model_eval N
        (__eo_to_smt_tuple_prepend head' headTy' tail') := by
  subst headTy'
  unfold __eo_to_smt_tuple_prepend
  rw [← hTailTy]
  cases hTailTy0 : __smtx_typeof tail with
  | Datatype s dd =>
      cases dd with
      | nil =>
          simp [__eo_to_smt_tuple_prepend_of_type, __smtx_model_eval]
      | cons s2 d rest =>
          cases rest with
          | cons s3 d3 rest3 =>
              simp [__eo_to_smt_tuple_prepend_of_type, __smtx_model_eval]
          | nil =>
              cases d with
              | null =>
                  simp [__eo_to_smt_tuple_prepend_of_type, __smtx_model_eval]
              | sum c dTail =>
                  cases dTail with
                  | sum c2 d2 =>
                      simp [__eo_to_smt_tuple_prepend_of_type, __smtx_model_eval]
                  | null =>
                      by_cases hs : s = native_string_lit "@Tuple"
                      · subst s
                        by_cases hs2 : s2 = native_string_lit "@Tuple"
                        · subst s2
                          let tailD := SmtDatatype.sum c SmtDatatype.null
                          let tailDD := __eo_to_smt_tuple_decl tailD
                          let fullD :=
                            SmtDatatype.sum (SmtDatatypeCons.cons headTy c)
                              SmtDatatype.null
                          let fullDD := __eo_to_smt_tuple_decl fullD
                          let seed :=
                            SmtTerm.Apply
                              (SmtTerm.DtCons (native_string_lit "@Tuple") fullDD
                                native_nat_zero) head
                          let seed' :=
                            SmtTerm.Apply
                              (SmtTerm.DtCons (native_string_lit "@Tuple") fullDD
                                native_nat_zero) head'
                          cases hWf :
                              __smtx_type_wf
                                (SmtType.Datatype
                                  (native_string_lit "@Tuple") fullDD)
                          · dsimp [fullDD, fullD,
                              __eo_to_smt_tuple_decl] at hWf
                            simp [__eo_to_smt_tuple_prepend_of_type,
                              __eo_to_smt_tuple_decl, native_ite,
                              native_streq, native_and, hWf,
                              __smtx_model_eval]
                          · dsimp [fullDD, fullD,
                              __eo_to_smt_tuple_decl] at hWf
                            simp [__eo_to_smt_tuple_prepend_of_type,
                              __eo_to_smt_tuple_decl, native_ite,
                              native_streq, native_and, hWf]
                            exact
                              smtx_model_eval_eo_to_smt_tuple_prepend_rec_cross_eq_of_eval_eq
                                hGlobals tailDD tailD tail tail' seed seed' hTail
                                (by intro s d i j h; simp [seed] at h)
                                (by intro s d i h; simp [seed] at h)
                                (by intro s d i j h; simp [seed'] at h)
                                (by intro s d i h; simp [seed'] at h)
                                (by
                                  exact
                                    smtx_model_eval_apply_same_head_cross_eq_of_eval_eq
                                      hGlobals
                                      (SmtTerm.DtCons
                                        (native_string_lit "@Tuple") fullDD
                                        native_nat_zero)
                                      head head'
                                      (by simp [__smtx_model_eval])
                                      hHead)
                                (__smtx_dt_num_sels tailD native_nat_zero)
                        · simp [__eo_to_smt_tuple_prepend_of_type, native_streq,
                            native_and, native_ite, hs2, __smtx_model_eval]
                      · simp [__eo_to_smt_tuple_prepend_of_type, native_streq,
                          native_and, native_ite, hs, __smtx_model_eval]
  | _ =>
      simp [__eo_to_smt_tuple_prepend_of_type, __smtx_model_eval]

theorem smtx_model_eval_eo_to_smt_set_insert_base_eq_of_eval_eq
    (M : SmtModel) :
    ∀ xs a b,
      __smtx_typeof a = __smtx_typeof b ->
      __smtx_model_eval M a = __smtx_model_eval M b ->
        __smtx_model_eval M (__eo_to_smt_set_insert xs a) =
          __smtx_model_eval M (__eo_to_smt_set_insert xs b) := by
  intro xs a b hTy hEval
  cases xs <;> try rfl
  case Apply f tail =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> try rfl
      case _at__at_TypedList_nil =>
        cases hGuard :
            native_Teq (__smtx_typeof b)
              (SmtType.Set (__eo_to_smt_type tail))
        · simp [__eo_to_smt_set_insert, hTy, hGuard, native_ite]
        · simpa [__eo_to_smt_set_insert, hTy, hGuard, native_ite] using hEval
    case Apply f' head =>
      cases f' <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        case _at__at_TypedList_cons =>
          change
            __smtx_model_eval M
                (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                  (__eo_to_smt_set_insert tail a)) =
              __smtx_model_eval M
                (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                  (__eo_to_smt_set_insert tail b))
          have hTailEval :=
            smtx_model_eval_eo_to_smt_set_insert_base_eq_of_eval_eq
              M tail a b hTy hEval
          simp only [__smtx_model_eval]
          rw [hTailEval]
termination_by xs a b _ _ => xs

theorem substFalse_eval_binary_tuple
    (x y xs ss bvs : Term) {M N : SmtModel}
    (hM : model_wf M) (hN : model_wf N)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp.tuple) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y) xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename) (Term.UOp UserOp.tuple) xs ss bvs =
        Term.UOp UserOp.tuple)
    (hGlobals : model_agrees_on_globals M N)
    (hRecX :
      eoHasSmtTranslation x →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt x))
    (hRecY :
      eoHasSmtTranslation y →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt y)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y) xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y)) := by
  let xSub := __substitute_simul_rec (Term.Boolean isRename) x xs ss bvs
  let ySub := __substitute_simul_rec (Term.Boolean isRename) y xs ss bvs
  have hSubstHead :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp UserOp.tuple) x) xs ss bvs =
        __eo_mk_apply (Term.UOp UserOp.tuple) xSub := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.UOp UserOp.tuple) x xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [xSub, hHeadSub] using hEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y) xs ss bvs =
        __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.tuple) xSub) ySub := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Apply (Term.UOp UserOp.tuple) x) y xs ss bvs
        hisr hxs hss hbvs hNotBinderOuter
    rw [hEq, hSubstHead]
  have hOuterNeStuck :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.tuple) xSub) ySub ≠
        Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hInnerNeStuck :
      __eo_mk_apply (Term.UOp UserOp.tuple) xSub ≠ Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  have hInnerMk :
      __eo_mk_apply (Term.UOp UserOp.tuple) xSub =
        Term.Apply (Term.UOp UserOp.tuple) xSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNeStuck
  have hOuterMk :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.tuple) xSub) ySub =
        Term.Apply (Term.Apply (Term.UOp UserOp.tuple) xSub) ySub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      rw [← hInnerMk]
      exact hOuterNeStuck)
  have hResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) y) xs ss bvs =
        Term.Apply (Term.Apply (Term.UOp UserOp.tuple) xSub) ySub := by
    rw [hSubstEq, hInnerMk, hOuterMk]
  have hArgsTrans := tuple_args_have_smt_translation_of_has_smt_translation hFTrans
  have hSubstFullTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) xSub) ySub) := by
    rw [← hResultEq]
    exact hSubstTrans
  have hSubstArgsTrans :=
    tuple_args_have_smt_translation_of_has_smt_translation hSubstFullTrans
  have hXEval := hRecX hArgsTrans.1 hSubstArgsTrans.1
  have hYEval := hRecY hArgsTrans.2 hSubstArgsTrans.2
  have hXTy :
      __smtx_typeof (__eo_to_smt xSub) =
        __smtx_typeof (__eo_to_smt x) :=
    smtx_typeof_eo_to_smt_eq_of_eval_eq hM hN xSub x
      hSubstArgsTrans.1 hArgsTrans.1 hXEval
  have hYTy :
      __smtx_typeof (__eo_to_smt ySub) =
        __smtx_typeof (__eo_to_smt y) :=
    smtx_typeof_eo_to_smt_eq_of_eval_eq hM hN ySub y
      hSubstArgsTrans.2 hArgsTrans.2 hYEval
  rw [hResultEq]
  change
    __smtx_model_eval M
        (__eo_to_smt_tuple_prepend (__eo_to_smt xSub)
          (__smtx_typeof (__eo_to_smt xSub)) (__eo_to_smt ySub)) =
      __smtx_model_eval N
        (__eo_to_smt_tuple_prepend (__eo_to_smt x)
          (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y))
  exact
    smtx_model_eval_eo_to_smt_tuple_prepend_cross_eq_of_eval_eq hGlobals
      (__eo_to_smt xSub) (__eo_to_smt x) (__eo_to_smt ySub) (__eo_to_smt y)
      (__smtx_typeof (__eo_to_smt xSub)) (__smtx_typeof (__eo_to_smt x))
      hXTy hYTy hXEval hYEval

theorem eo_to_smt_apply_apply_uop_generic_of_not_smt_binop
    {op : UserOp} {x y : Term}
    (hAnd : op ≠ UserOp.and)
    (hOr : op ≠ UserOp.or)
    (hImp : op ≠ UserOp.imp)
    (hXor : op ≠ UserOp.xor)
    (hEq : op ≠ UserOp.eq)
    (hPlus : op ≠ UserOp.plus)
    (hNeg : op ≠ UserOp.neg)
    (hMult : op ≠ UserOp.mult)
    (hLt : op ≠ UserOp.lt)
    (hLeq : op ≠ UserOp.leq)
    (hGt : op ≠ UserOp.gt)
    (hGeq : op ≠ UserOp.geq)
    (hDiv : op ≠ UserOp.div)
    (hMod : op ≠ UserOp.mod)
    (hSelect : op ≠ UserOp.select)
    (hDivisible : op ≠ UserOp.divisible)
    (hDivTotal : op ≠ UserOp.div_total)
    (hModTotal : op ≠ UserOp.mod_total)
    (hQdivTotal : op ≠ UserOp.qdiv_total)
    (hQdiv : op ≠ UserOp.qdiv)
    (hConcat : op ≠ UserOp.concat)
    (hBvand : op ≠ UserOp.bvand)
    (hBvor : op ≠ UserOp.bvor)
    (hBvnand : op ≠ UserOp.bvnand)
    (hBvnor : op ≠ UserOp.bvnor)
    (hBvxor : op ≠ UserOp.bvxor)
    (hBvxnor : op ≠ UserOp.bvxnor)
    (hBvcomp : op ≠ UserOp.bvcomp)
    (hBvadd : op ≠ UserOp.bvadd)
    (hBvmul : op ≠ UserOp.bvmul)
    (hBvudiv : op ≠ UserOp.bvudiv)
    (hBvurem : op ≠ UserOp.bvurem)
    (hBvsub : op ≠ UserOp.bvsub)
    (hBvsdiv : op ≠ UserOp.bvsdiv)
    (hBvsrem : op ≠ UserOp.bvsrem)
    (hBvsmod : op ≠ UserOp.bvsmod)
    (hBvshl : op ≠ UserOp.bvshl)
    (hBvlshr : op ≠ UserOp.bvlshr)
    (hBvashr : op ≠ UserOp.bvashr)
    (hBvult : op ≠ UserOp.bvult)
    (hBvule : op ≠ UserOp.bvule)
    (hBvugt : op ≠ UserOp.bvugt)
    (hBvuge : op ≠ UserOp.bvuge)
    (hBvslt : op ≠ UserOp.bvslt)
    (hBvsle : op ≠ UserOp.bvsle)
    (hBvsgt : op ≠ UserOp.bvsgt)
    (hBvsge : op ≠ UserOp.bvsge)
    (hBvuaddo : op ≠ UserOp.bvuaddo)
    (hBvsaddo : op ≠ UserOp.bvsaddo)
    (hBvumulo : op ≠ UserOp.bvumulo)
    (hBvsmulo : op ≠ UserOp.bvsmulo)
    (hBvusubo : op ≠ UserOp.bvusubo)
    (hBvssubo : op ≠ UserOp.bvssubo)
    (hBvsdivo : op ≠ UserOp.bvsdivo)
    (hBvultbv : op ≠ UserOp.bvultbv)
    (hBvsltbv : op ≠ UserOp.bvsltbv)
    (hFromBools : op ≠ UserOp._at_from_bools)
    (hStringsDeqDiff : op ≠ UserOp._at_strings_deq_diff)
    (hStringsStoiResult : op ≠ UserOp._at_strings_stoi_result)
    (hStrConcat : op ≠ UserOp.str_concat)
    (hStrContains : op ≠ UserOp.str_contains)
    (hStrAt : op ≠ UserOp.str_at)
    (hStrPrefixof : op ≠ UserOp.str_prefixof)
    (hStrSuffixof : op ≠ UserOp.str_suffixof)
    (hStrLt : op ≠ UserOp.str_lt)
    (hStrLeq : op ≠ UserOp.str_leq)
    (hReRange : op ≠ UserOp.re_range)
    (hReConcat : op ≠ UserOp.re_concat)
    (hReInter : op ≠ UserOp.re_inter)
    (hReUnion : op ≠ UserOp.re_union)
    (hReDiff : op ≠ UserOp.re_diff)
    (hStrInRe : op ≠ UserOp.str_in_re)
    (hSeqNth : op ≠ UserOp.seq_nth)
    (hSetUnion : op ≠ UserOp.set_union)
    (hSetInter : op ≠ UserOp.set_inter)
    (hSetMinus : op ≠ UserOp.set_minus)
    (hSetMember : op ≠ UserOp.set_member)
    (hSetSubset : op ≠ UserOp.set_subset)
    (hStringsItosResult : op ≠ UserOp._at_strings_itos_result)
    (hStringsNumOccur : op ≠ UserOp._at_strings_num_occur)
    (hStringsNumOccurRe : op ≠ UserOp._at_strings_num_occur_re)
    (hArrayDeqDiff : op ≠ UserOp._at_array_deq_diff)
    (hSetsDeqDiff : op ≠ UserOp._at_sets_deq_diff)
    (hTuple : op ≠ UserOp.tuple)
    (hSetInsert : op ≠ UserOp.set_insert)
    (hForall : op ≠ UserOp.forall)
    (hExists : op ≠ UserOp.exists) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y) =
      SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.UOp op) x)) (__eo_to_smt y) := by
  cases op <;> try rfl
  all_goals
    exfalso
    first
    | exact hAnd rfl
    | exact hOr rfl
    | exact hImp rfl
    | exact hXor rfl
    | exact hEq rfl
    | exact hPlus rfl
    | exact hNeg rfl
    | exact hMult rfl
    | exact hLt rfl
    | exact hLeq rfl
    | exact hGt rfl
    | exact hGeq rfl
    | exact hDiv rfl
    | exact hMod rfl
    | exact hSelect rfl
    | exact hDivisible rfl
    | exact hDivTotal rfl
    | exact hModTotal rfl
    | exact hQdivTotal rfl
    | exact hQdiv rfl
    | exact hConcat rfl
    | exact hBvand rfl
    | exact hBvor rfl
    | exact hBvnand rfl
    | exact hBvnor rfl
    | exact hBvxor rfl
    | exact hBvxnor rfl
    | exact hBvcomp rfl
    | exact hBvadd rfl
    | exact hBvmul rfl
    | exact hBvudiv rfl
    | exact hBvurem rfl
    | exact hBvsub rfl
    | exact hBvsdiv rfl
    | exact hBvsrem rfl
    | exact hBvsmod rfl
    | exact hBvshl rfl
    | exact hBvlshr rfl
    | exact hBvashr rfl
    | exact hBvult rfl
    | exact hBvule rfl
    | exact hBvugt rfl
    | exact hBvuge rfl
    | exact hBvslt rfl
    | exact hBvsle rfl
    | exact hBvsgt rfl
    | exact hBvsge rfl
    | exact hBvuaddo rfl
    | exact hBvsaddo rfl
    | exact hBvumulo rfl
    | exact hBvsmulo rfl
    | exact hBvusubo rfl
    | exact hBvssubo rfl
    | exact hBvsdivo rfl
    | exact hBvultbv rfl
    | exact hBvsltbv rfl
    | exact hFromBools rfl
    | exact hStringsDeqDiff rfl
    | exact hStringsStoiResult rfl
    | exact hStrConcat rfl
    | exact hStrContains rfl
    | exact hStrAt rfl
    | exact hStrPrefixof rfl
    | exact hStrSuffixof rfl
    | exact hStrLt rfl
    | exact hStrLeq rfl
    | exact hReRange rfl
    | exact hReConcat rfl
    | exact hReInter rfl
    | exact hReUnion rfl
    | exact hReDiff rfl
    | exact hStrInRe rfl
    | exact hSeqNth rfl
    | exact hSetUnion rfl
    | exact hSetInter rfl
    | exact hSetMinus rfl
    | exact hSetMember rfl
    | exact hSetSubset rfl
    | exact hStringsItosResult rfl
    | exact hStringsNumOccur rfl
    | exact hStringsNumOccurRe rfl
    | exact hArrayDeqDiff rfl
    | exact hSetsDeqDiff rfl
    | exact hTuple rfl
    | exact hSetInsert rfl
    | exact hForall rfl
    | exact hExists rfl

theorem substFalse_eval_binary_uop_generic_apply
    (op : UserOp) (x1 a xs ss bvs : Term) {M N : SmtModel}
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x1 ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hOrigTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x1) a) =
        SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.UOp op) x1))
          (__eo_to_smt a))
    (hSubstTranslate :
      __eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
        SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs)))
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)))
    (hFTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x1) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x1) a) xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename) (Term.UOp op) xs ss bvs =
        Term.UOp op)
    (hGlobals : model_agrees_on_globals M N)
    (hRecHead :
      eoHasSmtTranslation (Term.Apply (Term.UOp op) x1) →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.UOp op) x1) xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename)
                (Term.Apply (Term.UOp op) x1) xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp op) x1)))
    (hRecArg :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.UOp op) x1) a) xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x1) a)) := by
  have hOrigTy :
      generic_apply_type
        (__eo_to_smt (Term.Apply (Term.UOp op) x1))
        (__eo_to_smt a) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hOrigNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.UOp op) x1))
          (__eo_to_smt a)) := by
    unfold term_has_non_none_type
    rw [← hOrigTranslate]
    exact hFTrans
  rcases apply_args_have_smt_translation_of_non_none hOrigTy hOrigNN with
    ⟨hHeadTrans, hATrans⟩
  have hSubstHead :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) x1) xs ss bvs =
        __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.UOp op) x1 xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [hHeadSub] using hEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x1) a) xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Apply (Term.UOp op) x1) a xs ss bvs hisr hxs hss hbvs
        hNotBinderOuter
    rw [hEq, hSubstHead]
  have hOuterNeStuck :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) ≠
        Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hInnerNeStuck :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  have hInnerMk :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) =
        Term.Apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNeStuck
  have hOuterMk :
      __eo_mk_apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) =
        Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      rw [← hInnerMk]
      exact hOuterNeStuck)
  have hResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x1) a) xs ss bvs =
        Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) := by
    rw [hSubstEq, hInnerMk, hOuterMk]
  have hSubstTy :
      generic_apply_type
        (__eo_to_smt
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs)))
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hSubstAppTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) := by
    rw [← hResultEq]
    exact hSubstTrans
  have hSubstNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs)))
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs))) := by
    unfold term_has_non_none_type
    rw [← hSubstTranslate]
    exact hSubstAppTrans
  rcases apply_args_have_smt_translation_of_non_none hSubstTy hSubstNN with
    ⟨hSubstHeadTrans, hSubstATrans⟩
  have hHeadEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))) =
        __smtx_model_eval N
          (__eo_to_smt (Term.Apply (Term.UOp op) x1)) := by
    simpa [hSubstHead, hInnerMk] using
      hRecHead hHeadTrans
        (by
          rw [hSubstHead, hInnerMk]
          exact hSubstHeadTrans)
  have hArgEval := hRecArg hATrans hSubstATrans
  rw [hResultEq, hOrigTranslate, hSubstTranslate]
  exact
    smtx_model_eval_apply_cross_eq_of_eval_eq hGlobals
      (generic_apply_eval_of_non_datatype_head
        (by
          intro s d i j hSel
          exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
        (by
          intro s d i hTester
          exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester))
      (generic_apply_eval_of_non_datatype_head
        (by
          intro s d i j hSel
          exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
        (by
          intro s d i hTester
          exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester))
      hHeadEval hArgEval

theorem eo_to_smt_apply_apply_apply_uop_generic_of_not_smt_triop
    {op : UserOp} {x y z : Term}
    (hIte : op ≠ UserOp.ite)
    (hStore : op ≠ UserOp.store)
    (hBvite : op ≠ UserOp.bvite)
    (hStrSubstr : op ≠ UserOp.str_substr)
    (hStrIndexof : op ≠ UserOp.str_indexof)
    (hStrUpdate : op ≠ UserOp.str_update)
    (hStrReplace : op ≠ UserOp.str_replace)
    (hStrReplaceAll : op ≠ UserOp.str_replace_all)
    (hStrReplaceRe : op ≠ UserOp.str_replace_re)
    (hStrReplaceReAll : op ≠ UserOp.str_replace_re_all)
    (hStrIndexofRe : op ≠ UserOp.str_indexof_re)
    (hStringsOccurIndex : op ≠ UserOp._at_strings_occur_index)
    (hStringsOccurIndexRe : op ≠ UserOp._at_strings_occur_index_re) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) =
      SmtTerm.Apply
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y))
        (__eo_to_smt z) := by
  cases op <;> try rfl
  case ite => exact False.elim (hIte rfl)
  case store => exact False.elim (hStore rfl)
  case bvite => exact False.elim (hBvite rfl)
  case str_substr => exact False.elim (hStrSubstr rfl)
  case str_indexof => exact False.elim (hStrIndexof rfl)
  case str_update => exact False.elim (hStrUpdate rfl)
  case str_replace => exact False.elim (hStrReplace rfl)
  case str_replace_all => exact False.elim (hStrReplaceAll rfl)
  case str_replace_re => exact False.elim (hStrReplaceRe rfl)
  case str_replace_re_all => exact False.elim (hStrReplaceReAll rfl)
  case str_indexof_re => exact False.elim (hStrIndexofRe rfl)
  case _at_strings_occur_index =>
    exact False.elim (hStringsOccurIndex rfl)
  case _at_strings_occur_index_re =>
    exact False.elim (hStringsOccurIndexRe rfl)

theorem substFalse_eval_ternary_uop_generic_apply
    (op : UserOp) (x1 x2 a xs ss bvs : Term) {M N : SmtModel}
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.Apply (Term.UOp op) x1) x2 ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hOrigTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a) =
        SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x1) x2))
          (__eo_to_smt a))
    (hSubstTranslate :
      __eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp op)
                (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
              (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
        SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp op)
                (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
              (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs)))
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)))
    (hFTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a)
          xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename) (Term.UOp op) xs ss bvs =
        Term.UOp op)
    (hGlobals : model_agrees_on_globals M N)
    (hRecHead :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x1) x2) →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.UOp op) x1) x2) xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename)
                (Term.Apply (Term.Apply (Term.UOp op) x1) x2) xs ss bvs)) =
          __smtx_model_eval N
            (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x1) x2)))
    (hRecArg :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a)
            xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a)) := by
  have hOrigTy :
      generic_apply_type
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x1) x2))
        (__eo_to_smt a) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hOrigNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x1) x2))
          (__eo_to_smt a)) := by
    unfold term_has_non_none_type
    rw [← hOrigTranslate]
    exact hFTrans
  rcases apply_args_have_smt_translation_of_non_none hOrigTy hOrigNN with
    ⟨hHeadTrans, hATrans⟩
  have hSubstInner :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) x1) xs ss bvs =
        __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.UOp op) x1 xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [hHeadSub] using hEq
  have hNotBinderMiddle :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x1 ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
    intro q v vs hEq
    cases hEq
    by_cases hForall : op = UserOp.forall
    · subst op
      exact false_of_apply_apply_apply_forall_has_smt_translation hFTrans
    · by_cases hExists : op = UserOp.exists
      · subst op
        exact false_of_apply_apply_apply_exists_has_smt_translation hFTrans
      · exact
          apply_apply_uop_arg_not_list_of_nonquantifier_has_smt_translation
            hForall hExists hHeadTrans v vs rfl
  have hSubstHead :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x1) x2) xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Apply (Term.UOp op) x1) x2 xs ss bvs hisr hxs hss hbvs
        hNotBinderMiddle
    rw [hEq, hSubstInner]
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a)
          xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a xs ss bvs
        hisr hxs hss hbvs hNotBinderOuter
    rw [hEq, hSubstHead]
  have hOuterNeStuck :
      __eo_mk_apply
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) ≠
        Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hMidNeStuck :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs) ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  have hInnerNeStuck :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hMidNeStuck
  have hInnerMk :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) =
        Term.Apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNeStuck
  have hMidMk :
      __eo_mk_apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs) =
        Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      rw [← hInnerMk]
      exact hMidNeStuck)
  have hOuterMk :
      __eo_mk_apply
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) =
        Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      rw [← hMidMk, ← hInnerMk]
      exact hOuterNeStuck)
  have hHeadResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x1) x2) xs ss bvs =
        Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs) := by
    rw [hSubstHead, hInnerMk, hMidMk]
  have hResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a)
          xs ss bvs =
        Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) := by
    rw [hSubstEq, hInnerMk, hMidMk, hOuterMk]
  have hSubstTy :
      generic_apply_type
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs)))
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hSubstAppTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) := by
    rw [← hResultEq]
    exact hSubstTrans
  have hSubstNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp op)
                (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
              (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs)))
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs))) := by
    unfold term_has_non_none_type
    rw [← hSubstTranslate]
    exact hSubstAppTrans
  rcases apply_args_have_smt_translation_of_non_none hSubstTy hSubstNN with
    ⟨hSubstHeadTrans, hSubstATrans⟩
  have hHeadEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp op)
                (__substitute_simul_rec (Term.Boolean isRename) x1 xs ss bvs))
              (__substitute_simul_rec (Term.Boolean isRename) x2 xs ss bvs))) =
        __smtx_model_eval N
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x1) x2)) := by
    simpa [hHeadResultEq] using
      hRecHead hHeadTrans
        (by
          rw [hHeadResultEq]
          exact hSubstHeadTrans)
  have hArgEval := hRecArg hATrans hSubstATrans
  rw [hResultEq, hOrigTranslate, hSubstTranslate]
  exact
    smtx_model_eval_apply_cross_eq_of_eval_eq hGlobals
      (generic_apply_eval_of_non_datatype_head
        (by
          intro s d i j hSel
          exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
        (by
          intro s d i hTester
          exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester))
      (generic_apply_eval_of_non_datatype_head
        (by
          intro s d i j hSel
          exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
        (by
          intro s d i hTester
          exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester))
      hHeadEval hArgEval

theorem substFalse_eval_generic_apply
    (f a xs ss bvs : Term) {M N : SmtModel}
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotBinder :
      ∀ q v vs,
        f ≠ Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hOrigTranslate :
      __eo_to_smt (Term.Apply f a) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a))
    (hSubstTranslate :
      __eo_to_smt
          (Term.Apply
            (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
        SmtTerm.Apply
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs))
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)))
    (hOrigTy :
      generic_apply_type (__eo_to_smt f) (__eo_to_smt a))
    (hSubstTy :
      generic_apply_type
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs))
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)))
    (hOrigEval :
      generic_apply_eval (__eo_to_smt f) (__eo_to_smt a))
    (hSubstEval :
      generic_apply_eval
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs))
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)))
    (hFTrans : eoHasSmtTranslation (Term.Apply f a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename) (Term.Apply f a) xs ss bvs))
    (hGlobals : model_agrees_on_globals M N)
    (hRecHead :
      eoHasSmtTranslation f →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt f))
    (hRecArg :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename) (Term.Apply f a) xs ss bvs)) =
      __smtx_model_eval N (__eo_to_smt (Term.Apply f a)) := by
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename) (Term.Apply f a) xs ss bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) := by
    exact
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        f a xs ss bvs hisr hxs hss hbvs hNotBinder
  have hOuterNeStuck :
      __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) ≠
        Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hMk :
      __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) =
        Term.Apply
          (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hOuterNeStuck
  have hResultEq :
      __substitute_simul_rec (Term.Boolean isRename) (Term.Apply f a) xs ss bvs =
        Term.Apply
          (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) := by
    rw [hSubstEq, hMk]
  have hOrigNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a)) := by
    unfold term_has_non_none_type
    rw [← hOrigTranslate]
    exact hFTrans
  rcases apply_args_have_smt_translation_of_non_none hOrigTy hOrigNN with
    ⟨hFHeadTrans, hATrans⟩
  have hSubstAppTrans :
      eoHasSmtTranslation
        (Term.Apply
          (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs)
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) := by
    rw [← hResultEq]
    exact hSubstTrans
  have hSubstNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean isRename) f xs ss bvs))
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs))) := by
    unfold term_has_non_none_type
    rw [← hSubstTranslate]
    exact hSubstAppTrans
  rcases apply_args_have_smt_translation_of_non_none hSubstTy hSubstNN with
    ⟨hSubstHeadTrans, hSubstATrans⟩
  rw [hResultEq, hOrigTranslate, hSubstTranslate]
  exact
    smtx_model_eval_apply_cross_eq_of_eval_eq hGlobals
      hSubstEval hOrigEval
      (hRecHead hFHeadTrans hSubstHeadTrans)
      (hRecArg hATrans hSubstATrans)

theorem substFalse_eval_binary_uop1_update
    (idx x y xs ss bvs : Term) {M N : SmtModel}
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.UOp1 UserOp1.update idx) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) x) y))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) x) y)
          xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp1 UserOp1.update idx) xs ss bvs =
        Term.UOp1 UserOp1.update idx)
    (hGlobals : model_agrees_on_globals M N)
    (hRecX :
      eoHasSmtTranslation x →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt x))
    (hRecY :
      eoHasSmtTranslation y →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt y)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) x) y)
            xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) x) y)) := by
  have hArgsTrans :=
    update_index_sel_and_args_have_smt_translation hFTrans
  have hSubstInner :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.update idx) x) xs ss bvs =
        __eo_mk_apply (Term.UOp1 UserOp1.update idx)
          (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.UOp1 UserOp1.update idx) x xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [hHeadSub] using hEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) x) y)
          xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp1 UserOp1.update idx)
            (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Apply (Term.UOp1 UserOp1.update idx) x) y xs ss bvs
        hisr hxs hss hbvs hNotBinderOuter
    rw [hEq, hSubstInner]
  have hOuterNeStuck :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp1 UserOp1.update idx)
            (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs) ≠
        Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hInnerNeStuck :
      __eo_mk_apply (Term.UOp1 UserOp1.update idx)
          (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs) ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  have hInnerMk :
      __eo_mk_apply (Term.UOp1 UserOp1.update idx)
          (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs) =
        Term.Apply (Term.UOp1 UserOp1.update idx)
          (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNeStuck
  have hOuterMk :
      __eo_mk_apply
          (Term.Apply (Term.UOp1 UserOp1.update idx)
            (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs) =
        Term.Apply
          (Term.Apply (Term.UOp1 UserOp1.update idx)
            (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      rw [← hInnerMk]
      exact hOuterNeStuck)
  have hResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) x) y)
          xs ss bvs =
        Term.Apply
          (Term.Apply (Term.UOp1 UserOp1.update idx)
            (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs) := by
    rw [hSubstEq, hInnerMk, hOuterMk]
  have hSubstFullTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp1 UserOp1.update idx)
            (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs)) := by
    rw [← hResultEq]
    exact hSubstTrans
  have hSubstArgsTrans :=
    update_index_sel_and_args_have_smt_translation hSubstFullTrans
  have hXEval :=
    hRecX hArgsTrans.2.1 hSubstArgsTrans.2.1
  have hYEval :=
    hRecY hArgsTrans.2.2 hSubstArgsTrans.2.2
  rw [hResultEq]
  change
    __smtx_model_eval M
        (__eo_to_smt_updater (__eo_to_smt idx)
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs))
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs))) =
      __smtx_model_eval N
        (__eo_to_smt_updater (__eo_to_smt idx) (__eo_to_smt x) (__eo_to_smt y))
  exact
    smtx_model_eval_eo_to_smt_updater_cross_eq_of_eval_eq hGlobals
      (__eo_to_smt idx)
      (__eo_to_smt
        (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs))
      (__eo_to_smt x)
      (__eo_to_smt
        (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs))
      (__eo_to_smt y)
      hXEval hYEval

theorem substFalse_eval_binary_uop1_tuple_update
    (idx x y xs ss bvs : Term) {M N : SmtModel}
    (hM : model_wf M) (hN : model_wf N)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y)
          xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp1 UserOp1.tuple_update idx) xs ss bvs =
        Term.UOp1 UserOp1.tuple_update idx)
    (hGlobals : model_agrees_on_globals M N)
    (hRecX :
      eoHasSmtTranslation x →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt x))
    (hRecY :
      eoHasSmtTranslation y →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt y)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y)
            xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y)) := by
  have hArgsTrans :=
    tuple_update_index_nat_valid_and_args_have_smt_translation hFTrans
  have hSubstInner :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) xs ss bvs =
        __eo_mk_apply (Term.UOp1 UserOp1.tuple_update idx)
          (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.UOp1 UserOp1.tuple_update idx) x xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [hHeadSub] using hEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y)
          xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp1 UserOp1.tuple_update idx)
            (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y xs ss bvs
        hisr hxs hss hbvs hNotBinderOuter
    rw [hEq, hSubstInner]
  have hOuterNeStuck :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp1 UserOp1.tuple_update idx)
            (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs) ≠
        Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hInnerNeStuck :
      __eo_mk_apply (Term.UOp1 UserOp1.tuple_update idx)
          (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs) ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  have hInnerMk :
      __eo_mk_apply (Term.UOp1 UserOp1.tuple_update idx)
          (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs) =
        Term.Apply (Term.UOp1 UserOp1.tuple_update idx)
          (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNeStuck
  have hOuterMk :
      __eo_mk_apply
          (Term.Apply (Term.UOp1 UserOp1.tuple_update idx)
            (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs) =
        Term.Apply
          (Term.Apply (Term.UOp1 UserOp1.tuple_update idx)
            (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      rw [← hInnerMk]
      exact hOuterNeStuck)
  have hResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) x) y)
          xs ss bvs =
        Term.Apply
          (Term.Apply (Term.UOp1 UserOp1.tuple_update idx)
            (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs) := by
    rw [hSubstEq, hInnerMk, hOuterMk]
  have hSubstFullTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp1 UserOp1.tuple_update idx)
            (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs))
          (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs)) := by
    rw [← hResultEq]
    exact hSubstTrans
  have hSubstArgsTrans :=
    tuple_update_index_nat_valid_and_args_have_smt_translation hSubstFullTrans
  have hXEval :=
    hRecX hArgsTrans.2.1 hSubstArgsTrans.2.1
  have hYEval :=
    hRecY hArgsTrans.2.2 hSubstArgsTrans.2.2
  have hXTy :
      __smtx_typeof
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs)) =
        __smtx_typeof (__eo_to_smt x) :=
    smtx_typeof_eo_to_smt_eq_of_eval_eq hM hN
      (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs) x
      hSubstArgsTrans.2.1 hArgsTrans.2.1 hXEval
  rw [hResultEq]
  change
    __smtx_model_eval M
        (__eo_to_smt_tuple_update
          (__smtx_typeof
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs)))
          (__eo_to_smt idx)
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs))
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs))) =
      __smtx_model_eval N
        (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt x))
          (__eo_to_smt idx) (__eo_to_smt x) (__eo_to_smt y))
  rw [hXTy]
  exact
    smtx_model_eval_eo_to_smt_tuple_update_cross_eq_of_eval_eq hGlobals
      (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt idx)
      (__eo_to_smt
        (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs))
      (__eo_to_smt x)
      (__eo_to_smt
        (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs))
      (__eo_to_smt y)
      hXEval hYEval

theorem eo_to_smt_apply_apply_uop1_generic_of_not_update_tuple_update
    {op : UserOp1} {idx x y : Term}
    (hUpdate : op ≠ UserOp1.update)
    (hTupleUpdate : op ≠ UserOp1.tuple_update) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) =
      SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.UOp1 op idx) x))
        (__eo_to_smt y) := by
  cases op <;> try rfl
  · exact False.elim (hUpdate rfl)
  · exact False.elim (hTupleUpdate rfl)

theorem substFalse_eval_binary_uop1_generic_apply
    (op : UserOp1) (idx x y xs ss bvs : Term) {M N : SmtModel}
    (hM : model_wf M) (hN : model_wf N)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hUpdate : op ≠ UserOp1.update)
    (hTupleUpdate : op ≠ UserOp1.tuple_update)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.UOp1 op idx) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y)
          xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp1 op idx) xs ss bvs =
        Term.UOp1 op idx)
    (hGlobals : model_agrees_on_globals M N)
    (hRecX :
      eoHasSmtTranslation x →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt x))
    (hRecY :
      eoHasSmtTranslation y →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt y)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y)
            xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y)) := by
  let xSub := __substitute_simul_rec (Term.Boolean isRename) x xs ss bvs
  let ySub := __substitute_simul_rec (Term.Boolean isRename) y xs ss bvs
  have hSubstInner :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 op idx) x) xs ss bvs =
        __eo_mk_apply (Term.UOp1 op idx) xSub := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.UOp1 op idx) x xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [xSub, hHeadSub] using hEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y)
          xs ss bvs =
        __eo_mk_apply (__eo_mk_apply (Term.UOp1 op idx) xSub) ySub := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Apply (Term.UOp1 op idx) x) y xs ss bvs
        hisr hxs hss hbvs hNotBinderOuter
    rw [hEq, hSubstInner]
  have hOuterNeStuck :
      __eo_mk_apply (__eo_mk_apply (Term.UOp1 op idx) xSub) ySub ≠
        Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hInnerNeStuck :
      __eo_mk_apply (Term.UOp1 op idx) xSub ≠ Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  have hInnerMk :
      __eo_mk_apply (Term.UOp1 op idx) xSub =
        Term.Apply (Term.UOp1 op idx) xSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNeStuck
  have hOuterMk :
      __eo_mk_apply (Term.Apply (Term.UOp1 op idx) xSub) ySub =
        Term.Apply (Term.Apply (Term.UOp1 op idx) xSub) ySub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      rw [← hInnerMk]
      exact hOuterNeStuck)
  have hHeadResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 op idx) x) xs ss bvs =
        Term.Apply (Term.UOp1 op idx) xSub := by
    rw [hSubstInner, hInnerMk]
  have hResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y)
          xs ss bvs =
        Term.Apply (Term.Apply (Term.UOp1 op idx) xSub) ySub := by
    rw [hSubstEq, hInnerMk, hOuterMk]
  have hOrigTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.UOp1 op idx) x))
          (__eo_to_smt y) :=
    eo_to_smt_apply_apply_uop1_generic_of_not_update_tuple_update
      hUpdate hTupleUpdate
  have hSubstTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp1 op idx) xSub) ySub) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.UOp1 op idx) xSub))
          (__eo_to_smt ySub) :=
    eo_to_smt_apply_apply_uop1_generic_of_not_update_tuple_update
      hUpdate hTupleUpdate
  have hOrigTy :
      generic_apply_type
        (__eo_to_smt (Term.Apply (Term.UOp1 op idx) x))
        (__eo_to_smt y) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hOrigNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.UOp1 op idx) x))
          (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [← hOrigTranslate]
    exact hFTrans
  rcases apply_args_have_smt_translation_of_non_none hOrigTy hOrigNN with
    ⟨hHeadTrans, hYTrans⟩
  have hSubstTy :
      generic_apply_type
        (__eo_to_smt (Term.Apply (Term.UOp1 op idx) xSub))
        (__eo_to_smt ySub) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hSubstFullTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp1 op idx) xSub) ySub) := by
    rw [← hResultEq]
    exact hSubstTrans
  have hSubstNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.UOp1 op idx) xSub))
          (__eo_to_smt ySub)) := by
    unfold term_has_non_none_type
    rw [← hSubstTranslate]
    exact hSubstFullTrans
  rcases apply_args_have_smt_translation_of_non_none hSubstTy hSubstNN with
    ⟨hSubstHeadTrans, hSubstYTrans⟩
  have hHeadEval :
      __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp1 op idx) xSub)) =
        __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp1 op idx) x)) := by
    have hHeadEvalRaw :
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename)
                (Term.Apply (Term.UOp1 op idx) x) xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp1 op idx) x)) := by
      by_cases hTupleSelect : op = UserOp1.tuple_select
      · subst op
        exact
          substFalse_eval_unary_uop1_tuple_select idx x xs ss bvs hM hN
            hisr hxs hss hbvs hHeadTrans
            (by
              rw [hHeadResultEq]
              exact hSubstHeadTrans)
            (by simpa using hHeadSub)
            hGlobals hRecX
      · exact
          substFalse_eval_unary_uop1_nontuple_select op idx x xs ss bvs
            hisr hxs hss hbvs hTupleSelect hHeadTrans
            (by
              rw [hHeadResultEq]
              exact hSubstHeadTrans)
            hHeadSub hRecX
    simpa [hHeadResultEq] using hHeadEvalRaw
  have hYEval := hRecY hYTrans hSubstYTrans
  rw [hResultEq, hOrigTranslate, hSubstTranslate]
  exact
    smtx_model_eval_apply_cross_eq_of_eval_eq hGlobals
      (generic_apply_eval_of_non_datatype_head
        (by
          intro s d i j hSel
          exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
        (by
          intro s d i hTester
          exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester))
      (generic_apply_eval_of_non_datatype_head
        (by
          intro s d i j hSel
          exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
        (by
          intro s d i hTester
          exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester))
      hHeadEval hYEval

theorem eo_to_smt_apply_apply_atom_head_generic
    {g x y : Term}
    (hNotUOp : ∀ op, g ≠ Term.UOp op)
    (hNotUOp1 : ∀ op idx, g ≠ Term.UOp1 op idx)
    (hNotApply : ∀ f a, g ≠ Term.Apply f a) :
    __eo_to_smt (Term.Apply (Term.Apply g x) y) =
      SmtTerm.Apply (__eo_to_smt (Term.Apply g x)) (__eo_to_smt y) := by
  cases g <;> try rfl
  · exact False.elim (hNotUOp _ rfl)
  · exact False.elim (hNotUOp1 _ _ rfl)
  · exact False.elim (hNotApply _ _ rfl)

theorem eo_to_smt_apply_apply_generic_of_head_has_smt_translation
    (g x y : Term)
    (hG : eoHasSmtTranslation g) :
    __eo_to_smt (Term.Apply (Term.Apply g x) y) =
      SmtTerm.Apply (__eo_to_smt (Term.Apply g x)) (__eo_to_smt y) := by
  unfold eoHasSmtTranslation at hG
  cases g <;> try rfl
  case UOp op =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hG
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case UOp1 op idx =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hG
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> try rfl
      all_goals
        exfalso
        apply hG
        change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt a)) =
          SmtType.None
        simp [__smtx_typeof, __smtx_typeof_apply]
    case Apply h b =>
      cases h <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        all_goals
          exfalso
          apply hG
          exact
            TranslationProofs.typeof_apply_apply_none_head_eq
              (__eo_to_smt b) (__eo_to_smt a)

theorem eo_to_smt_apply_apply_apply_generic_of_head_has_smt_translation
    (g x y z : Term)
    (hG : eoHasSmtTranslation g) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.Apply g x) y) z) =
      SmtTerm.Apply
        (__eo_to_smt (Term.Apply (Term.Apply g x) y))
        (__eo_to_smt z) := by
  unfold eoHasSmtTranslation at hG
  cases g <;> try rfl
  case UOp op =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hG
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> try rfl
      all_goals
        exfalso
        apply hG
        exact TranslationProofs.typeof_apply_none_eq (__eo_to_smt a)

theorem eo_to_smt_apply_apply_apply_non_uop_head_generic
    {g x y z : Term}
    (hNotUOp : ∀ op, g ≠ Term.UOp op)
    (hNotApplyUOp : ∀ op a, g ≠ Term.Apply (Term.UOp op) a) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.Apply g x) y) z) =
      SmtTerm.Apply
        (__eo_to_smt (Term.Apply (Term.Apply g x) y))
        (__eo_to_smt z) := by
  cases g <;> try rfl
  case UOp op => exact False.elim (hNotUOp op rfl)
  case Apply f a =>
    cases f <;> try rfl
    case UOp op => exact False.elim (hNotApplyUOp op a rfl)

theorem eo_to_smt_apply_apply_apply_apply_head_generic
    (g x y z w : Term)
    (hStringsReplaceAllResult :
      g ≠ Term.UOp UserOp._at_strings_replace_all_result)
    (hStringsReplaceReAllResult :
      g ≠ Term.UOp UserOp._at_strings_replace_re_all_result) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.Apply g x) y) z) w) =
      SmtTerm.Apply
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply g x) y) z))
        (__eo_to_smt w) := by
  cases g <;> try rfl
  case UOp op =>
    cases op <;> try rfl
    all_goals
      exfalso
      first
      | exact hStringsReplaceAllResult rfl
      | exact hStringsReplaceReAllResult rfl

theorem substFalse_eval_binary_atom_head_generic_apply
    (g x y xs ss bvs : Term) {M N : SmtModel}
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotUOp : ∀ op, g ≠ Term.UOp op)
    (hNotUOp1 : ∀ op idx, g ≠ Term.UOp1 op idx)
    (hNotApply : ∀ f a, g ≠ Term.Apply f a)
    (hNotVar : ∀ s S, g ≠ Term.Var s S)
    (hNotStuck : g ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply g x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply g x) y))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply g x) y) xs ss bvs))
    (hGlobals : model_agrees_on_globals M N)
    (hRecHead :
      eoHasSmtTranslation (Term.Apply g x) →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply g x) xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename)
                (Term.Apply g x) xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt (Term.Apply g x)))
    (hRecY :
      eoHasSmtTranslation y →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt y)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply g x) y) xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt (Term.Apply (Term.Apply g x) y)) := by
  let xSub := __substitute_simul_rec (Term.Boolean isRename) x xs ss bvs
  let ySub := __substitute_simul_rec (Term.Boolean isRename) y xs ss bvs
  have hSubstInnerRaw :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply g x) xs ss bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename) g xs ss bvs) xSub := by
    simpa [xSub] using
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        g x xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; exact hNotApply _ _ hEq)
  have hSubstOuterRaw :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply g x) y) xs ss bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename) (Term.Apply g x) xs ss bvs)
          ySub := by
    simpa [ySub] using
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Apply g x) y xs ss bvs hisr hxs hss hbvs hNotBinderOuter
  have hOuterNeStuck :
      __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename) (Term.Apply g x) xs ss bvs)
          ySub ≠ Term.Stuck := by
    rw [← hSubstOuterRaw]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hInnerNeStuck :
      __substitute_simul_rec (Term.Boolean isRename) (Term.Apply g x) xs ss bvs ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  have hGSubNe :
      __substitute_simul_rec (Term.Boolean isRename) g xs ss bvs ≠ Term.Stuck := by
    rw [hSubstInnerRaw] at hInnerNeStuck
    exact instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hInnerNeStuck
  have hGSub :
      __substitute_simul_rec (Term.Boolean isRename) g xs ss bvs = g :=
    substitute_simul_rec_atom_eq_self_of_ne_stuck g xs ss bvs
      hXsEnv hBvsEnv hSsTrans
      hNotApply hNotVar hNotStuck hGSubNe
  have hSubstInner :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply g x) xs ss bvs =
        __eo_mk_apply g xSub := by
    rw [hSubstInnerRaw, hGSub]
  have hInnerMk :
      __eo_mk_apply g xSub = Term.Apply g xSub := by
    refine instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ ?_
    rw [← hSubstInner]
    exact hInnerNeStuck
  have hHeadResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply g x) xs ss bvs =
        Term.Apply g xSub := by
    rw [hSubstInner, hInnerMk]
  have hOrigTranslate :
      __eo_to_smt (Term.Apply (Term.Apply g x) y) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply g x)) (__eo_to_smt y) :=
    eo_to_smt_apply_apply_atom_head_generic hNotUOp hNotUOp1 hNotApply
  have hSubstTranslate :
      __eo_to_smt
          (Term.Apply
            (__substitute_simul_rec (Term.Boolean isRename) (Term.Apply g x) xs ss bvs)
            ySub) =
        SmtTerm.Apply
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean isRename) (Term.Apply g x) xs ss bvs))
          (__eo_to_smt ySub) := by
    rw [hHeadResultEq]
    exact eo_to_smt_apply_apply_atom_head_generic hNotUOp hNotUOp1 hNotApply
  have hOrigTy :
      generic_apply_type (__eo_to_smt (Term.Apply g x)) (__eo_to_smt y) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hSubstTy :
      generic_apply_type
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename) (Term.Apply g x) xs ss bvs))
        (__eo_to_smt ySub) := by
    rw [hHeadResultEq]
    exact generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hOrigEval :
      generic_apply_eval (__eo_to_smt (Term.Apply g x)) (__eo_to_smt y) :=
    generic_apply_eval_of_non_datatype_head
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hSubstEval :
      generic_apply_eval
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename) (Term.Apply g x) xs ss bvs))
        (__eo_to_smt ySub) := by
    rw [hHeadResultEq]
    exact generic_apply_eval_of_non_datatype_head
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  exact
    substFalse_eval_generic_apply (Term.Apply g x) y xs ss bvs
      hisr hxs hss hbvs hNotBinderOuter hOrigTranslate hSubstTranslate
      hOrigTy hSubstTy hOrigEval hSubstEval hFTrans hSubstTrans hGlobals
      hRecHead hRecY

theorem eo_to_smt_apply_atom_head_generic
    {g a : Term}
    (hNotUOp : ∀ op, g ≠ Term.UOp op)
    (hNotUOp1 : ∀ op idx, g ≠ Term.UOp1 op idx)
    (hNotUOp2 : ∀ op i j, g ≠ Term.UOp2 op i j)
    (hNotUOp3 : ∀ op i j k, g ≠ Term.UOp3 op i j k)
    (hNotApply : ∀ f x, g ≠ Term.Apply f x) :
    __eo_to_smt (Term.Apply g a) =
      SmtTerm.Apply (__eo_to_smt g) (__eo_to_smt a) := by
  cases g with
  | UOp op => exact False.elim (hNotUOp op rfl)
  | UOp1 op idx => exact False.elim (hNotUOp1 op idx rfl)
  | UOp2 op i j => exact False.elim (hNotUOp2 op i j rfl)
  | UOp3 op i j k => exact False.elim (hNotUOp3 op i j k rfl)
  | Apply f x => exact False.elim (hNotApply f x rfl)
  | _ => rfl

def instantiate_uopHasUnarySmtTranslation : UserOp -> Bool
  | UserOp.not
  | UserOp.distinct
  | UserOp._at_purify
  | UserOp.to_real
  | UserOp.to_int
  | UserOp.is_int
  | UserOp.abs
  | UserOp.__eoo_neg_2
  | UserOp.int_pow2
  | UserOp.int_log2
  | UserOp.int_ispow2
  | UserOp._at_int_div_by_zero
  | UserOp._at_mod_by_zero
  | UserOp._at_bvsize
  | UserOp.bvnot
  | UserOp.bvneg
  | UserOp.bvnego
  | UserOp.bvredand
  | UserOp.bvredor
  | UserOp.str_len
  | UserOp.str_rev
  | UserOp.str_to_lower
  | UserOp.str_to_upper
  | UserOp.str_to_code
  | UserOp.str_from_code
  | UserOp.str_is_digit
  | UserOp.str_to_int
  | UserOp.str_from_int
  | UserOp.str_to_re
  | UserOp._at_strings_stoi_non_digit
  | UserOp.re_mult
  | UserOp.re_plus
  | UserOp.re_opt
  | UserOp.re_comp
  | UserOp.seq_unit
  | UserOp.set_singleton
  | UserOp.set_choose
  | UserOp.set_is_empty
  | UserOp.set_is_singleton
  | UserOp._at_div_by_zero
  | UserOp.ubv_to_int
  | UserOp.sbv_to_int => true
  | _ => false

theorem instantiate_typeof_apply_none_head_eq_none
    (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply SmtTerm.None x) = SmtType.None := by
  have hGeneric : generic_apply_type SmtTerm.None x :=
    generic_apply_type_of_non_datatype_head
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric]
  simp [__smtx_typeof_apply]

theorem instantiate_typeof_apply_reglan_head_eq_none
    (f x : SmtTerm)
    (hF : __smtx_typeof f = SmtType.RegLan)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    __smtx_typeof (SmtTerm.Apply f x) = SmtType.None := by
  have hGeneric : generic_apply_type f x :=
    generic_apply_type_of_non_datatype_head hSel hTester
  rw [hGeneric, hF]
  rfl

theorem instantiate_typeof_apply_tuple_unit_head_eq_none
    (x : SmtTerm) :
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.DtCons (native_string_lit "@Tuple")
            (__eo_to_smt_tuple_decl
              (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)) 0) x) =
      SmtType.None := by
  have hGeneric :
      generic_apply_type
        (SmtTerm.DtCons (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl
            (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)) 0) x :=
    generic_apply_type_of_non_datatype_head
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric]
  simp [__eo_to_smt_tuple_decl,
    TranslationProofs.smtx_typeof_tuple_unit_translation]
  rfl

theorem instantiate_uop_apply_typeof_none_of_not_unary_smt_translation
    (op : UserOp) (x : Term) :
    instantiate_uopHasUnarySmtTranslation op = false ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) x)) =
      SmtType.None := by
  intro hUnary
  cases op <;>
    simp [instantiate_uopHasUnarySmtTranslation] at hUnary
  case re_allchar =>
    exact instantiate_typeof_apply_reglan_head_eq_none
      SmtTerm.re_allchar (__eo_to_smt x)
      (by unfold __smtx_typeof; rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  case re_none =>
    exact instantiate_typeof_apply_reglan_head_eq_none
      SmtTerm.re_none (__eo_to_smt x)
      (by unfold __smtx_typeof; rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  case re_all =>
    exact instantiate_typeof_apply_reglan_head_eq_none
      SmtTerm.re_all (__eo_to_smt x)
      (by unfold __smtx_typeof; rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  case tuple_unit =>
    exact instantiate_typeof_apply_tuple_unit_head_eq_none (__eo_to_smt x)
  all_goals
    change
      __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) =
        SmtType.None
    exact instantiate_typeof_apply_none_head_eq_none (__eo_to_smt x)

theorem instantiate_uop_apply_typeof_none_of_not_unary_special
    (op : UserOp) (x : Term)
    (hNot : Term.UOp op ≠ Term.UOp UserOp.not)
    (hDistinct : op ≠ UserOp.distinct)
    (hToReal : Term.UOp op ≠ Term.UOp UserOp.to_real)
    (hToInt : Term.UOp op ≠ Term.UOp UserOp.to_int)
    (hIsInt : Term.UOp op ≠ Term.UOp UserOp.is_int)
    (hAbs : Term.UOp op ≠ Term.UOp UserOp.abs)
    (hUneg : Term.UOp op ≠ Term.UOp UserOp.__eoo_neg_2)
    (hPow2 : Term.UOp op ≠ Term.UOp UserOp.int_pow2)
    (hLog2 : Term.UOp op ≠ Term.UOp UserOp.int_log2)
    (hPurify : Term.UOp op ≠ Term.UOp UserOp._at_purify)
    (hIntIspow2 : Term.UOp op ≠ Term.UOp UserOp.int_ispow2)
    (hBvnot : Term.UOp op ≠ Term.UOp UserOp.bvnot)
    (hBvneg : Term.UOp op ≠ Term.UOp UserOp.bvneg)
    (hBvnego : Term.UOp op ≠ Term.UOp UserOp.bvnego)
    (hStrLen : Term.UOp op ≠ Term.UOp UserOp.str_len)
    (hStrRev : Term.UOp op ≠ Term.UOp UserOp.str_rev)
    (hStrToInt : Term.UOp op ≠ Term.UOp UserOp.str_to_int)
    (hStrToRe : Term.UOp op ≠ Term.UOp UserOp.str_to_re)
    (hReMult : Term.UOp op ≠ Term.UOp UserOp.re_mult)
    (hSeqUnit : Term.UOp op ≠ Term.UOp UserOp.seq_unit)
    (hSetSingleton : Term.UOp op ≠ Term.UOp UserOp.set_singleton)
    (hStrToLower : Term.UOp op ≠ Term.UOp UserOp.str_to_lower)
    (hStrToUpper : Term.UOp op ≠ Term.UOp UserOp.str_to_upper)
    (hStrToCode : Term.UOp op ≠ Term.UOp UserOp.str_to_code)
    (hStrFromCode : Term.UOp op ≠ Term.UOp UserOp.str_from_code)
    (hStrIsDigit : Term.UOp op ≠ Term.UOp UserOp.str_is_digit)
    (hStrFromInt : Term.UOp op ≠ Term.UOp UserOp.str_from_int)
    (hRePlus : Term.UOp op ≠ Term.UOp UserOp.re_plus)
    (hReOpt : Term.UOp op ≠ Term.UOp UserOp.re_opt)
    (hReComp : Term.UOp op ≠ Term.UOp UserOp.re_comp)
    (hUbvToInt : Term.UOp op ≠ Term.UOp UserOp.ubv_to_int)
    (hSbvToInt : Term.UOp op ≠ Term.UOp UserOp.sbv_to_int)
    (hStringsStoiNonDigit :
      Term.UOp op ≠ Term.UOp UserOp._at_strings_stoi_non_digit)
    (hIntDivByZero : Term.UOp op ≠ Term.UOp UserOp._at_int_div_by_zero)
    (hModByZero : Term.UOp op ≠ Term.UOp UserOp._at_mod_by_zero)
    (hQdivByZero : Term.UOp op ≠ Term.UOp UserOp._at_div_by_zero)
    (hBvsize : Term.UOp op ≠ Term.UOp UserOp._at_bvsize)
    (hBvredand : Term.UOp op ≠ Term.UOp UserOp.bvredand)
    (hBvredor : Term.UOp op ≠ Term.UOp UserOp.bvredor)
    (hSetChoose : Term.UOp op ≠ Term.UOp UserOp.set_choose)
    (hSetEmpty : Term.UOp op ≠ Term.UOp UserOp.set_is_empty)
    (hSetIsSingleton : Term.UOp op ≠ Term.UOp UserOp.set_is_singleton) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) x)) =
      SmtType.None := by
  have hUnary : instantiate_uopHasUnarySmtTranslation op = false := by
    cases op <;> simp [instantiate_uopHasUnarySmtTranslation]
    case not => exact False.elim (hNot rfl)
    case distinct => exact False.elim (hDistinct rfl)
    case _at_purify => exact False.elim (hPurify rfl)
    case to_real => exact False.elim (hToReal rfl)
    case to_int => exact False.elim (hToInt rfl)
    case is_int => exact False.elim (hIsInt rfl)
    case abs => exact False.elim (hAbs rfl)
    case __eoo_neg_2 => exact False.elim (hUneg rfl)
    case int_pow2 => exact False.elim (hPow2 rfl)
    case int_log2 => exact False.elim (hLog2 rfl)
    case int_ispow2 => exact False.elim (hIntIspow2 rfl)
    case _at_int_div_by_zero => exact False.elim (hIntDivByZero rfl)
    case _at_mod_by_zero => exact False.elim (hModByZero rfl)
    case _at_bvsize => exact False.elim (hBvsize rfl)
    case bvnot => exact False.elim (hBvnot rfl)
    case bvneg => exact False.elim (hBvneg rfl)
    case bvnego => exact False.elim (hBvnego rfl)
    case bvredand => exact False.elim (hBvredand rfl)
    case bvredor => exact False.elim (hBvredor rfl)
    case str_len => exact False.elim (hStrLen rfl)
    case str_rev => exact False.elim (hStrRev rfl)
    case str_to_lower => exact False.elim (hStrToLower rfl)
    case str_to_upper => exact False.elim (hStrToUpper rfl)
    case str_to_code => exact False.elim (hStrToCode rfl)
    case str_from_code => exact False.elim (hStrFromCode rfl)
    case str_is_digit => exact False.elim (hStrIsDigit rfl)
    case str_to_int => exact False.elim (hStrToInt rfl)
    case str_from_int => exact False.elim (hStrFromInt rfl)
    case str_to_re => exact False.elim (hStrToRe rfl)
    case re_mult => exact False.elim (hReMult rfl)
    case re_plus => exact False.elim (hRePlus rfl)
    case re_opt => exact False.elim (hReOpt rfl)
    case re_comp => exact False.elim (hReComp rfl)
    case seq_unit => exact False.elim (hSeqUnit rfl)
    case _at_strings_stoi_non_digit =>
      exact False.elim (hStringsStoiNonDigit rfl)
    case set_singleton => exact False.elim (hSetSingleton rfl)
    case set_choose => exact False.elim (hSetChoose rfl)
    case set_is_empty => exact False.elim (hSetEmpty rfl)
    case set_is_singleton => exact False.elim (hSetIsSingleton rfl)
    case _at_div_by_zero => exact False.elim (hQdivByZero rfl)
    case ubv_to_int => exact False.elim (hUbvToInt rfl)
    case sbv_to_int => exact False.elim (hSbvToInt rfl)
  exact instantiate_uop_apply_typeof_none_of_not_unary_smt_translation
    op x hUnary

theorem eo_to_smt_atom_head_ne_dt_sel
    {g : Term}
    (hNotUOp : ∀ op, g ≠ Term.UOp op)
    (hNotUOp1 : ∀ op idx, g ≠ Term.UOp1 op idx)
    (hNotUOp2 : ∀ op i j, g ≠ Term.UOp2 op i j)
    (hNotUOp3 : ∀ op i j k, g ≠ Term.UOp3 op i j k)
    (hNotApply : ∀ f x, g ≠ Term.Apply f x)
    (hNotVar : ∀ s S, g ≠ Term.Var s S)
    (hNotDtSel : ∀ s d i j, g ≠ Term.DtSel s d i j) :
    ∀ s d i j, __eo_to_smt g ≠ SmtTerm.DtSel s d i j := by
  intro s d i j hEq
  cases g with
  | UOp op => exact False.elim (hNotUOp op rfl)
  | UOp1 op idx => exact False.elim (hNotUOp1 op idx rfl)
  | UOp2 op i0 j0 => exact False.elim (hNotUOp2 op i0 j0 rfl)
  | UOp3 op i0 j0 k0 => exact False.elim (hNotUOp3 op i0 j0 k0 rfl)
  | Apply f x => exact False.elim (hNotApply f x rfl)
  | Var name S => exact False.elim (hNotVar name S rfl)
  | DtCons s0 d0 i0 =>
    change
      native_ite (__eo_to_smt_reserved_datatype_name s0) SmtTerm.None
          (SmtTerm.DtCons s0 (__eo_to_smt_datatype_decl d0) i0) =
        SmtTerm.DtSel s d i j at hEq
    cases hRes : __eo_to_smt_reserved_datatype_name s0 <;>
      simp [native_ite, hRes] at hEq
  | DtSel s0 d0 i0 j0 => exact False.elim (hNotDtSel s0 d0 i0 j0 rfl)
  | _ => cases hEq

theorem eo_to_smt_atom_head_ne_dt_tester
    {g : Term}
    (hNotUOp : ∀ op, g ≠ Term.UOp op)
    (hNotUOp1 : ∀ op idx, g ≠ Term.UOp1 op idx)
    (hNotUOp2 : ∀ op i j, g ≠ Term.UOp2 op i j)
    (hNotUOp3 : ∀ op i j k, g ≠ Term.UOp3 op i j k)
    (hNotApply : ∀ f x, g ≠ Term.Apply f x)
    (hNotVar : ∀ s S, g ≠ Term.Var s S) :
    ∀ s d i, __eo_to_smt g ≠ SmtTerm.DtTester s d i := by
  intro s d i hEq
  cases g with
  | UOp op => exact False.elim (hNotUOp op rfl)
  | UOp1 op idx => exact False.elim (hNotUOp1 op idx rfl)
  | UOp2 op i0 j0 => exact False.elim (hNotUOp2 op i0 j0 rfl)
  | UOp3 op i0 j0 k0 => exact False.elim (hNotUOp3 op i0 j0 k0 rfl)
  | Apply f x => exact False.elim (hNotApply f x rfl)
  | Var name S => exact False.elim (hNotVar name S rfl)
  | DtCons s0 d0 i0 =>
    change
      native_ite (__eo_to_smt_reserved_datatype_name s0) SmtTerm.None
          (SmtTerm.DtCons s0 (__eo_to_smt_datatype_decl d0) i0) =
        SmtTerm.DtTester s d i at hEq
    cases hRes : __eo_to_smt_reserved_datatype_name s0 <;>
      simp [native_ite, hRes] at hEq
  | DtSel s0 d0 i0 j0 =>
    change
      native_ite (__eo_to_smt_reserved_datatype_name s0) SmtTerm.None
          (SmtTerm.DtSel s0 (__eo_to_smt_datatype_decl d0) i0 j0) =
        SmtTerm.DtTester s d i at hEq
    cases hRes : __eo_to_smt_reserved_datatype_name s0 <;>
      simp [native_ite, hRes] at hEq
  | _ => cases hEq

theorem smtx_model_eval_eo_to_smt_atom_head_eq_of_globals
    (g : Term) {M N : SmtModel}
    (hGlobals : model_agrees_on_globals M N)
    (hNotUOp : ∀ op, g ≠ Term.UOp op)
    (hNotUOp1 : ∀ op idx, g ≠ Term.UOp1 op idx)
    (hNotUOp2 : ∀ op i j, g ≠ Term.UOp2 op i j)
    (hNotUOp3 : ∀ op i j k, g ≠ Term.UOp3 op i j k)
    (hNotApply : ∀ f x, g ≠ Term.Apply f x)
    (hNotVar : ∀ s S, g ≠ Term.Var s S) :
    __smtx_model_eval M (__eo_to_smt g) =
      __smtx_model_eval N (__eo_to_smt g) := by
  cases g with
  | UOp op => exact False.elim (hNotUOp op rfl)
  | UOp1 op idx => exact False.elim (hNotUOp1 op idx rfl)
  | UOp2 op i j => exact False.elim (hNotUOp2 op i j rfl)
  | UOp3 op i j k => exact False.elim (hNotUOp3 op i j k rfl)
  | __eo_List =>
      change __smtx_model_eval M SmtTerm.None =
        __smtx_model_eval N SmtTerm.None
      simp [__smtx_model_eval]
  | __eo_List_nil =>
      change __smtx_model_eval M SmtTerm.None =
        __smtx_model_eval N SmtTerm.None
      simp [__smtx_model_eval]
  | __eo_List_cons =>
      change __smtx_model_eval M SmtTerm.None =
        __smtx_model_eval N SmtTerm.None
      simp [__smtx_model_eval]
  | Bool =>
      change __smtx_model_eval M SmtTerm.None =
        __smtx_model_eval N SmtTerm.None
      simp [__smtx_model_eval]
  | Boolean b =>
      change __smtx_model_eval M (SmtTerm.Boolean b) =
        __smtx_model_eval N (SmtTerm.Boolean b)
      simp [__smtx_model_eval]
  | Numeral n =>
      change __smtx_model_eval M (SmtTerm.Numeral n) =
        __smtx_model_eval N (SmtTerm.Numeral n)
      simp [__smtx_model_eval]
  | Rational q =>
      change __smtx_model_eval M (SmtTerm.Rational q) =
        __smtx_model_eval N (SmtTerm.Rational q)
      simp [__smtx_model_eval]
  | String s =>
      change __smtx_model_eval M (SmtTerm.String s) =
        __smtx_model_eval N (SmtTerm.String s)
      simp [__smtx_model_eval]
  | Binary w n =>
      change __smtx_model_eval M (SmtTerm.Binary w n) =
        __smtx_model_eval N (SmtTerm.Binary w n)
      simp [__smtx_model_eval]
  | «Type» =>
      change __smtx_model_eval M SmtTerm.None =
        __smtx_model_eval N SmtTerm.None
      simp [__smtx_model_eval]
  | Stuck =>
      change __smtx_model_eval M SmtTerm.None =
        __smtx_model_eval N SmtTerm.None
      simp [__smtx_model_eval]
  | Apply f x => exact False.elim (hNotApply f x rfl)
  | FunType =>
      change __smtx_model_eval M SmtTerm.None =
        __smtx_model_eval N SmtTerm.None
      simp [__smtx_model_eval]
  | Var s S => exact False.elim (hNotVar s S rfl)
  | DatatypeType s d =>
      change __smtx_model_eval M SmtTerm.None =
        __smtx_model_eval N SmtTerm.None
      simp [__smtx_model_eval]
  | DatatypeTypeRef s =>
      change __smtx_model_eval M SmtTerm.None =
        __smtx_model_eval N SmtTerm.None
      simp [__smtx_model_eval]
  | DtcAppType T U =>
      change __smtx_model_eval M SmtTerm.None =
        __smtx_model_eval N SmtTerm.None
      simp [__smtx_model_eval]
  | DtCons s d i =>
      change
        __smtx_model_eval M
            (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
              (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i)) =
          __smtx_model_eval N
            (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
              (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i))
      cases __eo_to_smt_reserved_datatype_name s <;> simp [native_ite, __smtx_model_eval]
  | DtSel s d i j =>
      change
        __smtx_model_eval M
            (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
              (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j)) =
          __smtx_model_eval N
            (native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
              (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j))
      cases __eo_to_smt_reserved_datatype_name s <;> simp [native_ite, __smtx_model_eval]
  | USort n =>
      change __smtx_model_eval M SmtTerm.None =
        __smtx_model_eval N SmtTerm.None
      simp [__smtx_model_eval]
  | UConst i T =>
      rw [TranslationProofs.eo_to_smt_uconst]
      simpa [__smtx_model_eval] using
        hGlobals.1 (native_uconst_id i) (__eo_to_smt_type T)

theorem eo_to_smt_var_ne_dt_sel
    (name S : Term) :
    ∀ s d i j, __eo_to_smt (Term.Var name S) ≠ SmtTerm.DtSel s d i j := by
  intro s d i j hEq
  cases name <;> cases hEq

theorem eo_to_smt_var_ne_dt_tester
    (name S : Term) :
    ∀ s d i, __eo_to_smt (Term.Var name S) ≠ SmtTerm.DtTester s d i := by
  intro s d i hEq
  cases name <;> cases hEq

theorem substFalse_eval_unary_var_head_apply
    (name S a xs ss bvs : Term) {M N : SmtModel}
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hFTrans : eoHasSmtTranslation (Term.Apply (Term.Var name S) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Var name S) a) xs ss bvs))
    (hGlobals : model_agrees_on_globals M N)
    (hRecHead :
      eoHasSmtTranslation (Term.Var name S) →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Var name S) xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename)
                (Term.Var name S) xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt (Term.Var name S)))
    (hRecArg :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Var name S) a) xs ss bvs)) =
      __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.Var name S) a)) := by
  let headSub :=
    __substitute_simul_rec (Term.Boolean isRename) (Term.Var name S) xs ss bvs
  let aSub := __substitute_simul_rec (Term.Boolean isRename) a xs ss bvs
  have hSubstRaw :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Var name S) a) xs ss bvs =
        __eo_mk_apply headSub aSub := by
    simpa [headSub, aSub] using
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Var name S) a xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
  have hMkNe :
      __eo_mk_apply headSub aSub ≠ Term.Stuck := by
    rw [← hSubstRaw]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hHeadSubNe : headSub ≠ Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hMkNe
  have hHeadSubTrans : eoHasSmtTranslation headSub :=
    substitute_simul_var_any_has_smt_translation_of_ne_stuck
      name S xs ss bvs hXsEnv hBvsEnv
      (by
        have hOrigTranslate :
            __eo_to_smt (Term.Apply (Term.Var name S) a) =
              SmtTerm.Apply (__eo_to_smt (Term.Var name S)) (__eo_to_smt a) := by
          rfl
        have hOrigTy :
            generic_apply_type (__eo_to_smt (Term.Var name S)) (__eo_to_smt a) :=
          generic_apply_type_of_non_special_head_closed _ _
            (eo_to_smt_var_ne_dt_sel name S)
            (eo_to_smt_var_ne_dt_tester name S)
        have hOrigNN :
            term_has_non_none_type
              (SmtTerm.Apply (__eo_to_smt (Term.Var name S)) (__eo_to_smt a)) := by
          unfold term_has_non_none_type
          rw [← hOrigTranslate]
          exact hFTrans
        exact (apply_args_have_smt_translation_of_non_none hOrigTy hOrigNN).1)
      hSsTrans
      (by simpa [headSub] using hHeadSubNe)
  have hOrigTranslate :
      __eo_to_smt (Term.Apply (Term.Var name S) a) =
        SmtTerm.Apply (__eo_to_smt (Term.Var name S)) (__eo_to_smt a) := by
    rfl
  have hSubstTranslate :
      __eo_to_smt
          (Term.Apply
            (__substitute_simul_rec (Term.Boolean isRename) (Term.Var name S) xs ss bvs)
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
        SmtTerm.Apply
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean isRename) (Term.Var name S) xs ss bvs))
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) := by
    simpa [headSub, aSub] using
      instantiate_eo_to_smt_apply_generic_of_has_smt_translation
        headSub aSub hHeadSubTrans
  have hOrigTy :
      generic_apply_type (__eo_to_smt (Term.Var name S)) (__eo_to_smt a) :=
    generic_apply_type_of_non_special_head_closed _ _
      (eo_to_smt_var_ne_dt_sel name S)
      (eo_to_smt_var_ne_dt_tester name S)
  have hSubstTy :
      generic_apply_type
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename) (Term.Var name S) xs ss bvs))
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) := by
    simpa [headSub, aSub] using
      instantiate_generic_apply_type_of_has_smt_translation
        headSub aSub hHeadSubTrans
  have hOrigEval :
      generic_apply_eval (__eo_to_smt (Term.Var name S)) (__eo_to_smt a) :=
    generic_apply_eval_of_non_datatype_head
      (eo_to_smt_var_ne_dt_sel name S)
      (eo_to_smt_var_ne_dt_tester name S)
  have hSubstEval :
      generic_apply_eval
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename) (Term.Var name S) xs ss bvs))
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) := by
    simpa [headSub, aSub] using
      generic_apply_eval_of_non_datatype_head
        (instantiate_smt_term_ne_dt_sel_of_non_none_type hHeadSubTrans)
        (instantiate_smt_term_ne_dt_tester_of_non_none_type hHeadSubTrans)
  exact
    substFalse_eval_generic_apply (Term.Var name S) a xs ss bvs
      hisr hxs hss hbvs
      (by intro q v vs hEq; cases hEq)
      hOrigTranslate hSubstTranslate
      hOrigTy hSubstTy hOrigEval hSubstEval
      hFTrans hSubstTrans hGlobals hRecHead
      hRecArg

theorem substFalse_eval_binary_var_head_generic_apply
    (name S x y xs ss bvs : Term) {M N : SmtModel}
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.Var name S) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.Var name S) x) y))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Var name S) x) y) xs ss bvs))
    (hGlobals : model_agrees_on_globals M N)
    (hRecHead :
      eoHasSmtTranslation (Term.Var name S) →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Var name S) xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename)
                (Term.Var name S) xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt (Term.Var name S)))
    (hRecX :
      eoHasSmtTranslation x →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt x))
    (hRecY :
      eoHasSmtTranslation y →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt y)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Var name S) x) y) xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Var name S) x) y)) := by
  let headSub :=
    __substitute_simul_rec (Term.Boolean isRename) (Term.Var name S) xs ss bvs
  let xSub := __substitute_simul_rec (Term.Boolean isRename) x xs ss bvs
  let ySub := __substitute_simul_rec (Term.Boolean isRename) y xs ss bvs
  have hSubstInnerRaw :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Var name S) x) xs ss bvs =
        __eo_mk_apply headSub xSub := by
    simpa [headSub, xSub] using
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Var name S) x xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
  have hSubstOuterRaw :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Var name S) x) y) xs ss bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Var name S) x) xs ss bvs)
          ySub := by
    simpa [ySub] using
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Apply (Term.Var name S) x) y xs ss bvs
        hisr hxs hss hbvs hNotBinderOuter
  have hOuterNeStuck :
      __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Var name S) x) xs ss bvs)
          ySub ≠ Term.Stuck := by
    rw [← hSubstOuterRaw]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hInnerNeStuck :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Var name S) x) xs ss bvs ≠ Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  have hHeadSubNe : headSub ≠ Term.Stuck := by
    rw [hSubstInnerRaw] at hInnerNeStuck
    exact instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hInnerNeStuck
  have hOrigTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Var name S) x) y) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Var name S) x))
          (__eo_to_smt y) := by
    rfl
  have hOrigTy :
      generic_apply_type (__eo_to_smt (Term.Apply (Term.Var name S) x))
        (__eo_to_smt y) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hOrigNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Var name S) x))
          (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [← hOrigTranslate]
    exact hFTrans
  rcases apply_args_have_smt_translation_of_non_none hOrigTy hOrigNN with
    ⟨hOrigHeadTrans, hYTrans⟩
  have hOrigInnerTranslate :
      __eo_to_smt (Term.Apply (Term.Var name S) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Var name S)) (__eo_to_smt x) := by
    rfl
  have hOrigInnerTy :
      generic_apply_type (__eo_to_smt (Term.Var name S)) (__eo_to_smt x) :=
    generic_apply_type_of_non_special_head_closed _ _
      (eo_to_smt_var_ne_dt_sel name S)
      (eo_to_smt_var_ne_dt_tester name S)
  have hOrigInnerNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt (Term.Var name S)) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hOrigInnerTranslate]
    exact hOrigHeadTrans
  have hOrigVarTrans : eoHasSmtTranslation (Term.Var name S) :=
    (apply_args_have_smt_translation_of_non_none
      hOrigInnerTy hOrigInnerNN).1
  have hHeadSubTrans : eoHasSmtTranslation headSub :=
    substitute_simul_var_any_has_smt_translation_of_ne_stuck
      name S xs ss bvs hXsEnv hBvsEnv hOrigVarTrans hSsTrans hHeadSubNe
  have hInnerMk :
      __eo_mk_apply headSub xSub = Term.Apply headSub xSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      rw [← hSubstInnerRaw]
      exact hInnerNeStuck)
  have hHeadResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Var name S) x) xs ss bvs =
        Term.Apply headSub xSub := by
    rw [hSubstInnerRaw, hInnerMk]
  have hOuterMk :
      __eo_mk_apply (Term.Apply headSub xSub) ySub =
        Term.Apply (Term.Apply headSub xSub) ySub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      rw [← hInnerMk, ← hSubstInnerRaw]
      exact hOuterNeStuck)
  have hResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Var name S) x) y) xs ss bvs =
        Term.Apply (Term.Apply headSub xSub) ySub := by
    rw [hSubstOuterRaw, hHeadResultEq, hOuterMk]
  have hSubstTranslate :
      __eo_to_smt (Term.Apply (Term.Apply headSub xSub) ySub) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply headSub xSub))
          (__eo_to_smt ySub) :=
    eo_to_smt_apply_apply_generic_of_head_has_smt_translation
      headSub xSub ySub hHeadSubTrans
  have hSubstTy :
      generic_apply_type (__eo_to_smt (Term.Apply headSub xSub))
        (__eo_to_smt ySub) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hSubstFullTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply headSub xSub) ySub) := by
    rw [← hResultEq]
    exact hSubstTrans
  have hSubstNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt (Term.Apply headSub xSub))
          (__eo_to_smt ySub)) := by
    unfold term_has_non_none_type
    rw [← hSubstTranslate]
    exact hSubstFullTrans
  rcases apply_args_have_smt_translation_of_non_none hSubstTy hSubstNN with
    ⟨hSubstHeadTrans, hSubstYTrans⟩
  have hOrigEval :
      generic_apply_eval (__eo_to_smt (Term.Apply (Term.Var name S) x))
        (__eo_to_smt y) :=
    generic_apply_eval_of_non_datatype_head
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hSubstEval :
      generic_apply_eval (__eo_to_smt (Term.Apply headSub xSub))
        (__eo_to_smt ySub) :=
    generic_apply_eval_of_non_datatype_head
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hHeadEval :
      __smtx_model_eval M (__eo_to_smt (Term.Apply headSub xSub)) =
        __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.Var name S) x)) := by
    have hHeadEvalRaw :
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename)
                (Term.Apply (Term.Var name S) x) xs ss bvs)) =
          __smtx_model_eval N
            (__eo_to_smt (Term.Apply (Term.Var name S) x)) := by
      exact
        substFalse_eval_unary_var_head_apply
          name S x xs ss bvs
          hXsEnv hBvsEnv hSsTrans
          hisr hxs hss hbvs
          hOrigHeadTrans
          (by
            rw [hHeadResultEq]
            exact hSubstHeadTrans)
          hGlobals hRecHead hRecX
    simpa [hHeadResultEq] using hHeadEvalRaw
  have hYEval := hRecY hYTrans hSubstYTrans
  rw [hResultEq, hOrigTranslate, hSubstTranslate]
  exact
    smtx_model_eval_apply_cross_eq_of_eval_eq hGlobals
      hSubstEval hOrigEval hHeadEval hYEval

theorem substFalse_eval_ternary_var_head_generic_apply
    (name S x y z xs ss bvs : Term) {M N : SmtModel}
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.Apply (Term.Var name S) x) y ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.Var name S) x) y) z))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply (Term.Var name S) x) y) z)
          xs ss bvs))
    (hGlobals : model_agrees_on_globals M N)
    (hRecArg :
      ∀ {b : Term},
        IsNonbinderSubterm b
          (Term.Apply (Term.Apply (Term.Apply (Term.Var name S) x) y) z) →
        sizeOf b <
          sizeOf (Term.Apply (Term.Apply (Term.Apply (Term.Var name S) x) y) z) →
        eoHasSmtTranslation b →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt b)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Apply (Term.Var name S) x) y) z)
            xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.Var name S) x) y) z)) := by
  let headSub :=
    __substitute_simul_rec (Term.Boolean isRename) (Term.Var name S) xs ss bvs
  let xSub := __substitute_simul_rec (Term.Boolean isRename) x xs ss bvs
  let ySub := __substitute_simul_rec (Term.Boolean isRename) y xs ss bvs
  let zSub := __substitute_simul_rec (Term.Boolean isRename) z xs ss bvs
  have hOrigTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.Var name S) x) y) z) =
        SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Var name S) x) y))
          (__eo_to_smt z) := by
    rfl
  have hOrigTy :
      generic_apply_type
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Var name S) x) y))
        (__eo_to_smt z) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hOrigNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Var name S) x) y))
          (__eo_to_smt z)) := by
    unfold term_has_non_none_type
    rw [← hOrigTranslate]
    exact hFTrans
  rcases apply_args_have_smt_translation_of_non_none hOrigTy hOrigNN with
    ⟨hOrigHeadTrans, hZTrans⟩
  have hOrigInnerTranslate :
      __eo_to_smt (Term.Apply (Term.Var name S) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Var name S)) (__eo_to_smt x) := by
    rfl
  have hOrigInnerTy :
      generic_apply_type (__eo_to_smt (Term.Var name S)) (__eo_to_smt x) :=
    generic_apply_type_of_non_special_head_closed _ _
      (eo_to_smt_var_ne_dt_sel name S)
      (eo_to_smt_var_ne_dt_tester name S)
  have hOrigInnerNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt (Term.Var name S)) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hOrigInnerTranslate]
    exact
      (apply_args_have_smt_translation_of_non_none
        (generic_apply_type_of_non_special_head_closed _ _
          (by
            intro s d i j hSel
            exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
          (by
            intro s d i hTester
            exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester))
        (by
          unfold term_has_non_none_type
          rw [← (by
            rfl :
              __eo_to_smt (Term.Apply (Term.Apply (Term.Var name S) x) y) =
                SmtTerm.Apply
                  (__eo_to_smt (Term.Apply (Term.Var name S) x))
                  (__eo_to_smt y))]
          exact hOrigHeadTrans)).1
  rcases apply_args_have_smt_translation_of_non_none
      hOrigInnerTy hOrigInnerNN with
    ⟨hOrigVarTrans, hXTrans⟩
  have hNotBinderMiddle :
      ∀ q v vs,
        Term.Apply (Term.Var name S) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
    intro q v vs hEq
    cases hEq
    exact term_not_eo_list_cons_of_has_smt_translation hXTrans v vs rfl
  have hOuterNonbinder :
      ¬ IsBinderHead (Term.Apply (Term.Apply (Term.Var name S) x) y) := by
    rintro ⟨q, v, vs, hEq⟩
    exact hNotBinderOuter q v vs hEq
  have hMiddleNonbinder :
      ¬ IsBinderHead (Term.Apply (Term.Var name S) x) := by
    rintro ⟨q, v, vs, hEq⟩
    exact hNotBinderMiddle q v vs hEq
  have hSubstInnerRaw :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Var name S) x) xs ss bvs =
        __eo_mk_apply headSub xSub := by
    simpa [headSub, xSub] using
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Var name S) x xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
  have hSubstMidRaw :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Var name S) x) y) xs ss bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Var name S) x) xs ss bvs)
          ySub := by
    simpa [ySub] using
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Apply (Term.Var name S) x) y xs ss bvs
        hisr hxs hss hbvs hNotBinderMiddle
  have hSubstOuterRaw :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply (Term.Var name S) x) y) z)
          xs ss bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Var name S) x) y) xs ss bvs)
          zSub := by
    simpa [zSub] using
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Apply (Term.Apply (Term.Var name S) x) y) z xs ss bvs
        hisr hxs hss hbvs hNotBinderOuter
  have hOuterNeStuck :
      __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Var name S) x) y) xs ss bvs)
          zSub ≠ Term.Stuck := by
    rw [← hSubstOuterRaw]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hMidSubstNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Var name S) x) y) xs ss bvs ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  have hMidMkNe :
      __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Var name S) x) xs ss bvs)
          ySub ≠ Term.Stuck := by
    rwa [hSubstMidRaw] at hMidSubstNe
  have hInnerSubstNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Var name S) x) xs ss bvs ≠ Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hMidMkNe
  have hInnerMkNe :
      __eo_mk_apply headSub xSub ≠ Term.Stuck := by
    rwa [hSubstInnerRaw] at hInnerSubstNe
  have hHeadSubNe : headSub ≠ Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hInnerMkNe
  have hHeadSubTrans : eoHasSmtTranslation headSub :=
    substitute_simul_var_any_has_smt_translation_of_ne_stuck
      name S xs ss bvs hXsEnv hBvsEnv hOrigVarTrans hSsTrans hHeadSubNe
  have hInnerMk :
      __eo_mk_apply headSub xSub = Term.Apply headSub xSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerMkNe
  have hMidMkNe' :
      __eo_mk_apply (Term.Apply headSub xSub) ySub ≠ Term.Stuck := by
    simpa [hSubstInnerRaw, hInnerMk] using hMidMkNe
  have hMidMk :
      __eo_mk_apply (Term.Apply headSub xSub) ySub =
        Term.Apply (Term.Apply headSub xSub) ySub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMidMkNe'
  have hHeadResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Var name S) x) y) xs ss bvs =
        Term.Apply (Term.Apply headSub xSub) ySub := by
    rw [hSubstMidRaw, hSubstInnerRaw, hInnerMk, hMidMk]
  have hOuterMkNe' :
      __eo_mk_apply (Term.Apply (Term.Apply headSub xSub) ySub) zSub ≠
        Term.Stuck := by
    simpa [hHeadResultEq] using hOuterNeStuck
  have hOuterMk :
      __eo_mk_apply (Term.Apply (Term.Apply headSub xSub) ySub) zSub =
        Term.Apply (Term.Apply (Term.Apply headSub xSub) ySub) zSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hOuterMkNe'
  have hResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply (Term.Var name S) x) y) z)
          xs ss bvs =
        Term.Apply (Term.Apply (Term.Apply headSub xSub) ySub) zSub := by
    rw [hSubstOuterRaw, hHeadResultEq, hOuterMk]
  have hSubstTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply headSub xSub) ySub) zSub) =
        SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.Apply headSub xSub) ySub))
          (__eo_to_smt zSub) :=
    eo_to_smt_apply_apply_apply_generic_of_head_has_smt_translation
      headSub xSub ySub zSub hHeadSubTrans
  have hSubstTy :
      generic_apply_type
        (__eo_to_smt (Term.Apply (Term.Apply headSub xSub) ySub))
        (__eo_to_smt zSub) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hSubstFullTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply headSub xSub) ySub) zSub) := by
    rw [← hResultEq]
    exact hSubstTrans
  have hSubstNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.Apply headSub xSub) ySub))
          (__eo_to_smt zSub)) := by
    unfold term_has_non_none_type
    rw [← hSubstTranslate]
    exact hSubstFullTrans
  rcases apply_args_have_smt_translation_of_non_none hSubstTy hSubstNN with
    ⟨hSubstHeadTrans, hSubstZTrans⟩
  have hHeadEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply headSub xSub) ySub)) =
        __smtx_model_eval N
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Var name S) x) y)) := by
    have hHeadEvalRaw :
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename)
                (Term.Apply (Term.Apply (Term.Var name S) x) y) xs ss bvs)) =
          __smtx_model_eval N
            (__eo_to_smt (Term.Apply (Term.Apply (Term.Var name S) x) y)) := by
      exact
        substFalse_eval_binary_var_head_generic_apply
          name S x y xs ss bvs
          hXsEnv hBvsEnv hSsTrans
          hisr hxs hss hbvs hNotBinderMiddle
          hOrigHeadTrans
          (by
            rw [hHeadResultEq]
            exact hSubstHeadTrans)
          hGlobals
          (fun ht hst => hRecArg
            (by simp [IsNonbinderSubterm, hOuterNonbinder, hMiddleNonbinder])
            (by simp; omega) ht hst)
          (fun ht hst => hRecArg
            (by simp [IsNonbinderSubterm, hOuterNonbinder, hMiddleNonbinder])
            (by simp; omega) ht hst)
          (fun ht hst => hRecArg
            (by simp [IsNonbinderSubterm, hOuterNonbinder, hMiddleNonbinder])
            (by simp; omega) ht hst)
    simpa [hHeadResultEq] using hHeadEvalRaw
  have hZEval := hRecArg
    (by simp [IsNonbinderSubterm, hOuterNonbinder])
    (by simp; omega) hZTrans hSubstZTrans
  have hOrigEval :
      generic_apply_eval
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Var name S) x) y))
        (__eo_to_smt z) :=
    generic_apply_eval_of_non_datatype_head
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hSubstEval :
      generic_apply_eval
        (__eo_to_smt (Term.Apply (Term.Apply headSub xSub) ySub))
        (__eo_to_smt zSub) :=
    generic_apply_eval_of_non_datatype_head
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  rw [hResultEq, hOrigTranslate, hSubstTranslate]
  exact
    smtx_model_eval_apply_cross_eq_of_eval_eq hGlobals
      hSubstEval hOrigEval hHeadEval hZEval

theorem substFalse_eval_ternary_uop1_head_generic_apply
    (op : UserOp1) (idx x y z xs ss bvs : Term) {M N : SmtModel}
    (hM : model_wf M) (hN : model_wf N)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.Apply (Term.UOp1 op idx) x) y ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) z))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) z)
          xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp1 op idx) xs ss bvs =
        Term.UOp1 op idx)
    (hGlobals : model_agrees_on_globals M N)
    (hRecArg :
      ∀ {b : Term},
        IsNonbinderSubterm b
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) z) →
        sizeOf b <
          sizeOf (Term.Apply (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) z) →
        eoHasSmtTranslation b →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt b)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) z)
            xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) z)) := by
  let xSub := __substitute_simul_rec (Term.Boolean isRename) x xs ss bvs
  let ySub := __substitute_simul_rec (Term.Boolean isRename) y xs ss bvs
  let zSub := __substitute_simul_rec (Term.Boolean isRename) z xs ss bvs
  have hOrigTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) z) =
        SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y))
          (__eo_to_smt z) :=
    eo_to_smt_apply_apply_apply_non_uop_head_generic
      (by intro op' hEq; cases hEq)
      (by intro op' a' hEq; cases hEq)
  have hOrigTy :
      generic_apply_type
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y))
        (__eo_to_smt z) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hOrigNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y))
          (__eo_to_smt z)) := by
    unfold term_has_non_none_type
    rw [← hOrigTranslate]
    exact hFTrans
  rcases apply_args_have_smt_translation_of_non_none hOrigTy hOrigNN with
    ⟨hOrigHeadTrans, _hZTrans⟩
  have hNotBinderMiddle :
      ∀ q v vs,
        Term.Apply (Term.UOp1 op idx) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
    intro q v vs hEq
    cases hEq
    exact false_of_apply_apply_uop1_raw_list_has_smt_translation hOrigHeadTrans
  have hOuterNonbinder :
      ¬ IsBinderHead (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) := by
    rintro ⟨q, v, vs, hEq⟩
    exact hNotBinderOuter q v vs hEq
  have hMiddleNonbinder :
      ¬ IsBinderHead (Term.Apply (Term.UOp1 op idx) x) := by
    rintro ⟨q, v, vs, hEq⟩
    exact hNotBinderMiddle q v vs hEq
  have hRecX :
      eoHasSmtTranslation x →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) x xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt x) :=
    fun ht hst => hRecArg
      (by simp [IsNonbinderSubterm, hOuterNonbinder, hMiddleNonbinder])
      (by simp; omega) ht hst
  have hRecY :
      eoHasSmtTranslation y →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt y) :=
    fun ht hst => hRecArg
      (by simp [IsNonbinderSubterm, hOuterNonbinder, hMiddleNonbinder])
      (by simp; omega) ht hst
  have hRecZ :
      eoHasSmtTranslation z →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) z xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) z xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt z) :=
    fun ht hst => hRecArg
      (by simp [IsNonbinderSubterm, hOuterNonbinder])
      (by simp; omega) ht hst
  have hSubstInner :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp1 op idx) x) xs ss bvs =
        __eo_mk_apply (Term.UOp1 op idx) xSub := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.UOp1 op idx) x xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [xSub, hHeadSub] using hEq
  have hSubstHead :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp1 op idx) xSub)
          ySub := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Apply (Term.UOp1 op idx) x) y xs ss bvs
        hisr hxs hss hbvs hNotBinderMiddle
    rw [hEq, hSubstInner]
  have hSubstOuter :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) z)
          xs ss bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) xs ss bvs)
          zSub := by
    simpa [zSub] using
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) z xs ss bvs
        hisr hxs hss hbvs hNotBinderOuter
  have hOuterNeStuck :
      __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) xs ss bvs)
          zSub ≠ Term.Stuck := by
    rw [← hSubstOuter]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hHeadNeStuck :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) xs ss bvs ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  have hHeadMkNe :
      __eo_mk_apply (__eo_mk_apply (Term.UOp1 op idx) xSub) ySub ≠
        Term.Stuck := by
    rwa [hSubstHead] at hHeadNeStuck
  have hInnerMkNe :
      __eo_mk_apply (Term.UOp1 op idx) xSub ≠ Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hHeadMkNe
  have hInnerMk :
      __eo_mk_apply (Term.UOp1 op idx) xSub =
        Term.Apply (Term.UOp1 op idx) xSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerMkNe
  have hHeadMkNe' :
      __eo_mk_apply (Term.Apply (Term.UOp1 op idx) xSub) ySub ≠
        Term.Stuck := by
    simpa [hInnerMk] using hHeadMkNe
  have hHeadMk :
      __eo_mk_apply (Term.Apply (Term.UOp1 op idx) xSub) ySub =
        Term.Apply (Term.Apply (Term.UOp1 op idx) xSub) ySub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hHeadMkNe'
  have hHeadResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) xs ss bvs =
        Term.Apply (Term.Apply (Term.UOp1 op idx) xSub) ySub := by
    rw [hSubstHead, hInnerMk, hHeadMk]
  have hSubstTranslate :
      __eo_to_smt
          (Term.Apply
            (__substitute_simul_rec (Term.Boolean isRename)
              (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) xs ss bvs)
            zSub) =
        SmtTerm.Apply
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean isRename)
              (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) xs ss bvs))
          (__eo_to_smt zSub) := by
    rw [hHeadResultEq]
    exact
      eo_to_smt_apply_apply_apply_non_uop_head_generic
        (by intro op' hEq; cases hEq)
        (by intro op' a' hEq; cases hEq)
  have hSubstTy :
      generic_apply_type
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) xs ss bvs))
        (__eo_to_smt zSub) := by
    rw [hHeadResultEq]
    exact generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hSubstEval :
      generic_apply_eval
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) xs ss bvs))
        (__eo_to_smt zSub) := by
    rw [hHeadResultEq]
    exact generic_apply_eval_of_non_datatype_head
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hOrigEval :
      generic_apply_eval
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y))
        (__eo_to_smt z) :=
    generic_apply_eval_of_non_datatype_head
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  exact
    substFalse_eval_generic_apply
      (Term.Apply (Term.Apply (Term.UOp1 op idx) x) y) z xs ss bvs
      hisr hxs hss hbvs hNotBinderOuter hOrigTranslate hSubstTranslate
      hOrigTy hSubstTy hOrigEval hSubstEval hFTrans hSubstTrans hGlobals
      (fun hHeadTrans hSubstHeadTrans => by
        by_cases hUpdate : op = UserOp1.update
        · subst op
          exact
            substFalse_eval_binary_uop1_update idx x y xs ss bvs
              hisr hxs hss hbvs hNotBinderMiddle hHeadTrans
              hSubstHeadTrans hHeadSub hGlobals hRecX hRecY
        · by_cases hTupleUpdate : op = UserOp1.tuple_update
          · subst op
            exact
              substFalse_eval_binary_uop1_tuple_update idx x y xs ss bvs
                hM hN hisr hxs hss hbvs hNotBinderMiddle hHeadTrans
                hSubstHeadTrans hHeadSub hGlobals hRecX hRecY
          · exact
              substFalse_eval_binary_uop1_generic_apply op idx x y xs ss bvs
                hM hN hisr hxs hss hbvs hUpdate hTupleUpdate
                hNotBinderMiddle hHeadTrans hSubstHeadTrans hHeadSub hGlobals
                hRecX hRecY)
      hRecZ

theorem substFalse_eval_unary_atom_head_apply
    (g a xs ss bvs : Term) {M N : SmtModel}
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotUOp : ∀ op, g ≠ Term.UOp op)
    (hNotUOp1 : ∀ op idx, g ≠ Term.UOp1 op idx)
    (hNotUOp2 : ∀ op i j, g ≠ Term.UOp2 op i j)
    (hNotUOp3 : ∀ op i j k, g ≠ Term.UOp3 op i j k)
    (hNotApply : ∀ f x, g ≠ Term.Apply f x)
    (hNotVar : ∀ s S, g ≠ Term.Var s S)
    (hNotStuck : g ≠ Term.Stuck)
    (hFTrans : eoHasSmtTranslation (Term.Apply g a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename) (Term.Apply g a)
          xs ss bvs))
    (hGlobals : model_agrees_on_globals M N)
    (hRecArg :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename) (Term.Apply g a)
            xs ss bvs)) =
      __smtx_model_eval N (__eo_to_smt (Term.Apply g a)) := by
  let aSub := __substitute_simul_rec (Term.Boolean isRename) a xs ss bvs
  have hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename) g xs ss bvs = g :=
    substitute_simul_rec_atom_head_eq_self_of_apply_subst_trans
      g a xs ss bvs hXsEnv hBvsEnv hSsTrans
      (by intro q v vs hEq; exact hNotApply _ _ hEq)
      hNotApply hNotVar hNotStuck hSubstTrans
  have hSubstRaw :
      __substitute_simul_rec (Term.Boolean isRename) (Term.Apply g a) xs ss bvs =
        __eo_mk_apply g aSub := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        g a xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; exact hNotApply _ _ hEq)
    simpa [aSub, hHeadSub] using hEq
  have hMkNe :
      __eo_mk_apply g aSub ≠ Term.Stuck := by
    rw [← hSubstRaw]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hMk :
      __eo_mk_apply g aSub = Term.Apply g aSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe
  have hResultEq :
      __substitute_simul_rec (Term.Boolean isRename) (Term.Apply g a) xs ss bvs =
        Term.Apply g aSub := by
    rw [hSubstRaw, hMk]
  have hOrigTranslate :
      __eo_to_smt (Term.Apply g a) =
        SmtTerm.Apply (__eo_to_smt g) (__eo_to_smt a) :=
    eo_to_smt_apply_atom_head_generic
      hNotUOp hNotUOp1 hNotUOp2 hNotUOp3 hNotApply
  have hSubstTranslate :
      __eo_to_smt (Term.Apply g aSub) =
        SmtTerm.Apply (__eo_to_smt g) (__eo_to_smt aSub) :=
    eo_to_smt_apply_atom_head_generic
      hNotUOp hNotUOp1 hNotUOp2 hNotUOp3 hNotApply
  have hArgTrans :
      eoHasSmtTranslation a ∧ eoHasSmtTranslation aSub := by
    by_cases hDtSel : ∃ s d i j, g = Term.DtSel s d i j
    · rcases hDtSel with ⟨s, d, i, j, rfl⟩
      have hSubstAppTrans : eoHasSmtTranslation (Term.Apply (Term.DtSel s d i j) aSub) := by
        rw [← hResultEq]
        exact hSubstTrans
      exact
        ⟨apply_dt_sel_arg_has_smt_translation_of_has_smt_translation hFTrans,
          apply_dt_sel_arg_has_smt_translation_of_has_smt_translation
            hSubstAppTrans⟩
    · have hNotDtSel : ∀ s d i j, g ≠ Term.DtSel s d i j := by
        intro s d i j hEq
        exact hDtSel ⟨s, d, i, j, hEq⟩
      have hOrigTy :
          generic_apply_type (__eo_to_smt g) (__eo_to_smt a) :=
        generic_apply_type_of_non_special_head_closed _ _
          (eo_to_smt_atom_head_ne_dt_sel
            hNotUOp hNotUOp1 hNotUOp2 hNotUOp3
            hNotApply hNotVar hNotDtSel)
          (eo_to_smt_atom_head_ne_dt_tester
            hNotUOp hNotUOp1 hNotUOp2 hNotUOp3
            hNotApply hNotVar)
      have hOrigNN :
          term_has_non_none_type
            (SmtTerm.Apply (__eo_to_smt g) (__eo_to_smt a)) := by
        unfold term_has_non_none_type
        rw [← hOrigTranslate]
        exact hFTrans
      have hSubstTy :
          generic_apply_type (__eo_to_smt g) (__eo_to_smt aSub) :=
        generic_apply_type_of_non_special_head_closed _ _
          (eo_to_smt_atom_head_ne_dt_sel
            hNotUOp hNotUOp1 hNotUOp2 hNotUOp3
            hNotApply hNotVar hNotDtSel)
          (eo_to_smt_atom_head_ne_dt_tester
            hNotUOp hNotUOp1 hNotUOp2 hNotUOp3
            hNotApply hNotVar)
      have hSubstAppTrans : eoHasSmtTranslation (Term.Apply g aSub) := by
        rw [← hResultEq]
        exact hSubstTrans
      have hSubstNN :
          term_has_non_none_type
            (SmtTerm.Apply (__eo_to_smt g) (__eo_to_smt aSub)) := by
        unfold term_has_non_none_type
        rw [← hSubstTranslate]
        exact hSubstAppTrans
      exact
        ⟨(apply_args_have_smt_translation_of_non_none hOrigTy hOrigNN).2,
          (apply_args_have_smt_translation_of_non_none hSubstTy hSubstNN).2⟩
  have hArgEval := hRecArg hArgTrans.1 hArgTrans.2
  have hHeadEval :
      __smtx_model_eval M (__eo_to_smt g) =
        __smtx_model_eval N (__eo_to_smt g) :=
    smtx_model_eval_eo_to_smt_atom_head_eq_of_globals g hGlobals
      hNotUOp hNotUOp1 hNotUOp2 hNotUOp3 hNotApply hNotVar
  rw [hResultEq, hOrigTranslate, hSubstTranslate]
  exact
    smtx_model_eval_apply_same_head_cross_eq_of_eval_eq hGlobals
      (__eo_to_smt g) (__eo_to_smt aSub) (__eo_to_smt a)
      hHeadEval hArgEval

theorem substFalse_eval_ternary_atom_head_generic_apply
    (g x y z xs ss bvs : Term) {M N : SmtModel}
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotUOp : ∀ op, g ≠ Term.UOp op)
    (hNotUOp1 : ∀ op idx, g ≠ Term.UOp1 op idx)
    (hNotApply : ∀ f a, g ≠ Term.Apply f a)
    (hNotVar : ∀ s S, g ≠ Term.Var s S)
    (hNotStuck : g ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.Apply g x) y ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.Apply g x) y) z))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply g x) y) z) xs ss bvs))
    (hGlobals : model_agrees_on_globals M N)
    (hRecArg :
      ∀ {b : Term},
        IsNonbinderSubterm b
          (Term.Apply (Term.Apply (Term.Apply g x) y) z) →
        sizeOf b < sizeOf (Term.Apply (Term.Apply (Term.Apply g x) y) z) →
        eoHasSmtTranslation b →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt b)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Apply g x) y) z) xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply g x) y) z)) := by
  let xSub := __substitute_simul_rec (Term.Boolean isRename) x xs ss bvs
  let ySub := __substitute_simul_rec (Term.Boolean isRename) y xs ss bvs
  let zSub := __substitute_simul_rec (Term.Boolean isRename) z xs ss bvs
  have hOrigTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply g x) y) z) =
        SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.Apply g x) y))
          (__eo_to_smt z) :=
    eo_to_smt_apply_apply_apply_non_uop_head_generic hNotUOp
      (fun op a => hNotApply (Term.UOp op) a)
  have hOrigTy :
      generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply g x) y))
        (__eo_to_smt z) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hOrigNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply g x) y))
          (__eo_to_smt z)) := by
    unfold term_has_non_none_type
    rw [← hOrigTranslate]
    exact hFTrans
  rcases apply_args_have_smt_translation_of_non_none hOrigTy hOrigNN with
    ⟨hOrigHeadTrans, _hZTrans⟩
  have hNotBinderMiddle :
      ∀ q v vs,
        Term.Apply g x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
    intro q v vs hEq
    cases hEq
    cases g with
    | UOp op => exact False.elim (hNotUOp op rfl)
    | UOp1 op idx => exact False.elim (hNotUOp1 op idx rfl)
    | UOp2 op i j =>
        exact false_of_apply_apply_uop2_raw_list_has_smt_translation
          hOrigHeadTrans
    | UOp3 op i j k =>
        exact false_of_apply_apply_uop3_raw_list_has_smt_translation
          hOrigHeadTrans
    | Apply f a => exact False.elim (hNotApply f a rfl)
    | Var s S => exact False.elim (hNotVar s S rfl)
    | Stuck => exact False.elim (hNotStuck rfl)
    | _ =>
        exact
          false_of_apply_apply_generic_raw_list_has_smt_translation
            (q := _)
            (body := y)
            (by rfl)
            (by rfl)
            (generic_apply_type_of_non_special_head_closed _ _
              (by
                intro s d i j hSel
                exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
              (by
                intro s d i hTester
                exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester))
            hOrigHeadTrans
  have hOuterNonbinder :
      ¬ IsBinderHead (Term.Apply (Term.Apply g x) y) := by
    rintro ⟨q, v, vs, hEq⟩
    exact hNotBinderOuter q v vs hEq
  have hMiddleNonbinder : ¬ IsBinderHead (Term.Apply g x) := by
    rintro ⟨q, v, vs, hEq⟩
    exact hNotBinderMiddle q v vs hEq
  have hRecGX :
      eoHasSmtTranslation (Term.Apply g x) →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply g x) xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename)
                (Term.Apply g x) xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt (Term.Apply g x)) :=
    fun ht hst => hRecArg
      (by simp [IsNonbinderSubterm, hOuterNonbinder, hMiddleNonbinder])
      (by simp; omega) ht hst
  have hRecY :
      eoHasSmtTranslation y →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) y xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt y) :=
    fun ht hst => hRecArg
      (by simp [IsNonbinderSubterm, hOuterNonbinder, hMiddleNonbinder])
      (by simp; omega) ht hst
  have hRecZ :
      eoHasSmtTranslation z →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) z xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) z xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt z) :=
    fun ht hst => hRecArg
      (by simp [IsNonbinderSubterm, hOuterNonbinder])
      (by simp; omega) ht hst
  have hSubstInnerRaw :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply g x) xs ss bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename) g xs ss bvs) xSub := by
    simpa [xSub] using
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        g x xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; exact hNotApply _ _ hEq)
  have hSubstHeadRaw :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply g x) y) xs ss bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply g x) xs ss bvs)
          ySub := by
    simpa [ySub] using
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Apply g x) y xs ss bvs hisr hxs hss hbvs hNotBinderMiddle
  have hSubstOuterRaw :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply g x) y) z) xs ss bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply g x) y) xs ss bvs)
          zSub := by
    simpa [zSub] using
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean isRename)
        (Term.Apply (Term.Apply g x) y) z xs ss bvs
        hisr hxs hss hbvs hNotBinderOuter
  have hOuterNeStuck :
      __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply g x) y) xs ss bvs)
          zSub ≠ Term.Stuck := by
    rw [← hSubstOuterRaw]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hHeadNeStuck :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply g x) y) xs ss bvs ≠ Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  have hHeadMkNe :
      __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename) (Term.Apply g x) xs ss bvs)
          ySub ≠ Term.Stuck := by
    rwa [hSubstHeadRaw] at hHeadNeStuck
  have hInnerNeStuck :
      __substitute_simul_rec (Term.Boolean isRename) (Term.Apply g x) xs ss bvs ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hHeadMkNe
  have hGSubNe :
      __substitute_simul_rec (Term.Boolean isRename) g xs ss bvs ≠ Term.Stuck := by
    rw [hSubstInnerRaw] at hInnerNeStuck
    exact instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hInnerNeStuck
  have hGSub :
      __substitute_simul_rec (Term.Boolean isRename) g xs ss bvs = g :=
    substitute_simul_rec_atom_eq_self_of_ne_stuck g xs ss bvs
      hXsEnv hBvsEnv hSsTrans hNotApply hNotVar hNotStuck hGSubNe
  have hSubstInner :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply g x) xs ss bvs =
        __eo_mk_apply g xSub := by
    rw [hSubstInnerRaw, hGSub]
  have hInnerMk :
      __eo_mk_apply g xSub = Term.Apply g xSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      rw [← hSubstInner]
      exact hInnerNeStuck)
  have hInnerResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply g x) xs ss bvs =
        Term.Apply g xSub := by
    rw [hSubstInner, hInnerMk]
  have hHeadMkNe' :
      __eo_mk_apply (Term.Apply g xSub) ySub ≠ Term.Stuck := by
    simpa [hInnerResultEq] using hHeadMkNe
  have hHeadMk :
      __eo_mk_apply (Term.Apply g xSub) ySub =
        Term.Apply (Term.Apply g xSub) ySub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hHeadMkNe'
  have hHeadResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply g x) y) xs ss bvs =
        Term.Apply (Term.Apply g xSub) ySub := by
    rw [hSubstHeadRaw, hInnerResultEq, hHeadMk]
  have hSubstTranslate :
      __eo_to_smt
          (Term.Apply
            (__substitute_simul_rec (Term.Boolean isRename)
              (Term.Apply (Term.Apply g x) y) xs ss bvs)
            zSub) =
        SmtTerm.Apply
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean isRename)
              (Term.Apply (Term.Apply g x) y) xs ss bvs))
          (__eo_to_smt zSub) := by
    rw [hHeadResultEq]
    exact
      eo_to_smt_apply_apply_apply_non_uop_head_generic hNotUOp
        (fun op a => hNotApply (Term.UOp op) a)
  have hSubstTy :
      generic_apply_type
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply g x) y) xs ss bvs))
        (__eo_to_smt zSub) := by
    rw [hHeadResultEq]
    exact generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hSubstEval :
      generic_apply_eval
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply g x) y) xs ss bvs))
        (__eo_to_smt zSub) := by
    rw [hHeadResultEq]
    exact generic_apply_eval_of_non_datatype_head
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hOrigEval :
      generic_apply_eval (__eo_to_smt (Term.Apply (Term.Apply g x) y))
        (__eo_to_smt z) :=
    generic_apply_eval_of_non_datatype_head
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  exact
    substFalse_eval_generic_apply (Term.Apply (Term.Apply g x) y) z xs ss bvs
      hisr hxs hss hbvs hNotBinderOuter hOrigTranslate hSubstTranslate
      hOrigTy hSubstTy hOrigEval hSubstEval hFTrans hSubstTrans hGlobals
      (fun hHeadTrans hSubstHeadTrans =>
        substFalse_eval_binary_atom_head_generic_apply
          g x y xs ss bvs hXsEnv hBvsEnv hSsTrans
          hisr hxs hss hbvs hNotUOp hNotUOp1 hNotApply hNotVar hNotStuck
          hNotBinderMiddle hHeadTrans hSubstHeadTrans hGlobals
          hRecGX
          hRecY)
      hRecZ

theorem substFalse_eval_quaternary_apply_head_generic_apply
    (g y x0 x1 a xs ss bvs : Term) {M N : SmtModel}
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hStringsReplaceAllResult :
      g ≠ Term.UOp UserOp._at_strings_replace_all_result)
    (hStringsReplaceReAllResult :
      g ≠ Term.UOp UserOp._at_strings_replace_re_all_result)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.Apply (Term.Apply g y) x0) x1 ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) a)
          xs ss bvs))
    (hGlobals : model_agrees_on_globals M N)
    (hRecArg :
      ∀ {b : Term},
        IsNonbinderSubterm b
          (Term.Apply (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) a) →
        sizeOf b <
          sizeOf (Term.Apply (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) a) →
        eoHasSmtTranslation b →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt b)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) a)
            xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) a)) := by
  let aSub := __substitute_simul_rec (Term.Boolean isRename) a xs ss bvs
  have hOuterNonbinder :
      ¬ IsBinderHead (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) := by
    rintro ⟨q, v, vs, hEq⟩
    exact hNotBinderOuter q v vs hEq
  have hRecHead :
      eoHasSmtTranslation
          (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename)
                (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) xs ss bvs)) =
          __smtx_model_eval N
            (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply g y) x0) x1)) :=
    fun ht hst => hRecArg
      (by simp [IsNonbinderSubterm, hOuterNonbinder])
      (by simp; omega) ht hst
  have hRecA :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a) :=
    fun ht hst => hRecArg
      (by simp [IsNonbinderSubterm, hOuterNonbinder])
      (by simp; omega) ht hst
  have hOrigTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) a) =
        SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply g y) x0) x1))
          (__eo_to_smt a) :=
    eo_to_smt_apply_apply_apply_apply_head_generic g y x0 x1 a
      hStringsReplaceAllResult hStringsReplaceReAllResult
  have hOrigTy :
      generic_apply_type
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply g y) x0) x1))
        (__eo_to_smt a) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hOrigEval :
      generic_apply_eval
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply g y) x0) x1))
        (__eo_to_smt a) :=
    generic_apply_eval_of_non_datatype_head
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hSubstOuterRaw :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) a)
          xs ss bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) xs ss bvs)
          aSub := by
    simpa [aSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename)
        (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) a xs ss bvs
        hisr hxs hss hbvs hNotBinderOuter
  have hOuterNeStuck :
      __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) xs ss bvs)
          aSub ≠ Term.Stuck := by
    rw [← hSubstOuterRaw]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hHeadSubNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) xs ss bvs ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  rcases
      substitute_simul_rec_apply_apply_apply_eq_apply_apply_apply_of_ne_stuck
        g y x0 x1 xs ss bvs hisr hxs hss hbvs hHeadSubNe
    with ⟨gSub, ySub, x0Sub, x1Sub, hHeadShape⟩
  have hGSubStringsReplaceAllResult :
      gSub ≠ Term.UOp UserOp._at_strings_replace_all_result :=
    substitute_simul_apply_apply_apply_head_ne_untranslatable_target
      g y x0 x1 a xs ss bvs
      (Term.UOp UserOp._at_strings_replace_all_result)
      gSub ySub x0Sub x1Sub
      hXsEnv hBvsEnv hSsTrans hStringsReplaceAllResult
      (by
        intro h
        exact h (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none))
      (by intro p q h; cases h)
      (by
        simpa [eoHasSmtTranslation, RuleProofs.eo_has_smt_translation]
          using hFTrans)
      hHeadSubNe hHeadShape
  have hGSubStringsReplaceReAllResult :
      gSub ≠ Term.UOp UserOp._at_strings_replace_re_all_result :=
    substitute_simul_apply_apply_apply_head_ne_untranslatable_target
      g y x0 x1 a xs ss bvs
      (Term.UOp UserOp._at_strings_replace_re_all_result)
      gSub ySub x0Sub x1Sub
      hXsEnv hBvsEnv hSsTrans hStringsReplaceReAllResult
      (by
        intro h
        exact h (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none))
      (by intro p q h; cases h)
      (by
        simpa [eoHasSmtTranslation, RuleProofs.eo_has_smt_translation]
          using hFTrans)
      hHeadSubNe hHeadShape
  have hSubstTranslate :
      __eo_to_smt
          (Term.Apply
            (__substitute_simul_rec (Term.Boolean isRename)
              (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) xs ss bvs)
            aSub) =
        SmtTerm.Apply
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean isRename)
              (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) xs ss bvs))
          (__eo_to_smt aSub) := by
    rw [hHeadShape]
    exact
      eo_to_smt_apply_apply_apply_apply_head_generic
        gSub ySub x0Sub x1Sub aSub
        hGSubStringsReplaceAllResult hGSubStringsReplaceReAllResult
  have hSubstTy :
      generic_apply_type
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) xs ss bvs))
        (__eo_to_smt aSub) := by
    rw [hHeadShape]
    exact generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hSubstEval :
      generic_apply_eval
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) xs ss bvs))
        (__eo_to_smt aSub) := by
    rw [hHeadShape]
    exact generic_apply_eval_of_non_datatype_head
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  exact
    substFalse_eval_generic_apply
      (Term.Apply (Term.Apply (Term.Apply g y) x0) x1) a xs ss bvs
      hisr hxs hss hbvs hNotBinderOuter hOrigTranslate hSubstTranslate
      hOrigTy hSubstTy hOrigEval hSubstEval hFTrans hSubstTrans hGlobals
      hRecHead hRecA

theorem substFalse_eval_unary_uop2_any
    (op : UserOp2) (i j a xs ss bvs : Term) {M N : SmtModel}
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hFTrans : eoHasSmtTranslation (Term.Apply (Term.UOp2 op i j) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp2 op i j) a) xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename) (Term.UOp2 op i j) xs ss bvs =
        Term.UOp2 op i j)
    (hGlobals : model_agrees_on_globals M N)
    (hRecHead :
      eoHasSmtTranslation (Term.UOp2 op i j) →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) (Term.UOp2 op i j)
            xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename)
                (Term.UOp2 op i j) xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt (Term.UOp2 op i j)))
    (hRecArg :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.UOp2 op i j) a) xs ss bvs)) =
      __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp2 op i j) a)) := by
  cases op
  case extract =>
    rcases extract_indices_nat_valid_and_arg_has_smt_translation hFTrans with
      ⟨⟨_iVal, hI⟩, hJ, _hArgTrans⟩
    exact substFalse_eval_unary_uop2_special UserOp2.extract i j a xs ss bvs
      hisr hxs hss hbvs hFTrans hSubstTrans hHeadSub
      (fun {t} h => by
        rcases extract_indices_nat_valid_and_arg_has_smt_translation h with
          ⟨_hI, _hJ, hArg⟩
        exact hArg)
      (smt_model_eval_eq_of_eo_to_smt_numeral hI)
      (smt_model_eval_eq_of_eo_to_smt_nat_is_valid hJ)
      (fun X Y hI hJ hArg => by
        show __smtx_model_eval M
            (SmtTerm.extract (__eo_to_smt i) (__eo_to_smt j) (__eo_to_smt X)) =
          __smtx_model_eval N
            (SmtTerm.extract (__eo_to_smt i) (__eo_to_smt j) (__eo_to_smt Y))
        simp only [__smtx_model_eval]
        rw [hI, hJ, hArg])
      hRecArg
  case re_loop =>
    rcases re_loop_indices_nat_valid_and_arg_has_smt_translation hFTrans with
      ⟨hI, hJ, _hArgTrans⟩
    exact substFalse_eval_unary_uop2_special UserOp2.re_loop i j a xs ss bvs
      hisr hxs hss hbvs hFTrans hSubstTrans hHeadSub
      (fun {t} h => by
        rcases re_loop_indices_nat_valid_and_arg_has_smt_translation h with
          ⟨_hI, _hJ, hArg⟩
        exact hArg)
      (smt_model_eval_eq_of_eo_to_smt_nat_is_valid hI)
      (smt_model_eval_eq_of_eo_to_smt_nat_is_valid hJ)
      (fun X Y hI hJ hArg => by
        show __smtx_model_eval M
            (SmtTerm.re_loop (__eo_to_smt i) (__eo_to_smt j) (__eo_to_smt X)) =
          __smtx_model_eval N
            (SmtTerm.re_loop (__eo_to_smt i) (__eo_to_smt j) (__eo_to_smt Y))
        simp only [__smtx_model_eval]
        rw [hI, hJ, hArg])
      hRecArg
  case _at_quantifiers_skolemize =>
    exact substFalse_eval_generic_apply
      (Term.UOp2 UserOp2._at_quantifiers_skolemize i j) a xs ss bvs
      hisr hxs hss hbvs
      (by intro q v vs hEq; cases hEq)
      (by rfl)
      (by
        rw [hHeadSub]
        rfl)
      (quant_skolemize_apply_generic_type i j a)
      (by
        rw [hHeadSub]
        exact quant_skolemize_apply_generic_type i j
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs))
      (quant_skolemize_apply_generic_eval i j a)
      (by
        simpa [hHeadSub] using
          quant_skolemize_apply_generic_eval i j
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs))
      hFTrans hSubstTrans hGlobals hRecHead hRecArg
  case _at_const =>
    exact substFalse_eval_generic_apply
      (Term.UOp2 UserOp2._at_const i j) a xs ss bvs
      hisr hxs hss hbvs
      (by intro q v vs hEq; cases hEq)
      (by rfl)
      (by
        rw [hHeadSub]
        rfl)
      (at_const_apply_generic_type i j a)
      (by
        rw [hHeadSub]
        exact at_const_apply_generic_type i j
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs))
      (at_const_apply_generic_eval i j a)
      (by
        simpa [hHeadSub] using
          at_const_apply_generic_eval i j
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs))
      hFTrans hSubstTrans hGlobals hRecHead hRecArg

theorem substFalse_eval_unary_uop3_any
    (op : UserOp3) (i j k a xs ss bvs : Term) {M N : SmtModel}
    (hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hFTrans : eoHasSmtTranslation (Term.Apply (Term.UOp3 op i j k) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp3 op i j k) a) xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename) (Term.UOp3 op i j k) xs ss bvs =
        Term.UOp3 op i j k)
    (hGlobals : model_agrees_on_globals M N)
    (hRecHead :
      eoHasSmtTranslation (Term.UOp3 op i j k) →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) (Term.UOp3 op i j k)
            xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename)
                (Term.UOp3 op i j k) xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt (Term.UOp3 op i j k)))
    (hRecArg :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.UOp3 op i j k) a) xs ss bvs)) =
      __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp3 op i j k) a)) := by
  cases op
  case _at_re_unfold_pos_component =>
    exact false_of_apply_re_unfold_pos_component hFTrans
  case _at_witness_string_length =>
    exact substFalse_eval_generic_apply
      (Term.UOp3 UserOp3._at_witness_string_length i j k) a xs ss bvs
      hisr hxs hss hbvs
      (by intro q v vs hEq; cases hEq)
      (by rfl)
      (by
        rw [hHeadSub]
        rfl)
      (witness_string_length_apply_generic_type i j k a)
      (by
        rw [hHeadSub]
        exact witness_string_length_apply_generic_type i j k
          (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs))
      (witness_string_length_apply_generic_eval i j k a)
      (by
        simpa [hHeadSub] using
          witness_string_length_apply_generic_eval i j k
            (__substitute_simul_rec (Term.Boolean isRename) a xs ss bvs))
      hFTrans hSubstTrans hGlobals hRecHead hRecArg

/--
Shared application case for simultaneous-substitution evaluation.

The mode-specific inductions supply evaluation equality for every proper
subterm.  Once the outer application is known not to be a binder, the rest of
the proof is independent of `isRename`: it is the common operator/application
dispatcher for both ordinary substitution and uniform renaming. -/
theorem substitute_simul_eval_nonbinder
    {isRename : Bool}
    (f a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    {M N : SmtModel}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hBinder : ¬ IsBinderHead f)
    (hFTrans : RuleProofs.eo_has_smt_translation (Term.Apply f a))
    (hSubstTrans : RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean isRename)
        (Term.Apply f a) xs ss bvs))
    (hM : model_wf M)
    (hN : model_wf N)
    (hGlobals : model_agrees_on_globals M N)
    (hRecArg :
      ∀ {b : Term},
        IsNonbinderSubterm b (Term.Apply f a) →
        sizeOf b < sizeOf (Term.Apply f a) →
        eoHasSmtTranslation b →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean isRename) b xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt b)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply f a) xs ss bvs)) =
      __smtx_model_eval N (__eo_to_smt (Term.Apply f a)) := by
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSsTrans
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by
    cases isRename <;> decide
  by_cases hNot : f = Term.UOp UserOp.not
  · subst f
    exact substFalse_eval_unary_op UserOp.not a xs ss bvs
      hisr hxs hss hbvs hFTrans hSubstTrans
      (substitute_simul_rec_uop_eq_self UserOp.not xs ss bvs
        hXsEnv hBvsEnv hSsTrans)
      (fun {t} h => not_arg_has_smt_translation_of_has_smt_translation h)
      (fun X Y h => by
        show __smtx_model_eval M (SmtTerm.not (__eo_to_smt X)) =
          __smtx_model_eval N (SmtTerm.not (__eo_to_smt Y))
        simp only [__smtx_model_eval]; rw [h])
      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
  · by_cases hToReal : f = Term.UOp UserOp.to_real
    · subst f
      exact substFalse_eval_unary_op UserOp.to_real a xs ss bvs
        hisr hxs hss hbvs hFTrans hSubstTrans
        (substitute_simul_rec_uop_eq_self UserOp.to_real xs ss bvs
          hXsEnv hBvsEnv hSsTrans)
        (fun {t} h => to_real_arg_has_smt_translation_of_has_smt_translation h)
        (fun X Y h => by
          show __smtx_model_eval M (SmtTerm.to_real (__eo_to_smt X)) =
            __smtx_model_eval N (SmtTerm.to_real (__eo_to_smt Y))
          simp only [__smtx_model_eval]; rw [h])
        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
    · by_cases hToInt : f = Term.UOp UserOp.to_int
      · subst f
        exact substFalse_eval_unary_op UserOp.to_int a xs ss bvs
          hisr hxs hss hbvs hFTrans hSubstTrans
          (substitute_simul_rec_uop_eq_self UserOp.to_int xs ss bvs
            hXsEnv hBvsEnv hSsTrans)
          (fun {t} h => to_int_arg_has_smt_translation_of_has_smt_translation h)
          (fun X Y h => by
            show __smtx_model_eval M (SmtTerm.to_int (__eo_to_smt X)) =
              __smtx_model_eval N (SmtTerm.to_int (__eo_to_smt Y))
            simp only [__smtx_model_eval]; rw [h])
          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
      · by_cases hIsInt : f = Term.UOp UserOp.is_int
        · subst f
          exact substFalse_eval_unary_op UserOp.is_int a xs ss bvs
            hisr hxs hss hbvs hFTrans hSubstTrans
            (substitute_simul_rec_uop_eq_self UserOp.is_int xs ss bvs
              hXsEnv hBvsEnv hSsTrans)
            (fun {t} h => is_int_arg_has_smt_translation_of_has_smt_translation h)
            (fun X Y h => by
              show __smtx_model_eval M (SmtTerm.is_int (__eo_to_smt X)) =
                __smtx_model_eval N (SmtTerm.is_int (__eo_to_smt Y))
              simp only [__smtx_model_eval]; rw [h])
            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
        · by_cases hAbs : f = Term.UOp UserOp.abs
          · subst f
            exact substFalse_eval_unary_op UserOp.abs a xs ss bvs
              hisr hxs hss hbvs hFTrans hSubstTrans
              (substitute_simul_rec_uop_eq_self UserOp.abs xs ss bvs
                hXsEnv hBvsEnv hSsTrans)
              (fun {t} h => abs_arg_has_smt_translation_of_has_smt_translation h)
              (fun X Y h => by
                show __smtx_model_eval M (SmtTerm.abs (__eo_to_smt X)) =
                  __smtx_model_eval N (SmtTerm.abs (__eo_to_smt Y))
                simp only [__smtx_model_eval]; rw [h])
              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
          · by_cases hUneg : f = Term.UOp UserOp.__eoo_neg_2
            · subst f
              exact substFalse_eval_unary_op UserOp.__eoo_neg_2 a xs ss bvs
                hisr hxs hss hbvs hFTrans hSubstTrans
                (substitute_simul_rec_uop_eq_self UserOp.__eoo_neg_2 xs ss bvs
                  hXsEnv hBvsEnv hSsTrans)
                (fun {t} h => uneg_arg_has_smt_translation_of_has_smt_translation h)
                (fun X Y h => by
                  show __smtx_model_eval M (SmtTerm.uneg (__eo_to_smt X)) =
                    __smtx_model_eval N (SmtTerm.uneg (__eo_to_smt Y))
                  simp only [__smtx_model_eval]; rw [h])
                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
            · by_cases hPow2 : f = Term.UOp UserOp.int_pow2
              · subst f
                exact substFalse_eval_unary_op UserOp.int_pow2 a xs ss bvs
                  hisr hxs hss hbvs hFTrans hSubstTrans
                  (substitute_simul_rec_uop_eq_self UserOp.int_pow2 xs ss bvs
                    hXsEnv hBvsEnv hSsTrans)
                  (fun {t} h => int_pow2_arg_has_smt_translation_of_has_smt_translation h)
                  (fun X Y h => by
                    show __smtx_model_eval M (SmtTerm.int_pow2 (__eo_to_smt X)) =
                      __smtx_model_eval N (SmtTerm.int_pow2 (__eo_to_smt Y))
                    simp only [__smtx_model_eval]; rw [h])
                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
              · by_cases hLog2 : f = Term.UOp UserOp.int_log2
                · subst f
                  exact substFalse_eval_unary_op UserOp.int_log2 a xs ss bvs
                    hisr hxs hss hbvs hFTrans hSubstTrans
                    (substitute_simul_rec_uop_eq_self UserOp.int_log2 xs ss bvs
                      hXsEnv hBvsEnv hSsTrans)
                    (fun {t} h => int_log2_arg_has_smt_translation_of_has_smt_translation h)
                    (fun X Y h => by
                      show __smtx_model_eval M (SmtTerm.int_log2 (__eo_to_smt X)) =
                        __smtx_model_eval N (SmtTerm.int_log2 (__eo_to_smt Y))
                      simp only [__smtx_model_eval]; rw [h])
                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                · by_cases hPurify : f = Term.UOp UserOp._at_purify
                  · subst f
                    exact substFalse_eval_unary_op UserOp._at_purify a xs ss bvs
                      hisr hxs hss hbvs hFTrans hSubstTrans
                      (substitute_simul_rec_uop_eq_self UserOp._at_purify xs ss bvs
                        hXsEnv hBvsEnv hSsTrans)
                      (fun {t} h => purify_arg_has_smt_translation_of_has_smt_translation h)
                      (fun X Y h => by
                        show __smtx_model_eval M (SmtTerm._at_purify (__eo_to_smt X)) =
                          __smtx_model_eval N (SmtTerm._at_purify (__eo_to_smt Y))
                        simp only [__smtx_model_eval]; rw [h])
                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                  · by_cases hIntIspow2 : f = Term.UOp UserOp.int_ispow2
                    · subst f
                      exact substFalse_eval_unary_op UserOp.int_ispow2 a xs ss bvs
                        hisr hxs hss hbvs hFTrans hSubstTrans
                        (substitute_simul_rec_uop_eq_self UserOp.int_ispow2 xs ss bvs
                          hXsEnv hBvsEnv hSsTrans)
                        (fun {t} h => int_ispow2_arg_has_smt_translation_of_has_smt_translation h)
                        (fun X Y h => by
                          show __smtx_model_eval M
                              (SmtTerm.and (SmtTerm.geq (__eo_to_smt X) (SmtTerm.Numeral 0))
                                (SmtTerm.eq (__eo_to_smt X)
                                  (SmtTerm.int_pow2 (SmtTerm.int_log2 (__eo_to_smt X))))) =
                            __smtx_model_eval N
                              (SmtTerm.and (SmtTerm.geq (__eo_to_smt Y) (SmtTerm.Numeral 0))
                                (SmtTerm.eq (__eo_to_smt Y)
                                  (SmtTerm.int_pow2 (SmtTerm.int_log2 (__eo_to_smt Y)))))
                          simp [__smtx_model_eval, h])
                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                    · by_cases hBvnot : f = Term.UOp UserOp.bvnot
                      · subst f
                        exact substFalse_eval_unary_op UserOp.bvnot a xs ss bvs
                          hisr hxs hss hbvs hFTrans hSubstTrans
                          (substitute_simul_rec_uop_eq_self UserOp.bvnot xs ss bvs
                            hXsEnv hBvsEnv hSsTrans)
                          (fun {t} h => bvnot_arg_has_smt_translation_of_has_smt_translation h)
                          (fun X Y h => by
                            show __smtx_model_eval M (SmtTerm.bvnot (__eo_to_smt X)) =
                              __smtx_model_eval N (SmtTerm.bvnot (__eo_to_smt Y))
                            simp only [__smtx_model_eval]; rw [h])
                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                      · by_cases hBvneg : f = Term.UOp UserOp.bvneg
                        · subst f
                          exact substFalse_eval_unary_op UserOp.bvneg a xs ss bvs
                            hisr hxs hss hbvs hFTrans hSubstTrans
                            (substitute_simul_rec_uop_eq_self UserOp.bvneg xs ss bvs
                              hXsEnv hBvsEnv hSsTrans)
                            (fun {t} h => bvneg_arg_has_smt_translation_of_has_smt_translation h)
                            (fun X Y h => by
                              show __smtx_model_eval M (SmtTerm.bvneg (__eo_to_smt X)) =
                                __smtx_model_eval N (SmtTerm.bvneg (__eo_to_smt Y))
                              simp only [__smtx_model_eval]; rw [h])
                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                        · by_cases hBvnego : f = Term.UOp UserOp.bvnego
                          · subst f
                            exact substFalse_eval_unary_op UserOp.bvnego a xs ss bvs
                              hisr hxs hss hbvs hFTrans hSubstTrans
                              (substitute_simul_rec_uop_eq_self UserOp.bvnego xs ss bvs
                                hXsEnv hBvsEnv hSsTrans)
                              (fun {t} h => bvnego_arg_has_smt_translation_of_has_smt_translation h)
                              (fun X Y h => by
                                show __smtx_model_eval M (SmtTerm.bvnego (__eo_to_smt X)) =
                                  __smtx_model_eval N (SmtTerm.bvnego (__eo_to_smt Y))
                                simp only [__smtx_model_eval]; rw [h])
                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                          · by_cases hStrLen : f = Term.UOp UserOp.str_len
                            · subst f
                              exact substFalse_eval_unary_op UserOp.str_len a xs ss bvs
                                hisr hxs hss hbvs hFTrans hSubstTrans
                                (substitute_simul_rec_uop_eq_self UserOp.str_len xs ss bvs
                                  hXsEnv hBvsEnv hSsTrans)
                                (fun {t} h => str_len_arg_has_smt_translation_of_has_smt_translation h)
                                (fun X Y h => by
                                  show __smtx_model_eval M (SmtTerm.str_len (__eo_to_smt X)) =
                                    __smtx_model_eval N (SmtTerm.str_len (__eo_to_smt Y))
                                  simp only [__smtx_model_eval]; rw [h])
                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                            · by_cases hStrRev : f = Term.UOp UserOp.str_rev
                              · subst f
                                exact substFalse_eval_unary_op UserOp.str_rev a xs ss bvs
                                  hisr hxs hss hbvs hFTrans hSubstTrans
                                  (substitute_simul_rec_uop_eq_self UserOp.str_rev xs ss bvs
                                    hXsEnv hBvsEnv hSsTrans)
                                  (fun {t} h => str_rev_arg_has_smt_translation_of_has_smt_translation h)
                                  (fun X Y h => by
                                    show __smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt X)) =
                                      __smtx_model_eval N (SmtTerm.str_rev (__eo_to_smt Y))
                                    simp only [__smtx_model_eval]; rw [h])
                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                              · by_cases hStrToInt : f = Term.UOp UserOp.str_to_int
                                · subst f
                                  exact substFalse_eval_unary_op UserOp.str_to_int a xs ss bvs
                                    hisr hxs hss hbvs hFTrans hSubstTrans
                                    (substitute_simul_rec_uop_eq_self UserOp.str_to_int xs ss bvs
                                      hXsEnv hBvsEnv hSsTrans)
                                    (fun {t} h => str_to_int_arg_has_smt_translation_of_has_smt_translation h)
                                    (fun X Y h => by
                                      show __smtx_model_eval M (SmtTerm.str_to_int (__eo_to_smt X)) =
                                        __smtx_model_eval N (SmtTerm.str_to_int (__eo_to_smt Y))
                                      simp only [__smtx_model_eval]; rw [h])
                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                · by_cases hStrToRe : f = Term.UOp UserOp.str_to_re
                                  · subst f
                                    exact substFalse_eval_unary_op UserOp.str_to_re a xs ss bvs
                                      hisr hxs hss hbvs hFTrans hSubstTrans
                                      (substitute_simul_rec_uop_eq_self UserOp.str_to_re xs ss bvs
                                        hXsEnv hBvsEnv hSsTrans)
                                      (fun {t} h => str_to_re_arg_has_smt_translation_of_has_smt_translation h)
                                      (fun X Y h => by
                                        show __smtx_model_eval M (SmtTerm.str_to_re (__eo_to_smt X)) =
                                          __smtx_model_eval N (SmtTerm.str_to_re (__eo_to_smt Y))
                                        simp only [__smtx_model_eval]; rw [h])
                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                  · by_cases hReMult : f = Term.UOp UserOp.re_mult
                                    · subst f
                                      exact substFalse_eval_unary_op UserOp.re_mult a xs ss bvs
                                        hisr hxs hss hbvs hFTrans hSubstTrans
                                        (substitute_simul_rec_uop_eq_self UserOp.re_mult xs ss bvs
                                          hXsEnv hBvsEnv hSsTrans)
                                        (fun {t} h => re_mult_arg_has_smt_translation_of_has_smt_translation h)
                                        (fun X Y h => by
                                          show __smtx_model_eval M (SmtTerm.re_mult (__eo_to_smt X)) =
                                            __smtx_model_eval N (SmtTerm.re_mult (__eo_to_smt Y))
                                          simp only [__smtx_model_eval]; rw [h])
                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                    · by_cases hSeqUnit : f = Term.UOp UserOp.seq_unit
                                      · subst f
                                        exact substFalse_eval_unary_op UserOp.seq_unit a xs ss bvs
                                          hisr hxs hss hbvs hFTrans hSubstTrans
                                          (substitute_simul_rec_uop_eq_self UserOp.seq_unit xs ss bvs
                                            hXsEnv hBvsEnv hSsTrans)
                                          (fun {t} h => seq_unit_arg_has_smt_translation_of_has_smt_translation h)
                                          (fun X Y h => by
                                            show __smtx_model_eval M (SmtTerm.seq_unit (__eo_to_smt X)) =
                                              __smtx_model_eval N (SmtTerm.seq_unit (__eo_to_smt Y))
                                            simp only [__smtx_model_eval]; rw [h])
                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                      · by_cases hSetSingletonOp : f = Term.UOp UserOp.set_singleton
                                        · subst f
                                          exact substFalse_eval_unary_op UserOp.set_singleton a xs ss bvs
                                            hisr hxs hss hbvs hFTrans hSubstTrans
                                            (substitute_simul_rec_uop_eq_self UserOp.set_singleton xs ss bvs
                                              hXsEnv hBvsEnv hSsTrans)
                                            (fun {t} h => set_singleton_arg_has_smt_translation_of_has_smt_translation h)
                                            (fun X Y h => by
                                              show __smtx_model_eval M (SmtTerm.set_singleton (__eo_to_smt X)) =
                                                __smtx_model_eval N (SmtTerm.set_singleton (__eo_to_smt Y))
                                              simp only [__smtx_model_eval]; rw [h])
                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                        · by_cases hStrToLower : f = Term.UOp UserOp.str_to_lower
                                          · subst f
                                            exact substFalse_eval_unary_op UserOp.str_to_lower a xs ss bvs
                                              hisr hxs hss hbvs hFTrans hSubstTrans
                                              (substitute_simul_rec_uop_eq_self UserOp.str_to_lower xs ss bvs
                                                hXsEnv hBvsEnv hSsTrans)
                                              (fun {t} h => str_to_lower_arg_has_smt_translation_of_has_smt_translation h)
                                              (fun X Y h => by
                                                show __smtx_model_eval M (SmtTerm.str_to_lower (__eo_to_smt X)) =
                                                  __smtx_model_eval N (SmtTerm.str_to_lower (__eo_to_smt Y))
                                                simp only [__smtx_model_eval]; rw [h])
                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                          · by_cases hStrToUpper : f = Term.UOp UserOp.str_to_upper
                                            · subst f
                                              exact substFalse_eval_unary_op UserOp.str_to_upper a xs ss bvs
                                                hisr hxs hss hbvs hFTrans hSubstTrans
                                                (substitute_simul_rec_uop_eq_self UserOp.str_to_upper xs ss bvs
                                                  hXsEnv hBvsEnv hSsTrans)
                                                (fun {t} h => str_to_upper_arg_has_smt_translation_of_has_smt_translation h)
                                                (fun X Y h => by
                                                  show __smtx_model_eval M (SmtTerm.str_to_upper (__eo_to_smt X)) =
                                                    __smtx_model_eval N (SmtTerm.str_to_upper (__eo_to_smt Y))
                                                  simp only [__smtx_model_eval]; rw [h])
                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                            · by_cases hStrToCode : f = Term.UOp UserOp.str_to_code
                                              · subst f
                                                exact substFalse_eval_unary_op UserOp.str_to_code a xs ss bvs
                                                  hisr hxs hss hbvs hFTrans hSubstTrans
                                                  (substitute_simul_rec_uop_eq_self UserOp.str_to_code xs ss bvs
                                                    hXsEnv hBvsEnv hSsTrans)
                                                  (fun {t} h => str_to_code_arg_has_smt_translation_of_has_smt_translation h)
                                                  (fun X Y h => by
                                                    show __smtx_model_eval M (SmtTerm.str_to_code (__eo_to_smt X)) =
                                                      __smtx_model_eval N (SmtTerm.str_to_code (__eo_to_smt Y))
                                                    simp only [__smtx_model_eval]; rw [h])
                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                              · by_cases hStrFromCode : f = Term.UOp UserOp.str_from_code
                                                · subst f
                                                  exact substFalse_eval_unary_op UserOp.str_from_code a xs ss bvs
                                                    hisr hxs hss hbvs hFTrans hSubstTrans
                                                    (substitute_simul_rec_uop_eq_self UserOp.str_from_code xs ss bvs
                                                      hXsEnv hBvsEnv hSsTrans)
                                                    (fun {t} h => str_from_code_arg_has_smt_translation_of_has_smt_translation h)
                                                    (fun X Y h => by
                                                      show __smtx_model_eval M (SmtTerm.str_from_code (__eo_to_smt X)) =
                                                        __smtx_model_eval N (SmtTerm.str_from_code (__eo_to_smt Y))
                                                      simp only [__smtx_model_eval]; rw [h])
                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                · by_cases hStrIsDigit : f = Term.UOp UserOp.str_is_digit
                                                  · subst f
                                                    exact substFalse_eval_unary_op UserOp.str_is_digit a xs ss bvs
                                                      hisr hxs hss hbvs hFTrans hSubstTrans
                                                      (substitute_simul_rec_uop_eq_self UserOp.str_is_digit xs ss bvs
                                                        hXsEnv hBvsEnv hSsTrans)
                                                      (fun {t} h => str_is_digit_arg_has_smt_translation_of_has_smt_translation h)
                                                      (fun X Y h => by
                                                        show __smtx_model_eval M (SmtTerm.str_is_digit (__eo_to_smt X)) =
                                                          __smtx_model_eval N (SmtTerm.str_is_digit (__eo_to_smt Y))
                                                        simp only [__smtx_model_eval]; rw [h])
                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                  · by_cases hStrFromInt : f = Term.UOp UserOp.str_from_int
                                                    · subst f
                                                      exact substFalse_eval_unary_op UserOp.str_from_int a xs ss bvs
                                                        hisr hxs hss hbvs hFTrans hSubstTrans
                                                        (substitute_simul_rec_uop_eq_self UserOp.str_from_int xs ss bvs
                                                          hXsEnv hBvsEnv hSsTrans)
                                                        (fun {t} h => str_from_int_arg_has_smt_translation_of_has_smt_translation h)
                                                        (fun X Y h => by
                                                          show __smtx_model_eval M (SmtTerm.str_from_int (__eo_to_smt X)) =
                                                            __smtx_model_eval N (SmtTerm.str_from_int (__eo_to_smt Y))
                                                          simp only [__smtx_model_eval]; rw [h])
                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                    · by_cases hRePlus : f = Term.UOp UserOp.re_plus
                                                      · subst f
                                                        exact substFalse_eval_unary_op UserOp.re_plus a xs ss bvs
                                                          hisr hxs hss hbvs hFTrans hSubstTrans
                                                          (substitute_simul_rec_uop_eq_self UserOp.re_plus xs ss bvs
                                                            hXsEnv hBvsEnv hSsTrans)
                                                          (fun {t} h => re_plus_arg_has_smt_translation_of_has_smt_translation h)
                                                          (fun X Y h => by
                                                            show __smtx_model_eval M (SmtTerm.re_plus (__eo_to_smt X)) =
                                                              __smtx_model_eval N (SmtTerm.re_plus (__eo_to_smt Y))
                                                            simp only [__smtx_model_eval]; rw [h])
                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                      · by_cases hReOpt : f = Term.UOp UserOp.re_opt
                                                        · subst f
                                                          exact substFalse_eval_unary_op UserOp.re_opt a xs ss bvs
                                                            hisr hxs hss hbvs hFTrans hSubstTrans
                                                            (substitute_simul_rec_uop_eq_self UserOp.re_opt xs ss bvs
                                                              hXsEnv hBvsEnv hSsTrans)
                                                            (fun {t} h => re_opt_arg_has_smt_translation_of_has_smt_translation h)
                                                            (fun X Y h => by
                                                              show __smtx_model_eval M (SmtTerm.re_opt (__eo_to_smt X)) =
                                                                __smtx_model_eval N (SmtTerm.re_opt (__eo_to_smt Y))
                                                              simp only [__smtx_model_eval]; rw [h])
                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                        · by_cases hReComp : f = Term.UOp UserOp.re_comp
                                                          · subst f
                                                            exact substFalse_eval_unary_op UserOp.re_comp a xs ss bvs
                                                              hisr hxs hss hbvs hFTrans hSubstTrans
                                                              (substitute_simul_rec_uop_eq_self UserOp.re_comp xs ss bvs
                                                                hXsEnv hBvsEnv hSsTrans)
                                                              (fun {t} h => re_comp_arg_has_smt_translation_of_has_smt_translation h)
                                                              (fun X Y h => by
                                                                show __smtx_model_eval M (SmtTerm.re_comp (__eo_to_smt X)) =
                                                                  __smtx_model_eval N (SmtTerm.re_comp (__eo_to_smt Y))
                                                                simp only [__smtx_model_eval]; rw [h])
                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                          · by_cases hUbvToInt : f = Term.UOp UserOp.ubv_to_int
                                                            · subst f
                                                              exact substFalse_eval_unary_op UserOp.ubv_to_int a xs ss bvs
                                                                hisr hxs hss hbvs hFTrans hSubstTrans
                                                                (substitute_simul_rec_uop_eq_self UserOp.ubv_to_int xs ss bvs
                                                                  hXsEnv hBvsEnv hSsTrans)
                                                                (fun {t} h => ubv_to_int_arg_has_smt_translation_of_has_smt_translation h)
                                                                (fun X Y h => by
                                                                  show __smtx_model_eval M (SmtTerm.ubv_to_int (__eo_to_smt X)) =
                                                                    __smtx_model_eval N (SmtTerm.ubv_to_int (__eo_to_smt Y))
                                                                  simp only [__smtx_model_eval]; rw [h])
                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                            · by_cases hSbvToInt : f = Term.UOp UserOp.sbv_to_int
                                                              · subst f
                                                                exact substFalse_eval_unary_op UserOp.sbv_to_int a xs ss bvs
                                                                  hisr hxs hss hbvs hFTrans hSubstTrans
                                                                  (substitute_simul_rec_uop_eq_self UserOp.sbv_to_int xs ss bvs
                                                                    hXsEnv hBvsEnv hSsTrans)
                                                                  (fun {t} h => sbv_to_int_arg_has_smt_translation_of_has_smt_translation h)
                                                                  (fun X Y h => by
                                                                    show __smtx_model_eval M (SmtTerm.sbv_to_int (__eo_to_smt X)) =
                                                                      __smtx_model_eval N (SmtTerm.sbv_to_int (__eo_to_smt Y))
                                                                    simp only [__smtx_model_eval]; rw [h])
                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                              · by_cases hStringsStoiNonDigit : f = Term.UOp UserOp._at_strings_stoi_non_digit
                                                                · subst f
                                                                  exact substFalse_eval_unary_op UserOp._at_strings_stoi_non_digit a xs ss bvs
                                                                    hisr hxs hss hbvs hFTrans hSubstTrans
                                                                    (substitute_simul_rec_uop_eq_self UserOp._at_strings_stoi_non_digit xs ss bvs
                                                                      hXsEnv hBvsEnv hSsTrans)
                                                                    (fun {t} h => strings_stoi_non_digit_arg_has_smt_translation_of_has_smt_translation h)
                                                                    (fun X Y h => by
                                                                      show __smtx_model_eval M
                                                                          (SmtTerm.str_indexof_re (__eo_to_smt X)
                                                                            (SmtTerm.re_inter SmtTerm.re_allchar
                                                                              (SmtTerm.re_comp
                                                                                (SmtTerm.re_range (SmtTerm.String (native_string_lit "0"))
                                                                                  (SmtTerm.String (native_string_lit "9")))))
                                                                            (SmtTerm.Numeral 0)) =
                                                                        __smtx_model_eval N
                                                                          (SmtTerm.str_indexof_re (__eo_to_smt Y)
                                                                            (SmtTerm.re_inter SmtTerm.re_allchar
                                                                              (SmtTerm.re_comp
                                                                                (SmtTerm.re_range (SmtTerm.String (native_string_lit "0"))
                                                                                  (SmtTerm.String (native_string_lit "9")))))
                                                                            (SmtTerm.Numeral 0))
                                                                      simp [__smtx_model_eval, h])
                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                · by_cases hIntDivByZero : f = Term.UOp UserOp._at_int_div_by_zero
                                                                  · subst f
                                                                    exact substFalse_eval_unary_op UserOp._at_int_div_by_zero a xs ss bvs
                                                                      hisr hxs hss hbvs hFTrans hSubstTrans
                                                                      (substitute_simul_rec_uop_eq_self UserOp._at_int_div_by_zero xs ss bvs
                                                                        hXsEnv hBvsEnv hSsTrans)
                                                                      (fun {t} h => int_div_by_zero_arg_has_smt_translation_of_has_smt_translation h)
                                                                      (fun X Y h => by
                                                                        show __smtx_model_eval M (SmtTerm.div (__eo_to_smt X) (SmtTerm.Numeral 0)) =
                                                                          __smtx_model_eval N (SmtTerm.div (__eo_to_smt Y) (SmtTerm.Numeral 0))
                                                                        simp [__smtx_model_eval, h,
                                                                          smtx_model_eval_apply_eq_of_globals hGlobals,
                                                                          hGlobals.1])
                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                  · by_cases hModByZero : f = Term.UOp UserOp._at_mod_by_zero
                                                                    · subst f
                                                                      exact substFalse_eval_unary_op UserOp._at_mod_by_zero a xs ss bvs
                                                                        hisr hxs hss hbvs hFTrans hSubstTrans
                                                                        (substitute_simul_rec_uop_eq_self UserOp._at_mod_by_zero xs ss bvs
                                                                          hXsEnv hBvsEnv hSsTrans)
                                                                        (fun {t} h => mod_by_zero_arg_has_smt_translation_of_has_smt_translation h)
                                                                        (fun X Y h => by
                                                                          show __smtx_model_eval M (SmtTerm.mod (__eo_to_smt X) (SmtTerm.Numeral 0)) =
                                                                            __smtx_model_eval N (SmtTerm.mod (__eo_to_smt Y) (SmtTerm.Numeral 0))
                                                                          simp [__smtx_model_eval, h,
                                                                            smtx_model_eval_apply_eq_of_globals hGlobals,
                                                                            hGlobals.1])
                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                    · by_cases hQdivByZero : f = Term.UOp UserOp._at_div_by_zero
                                                                      · subst f
                                                                        exact substFalse_eval_unary_op UserOp._at_div_by_zero a xs ss bvs
                                                                          hisr hxs hss hbvs hFTrans hSubstTrans
                                                                          (substitute_simul_rec_uop_eq_self UserOp._at_div_by_zero xs ss bvs
                                                                            hXsEnv hBvsEnv hSsTrans)
                                                                          (fun {t} h => qdiv_by_zero_arg_has_smt_translation_of_has_smt_translation h)
                                                                          (fun X Y h => by
                                                                            show __smtx_model_eval M
                                                                                (SmtTerm.qdiv (__eo_to_smt X)
                                                                                  (SmtTerm.Rational (native_mk_rational 0 1))) =
                                                                              __smtx_model_eval N
                                                                                (SmtTerm.qdiv (__eo_to_smt Y)
                                                                                  (SmtTerm.Rational (native_mk_rational 0 1)))
                                                                            simp [__smtx_model_eval, h,
                                                                              smtx_model_eval_apply_eq_of_globals hGlobals,
                                                                              hGlobals.1])
                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                      · by_cases hBvsize : f = Term.UOp UserOp._at_bvsize
                                                                        · subst f
                                                                          exact substFalse_eval_unary_op_type_dependent
                                                                            UserOp._at_bvsize a xs ss bvs hM hN
                                                                            hisr hxs hss hbvs hFTrans hSubstTrans
                                                                            (substitute_simul_rec_uop_eq_self UserOp._at_bvsize xs ss bvs
                                                                              hXsEnv hBvsEnv hSsTrans)
                                                                            (fun {t} h => bvsize_arg_has_smt_translation_of_has_smt_translation h)
                                                                            (fun X Y hTy _hArg => by
                                                                              show __smtx_model_eval M
                                                                                  (native_ite
                                                                                    (native_zleq 0
                                                                                      (__eo_to_smt_bv_size
                                                                                        (__smtx_typeof (__eo_to_smt X))))
                                                                                    (SmtTerm._at_purify
                                                                                      (SmtTerm.Numeral
                                                                                        (__eo_to_smt_bv_size
                                                                                          (__smtx_typeof (__eo_to_smt X)))))
                                                                                    SmtTerm.None) =
                                                                                __smtx_model_eval N
                                                                                  (native_ite
                                                                                    (native_zleq 0
                                                                                      (__eo_to_smt_bv_size
                                                                                        (__smtx_typeof (__eo_to_smt Y))))
                                                                                      (SmtTerm._at_purify
                                                                                        (SmtTerm.Numeral
                                                                                          (__eo_to_smt_bv_size
                                                                                            (__smtx_typeof (__eo_to_smt Y)))))
                                                                                        SmtTerm.None)
                                                                              rw [hTy]
                                                                              cases native_zleq 0
                                                                                  (__eo_to_smt_bv_size
                                                                                    (__smtx_typeof (__eo_to_smt Y))) <;>
                                                                                simp [native_ite, __smtx_model_eval, __smtx_model_eval__at_purify])
                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                        · by_cases hBvredand : f = Term.UOp UserOp.bvredand
                                                                          · subst f
                                                                            exact substFalse_eval_unary_op_type_dependent
                                                                              UserOp.bvredand a xs ss bvs hM hN
                                                                              hisr hxs hss hbvs hFTrans hSubstTrans
                                                                              (substitute_simul_rec_uop_eq_self UserOp.bvredand xs ss bvs
                                                                                hXsEnv hBvsEnv hSsTrans)
                                                                              (fun {t} h => bvredand_arg_has_smt_translation_of_has_smt_translation h)
                                                                              (fun X Y hTy hArg => by
                                                                                show __smtx_model_eval M
                                                                                    (SmtTerm.bvcomp (__eo_to_smt X)
                                                                                      (SmtTerm.bvnot
                                                                                        (SmtTerm.Binary
                                                                                          (__eo_to_smt_bv_size
                                                                                            (__smtx_typeof (__eo_to_smt X)))
                                                                                          0))) =
                                                                                  __smtx_model_eval N
                                                                                    (SmtTerm.bvcomp (__eo_to_smt Y)
                                                                                        (SmtTerm.bvnot
                                                                                          (SmtTerm.Binary
                                                                                            (__eo_to_smt_bv_size
                                                                                              (__smtx_typeof (__eo_to_smt Y)))
                                                                                                0)))
                                                                                rw [hTy]
                                                                                simp [__smtx_model_eval, hArg])
                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                          · by_cases hBvredor : f = Term.UOp UserOp.bvredor
                                                                            · subst f
                                                                              exact substFalse_eval_unary_op_type_dependent
                                                                                UserOp.bvredor a xs ss bvs hM hN
                                                                                hisr hxs hss hbvs hFTrans hSubstTrans
                                                                                (substitute_simul_rec_uop_eq_self UserOp.bvredor xs ss bvs
                                                                                  hXsEnv hBvsEnv hSsTrans)
                                                                                (fun {t} h => bvredor_arg_has_smt_translation_of_has_smt_translation h)
                                                                                (fun X Y hTy hArg => by
                                                                                  show __smtx_model_eval M
                                                                                      (SmtTerm.bvnot
                                                                                        (SmtTerm.bvcomp (__eo_to_smt X)
                                                                                          (SmtTerm.Binary
                                                                                            (__eo_to_smt_bv_size
                                                                                              (__smtx_typeof (__eo_to_smt X)))
                                                                                            0))) =
                                                                                    __smtx_model_eval N
                                                                                      (SmtTerm.bvnot
                                                                                          (SmtTerm.bvcomp (__eo_to_smt Y)
                                                                                            (SmtTerm.Binary
                                                                                              (__eo_to_smt_bv_size
                                                                                                (__smtx_typeof (__eo_to_smt Y)))
                                                                                                  0)))
                                                                                  rw [hTy]
                                                                                  simp [__smtx_model_eval, hArg])
                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                            · by_cases hSetChoose : f = Term.UOp UserOp.set_choose
                                                                              · subst f
                                                                                exact substFalse_eval_unary_op_type_dependent
                                                                                  UserOp.set_choose a xs ss bvs hM hN
                                                                                  hisr hxs hss hbvs hFTrans hSubstTrans
                                                                                  (substitute_simul_rec_uop_eq_self UserOp.set_choose xs ss bvs
                                                                                    hXsEnv hBvsEnv hSsTrans)
                                                                                  (fun {t} h => set_choose_arg_has_smt_translation_of_has_smt_translation h)
                                                                                  (fun X Y hTy hArg => by
                                                                                    show __smtx_model_eval M
                                                                                        (SmtTerm.map_diff (__eo_to_smt X)
                                                                                          (SmtTerm.set_empty
                                                                                            (__eo_to_smt_set_elem_type
                                                                                              (__smtx_typeof (__eo_to_smt X))))) =
                                                                                      __smtx_model_eval N
                                                                                        (SmtTerm.map_diff (__eo_to_smt Y)
                                                                                            (SmtTerm.set_empty
                                                                                                (__eo_to_smt_set_elem_type
                                                                                                    (__smtx_typeof (__eo_to_smt Y)))))
                                                                                    rw [hTy]
                                                                                    simp [__smtx_model_eval, hArg])
                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                              · by_cases hSetEmpty : f = Term.UOp UserOp.set_is_empty
                                                                                · subst f
                                                                                  exact substFalse_eval_unary_op_type_dependent
                                                                                    UserOp.set_is_empty a xs ss bvs hM hN
                                                                                    hisr hxs hss hbvs hFTrans hSubstTrans
                                                                                    (substitute_simul_rec_uop_eq_self UserOp.set_is_empty xs ss bvs
                                                                                      hXsEnv hBvsEnv hSsTrans)
                                                                                    (fun {t} h => set_is_empty_arg_has_smt_translation_of_has_smt_translation h)
                                                                                    (fun X Y hTy hArg => by
                                                                                      show __smtx_model_eval M
                                                                                          (SmtTerm.eq (__eo_to_smt X)
                                                                                            (SmtTerm.set_empty
                                                                                              (__eo_to_smt_set_elem_type
                                                                                                (__smtx_typeof (__eo_to_smt X))))) =
                                                                                        __smtx_model_eval N
                                                                                          (SmtTerm.eq (__eo_to_smt Y)
                                                                                              (SmtTerm.set_empty
                                                                                                  (__eo_to_smt_set_elem_type
                                                                                                      (__smtx_typeof (__eo_to_smt Y)))))
                                                                                      rw [hTy]
                                                                                      simp [__smtx_model_eval, hArg])
                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                · by_cases hSetIsSingleton : f = Term.UOp UserOp.set_is_singleton
                                                                                  · subst f
                                                                                    exact substFalse_eval_unary_op_type_dependent
                                                                                      UserOp.set_is_singleton a xs ss bvs hM hN
                                                                                      hisr hxs hss hbvs hFTrans hSubstTrans
                                                                                      (substitute_simul_rec_uop_eq_self UserOp.set_is_singleton xs ss bvs
                                                                                        hXsEnv hBvsEnv hSsTrans)
                                                                                      (fun {t} h => set_is_singleton_arg_has_smt_translation_of_has_smt_translation h)
                                                                                      (fun X Y hTy hArg => by
                                                                                        show __smtx_model_eval M
                                                                                            (SmtTerm.eq (__eo_to_smt X)
                                                                                              (SmtTerm.set_singleton
                                                                                                (SmtTerm.map_diff (__eo_to_smt X)
                                                                                                  (SmtTerm.set_empty
                                                                                                    (__eo_to_smt_set_elem_type
                                                                                                      (__smtx_typeof (__eo_to_smt X))))))) =
                                                                                          __smtx_model_eval N
                                                                                            (SmtTerm.eq (__eo_to_smt Y)
                                                                                              (SmtTerm.set_singleton
                                                                                                (SmtTerm.map_diff (__eo_to_smt Y)
                                                                                                    (SmtTerm.set_empty
                                                                                                        (__eo_to_smt_set_elem_type
                                                                                                            (__smtx_typeof (__eo_to_smt Y)))))))
                                                                                        rw [hTy]
                                                                                        simp [__smtx_model_eval, hArg])
                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                  · -- `f` is not one of the handled unary heads: dispatch on its
                                                                                    -- structure for binary heads (`Apply (UOp op) x1`).
                                                                                    cases f with
                                                                                    | Apply g x1 =>
                                                                                        cases g with
                                                                                        | UOp op =>
                                                                                            -- Binary special heads `(Apply (Apply (UOp op) x1) a)`; dispatch on `op`.
                                                                                            -- (div/mod and other model-global-dependent ops are left for later.)
                                                                                            by_cases h_and : op = UserOp.and
                                                                                            · subst op
                                                                                              exact substFalse_eval_binary_op UserOp.and x1 a xs ss bvs
                                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                hFTrans hSubstTrans
                                                                                                (substitute_simul_rec_uop_eq_self UserOp.and xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                (fun {s t} h => and_args_have_smt_translation_of_has_smt_translation h)
                                                                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                  show __smtx_model_eval M (SmtTerm.and (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                    __smtx_model_eval N (SmtTerm.and (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                  simp only [__smtx_model_eval]; rw [h1, h2])
                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                            ·
                                                                                              by_cases h_or : op = UserOp.or
                                                                                              · subst op
                                                                                                exact substFalse_eval_binary_op UserOp.or x1 a xs ss bvs
                                                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                  hFTrans hSubstTrans
                                                                                                  (substitute_simul_rec_uop_eq_self UserOp.or xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                  (fun {s t} h => or_args_have_smt_translation_of_has_smt_translation h)
                                                                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                    show __smtx_model_eval M (SmtTerm.or (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                      __smtx_model_eval N (SmtTerm.or (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                    simp only [__smtx_model_eval]; rw [h1, h2])
                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                              ·
                                                                                                by_cases h_imp : op = UserOp.imp
                                                                                                · subst op
                                                                                                  exact substFalse_eval_binary_op UserOp.imp x1 a xs ss bvs
                                                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                    hFTrans hSubstTrans
                                                                                                    (substitute_simul_rec_uop_eq_self UserOp.imp xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                    (fun {s t} h => imp_args_have_smt_translation_of_has_smt_translation h)
                                                                                                    (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                      show __smtx_model_eval M (SmtTerm.imp (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                        __smtx_model_eval N (SmtTerm.imp (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                      simp only [__smtx_model_eval]; rw [h1, h2])
                                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                ·
                                                                                                  by_cases h_xor : op = UserOp.xor
                                                                                                  · subst op
                                                                                                    exact substFalse_eval_binary_op UserOp.xor x1 a xs ss bvs
                                                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                      hFTrans hSubstTrans
                                                                                                      (substitute_simul_rec_uop_eq_self UserOp.xor xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                      (fun {s t} h => xor_args_have_smt_translation_of_has_smt_translation h)
                                                                                                      (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                        show __smtx_model_eval M (SmtTerm.xor (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                          __smtx_model_eval N (SmtTerm.xor (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                        simp only [__smtx_model_eval]; rw [h1, h2])
                                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                  ·
                                                                                                    by_cases h_eq : op = UserOp.eq
                                                                                                    · subst op
                                                                                                      exact substFalse_eval_binary_op UserOp.eq x1 a xs ss bvs
                                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                        hFTrans hSubstTrans
                                                                                                        (substitute_simul_rec_uop_eq_self UserOp.eq xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                        (fun {s t} h => eq_args_have_smt_translation_of_has_smt_translation h)
                                                                                                        (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                          show __smtx_model_eval M (SmtTerm.eq (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                            __smtx_model_eval N (SmtTerm.eq (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                          simp only [__smtx_model_eval]; rw [h1, h2])
                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                    ·
                                                                                                      by_cases h_plus : op = UserOp.plus
                                                                                                      · subst op
                                                                                                        exact substFalse_eval_binary_op UserOp.plus x1 a xs ss bvs
                                                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                          hFTrans hSubstTrans
                                                                                                          (substitute_simul_rec_uop_eq_self UserOp.plus xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                          (fun {s t} h => plus_args_have_smt_translation_of_has_smt_translation h)
                                                                                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                            show __smtx_model_eval M (SmtTerm.plus (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                              __smtx_model_eval N (SmtTerm.plus (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                            simp only [__smtx_model_eval]; rw [h1, h2])
                                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                      ·
                                                                                                        by_cases h_neg : op = UserOp.neg
                                                                                                        · subst op
                                                                                                          exact substFalse_eval_binary_op UserOp.neg x1 a xs ss bvs
                                                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                            hFTrans hSubstTrans
                                                                                                            (substitute_simul_rec_uop_eq_self UserOp.neg xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                            (fun {s t} h => neg_args_have_smt_translation_of_has_smt_translation h)
                                                                                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                              show __smtx_model_eval M (SmtTerm.neg (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                __smtx_model_eval N (SmtTerm.neg (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                              simp only [__smtx_model_eval]; rw [h1, h2])
                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                        ·
                                                                                                          by_cases h_mult : op = UserOp.mult
                                                                                                          · subst op
                                                                                                            exact substFalse_eval_binary_op UserOp.mult x1 a xs ss bvs
                                                                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                              hFTrans hSubstTrans
                                                                                                              (substitute_simul_rec_uop_eq_self UserOp.mult xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                              (fun {s t} h => mult_args_have_smt_translation_of_has_smt_translation h)
                                                                                                              (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                show __smtx_model_eval M (SmtTerm.mult (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                  __smtx_model_eval N (SmtTerm.mult (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                simp only [__smtx_model_eval]; rw [h1, h2])
                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                          ·
                                                                                                            by_cases h_lt : op = UserOp.lt
                                                                                                            · subst op
                                                                                                              exact substFalse_eval_binary_op UserOp.lt x1 a xs ss bvs
                                                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                hFTrans hSubstTrans
                                                                                                                (substitute_simul_rec_uop_eq_self UserOp.lt xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                (fun {s t} h => lt_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                  show __smtx_model_eval M (SmtTerm.lt (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                    __smtx_model_eval N (SmtTerm.lt (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                  simp only [__smtx_model_eval]; rw [h1, h2])
                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                            ·
                                                                                                              by_cases h_leq : op = UserOp.leq
                                                                                                              · subst op
                                                                                                                exact substFalse_eval_binary_op UserOp.leq x1 a xs ss bvs
                                                                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                  hFTrans hSubstTrans
                                                                                                                  (substitute_simul_rec_uop_eq_self UserOp.leq xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                  (fun {s t} h => leq_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                    show __smtx_model_eval M (SmtTerm.leq (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                      __smtx_model_eval N (SmtTerm.leq (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                    simp only [__smtx_model_eval]; rw [h1, h2])
                                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                              ·
                                                                                                                by_cases h_gt : op = UserOp.gt
                                                                                                                · subst op
                                                                                                                  exact substFalse_eval_binary_op UserOp.gt x1 a xs ss bvs
                                                                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                    hFTrans hSubstTrans
                                                                                                                    (substitute_simul_rec_uop_eq_self UserOp.gt xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                    (fun {s t} h => gt_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                    (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                      show __smtx_model_eval M (SmtTerm.gt (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                        __smtx_model_eval N (SmtTerm.gt (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                      simp only [__smtx_model_eval]; rw [h1, h2])
                                                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                ·
                                                                                                                  by_cases h_geq : op = UserOp.geq
                                                                                                                  · subst op
                                                                                                                    exact substFalse_eval_binary_op UserOp.geq x1 a xs ss bvs
                                                                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                      hFTrans hSubstTrans
                                                                                                                      (substitute_simul_rec_uop_eq_self UserOp.geq xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                      (fun {s t} h => geq_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                      (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                        show __smtx_model_eval M (SmtTerm.geq (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                          __smtx_model_eval N (SmtTerm.geq (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                        simp only [__smtx_model_eval]; rw [h1, h2])
                                                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                  · by_cases h_div : op = UserOp.div
                                                                                                                    · subst op
                                                                                                                      exact substFalse_eval_binary_op UserOp.div x1 a xs ss bvs
                                                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                        hFTrans hSubstTrans
                                                                                                                        (substitute_simul_rec_uop_eq_self UserOp.div xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                        (fun {s t} h => div_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                        (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                          show __smtx_model_eval M (SmtTerm.div (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                            __smtx_model_eval N (SmtTerm.div (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                          simp only [__smtx_model_eval]
                                                                                                                          rw [h1, h2, smtx_model_eval_apply_eq_of_globals hGlobals,
                                                                                                                            hGlobals.1])
                                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                    · by_cases h_mod : op = UserOp.mod
                                                                                                                      · subst op
                                                                                                                        exact substFalse_eval_binary_op UserOp.mod x1 a xs ss bvs
                                                                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                          hFTrans hSubstTrans
                                                                                                                          (substitute_simul_rec_uop_eq_self UserOp.mod xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                          (fun {s t} h => mod_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                            show __smtx_model_eval M (SmtTerm.mod (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                              __smtx_model_eval N (SmtTerm.mod (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                            simp only [__smtx_model_eval]
                                                                                                                            rw [h1, h2, smtx_model_eval_apply_eq_of_globals hGlobals,
                                                                                                                              hGlobals.1])
                                                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                      ·
                                                                                                                        by_cases h_select : op = UserOp.select
                                                                                                                        · subst op
                                                                                                                          exact substFalse_eval_binary_op UserOp.select x1 a xs ss bvs
                                                                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                            hFTrans hSubstTrans
                                                                                                                            (substitute_simul_rec_uop_eq_self UserOp.select xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                            (fun {s t} h => select_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                              show __smtx_model_eval M (SmtTerm.select (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                __smtx_model_eval N (SmtTerm.select (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                              simp only [__smtx_model_eval]; rw [h1, h2])
                                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                        ·
                                                                                                                          by_cases h_divisible : op = UserOp.divisible
                                                                                                                          · subst op
                                                                                                                            exact substFalse_eval_binary_op UserOp.divisible x1 a xs ss bvs
                                                                                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                              hFTrans hSubstTrans
                                                                                                                              (substitute_simul_rec_uop_eq_self UserOp.divisible xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                              (fun {s t} h => divisible_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                              (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                show __smtx_model_eval M (SmtTerm.divisible (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                  __smtx_model_eval N (SmtTerm.divisible (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                simp only [__smtx_model_eval]; rw [h1, h2])
                                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                          ·
                                                                                                                            by_cases h_div_total : op = UserOp.div_total
                                                                                                                            · subst op
                                                                                                                              exact substFalse_eval_binary_op UserOp.div_total x1 a xs ss bvs
                                                                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                hFTrans hSubstTrans
                                                                                                                                (substitute_simul_rec_uop_eq_self UserOp.div_total xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                (fun {s t} h => div_total_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                  show __smtx_model_eval M (SmtTerm.div_total (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                    __smtx_model_eval N (SmtTerm.div_total (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                  simp only [__smtx_model_eval]; rw [h1, h2])
                                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                            ·
                                                                                                                              by_cases h_mod_total : op = UserOp.mod_total
                                                                                                                              · subst op
                                                                                                                                exact substFalse_eval_binary_op UserOp.mod_total x1 a xs ss bvs
                                                                                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                  hFTrans hSubstTrans
                                                                                                                                  (substitute_simul_rec_uop_eq_self UserOp.mod_total xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                  (fun {s t} h => mod_total_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                    show __smtx_model_eval M (SmtTerm.mod_total (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                      __smtx_model_eval N (SmtTerm.mod_total (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                    simp only [__smtx_model_eval]; rw [h1, h2])
                                                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                              ·
                                                                                                                                first
                                                                                                                                | first
                                                                                                                                  | by_cases h_qdiv_total : op = UserOp.qdiv_total
                                                                                                                                    · subst op
                                                                                                                                      exact substFalse_eval_binary_op UserOp.qdiv_total x1 a xs ss bvs
                                                                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                        hFTrans hSubstTrans
                                                                                                                                        (substitute_simul_rec_uop_eq_self UserOp.qdiv_total xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                        (fun {s t} h => qdiv_total_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                        (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                          show __smtx_model_eval M (SmtTerm.qdiv_total (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                            __smtx_model_eval N (SmtTerm.qdiv_total (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                          simp only [__smtx_model_eval]
                                                                                                                                          rw [h1, h2])
                                                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                    · by_cases h_qdiv : op = UserOp.qdiv
                                                                                                                                      · subst op
                                                                                                                                        exact substFalse_eval_binary_op UserOp.qdiv x1 a xs ss bvs
                                                                                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                          hFTrans hSubstTrans
                                                                                                                                          (substitute_simul_rec_uop_eq_self UserOp.qdiv xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                          (fun {s t} h => qdiv_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                            show __smtx_model_eval M (SmtTerm.qdiv (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                              __smtx_model_eval N (SmtTerm.qdiv (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                            simp only [__smtx_model_eval]
                                                                                                                                            rw [h1, h2, smtx_model_eval_apply_eq_of_globals hGlobals,
                                                                                                                                              hGlobals.1])
                                                                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                      · by_cases h_concat : op = UserOp.concat
                                                                                                                                        · subst op
                                                                                                                                          exact substFalse_eval_binary_op UserOp.concat x1 a xs ss bvs
                                                                                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                            hFTrans hSubstTrans
                                                                                                                                            (substitute_simul_rec_uop_eq_self UserOp.concat xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                            (fun {s t} h =>
                                                                                                                                              apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                (eoOp := UserOp.concat) (smtOp := SmtTerm.concat)
                                                                                                                                                (by rfl) bv_concat_args_have_smt_translation_of_non_none h)
                                                                                                                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                              show __smtx_model_eval M (SmtTerm.concat (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                __smtx_model_eval N (SmtTerm.concat (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                              simp only [__smtx_model_eval]
                                                                                                                                              rw [h1, h2])
                                                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                        · by_cases h_bvand : op = UserOp.bvand
                                                                                                                                          · subst op
                                                                                                                                            exact substFalse_eval_binary_op UserOp.bvand x1 a xs ss bvs
                                                                                                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                              hFTrans hSubstTrans
                                                                                                                                              (substitute_simul_rec_uop_eq_self UserOp.bvand xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                              (fun {s t} h =>
                                                                                                                                                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                  (eoOp := UserOp.bvand) (smtOp := SmtTerm.bvand)
                                                                                                                                                  (by rfl)
                                                                                                                                                  (fun hNN =>
                                                                                                                                                    bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                      (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                  h)
                                                                                                                                              (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                show __smtx_model_eval M (SmtTerm.bvand (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                  __smtx_model_eval N (SmtTerm.bvand (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                simp only [__smtx_model_eval]
                                                                                                                                                rw [h1, h2])
                                                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                          · by_cases h_bvor : op = UserOp.bvor
                                                                                                                                            · subst op
                                                                                                                                              exact substFalse_eval_binary_op UserOp.bvor x1 a xs ss bvs
                                                                                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                hFTrans hSubstTrans
                                                                                                                                                (substitute_simul_rec_uop_eq_self UserOp.bvor xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                (fun {s t} h =>
                                                                                                                                                  apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                    (eoOp := UserOp.bvor) (smtOp := SmtTerm.bvor)
                                                                                                                                                    (by rfl)
                                                                                                                                                    (fun hNN =>
                                                                                                                                                      bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                        (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                    h)
                                                                                                                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                  show __smtx_model_eval M (SmtTerm.bvor (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                    __smtx_model_eval N (SmtTerm.bvor (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                  simp only [__smtx_model_eval]
                                                                                                                                                  rw [h1, h2])
                                                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                            · by_cases h_bvnand : op = UserOp.bvnand
                                                                                                                                              · subst op
                                                                                                                                                exact substFalse_eval_binary_op UserOp.bvnand x1 a xs ss bvs
                                                                                                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                  hFTrans hSubstTrans
                                                                                                                                                  (substitute_simul_rec_uop_eq_self UserOp.bvnand xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                  (fun {s t} h =>
                                                                                                                                                    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                      (eoOp := UserOp.bvnand) (smtOp := SmtTerm.bvnand)
                                                                                                                                                      (by rfl)
                                                                                                                                                      (fun hNN =>
                                                                                                                                                        bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                          (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                      h)
                                                                                                                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                    show __smtx_model_eval M (SmtTerm.bvnand (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                      __smtx_model_eval N (SmtTerm.bvnand (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                    simp only [__smtx_model_eval]
                                                                                                                                                    rw [h1, h2])
                                                                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                              · by_cases h_bvnor : op = UserOp.bvnor
                                                                                                                                                · subst op
                                                                                                                                                  exact substFalse_eval_binary_op UserOp.bvnor x1 a xs ss bvs
                                                                                                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                    hFTrans hSubstTrans
                                                                                                                                                    (substitute_simul_rec_uop_eq_self UserOp.bvnor xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                    (fun {s t} h =>
                                                                                                                                                      apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                        (eoOp := UserOp.bvnor) (smtOp := SmtTerm.bvnor)
                                                                                                                                                        (by rfl)
                                                                                                                                                        (fun hNN =>
                                                                                                                                                          bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                            (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                        h)
                                                                                                                                                    (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                      show __smtx_model_eval M (SmtTerm.bvnor (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                        __smtx_model_eval N (SmtTerm.bvnor (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                      simp only [__smtx_model_eval]
                                                                                                                                                      rw [h1, h2])
                                                                                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                · by_cases h_bvxor : op = UserOp.bvxor
                                                                                                                                                  · subst op
                                                                                                                                                    exact substFalse_eval_binary_op UserOp.bvxor x1 a xs ss bvs
                                                                                                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                      hFTrans hSubstTrans
                                                                                                                                                      (substitute_simul_rec_uop_eq_self UserOp.bvxor xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                      (fun {s t} h =>
                                                                                                                                                        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                          (eoOp := UserOp.bvxor) (smtOp := SmtTerm.bvxor)
                                                                                                                                                          (by rfl)
                                                                                                                                                          (fun hNN =>
                                                                                                                                                            bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                              (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                          h)
                                                                                                                                                      (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                        show __smtx_model_eval M (SmtTerm.bvxor (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                          __smtx_model_eval N (SmtTerm.bvxor (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                        simp only [__smtx_model_eval]
                                                                                                                                                        rw [h1, h2])
                                                                                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                  · by_cases h_bvxnor : op = UserOp.bvxnor
                                                                                                                                                    · subst op
                                                                                                                                                      exact substFalse_eval_binary_op UserOp.bvxnor x1 a xs ss bvs
                                                                                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                        hFTrans hSubstTrans
                                                                                                                                                        (substitute_simul_rec_uop_eq_self UserOp.bvxnor xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                        (fun {s t} h =>
                                                                                                                                                          apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                            (eoOp := UserOp.bvxnor) (smtOp := SmtTerm.bvxnor)
                                                                                                                                                            (by rfl)
                                                                                                                                                            (fun hNN =>
                                                                                                                                                              bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                            h)
                                                                                                                                                        (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                          show __smtx_model_eval M (SmtTerm.bvxnor (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                            __smtx_model_eval N (SmtTerm.bvxnor (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                          simp only [__smtx_model_eval]
                                                                                                                                                          rw [h1, h2])
                                                                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                    · by_cases h_bvcomp : op = UserOp.bvcomp
                                                                                                                                                      · subst op
                                                                                                                                                        exact substFalse_eval_binary_op UserOp.bvcomp x1 a xs ss bvs
                                                                                                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                          hFTrans hSubstTrans
                                                                                                                                                          (substitute_simul_rec_uop_eq_self UserOp.bvcomp xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                          (fun {s t} h =>
                                                                                                                                                            apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                              (eoOp := UserOp.bvcomp) (smtOp := SmtTerm.bvcomp)
                                                                                                                                                              (by rfl)
                                                                                                                                                              (fun hNN =>
                                                                                                                                                                bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                  (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                              h)
                                                                                                                                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                            show __smtx_model_eval M (SmtTerm.bvcomp (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                              __smtx_model_eval N (SmtTerm.bvcomp (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                            simp only [__smtx_model_eval]
                                                                                                                                                            rw [h1, h2])
                                                                                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                      · by_cases h_bvadd : op = UserOp.bvadd
                                                                                                                                                        · subst op
                                                                                                                                                          exact substFalse_eval_binary_op UserOp.bvadd x1 a xs ss bvs
                                                                                                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                            hFTrans hSubstTrans
                                                                                                                                                            (substitute_simul_rec_uop_eq_self UserOp.bvadd xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                            (fun {s t} h =>
                                                                                                                                                              apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                (eoOp := UserOp.bvadd) (smtOp := SmtTerm.bvadd)
                                                                                                                                                                (by rfl)
                                                                                                                                                                (fun hNN =>
                                                                                                                                                                  bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                    (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                h)
                                                                                                                                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                              show __smtx_model_eval M (SmtTerm.bvadd (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                __smtx_model_eval N (SmtTerm.bvadd (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                              simp only [__smtx_model_eval]
                                                                                                                                                              rw [h1, h2])
                                                                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                        · by_cases h_bvmul : op = UserOp.bvmul
                                                                                                                                                          · subst op
                                                                                                                                                            exact substFalse_eval_binary_op UserOp.bvmul x1 a xs ss bvs
                                                                                                                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                              hFTrans hSubstTrans
                                                                                                                                                              (substitute_simul_rec_uop_eq_self UserOp.bvmul xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                              (fun {s t} h =>
                                                                                                                                                                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                  (eoOp := UserOp.bvmul) (smtOp := SmtTerm.bvmul)
                                                                                                                                                                  (by rfl)
                                                                                                                                                                  (fun hNN =>
                                                                                                                                                                    bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                      (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                  h)
                                                                                                                                                              (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                show __smtx_model_eval M (SmtTerm.bvmul (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                  __smtx_model_eval N (SmtTerm.bvmul (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                simp only [__smtx_model_eval]
                                                                                                                                                                rw [h1, h2])
                                                                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                          · by_cases h_bvudiv : op = UserOp.bvudiv
                                                                                                                                                            · subst op
                                                                                                                                                              exact substFalse_eval_binary_op UserOp.bvudiv x1 a xs ss bvs
                                                                                                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                hFTrans hSubstTrans
                                                                                                                                                                (substitute_simul_rec_uop_eq_self UserOp.bvudiv xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                (fun {s t} h =>
                                                                                                                                                                  apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                    (eoOp := UserOp.bvudiv) (smtOp := SmtTerm.bvudiv)
                                                                                                                                                                    (by rfl)
                                                                                                                                                                    (fun hNN =>
                                                                                                                                                                      bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                        (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                    h)
                                                                                                                                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                  show __smtx_model_eval M (SmtTerm.bvudiv (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                    __smtx_model_eval N (SmtTerm.bvudiv (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                  simp only [__smtx_model_eval]
                                                                                                                                                                  rw [h1, h2])
                                                                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                            · by_cases h_bvurem : op = UserOp.bvurem
                                                                                                                                                              · subst op
                                                                                                                                                                exact substFalse_eval_binary_op UserOp.bvurem x1 a xs ss bvs
                                                                                                                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                  hFTrans hSubstTrans
                                                                                                                                                                  (substitute_simul_rec_uop_eq_self UserOp.bvurem xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                  (fun {s t} h =>
                                                                                                                                                                    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                      (eoOp := UserOp.bvurem) (smtOp := SmtTerm.bvurem)
                                                                                                                                                                      (by rfl)
                                                                                                                                                                      (fun hNN =>
                                                                                                                                                                        bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                          (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                      h)
                                                                                                                                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                    show __smtx_model_eval M (SmtTerm.bvurem (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                      __smtx_model_eval N (SmtTerm.bvurem (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                    simp only [__smtx_model_eval]
                                                                                                                                                                    rw [h1, h2])
                                                                                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                              · by_cases h_bvsub : op = UserOp.bvsub
                                                                                                                                                                · subst op
                                                                                                                                                                  exact substFalse_eval_binary_op UserOp.bvsub x1 a xs ss bvs
                                                                                                                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                    hFTrans hSubstTrans
                                                                                                                                                                    (substitute_simul_rec_uop_eq_self UserOp.bvsub xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                    (fun {s t} h =>
                                                                                                                                                                      apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                        (eoOp := UserOp.bvsub) (smtOp := SmtTerm.bvsub)
                                                                                                                                                                        (by rfl)
                                                                                                                                                                        (fun hNN =>
                                                                                                                                                                          bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                            (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                        h)
                                                                                                                                                                    (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                      show __smtx_model_eval M (SmtTerm.bvsub (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                        __smtx_model_eval N (SmtTerm.bvsub (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                      simp only [__smtx_model_eval]
                                                                                                                                                                      rw [h1, h2])
                                                                                                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                · by_cases h_bvsdiv : op = UserOp.bvsdiv
                                                                                                                                                                  · subst op
                                                                                                                                                                    exact substFalse_eval_binary_op UserOp.bvsdiv x1 a xs ss bvs
                                                                                                                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                      hFTrans hSubstTrans
                                                                                                                                                                      (substitute_simul_rec_uop_eq_self UserOp.bvsdiv xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                      (fun {s t} h =>
                                                                                                                                                                        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                          (eoOp := UserOp.bvsdiv) (smtOp := SmtTerm.bvsdiv)
                                                                                                                                                                          (by rfl)
                                                                                                                                                                          (fun hNN =>
                                                                                                                                                                            bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                              (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                          h)
                                                                                                                                                                      (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                        show __smtx_model_eval M (SmtTerm.bvsdiv (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                          __smtx_model_eval N (SmtTerm.bvsdiv (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                        simp only [__smtx_model_eval]
                                                                                                                                                                        rw [h1, h2])
                                                                                                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                  · by_cases h_bvsrem : op = UserOp.bvsrem
                                                                                                                                                                    · subst op
                                                                                                                                                                      exact substFalse_eval_binary_op UserOp.bvsrem x1 a xs ss bvs
                                                                                                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                        hFTrans hSubstTrans
                                                                                                                                                                        (substitute_simul_rec_uop_eq_self UserOp.bvsrem xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                        (fun {s t} h =>
                                                                                                                                                                          apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                            (eoOp := UserOp.bvsrem) (smtOp := SmtTerm.bvsrem)
                                                                                                                                                                            (by rfl)
                                                                                                                                                                            (fun hNN =>
                                                                                                                                                                              bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                            h)
                                                                                                                                                                        (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                          show __smtx_model_eval M (SmtTerm.bvsrem (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                            __smtx_model_eval N (SmtTerm.bvsrem (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                          simp only [__smtx_model_eval]
                                                                                                                                                                          rw [h1, h2])
                                                                                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                    · by_cases h_bvsmod : op = UserOp.bvsmod
                                                                                                                                                                      · subst op
                                                                                                                                                                        exact substFalse_eval_binary_op UserOp.bvsmod x1 a xs ss bvs
                                                                                                                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                          hFTrans hSubstTrans
                                                                                                                                                                          (substitute_simul_rec_uop_eq_self UserOp.bvsmod xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                          (fun {s t} h =>
                                                                                                                                                                            apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                              (eoOp := UserOp.bvsmod) (smtOp := SmtTerm.bvsmod)
                                                                                                                                                                              (by rfl)
                                                                                                                                                                              (fun hNN =>
                                                                                                                                                                                bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                  (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                              h)
                                                                                                                                                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                            show __smtx_model_eval M (SmtTerm.bvsmod (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                              __smtx_model_eval N (SmtTerm.bvsmod (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                            simp only [__smtx_model_eval]
                                                                                                                                                                            rw [h1, h2])
                                                                                                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                      · by_cases h_bvshl : op = UserOp.bvshl
                                                                                                                                                                        · subst op
                                                                                                                                                                          exact substFalse_eval_binary_op UserOp.bvshl x1 a xs ss bvs
                                                                                                                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                            hFTrans hSubstTrans
                                                                                                                                                                            (substitute_simul_rec_uop_eq_self UserOp.bvshl xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                            (fun {s t} h =>
                                                                                                                                                                              apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                (eoOp := UserOp.bvshl) (smtOp := SmtTerm.bvshl)
                                                                                                                                                                                (by rfl)
                                                                                                                                                                                (fun hNN =>
                                                                                                                                                                                  bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                    (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                                h)
                                                                                                                                                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                              show __smtx_model_eval M (SmtTerm.bvshl (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                __smtx_model_eval N (SmtTerm.bvshl (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                              simp only [__smtx_model_eval]
                                                                                                                                                                              rw [h1, h2])
                                                                                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                        · by_cases h_bvlshr : op = UserOp.bvlshr
                                                                                                                                                                          · subst op
                                                                                                                                                                            exact substFalse_eval_binary_op UserOp.bvlshr x1 a xs ss bvs
                                                                                                                                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                              hFTrans hSubstTrans
                                                                                                                                                                              (substitute_simul_rec_uop_eq_self UserOp.bvlshr xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                              (fun {s t} h =>
                                                                                                                                                                                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                  (eoOp := UserOp.bvlshr) (smtOp := SmtTerm.bvlshr)
                                                                                                                                                                                  (by rfl)
                                                                                                                                                                                  (fun hNN =>
                                                                                                                                                                                    bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                      (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                                  h)
                                                                                                                                                                              (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                show __smtx_model_eval M (SmtTerm.bvlshr (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                  __smtx_model_eval N (SmtTerm.bvlshr (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                simp only [__smtx_model_eval]
                                                                                                                                                                                rw [h1, h2])
                                                                                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                          · by_cases h_bvashr : op = UserOp.bvashr
                                                                                                                                                                            · subst op
                                                                                                                                                                              exact substFalse_eval_binary_op UserOp.bvashr x1 a xs ss bvs
                                                                                                                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                hFTrans hSubstTrans
                                                                                                                                                                                (substitute_simul_rec_uop_eq_self UserOp.bvashr xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                (fun {s t} h =>
                                                                                                                                                                                  apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                    (eoOp := UserOp.bvashr) (smtOp := SmtTerm.bvashr)
                                                                                                                                                                                    (by rfl)
                                                                                                                                                                                    (fun hNN =>
                                                                                                                                                                                      bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                        (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                                    h)
                                                                                                                                                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                  show __smtx_model_eval M (SmtTerm.bvashr (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                    __smtx_model_eval N (SmtTerm.bvashr (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                  simp only [__smtx_model_eval]
                                                                                                                                                                                  rw [h1, h2])
                                                                                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                            · by_cases h_bvult : op = UserOp.bvult
                                                                                                                                                                              · subst op
                                                                                                                                                                                exact substFalse_eval_binary_op UserOp.bvult x1 a xs ss bvs
                                                                                                                                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                  hFTrans hSubstTrans
                                                                                                                                                                                  (substitute_simul_rec_uop_eq_self UserOp.bvult xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                  (fun {s t} h =>
                                                                                                                                                                                    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                      (eoOp := UserOp.bvult) (smtOp := SmtTerm.bvult)
                                                                                                                                                                                      (by rfl)
                                                                                                                                                                                      (fun hNN =>
                                                                                                                                                                                        bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                          (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                                      h)
                                                                                                                                                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                    show __smtx_model_eval M (SmtTerm.bvult (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                      __smtx_model_eval N (SmtTerm.bvult (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                    simp only [__smtx_model_eval]
                                                                                                                                                                                    rw [h1, h2])
                                                                                                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                              · by_cases h_bvule : op = UserOp.bvule
                                                                                                                                                                                · subst op
                                                                                                                                                                                  exact substFalse_eval_binary_op UserOp.bvule x1 a xs ss bvs
                                                                                                                                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                    hFTrans hSubstTrans
                                                                                                                                                                                    (substitute_simul_rec_uop_eq_self UserOp.bvule xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                    (fun {s t} h =>
                                                                                                                                                                                      apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                        (eoOp := UserOp.bvule) (smtOp := SmtTerm.bvule)
                                                                                                                                                                                        (by rfl)
                                                                                                                                                                                        (fun hNN =>
                                                                                                                                                                                          bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                            (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                                        h)
                                                                                                                                                                                    (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                      show __smtx_model_eval M (SmtTerm.bvule (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                        __smtx_model_eval N (SmtTerm.bvule (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                      simp only [__smtx_model_eval]
                                                                                                                                                                                      rw [h1, h2])
                                                                                                                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                · by_cases h_bvugt : op = UserOp.bvugt
                                                                                                                                                                                  · subst op
                                                                                                                                                                                    exact substFalse_eval_binary_op UserOp.bvugt x1 a xs ss bvs
                                                                                                                                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                      hFTrans hSubstTrans
                                                                                                                                                                                      (substitute_simul_rec_uop_eq_self UserOp.bvugt xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                      (fun {s t} h =>
                                                                                                                                                                                        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                          (eoOp := UserOp.bvugt) (smtOp := SmtTerm.bvugt)
                                                                                                                                                                                          (by rfl)
                                                                                                                                                                                          (fun hNN =>
                                                                                                                                                                                            bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                              (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                                          h)
                                                                                                                                                                                      (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                        show __smtx_model_eval M (SmtTerm.bvugt (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                          __smtx_model_eval N (SmtTerm.bvugt (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                        simp only [__smtx_model_eval]
                                                                                                                                                                                        rw [h1, h2])
                                                                                                                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                  · by_cases h_bvuge : op = UserOp.bvuge
                                                                                                                                                                                    · subst op
                                                                                                                                                                                      exact substFalse_eval_binary_op UserOp.bvuge x1 a xs ss bvs
                                                                                                                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                        hFTrans hSubstTrans
                                                                                                                                                                                        (substitute_simul_rec_uop_eq_self UserOp.bvuge xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                        (fun {s t} h =>
                                                                                                                                                                                          apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                            (eoOp := UserOp.bvuge) (smtOp := SmtTerm.bvuge)
                                                                                                                                                                                            (by rfl)
                                                                                                                                                                                            (fun hNN =>
                                                                                                                                                                                              bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                                            h)
                                                                                                                                                                                        (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                          show __smtx_model_eval M (SmtTerm.bvuge (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                            __smtx_model_eval N (SmtTerm.bvuge (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                          simp only [__smtx_model_eval]
                                                                                                                                                                                          rw [h1, h2])
                                                                                                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                    · by_cases h_bvslt : op = UserOp.bvslt
                                                                                                                                                                                      · subst op
                                                                                                                                                                                        exact substFalse_eval_binary_op UserOp.bvslt x1 a xs ss bvs
                                                                                                                                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                          hFTrans hSubstTrans
                                                                                                                                                                                          (substitute_simul_rec_uop_eq_self UserOp.bvslt xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                          (fun {s t} h =>
                                                                                                                                                                                            apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                              (eoOp := UserOp.bvslt) (smtOp := SmtTerm.bvslt)
                                                                                                                                                                                              (by rfl)
                                                                                                                                                                                              (fun hNN =>
                                                                                                                                                                                                bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                  (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                                              h)
                                                                                                                                                                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                            show __smtx_model_eval M (SmtTerm.bvslt (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                              __smtx_model_eval N (SmtTerm.bvslt (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                            simp only [__smtx_model_eval]
                                                                                                                                                                                            rw [h1, h2])
                                                                                                                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                      · by_cases h_bvsle : op = UserOp.bvsle
                                                                                                                                                                                        · subst op
                                                                                                                                                                                          exact substFalse_eval_binary_op UserOp.bvsle x1 a xs ss bvs
                                                                                                                                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                            hFTrans hSubstTrans
                                                                                                                                                                                            (substitute_simul_rec_uop_eq_self UserOp.bvsle xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                            (fun {s t} h =>
                                                                                                                                                                                              apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                (eoOp := UserOp.bvsle) (smtOp := SmtTerm.bvsle)
                                                                                                                                                                                                (by rfl)
                                                                                                                                                                                                (fun hNN =>
                                                                                                                                                                                                  bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                    (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                                                h)
                                                                                                                                                                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                              show __smtx_model_eval M (SmtTerm.bvsle (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                __smtx_model_eval N (SmtTerm.bvsle (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                              simp only [__smtx_model_eval]
                                                                                                                                                                                              rw [h1, h2])
                                                                                                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                        · by_cases h_bvsgt : op = UserOp.bvsgt
                                                                                                                                                                                          · subst op
                                                                                                                                                                                            exact substFalse_eval_binary_op UserOp.bvsgt x1 a xs ss bvs
                                                                                                                                                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                              hFTrans hSubstTrans
                                                                                                                                                                                              (substitute_simul_rec_uop_eq_self UserOp.bvsgt xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                              (fun {s t} h =>
                                                                                                                                                                                                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                  (eoOp := UserOp.bvsgt) (smtOp := SmtTerm.bvsgt)
                                                                                                                                                                                                  (by rfl)
                                                                                                                                                                                                  (fun hNN =>
                                                                                                                                                                                                    bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                      (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                                                  h)
                                                                                                                                                                                              (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                show __smtx_model_eval M (SmtTerm.bvsgt (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                  __smtx_model_eval N (SmtTerm.bvsgt (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                simp only [__smtx_model_eval]
                                                                                                                                                                                                rw [h1, h2])
                                                                                                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                          · by_cases h_bvsge : op = UserOp.bvsge
                                                                                                                                                                                            · subst op
                                                                                                                                                                                              exact substFalse_eval_binary_op UserOp.bvsge x1 a xs ss bvs
                                                                                                                                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                hFTrans hSubstTrans
                                                                                                                                                                                                (substitute_simul_rec_uop_eq_self UserOp.bvsge xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                (fun {s t} h =>
                                                                                                                                                                                                  apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                    (eoOp := UserOp.bvsge) (smtOp := SmtTerm.bvsge)
                                                                                                                                                                                                    (by rfl)
                                                                                                                                                                                                    (fun hNN =>
                                                                                                                                                                                                      bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                        (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                                                    h)
                                                                                                                                                                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                  show __smtx_model_eval M (SmtTerm.bvsge (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                    __smtx_model_eval N (SmtTerm.bvsge (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                  simp only [__smtx_model_eval]
                                                                                                                                                                                                  rw [h1, h2])
                                                                                                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                            · by_cases h_bvuaddo : op = UserOp.bvuaddo
                                                                                                                                                                                              · subst op
                                                                                                                                                                                                exact substFalse_eval_binary_op UserOp.bvuaddo x1 a xs ss bvs
                                                                                                                                                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                  hFTrans hSubstTrans
                                                                                                                                                                                                  (substitute_simul_rec_uop_eq_self UserOp.bvuaddo xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                  (fun {s t} h =>
                                                                                                                                                                                                    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                      (eoOp := UserOp.bvuaddo) (smtOp := SmtTerm.bvuaddo)
                                                                                                                                                                                                      (by rfl)
                                                                                                                                                                                                      (fun hNN =>
                                                                                                                                                                                                        bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                          (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                                                      h)
                                                                                                                                                                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                    show __smtx_model_eval M (SmtTerm.bvuaddo (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                      __smtx_model_eval N (SmtTerm.bvuaddo (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                    simp only [__smtx_model_eval]
                                                                                                                                                                                                    rw [h1, h2])
                                                                                                                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                              · by_cases h_bvsaddo : op = UserOp.bvsaddo
                                                                                                                                                                                                · subst op
                                                                                                                                                                                                  exact substFalse_eval_binary_op UserOp.bvsaddo x1 a xs ss bvs
                                                                                                                                                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                    hFTrans hSubstTrans
                                                                                                                                                                                                    (substitute_simul_rec_uop_eq_self UserOp.bvsaddo xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                    (fun {s t} h =>
                                                                                                                                                                                                      apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                        (eoOp := UserOp.bvsaddo) (smtOp := SmtTerm.bvsaddo)
                                                                                                                                                                                                        (by rfl)
                                                                                                                                                                                                        (fun hNN =>
                                                                                                                                                                                                          bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                            (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                                                        h)
                                                                                                                                                                                                    (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                      show __smtx_model_eval M (SmtTerm.bvsaddo (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                        __smtx_model_eval N (SmtTerm.bvsaddo (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                      simp only [__smtx_model_eval]
                                                                                                                                                                                                      rw [h1, h2])
                                                                                                                                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                · by_cases h_bvumulo : op = UserOp.bvumulo
                                                                                                                                                                                                  · subst op
                                                                                                                                                                                                    exact substFalse_eval_binary_op UserOp.bvumulo x1 a xs ss bvs
                                                                                                                                                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                      hFTrans hSubstTrans
                                                                                                                                                                                                      (substitute_simul_rec_uop_eq_self UserOp.bvumulo xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                      (fun {s t} h =>
                                                                                                                                                                                                        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                          (eoOp := UserOp.bvumulo) (smtOp := SmtTerm.bvumulo)
                                                                                                                                                                                                          (by rfl)
                                                                                                                                                                                                          (fun hNN =>
                                                                                                                                                                                                            bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                              (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                                                          h)
                                                                                                                                                                                                      (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                        show __smtx_model_eval M (SmtTerm.bvumulo (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                          __smtx_model_eval N (SmtTerm.bvumulo (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                        simp only [__smtx_model_eval]
                                                                                                                                                                                                        rw [h1, h2])
                                                                                                                                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                  · by_cases h_bvsmulo : op = UserOp.bvsmulo
                                                                                                                                                                                                    · subst op
                                                                                                                                                                                                      exact substFalse_eval_binary_op UserOp.bvsmulo x1 a xs ss bvs
                                                                                                                                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                        hFTrans hSubstTrans
                                                                                                                                                                                                        (substitute_simul_rec_uop_eq_self UserOp.bvsmulo xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                        (fun {s t} h =>
                                                                                                                                                                                                          apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                            (eoOp := UserOp.bvsmulo) (smtOp := SmtTerm.bvsmulo)
                                                                                                                                                                                                            (by rfl)
                                                                                                                                                                                                            (fun hNN =>
                                                                                                                                                                                                              bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                                                            h)
                                                                                                                                                                                                        (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                          show __smtx_model_eval M (SmtTerm.bvsmulo (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                            __smtx_model_eval N (SmtTerm.bvsmulo (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                          simp only [__smtx_model_eval]
                                                                                                                                                                                                          rw [h1, h2])
                                                                                                                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                    · by_cases h_bvusubo : op = UserOp.bvusubo
                                                                                                                                                                                                      · subst op
                                                                                                                                                                                                        exact substFalse_eval_binary_op UserOp.bvusubo x1 a xs ss bvs
                                                                                                                                                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                          hFTrans hSubstTrans
                                                                                                                                                                                                          (substitute_simul_rec_uop_eq_self UserOp.bvusubo xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                          (fun {s t} h =>
                                                                                                                                                                                                            apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                              (eoOp := UserOp.bvusubo) (smtOp := SmtTerm.bvusubo)
                                                                                                                                                                                                              (by rfl)
                                                                                                                                                                                                              (fun hNN =>
                                                                                                                                                                                                                bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                  (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                                                              h)
                                                                                                                                                                                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                            show __smtx_model_eval M (SmtTerm.bvusubo (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                              __smtx_model_eval N (SmtTerm.bvusubo (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                            simp only [__smtx_model_eval]
                                                                                                                                                                                                            rw [h1, h2])
                                                                                                                                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                      · by_cases h_bvssubo : op = UserOp.bvssubo
                                                                                                                                                                                                        · subst op
                                                                                                                                                                                                          exact substFalse_eval_binary_op UserOp.bvssubo x1 a xs ss bvs
                                                                                                                                                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                            hFTrans hSubstTrans
                                                                                                                                                                                                            (substitute_simul_rec_uop_eq_self UserOp.bvssubo xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                            (fun {s t} h =>
                                                                                                                                                                                                              apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                (eoOp := UserOp.bvssubo) (smtOp := SmtTerm.bvssubo)
                                                                                                                                                                                                                (by rfl)
                                                                                                                                                                                                                (fun hNN =>
                                                                                                                                                                                                                  bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                    (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                                                                h)
                                                                                                                                                                                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                              show __smtx_model_eval M (SmtTerm.bvssubo (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                __smtx_model_eval N (SmtTerm.bvssubo (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                              simp only [__smtx_model_eval]
                                                                                                                                                                                                              rw [h1, h2])
                                                                                                                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                        · by_cases h_bvsdivo : op = UserOp.bvsdivo
                                                                                                                                                                                                          · subst op
                                                                                                                                                                                                            exact substFalse_eval_binary_op UserOp.bvsdivo x1 a xs ss bvs
                                                                                                                                                                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                              hFTrans hSubstTrans
                                                                                                                                                                                                              (substitute_simul_rec_uop_eq_self UserOp.bvsdivo xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                              (fun {s t} h =>
                                                                                                                                                                                                                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                  (eoOp := UserOp.bvsdivo) (smtOp := SmtTerm.bvsdivo)
                                                                                                                                                                                                                  (by rfl)
                                                                                                                                                                                                                  (fun hNN =>
                                                                                                                                                                                                                    bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                      (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                                                                                  h)
                                                                                                                                                                                                              (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                show __smtx_model_eval M (SmtTerm.bvsdivo (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                  __smtx_model_eval N (SmtTerm.bvsdivo (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                simp only [__smtx_model_eval]
                                                                                                                                                                                                                rw [h1, h2])
                                                                                                                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                          · by_cases h_bvultbv : op = UserOp.bvultbv
                                                                                                                                                                                                            · subst op
                                                                                                                                                                                                              exact substFalse_eval_binary_op UserOp.bvultbv x1 a xs ss bvs
                                                                                                                                                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                hFTrans hSubstTrans
                                                                                                                                                                                                                (substitute_simul_rec_uop_eq_self UserOp.bvultbv xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                (fun {s t} h => bvultbv_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                  show __smtx_model_eval M
                                                                                                                                                                                                                      (SmtTerm.ite (SmtTerm.bvult (__eo_to_smt X1) (__eo_to_smt X2))
                                                                                                                                                                                                                        (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) =
                                                                                                                                                                                                                    __smtx_model_eval N
                                                                                                                                                                                                                      (SmtTerm.ite (SmtTerm.bvult (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                        (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
                                                                                                                                                                                                                  simp only [__smtx_model_eval]
                                                                                                                                                                                                                  rw [h1, h2])
                                                                                                                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                            · by_cases h_bvsltbv : op = UserOp.bvsltbv
                                                                                                                                                                                                              · subst op
                                                                                                                                                                                                                exact substFalse_eval_binary_op UserOp.bvsltbv x1 a xs ss bvs
                                                                                                                                                                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                  hFTrans hSubstTrans
                                                                                                                                                                                                                  (substitute_simul_rec_uop_eq_self UserOp.bvsltbv xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                  (fun {s t} h => bvsltbv_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                    show __smtx_model_eval M
                                                                                                                                                                                                                        (SmtTerm.ite (SmtTerm.bvslt (__eo_to_smt X1) (__eo_to_smt X2))
                                                                                                                                                                                                                          (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) =
                                                                                                                                                                                                                      __smtx_model_eval N
                                                                                                                                                                                                                        (SmtTerm.ite (SmtTerm.bvslt (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                          (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
                                                                                                                                                                                                                    simp only [__smtx_model_eval]
                                                                                                                                                                                                                    rw [h1, h2])
                                                                                                                                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                              · by_cases h_from_bools : op = UserOp._at_from_bools
                                                                                                                                                                                                                · subst op
                                                                                                                                                                                                                  exact substFalse_eval_binary_op UserOp._at_from_bools x1 a xs ss bvs
                                                                                                                                                                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                    hFTrans hSubstTrans
                                                                                                                                                                                                                    (substitute_simul_rec_uop_eq_self UserOp._at_from_bools xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                    (fun {s t} h => from_bools_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                                                                    (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                      show __smtx_model_eval M
                                                                                                                                                                                                                          (SmtTerm.concat
                                                                                                                                                                                                                            (__eo_to_smt X2)
                                                                                                                                                                                                                            (SmtTerm.ite (__eo_to_smt X1)
                                                                                                                                                                                                                              (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))) =
                                                                                                                                                                                                                        __smtx_model_eval N
                                                                                                                                                                                                                          (SmtTerm.concat
                                                                                                                                                                                                                            (__eo_to_smt Y2)
                                                                                                                                                                                                                            (SmtTerm.ite (__eo_to_smt Y1)
                                                                                                                                                                                                                              (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)))
                                                                                                                                                                                                                      simp only [__smtx_model_eval]
                                                                                                                                                                                                                      rw [h1, h2])
                                                                                                                                                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                · by_cases h_strings_deq_diff : op = UserOp._at_strings_deq_diff
                                                                                                                                                                                                                  · subst op
                                                                                                                                                                                                                    exact substFalse_eval_binary_op UserOp._at_strings_deq_diff x1 a xs ss bvs
                                                                                                                                                                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                      hFTrans hSubstTrans
                                                                                                                                                                                                                      (substitute_simul_rec_uop_eq_self UserOp._at_strings_deq_diff xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                      (fun {s t} h => strings_deq_diff_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                                                                      (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                        show __smtx_model_eval M (SmtTerm.seq_diff (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                          __smtx_model_eval N (SmtTerm.seq_diff (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                        simp only [__smtx_model_eval]
                                                                                                                                                                                                                        rw [h1, h2])
                                                                                                                                                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                  · by_cases h_strings_stoi_result : op = UserOp._at_strings_stoi_result
                                                                                                                                                                                                                    · subst op
                                                                                                                                                                                                                      exact substFalse_eval_binary_op UserOp._at_strings_stoi_result x1 a xs ss bvs
                                                                                                                                                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                        hFTrans hSubstTrans
                                                                                                                                                                                                                        (substitute_simul_rec_uop_eq_self UserOp._at_strings_stoi_result xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                        (fun {s t} h => strings_stoi_result_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                                                                        (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                          show __smtx_model_eval M
                                                                                                                                                                                                                              (SmtTerm.ite
                                                                                                                                                                                                                                (SmtTerm.eq (__eo_to_smt X2) (SmtTerm.Numeral 0))
                                                                                                                                                                                                                                (SmtTerm.Numeral 0)
                                                                                                                                                                                                                                (SmtTerm.str_to_int
                                                                                                                                                                                                                                  (SmtTerm.str_substr (__eo_to_smt X1)
                                                                                                                                                                                                                                    (SmtTerm.Numeral 0) (__eo_to_smt X2)))) =
                                                                                                                                                                                                                            __smtx_model_eval N
                                                                                                                                                                                                                              (SmtTerm.ite
                                                                                                                                                                                                                                (SmtTerm.eq (__eo_to_smt Y2) (SmtTerm.Numeral 0))
                                                                                                                                                                                                                                (SmtTerm.Numeral 0)
                                                                                                                                                                                                                                (SmtTerm.str_to_int
                                                                                                                                                                                                                                  (SmtTerm.str_substr (__eo_to_smt Y1)
                                                                                                                                                                                                                                    (SmtTerm.Numeral 0) (__eo_to_smt Y2))))
                                                                                                                                                                                                                          simp only [__smtx_model_eval]
                                                                                                                                                                                                                          rw [h1, h2])
                                                                                                                                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                    · by_cases h_str_concat : op = UserOp.str_concat
                                                                                                                                                                                                                      · subst op
                                                                                                                                                                                                                        exact substFalse_eval_binary_op UserOp.str_concat x1 a xs ss bvs
                                                                                                                                                                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                          hFTrans hSubstTrans
                                                                                                                                                                                                                          (substitute_simul_rec_uop_eq_self UserOp.str_concat xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                          (fun {s t} h =>
                                                                                                                                                                                                                            apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                              (eoOp := UserOp.str_concat) (smtOp := SmtTerm.str_concat)
                                                                                                                                                                                                                              (by rfl)
                                                                                                                                                                                                                              (fun hNN =>
                                                                                                                                                                                                                                seq_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                  (typeof_str_concat_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                                              h)
                                                                                                                                                                                                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                            show __smtx_model_eval M (SmtTerm.str_concat (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                              __smtx_model_eval N (SmtTerm.str_concat (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                            simp only [__smtx_model_eval]
                                                                                                                                                                                                                            rw [h1, h2])
                                                                                                                                                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                      · by_cases h_str_contains : op = UserOp.str_contains
                                                                                                                                                                                                                        · subst op
                                                                                                                                                                                                                          exact substFalse_eval_binary_op UserOp.str_contains x1 a xs ss bvs
                                                                                                                                                                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                            hFTrans hSubstTrans
                                                                                                                                                                                                                            (substitute_simul_rec_uop_eq_self UserOp.str_contains xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                            (fun {s t} h =>
                                                                                                                                                                                                                              apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                                (eoOp := UserOp.str_contains) (smtOp := SmtTerm.str_contains)
                                                                                                                                                                                                                                (by rfl)
                                                                                                                                                                                                                                (fun hNN =>
                                                                                                                                                                                                                                  seq_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                    (ret := SmtType.Bool)
                                                                                                                                                                                                                                    (typeof_str_contains_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                                                h)
                                                                                                                                                                                                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                              show __smtx_model_eval M (SmtTerm.str_contains (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                                __smtx_model_eval N (SmtTerm.str_contains (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                              simp only [__smtx_model_eval]
                                                                                                                                                                                                                              rw [h1, h2])
                                                                                                                                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                        · by_cases h_str_at : op = UserOp.str_at
                                                                                                                                                                                                                          · subst op
                                                                                                                                                                                                                            exact substFalse_eval_binary_op UserOp.str_at x1 a xs ss bvs
                                                                                                                                                                                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                              hFTrans hSubstTrans
                                                                                                                                                                                                                              (substitute_simul_rec_uop_eq_self UserOp.str_at xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                              (fun {s t} h =>
                                                                                                                                                                                                                                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                                  (eoOp := UserOp.str_at) (smtOp := SmtTerm.str_at)
                                                                                                                                                                                                                                  (by rfl) str_at_args_have_smt_translation_of_non_none h)
                                                                                                                                                                                                                              (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                                show __smtx_model_eval M (SmtTerm.str_at (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                                  __smtx_model_eval N (SmtTerm.str_at (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                                simp only [__smtx_model_eval]
                                                                                                                                                                                                                                rw [h1, h2])
                                                                                                                                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                          · by_cases h_str_prefixof : op = UserOp.str_prefixof
                                                                                                                                                                                                                            · subst op
                                                                                                                                                                                                                              exact substFalse_eval_binary_op UserOp.str_prefixof x1 a xs ss bvs
                                                                                                                                                                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                hFTrans hSubstTrans
                                                                                                                                                                                                                                (substitute_simul_rec_uop_eq_self UserOp.str_prefixof xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                (fun {s t} h =>
                                                                                                                                                                                                                                  apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                                    (eoOp := UserOp.str_prefixof) (smtOp := SmtTerm.str_prefixof)
                                                                                                                                                                                                                                    (by rfl)
                                                                                                                                                                                                                                    (fun hNN =>
                                                                                                                                                                                                                                      seq_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                        (typeof_str_prefixof_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                                                    h)
                                                                                                                                                                                                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                                  show __smtx_model_eval M (SmtTerm.str_prefixof (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                                    __smtx_model_eval N (SmtTerm.str_prefixof (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                                  simp only [__smtx_model_eval]
                                                                                                                                                                                                                                  rw [h1, h2])
                                                                                                                                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                            · by_cases h_str_suffixof : op = UserOp.str_suffixof
                                                                                                                                                                                                                              · subst op
                                                                                                                                                                                                                                exact substFalse_eval_binary_op UserOp.str_suffixof x1 a xs ss bvs
                                                                                                                                                                                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                  hFTrans hSubstTrans
                                                                                                                                                                                                                                  (substitute_simul_rec_uop_eq_self UserOp.str_suffixof xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                  (fun {s t} h =>
                                                                                                                                                                                                                                    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                                      (eoOp := UserOp.str_suffixof) (smtOp := SmtTerm.str_suffixof)
                                                                                                                                                                                                                                      (by rfl)
                                                                                                                                                                                                                                      (fun hNN =>
                                                                                                                                                                                                                                        seq_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                          (typeof_str_suffixof_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                                                      h)
                                                                                                                                                                                                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                                    show __smtx_model_eval M (SmtTerm.str_suffixof (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                                      __smtx_model_eval N (SmtTerm.str_suffixof (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                                    simp only [__smtx_model_eval]
                                                                                                                                                                                                                                    rw [h1, h2])
                                                                                                                                                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                              · by_cases h_str_lt : op = UserOp.str_lt
                                                                                                                                                                                                                                · subst op
                                                                                                                                                                                                                                  exact substFalse_eval_binary_op UserOp.str_lt x1 a xs ss bvs
                                                                                                                                                                                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                    hFTrans hSubstTrans
                                                                                                                                                                                                                                    (substitute_simul_rec_uop_eq_self UserOp.str_lt xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                    (fun {s t} h =>
                                                                                                                                                                                                                                      apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                                        (eoOp := UserOp.str_lt) (smtOp := SmtTerm.str_lt)
                                                                                                                                                                                                                                        (by rfl)
                                                                                                                                                                                                                                        (fun hNN =>
                                                                                                                                                                                                                                          seq_char_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                            (ret := SmtType.Bool)
                                                                                                                                                                                                                                            (typeof_str_lt_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                                                        h)
                                                                                                                                                                                                                                    (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                                      show __smtx_model_eval M (SmtTerm.str_lt (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                                        __smtx_model_eval N (SmtTerm.str_lt (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                                      simp only [__smtx_model_eval]
                                                                                                                                                                                                                                      rw [h1, h2])
                                                                                                                                                                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                · by_cases h_str_leq : op = UserOp.str_leq
                                                                                                                                                                                                                                  · subst op
                                                                                                                                                                                                                                    exact substFalse_eval_binary_op UserOp.str_leq x1 a xs ss bvs
                                                                                                                                                                                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                      hFTrans hSubstTrans
                                                                                                                                                                                                                                      (substitute_simul_rec_uop_eq_self UserOp.str_leq xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                      (fun {s t} h =>
                                                                                                                                                                                                                                        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                                          (eoOp := UserOp.str_leq) (smtOp := SmtTerm.str_leq)
                                                                                                                                                                                                                                          (by rfl)
                                                                                                                                                                                                                                          (fun hNN =>
                                                                                                                                                                                                                                            seq_char_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                              (ret := SmtType.Bool)
                                                                                                                                                                                                                                              (typeof_str_leq_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                                                          h)
                                                                                                                                                                                                                                      (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                                        show __smtx_model_eval M (SmtTerm.str_leq (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                                          __smtx_model_eval N (SmtTerm.str_leq (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                                        simp only [__smtx_model_eval]
                                                                                                                                                                                                                                        rw [h1, h2])
                                                                                                                                                                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                  · by_cases h_re_range : op = UserOp.re_range
                                                                                                                                                                                                                                    · subst op
                                                                                                                                                                                                                                      exact substFalse_eval_binary_op UserOp.re_range x1 a xs ss bvs
                                                                                                                                                                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                        hFTrans hSubstTrans
                                                                                                                                                                                                                                        (substitute_simul_rec_uop_eq_self UserOp.re_range xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                        (fun {s t} h =>
                                                                                                                                                                                                                                          apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                                            (eoOp := UserOp.re_range) (smtOp := SmtTerm.re_range)
                                                                                                                                                                                                                                            (by rfl)
                                                                                                                                                                                                                                            (fun hNN =>
                                                                                                                                                                                                                                              seq_char_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                (ret := SmtType.RegLan)
                                                                                                                                                                                                                                                (typeof_re_range_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                                                            h)
                                                                                                                                                                                                                                        (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                                          show __smtx_model_eval M (SmtTerm.re_range (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                                            __smtx_model_eval N (SmtTerm.re_range (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                                          simp only [__smtx_model_eval]
                                                                                                                                                                                                                                          rw [h1, h2])
                                                                                                                                                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                    · by_cases h_re_concat : op = UserOp.re_concat
                                                                                                                                                                                                                                      · subst op
                                                                                                                                                                                                                                        exact substFalse_eval_binary_op UserOp.re_concat x1 a xs ss bvs
                                                                                                                                                                                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                          hFTrans hSubstTrans
                                                                                                                                                                                                                                          (substitute_simul_rec_uop_eq_self UserOp.re_concat xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                          (fun {s t} h =>
                                                                                                                                                                                                                                            apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                                              (eoOp := UserOp.re_concat) (smtOp := SmtTerm.re_concat)
                                                                                                                                                                                                                                              (by rfl)
                                                                                                                                                                                                                                              (fun hNN =>
                                                                                                                                                                                                                                                reglan_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                  (typeof_re_concat_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                                                              h)
                                                                                                                                                                                                                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                                            show __smtx_model_eval M (SmtTerm.re_concat (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                                              __smtx_model_eval N (SmtTerm.re_concat (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                                            simp only [__smtx_model_eval]
                                                                                                                                                                                                                                            rw [h1, h2])
                                                                                                                                                                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                      · by_cases h_re_inter : op = UserOp.re_inter
                                                                                                                                                                                                                                        · subst op
                                                                                                                                                                                                                                          exact substFalse_eval_binary_op UserOp.re_inter x1 a xs ss bvs
                                                                                                                                                                                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                            hFTrans hSubstTrans
                                                                                                                                                                                                                                            (substitute_simul_rec_uop_eq_self UserOp.re_inter xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                            (fun {s t} h =>
                                                                                                                                                                                                                                              apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                                                (eoOp := UserOp.re_inter) (smtOp := SmtTerm.re_inter)
                                                                                                                                                                                                                                                (by rfl)
                                                                                                                                                                                                                                                (fun hNN =>
                                                                                                                                                                                                                                                  reglan_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                    (typeof_re_inter_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                                                                h)
                                                                                                                                                                                                                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                                              show __smtx_model_eval M (SmtTerm.re_inter (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                                                __smtx_model_eval N (SmtTerm.re_inter (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                                              simp only [__smtx_model_eval]
                                                                                                                                                                                                                                              rw [h1, h2])
                                                                                                                                                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                        · by_cases h_re_union : op = UserOp.re_union
                                                                                                                                                                                                                                          · subst op
                                                                                                                                                                                                                                            exact substFalse_eval_binary_op UserOp.re_union x1 a xs ss bvs
                                                                                                                                                                                                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                              hFTrans hSubstTrans
                                                                                                                                                                                                                                              (substitute_simul_rec_uop_eq_self UserOp.re_union xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                              (fun {s t} h =>
                                                                                                                                                                                                                                                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                                                  (eoOp := UserOp.re_union) (smtOp := SmtTerm.re_union)
                                                                                                                                                                                                                                                  (by rfl)
                                                                                                                                                                                                                                                  (fun hNN =>
                                                                                                                                                                                                                                                    reglan_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                      (typeof_re_union_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                                                                  h)
                                                                                                                                                                                                                                              (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                                                show __smtx_model_eval M (SmtTerm.re_union (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                                                  __smtx_model_eval N (SmtTerm.re_union (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                                                simp only [__smtx_model_eval]
                                                                                                                                                                                                                                                rw [h1, h2])
                                                                                                                                                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                          · by_cases h_re_diff : op = UserOp.re_diff
                                                                                                                                                                                                                                            · subst op
                                                                                                                                                                                                                                              exact substFalse_eval_binary_op UserOp.re_diff x1 a xs ss bvs
                                                                                                                                                                                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                                hFTrans hSubstTrans
                                                                                                                                                                                                                                                (substitute_simul_rec_uop_eq_self UserOp.re_diff xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                                (fun {s t} h =>
                                                                                                                                                                                                                                                  apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                                                    (eoOp := UserOp.re_diff) (smtOp := SmtTerm.re_diff)
                                                                                                                                                                                                                                                    (by rfl)
                                                                                                                                                                                                                                                    (fun hNN =>
                                                                                                                                                                                                                                                      reglan_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                        (typeof_re_diff_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                                                                    h)
                                                                                                                                                                                                                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                                                  show __smtx_model_eval M (SmtTerm.re_diff (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                                                    __smtx_model_eval N (SmtTerm.re_diff (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                                                  simp only [__smtx_model_eval]
                                                                                                                                                                                                                                                  rw [h1, h2])
                                                                                                                                                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                            · by_cases h_str_in_re : op = UserOp.str_in_re
                                                                                                                                                                                                                                              · subst op
                                                                                                                                                                                                                                                exact substFalse_eval_binary_op UserOp.str_in_re x1 a xs ss bvs
                                                                                                                                                                                                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                                  hFTrans hSubstTrans
                                                                                                                                                                                                                                                  (substitute_simul_rec_uop_eq_self UserOp.str_in_re xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                                  (fun {s t} h =>
                                                                                                                                                                                                                                                    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                                                      (eoOp := UserOp.str_in_re) (smtOp := SmtTerm.str_in_re)
                                                                                                                                                                                                                                                      (by rfl)
                                                                                                                                                                                                                                                      (fun hNN =>
                                                                                                                                                                                                                                                        seq_char_reglan_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                          (ret := SmtType.Bool)
                                                                                                                                                                                                                                                          (typeof_str_in_re_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                                                                      h)
                                                                                                                                                                                                                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                                                    show __smtx_model_eval M (SmtTerm.str_in_re (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                                                      __smtx_model_eval N (SmtTerm.str_in_re (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                                                    simp only [__smtx_model_eval]
                                                                                                                                                                                                                                                    rw [h1, h2])
                                                                                                                                                                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                              · by_cases h_seq_nth : op = UserOp.seq_nth
                                                                                                                                                                                                                                                · subst op
                                                                                                                                                                                                                                                  exact substFalse_eval_binary_op UserOp.seq_nth x1 a xs ss bvs
                                                                                                                                                                                                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                                    hFTrans hSubstTrans
                                                                                                                                                                                                                                                    (substitute_simul_rec_uop_eq_self UserOp.seq_nth xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                                    (fun {s t} h =>
                                                                                                                                                                                                                                                      apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                                                        (eoOp := UserOp.seq_nth) (smtOp := SmtTerm.seq_nth)
                                                                                                                                                                                                                                                        (by rfl) seq_nth_args_have_smt_translation_of_non_none h)
                                                                                                                                                                                                                                                    (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                                                      show __smtx_model_eval M (SmtTerm.seq_nth (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                                                        __smtx_model_eval N (SmtTerm.seq_nth (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                                                      simp only [__smtx_model_eval]
                                                                                                                                                                                                                                                      rw [h1, h2, smtx_seq_nth_eq_of_globals hGlobals])
                                                                                                                                                                                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                · by_cases h_set_union : op = UserOp.set_union
                                                                                                                                                                                                                                                  · subst op
                                                                                                                                                                                                                                                    exact substFalse_eval_binary_op UserOp.set_union x1 a xs ss bvs
                                                                                                                                                                                                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                                      hFTrans hSubstTrans
                                                                                                                                                                                                                                                      (substitute_simul_rec_uop_eq_self UserOp.set_union xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                                      (fun {s t} h =>
                                                                                                                                                                                                                                                        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                                                          (eoOp := UserOp.set_union) (smtOp := SmtTerm.set_union)
                                                                                                                                                                                                                                                          (by rfl)
                                                                                                                                                                                                                                                          (fun hNN =>
                                                                                                                                                                                                                                                            set_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                              (typeof_set_union_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                                                                          h)
                                                                                                                                                                                                                                                      (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                                                        show __smtx_model_eval M (SmtTerm.set_union (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                                                          __smtx_model_eval N (SmtTerm.set_union (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                                                        simp only [__smtx_model_eval]
                                                                                                                                                                                                                                                        rw [h1, h2])
                                                                                                                                                                                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                  · by_cases h_set_inter : op = UserOp.set_inter
                                                                                                                                                                                                                                                    · subst op
                                                                                                                                                                                                                                                      exact substFalse_eval_binary_op UserOp.set_inter x1 a xs ss bvs
                                                                                                                                                                                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                                        hFTrans hSubstTrans
                                                                                                                                                                                                                                                        (substitute_simul_rec_uop_eq_self UserOp.set_inter xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                                        (fun {s t} h =>
                                                                                                                                                                                                                                                          apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                                                            (eoOp := UserOp.set_inter) (smtOp := SmtTerm.set_inter)
                                                                                                                                                                                                                                                            (by rfl)
                                                                                                                                                                                                                                                            (fun hNN =>
                                                                                                                                                                                                                                                              set_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                                (typeof_set_inter_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                                                                            h)
                                                                                                                                                                                                                                                        (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                                                          show __smtx_model_eval M (SmtTerm.set_inter (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                                                            __smtx_model_eval N (SmtTerm.set_inter (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                                                          simp only [__smtx_model_eval]
                                                                                                                                                                                                                                                          rw [h1, h2])
                                                                                                                                                                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                    · by_cases h_set_minus : op = UserOp.set_minus
                                                                                                                                                                                                                                                      · subst op
                                                                                                                                                                                                                                                        exact substFalse_eval_binary_op UserOp.set_minus x1 a xs ss bvs
                                                                                                                                                                                                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                                          hFTrans hSubstTrans
                                                                                                                                                                                                                                                          (substitute_simul_rec_uop_eq_self UserOp.set_minus xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                                          (fun {s t} h =>
                                                                                                                                                                                                                                                            apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                                                              (eoOp := UserOp.set_minus) (smtOp := SmtTerm.set_minus)
                                                                                                                                                                                                                                                              (by rfl)
                                                                                                                                                                                                                                                              (fun hNN =>
                                                                                                                                                                                                                                                                set_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                                  (typeof_set_minus_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                                                                              h)
                                                                                                                                                                                                                                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                                                            show __smtx_model_eval M (SmtTerm.set_minus (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                                                              __smtx_model_eval N (SmtTerm.set_minus (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                                                            simp only [__smtx_model_eval]
                                                                                                                                                                                                                                                            rw [h1, h2])
                                                                                                                                                                                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                      · by_cases h_set_member : op = UserOp.set_member
                                                                                                                                                                                                                                                        · subst op
                                                                                                                                                                                                                                                          exact substFalse_eval_binary_op UserOp.set_member x1 a xs ss bvs
                                                                                                                                                                                                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                                            hFTrans hSubstTrans
                                                                                                                                                                                                                                                            (substitute_simul_rec_uop_eq_self UserOp.set_member xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                                            (fun {s t} h =>
                                                                                                                                                                                                                                                              apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                                                                (eoOp := UserOp.set_member) (smtOp := SmtTerm.set_member)
                                                                                                                                                                                                                                                                (by rfl) set_member_args_have_smt_translation_of_non_none h)
                                                                                                                                                                                                                                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                                                              show __smtx_model_eval M (SmtTerm.set_member (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                                                                __smtx_model_eval N (SmtTerm.set_member (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                                                              simp only [__smtx_model_eval]
                                                                                                                                                                                                                                                              rw [h1, h2])
                                                                                                                                                                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                        · by_cases h_set_subset : op = UserOp.set_subset
                                                                                                                                                                                                                                                          · subst op
                                                                                                                                                                                                                                                            exact substFalse_eval_binary_op UserOp.set_subset x1 a xs ss bvs
                                                                                                                                                                                                                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                                              hFTrans hSubstTrans
                                                                                                                                                                                                                                                              (substitute_simul_rec_uop_eq_self UserOp.set_subset xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                                              (fun {s t} h =>
                                                                                                                                                                                                                                                                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                                                                                  (eoOp := UserOp.set_subset) (smtOp := SmtTerm.set_subset)
                                                                                                                                                                                                                                                                  (by rfl)
                                                                                                                                                                                                                                                                  (fun hNN =>
                                                                                                                                                                                                                                                                    set_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                                      (ret := SmtType.Bool)
                                                                                                                                                                                                                                                                      (typeof_set_subset_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                                                                                  h)
                                                                                                                                                                                                                                                              (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                                                                show __smtx_model_eval M (SmtTerm.set_subset (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                                                                                  __smtx_model_eval N (SmtTerm.set_subset (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                                                                                simp only [__smtx_model_eval]
                                                                                                                                                                                                                                                                rw [h1, h2])
                                                                                                                                                                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                          · by_cases h_strings_itos_result : op = UserOp._at_strings_itos_result
                                                                                                                                                                                                                                                            · subst op
                                                                                                                                                                                                                                                              exact substFalse_eval_binary_op UserOp._at_strings_itos_result x1 a xs ss bvs
                                                                                                                                                                                                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                                                hFTrans hSubstTrans
                                                                                                                                                                                                                                                                (substitute_simul_rec_uop_eq_self UserOp._at_strings_itos_result xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                                                (fun {s t} h => strings_itos_result_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                                                                                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                                                                  show __smtx_model_eval M
                                                                                                                                                                                                                                                                      (SmtTerm.ite
                                                                                                                                                                                                                                                                        (SmtTerm.eq (__eo_to_smt X2) (SmtTerm.Numeral 0))
                                                                                                                                                                                                                                                                        (SmtTerm.Numeral 0)
                                                                                                                                                                                                                                                                        (SmtTerm.str_to_int
                                                                                                                                                                                                                                                                          (SmtTerm.str_substr
                                                                                                                                                                                                                                                                            (SmtTerm.str_from_int (__eo_to_smt X1))
                                                                                                                                                                                                                                                                            (SmtTerm.Numeral 0) (__eo_to_smt X2)))) =
                                                                                                                                                                                                                                                                    __smtx_model_eval N
                                                                                                                                                                                                                                                                      (SmtTerm.ite
                                                                                                                                                                                                                                                                        (SmtTerm.eq (__eo_to_smt Y2) (SmtTerm.Numeral 0))
                                                                                                                                                                                                                                                                        (SmtTerm.Numeral 0)
                                                                                                                                                                                                                                                                        (SmtTerm.str_to_int
                                                                                                                                                                                                                                                                          (SmtTerm.str_substr
                                                                                                                                                                                                                                                                            (SmtTerm.str_from_int (__eo_to_smt Y1))
                                                                                                                                                                                                                                                                            (SmtTerm.Numeral 0) (__eo_to_smt Y2))))
                                                                                                                                                                                                                                                                  simp [__smtx_model_eval, h1, h2])
                                                                                                                                                                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                            · by_cases h_strings_num_occur : op = UserOp._at_strings_num_occur
                                                                                                                                                                                                                                                              · subst op
                                                                                                                                                                                                                                                                exact substFalse_eval_binary_op UserOp._at_strings_num_occur x1 a xs ss bvs
                                                                                                                                                                                                                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                                                  hFTrans hSubstTrans
                                                                                                                                                                                                                                                                  (substitute_simul_rec_uop_eq_self UserOp._at_strings_num_occur xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                                                  (fun {s t} h => strings_num_occur_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                                                                                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                                                                    show __smtx_model_eval M
                                                                                                                                                                                                                                                                        (SmtTerm.neg
                                                                                                                                                                                                                                                                          (SmtTerm.str_len
                                                                                                                                                                                                                                                                            (SmtTerm.str_replace_all (__eo_to_smt X1) (__eo_to_smt X2)
                                                                                                                                                                                                                                                                              (SmtTerm.str_substr (__eo_to_smt X1) (SmtTerm.Numeral 0) (SmtTerm.Numeral 1))))
                                                                                                                                                                                                                                                                          (SmtTerm.str_len
                                                                                                                                                                                                                                                                            (SmtTerm.str_replace_all (__eo_to_smt X1) (__eo_to_smt X2)
                                                                                                                                                                                                                                                                              (SmtTerm.str_substr (__eo_to_smt X1) (SmtTerm.Numeral 0) (SmtTerm.Numeral 0))))) =
                                                                                                                                                                                                                                                                      __smtx_model_eval N
                                                                                                                                                                                                                                                                        (SmtTerm.neg
                                                                                                                                                                                                                                                                          (SmtTerm.str_len
                                                                                                                                                                                                                                                                            (SmtTerm.str_replace_all (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                                                                                                                                                                                                                                              (SmtTerm.str_substr (__eo_to_smt Y1) (SmtTerm.Numeral 0) (SmtTerm.Numeral 1))))
                                                                                                                                                                                                                                                                          (SmtTerm.str_len
                                                                                                                                                                                                                                                                            (SmtTerm.str_replace_all (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                                                                                                                                                                                                                                              (SmtTerm.str_substr (__eo_to_smt Y1) (SmtTerm.Numeral 0) (SmtTerm.Numeral 0)))))
                                                                                                                                                                                                                                                                    simp [__smtx_model_eval, h1, h2])
                                                                                                                                                                                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                              · by_cases h_strings_num_occur_re : op = UserOp._at_strings_num_occur_re
                                                                                                                                                                                                                                                                · subst op
                                                                                                                                                                                                                                                                  exact substFalse_eval_binary_op UserOp._at_strings_num_occur_re x1 a xs ss bvs
                                                                                                                                                                                                                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                                                    hFTrans hSubstTrans
                                                                                                                                                                                                                                                                    (substitute_simul_rec_uop_eq_self UserOp._at_strings_num_occur_re xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                                                    (fun {s t} h => strings_num_occur_re_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                                                                                                                    (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                                                                                      show __smtx_model_eval M
                                                                                                                                                                                                                                                                          (SmtTerm.neg
                                                                                                                                                                                                                                                                            (SmtTerm.str_len
                                                                                                                                                                                                                                                                              (SmtTerm.str_replace_re_all (__eo_to_smt X1) (__eo_to_smt X2)
                                                                                                                                                                                                                                                                                (SmtTerm.str_substr (__eo_to_smt X1) (SmtTerm.Numeral 0) (SmtTerm.Numeral 1))))
                                                                                                                                                                                                                                                                            (SmtTerm.str_len
                                                                                                                                                                                                                                                                              (SmtTerm.str_replace_re_all (__eo_to_smt X1) (__eo_to_smt X2)
                                                                                                                                                                                                                                                                                (SmtTerm.str_substr (__eo_to_smt X1) (SmtTerm.Numeral 0) (SmtTerm.Numeral 0))))) =
                                                                                                                                                                                                                                                                        __smtx_model_eval N
                                                                                                                                                                                                                                                                          (SmtTerm.neg
                                                                                                                                                                                                                                                                            (SmtTerm.str_len
                                                                                                                                                                                                                                                                              (SmtTerm.str_replace_re_all (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                                                                                                                                                                                                                                                (SmtTerm.str_substr (__eo_to_smt Y1) (SmtTerm.Numeral 0) (SmtTerm.Numeral 1))))
                                                                                                                                                                                                                                                                            (SmtTerm.str_len
                                                                                                                                                                                                                                                                              (SmtTerm.str_replace_re_all (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                                                                                                                                                                                                                                                (SmtTerm.str_substr (__eo_to_smt Y1) (SmtTerm.Numeral 0) (SmtTerm.Numeral 0)))))
                                                                                                                                                                                                                                                                      simp [__smtx_model_eval, h1, h2])
                                                                                                                                                                                                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                                    (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                                · by_cases h_array_deq_diff : op = UserOp._at_array_deq_diff
                                                                                                                                                                                                                                                                  · subst op
                                                                                                                                                                                                                                                                    exact substFalse_eval_binary_op_with_app_trans UserOp._at_array_deq_diff x1 a xs ss bvs
                                                                                                                                                                                                                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                                                      hFTrans hSubstTrans
                                                                                                                                                                                                                                                                      (substitute_simul_rec_uop_eq_self UserOp._at_array_deq_diff xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                                                      (fun {s t} h => array_deq_diff_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                                                                                                                      (fun X1 Y1 X2 Y2 hSubApp hOrigApp h1 h2 => by
                                                                                                                                                                                                                                                                        unfold eoHasSmtTranslation at hSubApp hOrigApp
                                                                                                                                                                                                                                                                        change
                                                                                                                                                                                                                                                                            __smtx_model_eval M
                                                                                                                                                                                                                                                                                (__eo_to_smt_array_deq_diff (__eo_to_smt X1)
                                                                                                                                                                                                                                                                                  (__smtx_typeof (__eo_to_smt X1))
                                                                                                                                                                                                                                                                                  (__eo_to_smt X2)
                                                                                                                                                                                                                                                                                  (__smtx_typeof (__eo_to_smt X2))) =
                                                                                                                                                                                                                                                                              __smtx_model_eval N
                                                                                                                                                                                                                                                                                (__eo_to_smt_array_deq_diff (__eo_to_smt Y1)
                                                                                                                                                                                                                                                                                  (__smtx_typeof (__eo_to_smt Y1))
                                                                                                                                                                                                                                                                                  (__eo_to_smt Y2)
                                                                                                                                                                                                                                                                                  (__smtx_typeof (__eo_to_smt Y2)))
                                                                                                                                                                                                                                                                        change
                                                                                                                                                                                                                                                                            __smtx_typeof
                                                                                                                                                                                                                                                                                (__eo_to_smt_array_deq_diff (__eo_to_smt X1)
                                                                                                                                                                                                                                                                                  (__smtx_typeof (__eo_to_smt X1))
                                                                                                                                                                                                                                                                                  (__eo_to_smt X2)
                                                                                                                                                                                                                                                                                  (__smtx_typeof (__eo_to_smt X2))) ≠
                                                                                                                                                                                                                                                                              SmtType.None at hSubApp
                                                                                                                                                                                                                                                                        change
                                                                                                                                                                                                                                                                            __smtx_typeof
                                                                                                                                                                                                                                                                                (__eo_to_smt_array_deq_diff (__eo_to_smt Y1)
                                                                                                                                                                                                                                                                                  (__smtx_typeof (__eo_to_smt Y1))
                                                                                                                                                                                                                                                                                  (__eo_to_smt Y2)
                                                                                                                                                                                                                                                                                  (__smtx_typeof (__eo_to_smt Y2))) ≠
                                                                                                                                                                                                                                                                              SmtType.None at hOrigApp
                                                                                                                                                                                                                                                                        cases hX1Ty : __smtx_typeof (__eo_to_smt X1) <;>
                                                                                                                                                                                                                                                                          cases hX2Ty : __smtx_typeof (__eo_to_smt X2) <;>
                                                                                                                                                                                                                                                                          simp [__eo_to_smt_array_deq_diff, hX1Ty, hX2Ty,
                                                                                                                                                                                                                                                                            TranslationProofs.smtx_typeof_none] at hSubApp ⊢
                                                                                                                                                                                                                                                                        case Map.Map A B C D =>
                                                                                                                                                                                                                                                                          cases hY1Ty : __smtx_typeof (__eo_to_smt Y1) <;>
                                                                                                                                                                                                                                                                            cases hY2Ty : __smtx_typeof (__eo_to_smt Y2) <;>
                                                                                                                                                                                                                                                                            simp [__eo_to_smt_array_deq_diff, hY1Ty, hY2Ty,
                                                                                                                                                                                                                                                                              TranslationProofs.smtx_typeof_none] at hOrigApp ⊢
                                                                                                                                                                                                                                                                          case Map.Map A' B' C' D' =>
                                                                                                                                                                                                                                                                            simp [__smtx_model_eval, h1, h2])
                                                                                                                                                                                                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                                      (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                                  · by_cases h_sets_deq_diff : op = UserOp._at_sets_deq_diff
                                                                                                                                                                                                                                                                    · subst op
                                                                                                                                                                                                                                                                      exact substFalse_eval_binary_op_with_app_trans UserOp._at_sets_deq_diff x1 a xs ss bvs
                                                                                                                                                                                                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                                                        hFTrans hSubstTrans
                                                                                                                                                                                                                                                                        (substitute_simul_rec_uop_eq_self UserOp._at_sets_deq_diff xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                                                        (fun {s t} h => sets_deq_diff_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                                                                                                                        (fun X1 Y1 X2 Y2 hSubApp hOrigApp h1 h2 => by
                                                                                                                                                                                                                                                                          unfold eoHasSmtTranslation at hSubApp hOrigApp
                                                                                                                                                                                                                                                                          change
                                                                                                                                                                                                                                                                              __smtx_model_eval M
                                                                                                                                                                                                                                                                                  (__eo_to_smt_sets_deq_diff (__eo_to_smt X1)
                                                                                                                                                                                                                                                                                    (__smtx_typeof (__eo_to_smt X1))
                                                                                                                                                                                                                                                                                    (__eo_to_smt X2)
                                                                                                                                                                                                                                                                                    (__smtx_typeof (__eo_to_smt X2))) =
                                                                                                                                                                                                                                                                                __smtx_model_eval N
                                                                                                                                                                                                                                                                                  (__eo_to_smt_sets_deq_diff (__eo_to_smt Y1)
                                                                                                                                                                                                                                                                                    (__smtx_typeof (__eo_to_smt Y1))
                                                                                                                                                                                                                                                                                    (__eo_to_smt Y2)
                                                                                                                                                                                                                                                                                    (__smtx_typeof (__eo_to_smt Y2)))
                                                                                                                                                                                                                                                                          change
                                                                                                                                                                                                                                                                              __smtx_typeof
                                                                                                                                                                                                                                                                                  (__eo_to_smt_sets_deq_diff (__eo_to_smt X1)
                                                                                                                                                                                                                                                                                    (__smtx_typeof (__eo_to_smt X1))
                                                                                                                                                                                                                                                                                    (__eo_to_smt X2)
                                                                                                                                                                                                                                                                                    (__smtx_typeof (__eo_to_smt X2))) ≠
                                                                                                                                                                                                                                                                                SmtType.None at hSubApp
                                                                                                                                                                                                                                                                          change
                                                                                                                                                                                                                                                                              __smtx_typeof
                                                                                                                                                                                                                                                                                  (__eo_to_smt_sets_deq_diff (__eo_to_smt Y1)
                                                                                                                                                                                                                                                                                    (__smtx_typeof (__eo_to_smt Y1))
                                                                                                                                                                                                                                                                                    (__eo_to_smt Y2)
                                                                                                                                                                                                                                                                                    (__smtx_typeof (__eo_to_smt Y2))) ≠
                                                                                                                                                                                                                                                                                SmtType.None at hOrigApp
                                                                                                                                                                                                                                                                          cases hX1Ty : __smtx_typeof (__eo_to_smt X1) <;>
                                                                                                                                                                                                                                                                            cases hX2Ty : __smtx_typeof (__eo_to_smt X2) <;>
                                                                                                                                                                                                                                                                            simp [__eo_to_smt_sets_deq_diff, hX1Ty, hX2Ty,
                                                                                                                                                                                                                                                                              TranslationProofs.smtx_typeof_none] at hSubApp ⊢
                                                                                                                                                                                                                                                                          case Set.Set A B =>
                                                                                                                                                                                                                                                                            cases hY1Ty : __smtx_typeof (__eo_to_smt Y1) <;>
                                                                                                                                                                                                                                                                              cases hY2Ty : __smtx_typeof (__eo_to_smt Y2) <;>
                                                                                                                                                                                                                                                                              simp [__eo_to_smt_sets_deq_diff, hY1Ty, hY2Ty,
                                                                                                                                                                                                                                                                                TranslationProofs.smtx_typeof_none] at hOrigApp ⊢
                                                                                                                                                                                                                                                                            case Set.Set A' B' =>
                                                                                                                                                                                                                                                                              simp [__smtx_model_eval, h1, h2])
                                                                                                                                                                                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                                        (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                                    · by_cases h_forall : op = UserOp.forall
                                                                                                                                                                                                                                                                      · subst op
                                                                                                                                                                                                                                                                        exact
                                                                                                                                                                                                                                                                          false_of_forall_non_list_has_smt_translation
                                                                                                                                                                                                                                                                            (by
                                                                                                                                                                                                                                                                              intro v vs hEq
                                                                                                                                                                                                                                                                              exact hBinder ⟨Term.UOp UserOp.forall, v, vs, by rw [hEq]⟩)
                                                                                                                                                                                                                                                                            hFTrans
                                                                                                                                                                                                                                                                      · by_cases h_exists : op = UserOp.exists
                                                                                                                                                                                                                                                                        · subst op
                                                                                                                                                                                                                                                                          exact
                                                                                                                                                                                                                                                                            false_of_exists_non_list_has_smt_translation
                                                                                                                                                                                                                                                                              (by
                                                                                                                                                                                                                                                                                intro v vs hEq
                                                                                                                                                                                                                                                                                exact hBinder ⟨Term.UOp UserOp.exists, v, vs, by rw [hEq]⟩)
                                                                                                                                                                                                                                                                              hFTrans
                                                                                                                                                                                                                                                                        · by_cases h_tuple : op = UserOp.tuple
                                                                                                                                                                                                                                                                          · subst op
                                                                                                                                                                                                                                                                            exact substFalse_eval_binary_tuple x1 a xs ss bvs hM hN
                                                                                                                                                                                                                                                                              hisr hxs hss hbvs
                                                                                                                                                                                                                                                                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                                                              hFTrans hSubstTrans
                                                                                                                                                                                                                                                                              (substitute_simul_rec_uop_eq_self UserOp.tuple xs ss bvs
                                                                                                                                                                                                                                                                                hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                                                              hGlobals
                                                                                                                                                                                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                                          · by_cases h_set_insert : op = UserOp.set_insert
                                                                                                                                                                                                                                                                            · subst op
                                                                                                                                                                                                                                                                              exact substFalse_eval_set_insert x1 a xs ss bvs
                                                                                                                                                                                                                                                                                hXsEnv hBvsEnv hSsTrans
                                                                                                                                                                                                                                                                                hisr hxs hss hbvs
                                                                                                                                                                                                                                                                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                                                                hFTrans hSubstTrans
                                                                                                                                                                                                                                                                                (substitute_simul_rec_uop_eq_self UserOp.set_insert xs ss bvs
                                                                                                                                                                                                                                                                                  hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                                                                hRecArg
                                                                                                                                                                                                                                                                            · exact substFalse_eval_binary_uop_generic_apply op x1 a xs ss bvs
                                                                                                                                                                                                                                                                                hisr hxs hss hbvs
                                                                                                                                                                                                                                                                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                                                                (eo_to_smt_apply_apply_uop_generic_of_not_smt_binop
                                                                                                                                                                                                                                                                                  h_and h_or h_imp h_xor h_eq h_plus h_neg h_mult
                                                                                                                                                                                                                                                                                  h_lt h_leq h_gt h_geq h_div h_mod h_select
                                                                                                                                                                                                                                                                                  h_divisible h_div_total h_mod_total h_qdiv_total h_qdiv h_concat
                                                                                                                                                                                                                                                                                  h_bvand h_bvor h_bvnand h_bvnor h_bvxor h_bvxnor
                                                                                                                                                                                                                                                                                  h_bvcomp h_bvadd h_bvmul h_bvudiv h_bvurem h_bvsub
                                                                                                                                                                                                                                                                                  h_bvsdiv h_bvsrem h_bvsmod h_bvshl h_bvlshr
                                                                                                                                                                                                                                                                                  h_bvashr h_bvult h_bvule h_bvugt h_bvuge h_bvslt
                                                                                                                                                                                                                                                                                  h_bvsle h_bvsgt h_bvsge h_bvuaddo h_bvsaddo
                                                                                                                                                                                                                                                                                  h_bvumulo h_bvsmulo h_bvusubo h_bvssubo h_bvsdivo
                                                                                                                                                                                                                                                                                  h_bvultbv h_bvsltbv h_from_bools h_strings_deq_diff
                                                                                                                                                                                                                                                                                  h_strings_stoi_result h_str_concat h_str_contains h_str_at
                                                                                                                                                                                                                                                                                  h_str_prefixof h_str_suffixof h_str_lt h_str_leq
                                                                                                                                                                                                                                                                                  h_re_range h_re_concat h_re_inter h_re_union h_re_diff
                                                                                                                                                                                                                                                                                  h_str_in_re h_seq_nth h_set_union h_set_inter
                                                                                                                                                                                                                                                                                  h_set_minus h_set_member h_set_subset h_strings_itos_result
                                                                                                                                                                                                                                                                                  h_strings_num_occur h_strings_num_occur_re
                                                                                                                                                                                                                                                                                  h_array_deq_diff h_sets_deq_diff
                                                                                                                                                                                                                                                                                  h_tuple h_set_insert h_forall h_exists)
                                                                                                                                                                                                                                                                                (eo_to_smt_apply_apply_uop_generic_of_not_smt_binop
                                                                                                                                                                                                                                                                                  h_and h_or h_imp h_xor h_eq h_plus h_neg h_mult
                                                                                                                                                                                                                                                                                  h_lt h_leq h_gt h_geq h_div h_mod h_select
                                                                                                                                                                                                                                                                                  h_divisible h_div_total h_mod_total h_qdiv_total h_qdiv h_concat
                                                                                                                                                                                                                                                                                  h_bvand h_bvor h_bvnand h_bvnor h_bvxor h_bvxnor
                                                                                                                                                                                                                                                                                  h_bvcomp h_bvadd h_bvmul h_bvudiv h_bvurem h_bvsub
                                                                                                                                                                                                                                                                                  h_bvsdiv h_bvsrem h_bvsmod h_bvshl h_bvlshr
                                                                                                                                                                                                                                                                                  h_bvashr h_bvult h_bvule h_bvugt h_bvuge h_bvslt
                                                                                                                                                                                                                                                                                  h_bvsle h_bvsgt h_bvsge h_bvuaddo h_bvsaddo
                                                                                                                                                                                                                                                                                  h_bvumulo h_bvsmulo h_bvusubo h_bvssubo h_bvsdivo
                                                                                                                                                                                                                                                                                  h_bvultbv h_bvsltbv h_from_bools h_strings_deq_diff
                                                                                                                                                                                                                                                                                  h_strings_stoi_result h_str_concat h_str_contains h_str_at
                                                                                                                                                                                                                                                                                  h_str_prefixof h_str_suffixof h_str_lt h_str_leq
                                                                                                                                                                                                                                                                                  h_re_range h_re_concat h_re_inter h_re_union h_re_diff
                                                                                                                                                                                                                                                                                  h_str_in_re h_seq_nth h_set_union h_set_inter
                                                                                                                                                                                                                                                                                  h_set_minus h_set_member h_set_subset h_strings_itos_result
                                                                                                                                                                                                                                                                                  h_strings_num_occur h_strings_num_occur_re
                                                                                                                                                                                                                                                                                  h_array_deq_diff h_sets_deq_diff
                                                                                                                                                                                                                                                                                  h_tuple h_set_insert h_forall h_exists)
                                                                                                                                                                                                                                                                                hFTrans hSubstTrans
                                                                                                                                                                                                                                                                                (substitute_simul_rec_uop_eq_self op xs ss bvs
                                                                                                                                                                                                                                                                                  hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                                                                                hGlobals
                                                                                                                                                                                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                                                                                                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                        | Apply h x0 =>
                                                                                            cases h with
                                                                                            | UOp op =>
                                                                                                by_cases h_ite : op = UserOp.ite
                                                                                                · subst op
                                                                                                  exact substFalse_eval_ternary_op UserOp.ite x0 x1 a xs ss bvs
                                                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                    hFTrans hSubstTrans
                                                                                                    (substitute_simul_rec_uop_eq_self UserOp.ite xs ss bvs
                                                                                                      hXsEnv hBvsEnv hSsTrans)
                                                                                                    (fun {c x y} h => ite_args_have_smt_translation_of_has_smt_translation h)
                                                                                                    (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                                                                      show __smtx_model_eval M
                                                                                                          (SmtTerm.ite (__eo_to_smt X1) (__eo_to_smt X2) (__eo_to_smt X3)) =
                                                                                                        __smtx_model_eval N
                                                                                                          (SmtTerm.ite (__eo_to_smt Y1) (__eo_to_smt Y2) (__eo_to_smt Y3))
                                                                                                      simp only [__smtx_model_eval]
                                                                                                      rw [h1, h2, h3])
                                                                                                    hRecArg
                                                                                                · by_cases h_store : op = UserOp.store
                                                                                                  · subst op
                                                                                                    exact substFalse_eval_ternary_op UserOp.store x0 x1 a xs ss bvs
                                                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                      hFTrans hSubstTrans
                                                                                                      (substitute_simul_rec_uop_eq_self UserOp.store xs ss bvs
                                                                                                        hXsEnv hBvsEnv hSsTrans)
                                                                                                      (fun {x y z} h => store_args_have_smt_translation_of_has_smt_translation h)
                                                                                                      (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                                                                        show __smtx_model_eval M
                                                                                                            (SmtTerm.store (__eo_to_smt X1) (__eo_to_smt X2) (__eo_to_smt X3)) =
                                                                                                          __smtx_model_eval N
                                                                                                            (SmtTerm.store (__eo_to_smt Y1) (__eo_to_smt Y2) (__eo_to_smt Y3))
                                                                                                        simp only [__smtx_model_eval]
                                                                                                        rw [h1, h2, h3])
                                                                                                      hRecArg
                                                                                                  · by_cases h_bvite : op = UserOp.bvite
                                                                                                    · subst op
                                                                                                      exact substFalse_eval_ternary_op UserOp.bvite x0 x1 a xs ss bvs
                                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                        hFTrans hSubstTrans
                                                                                                        (substitute_simul_rec_uop_eq_self UserOp.bvite xs ss bvs
                                                                                                          hXsEnv hBvsEnv hSsTrans)
                                                                                                        (fun {x y z} h => bvite_args_have_smt_translation_of_has_smt_translation h)
                                                                                                        (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                                                                          show __smtx_model_eval M
                                                                                                              (SmtTerm.ite
                                                                                                                (SmtTerm.eq (__eo_to_smt X1) (SmtTerm.Binary 1 1))
                                                                                                                (__eo_to_smt X2) (__eo_to_smt X3)) =
                                                                                                            __smtx_model_eval N
                                                                                                              (SmtTerm.ite
                                                                                                                (SmtTerm.eq (__eo_to_smt Y1) (SmtTerm.Binary 1 1))
                                                                                                                (__eo_to_smt Y2) (__eo_to_smt Y3))
                                                                                                          simp only [__smtx_model_eval]
                                                                                                          rw [h1, h2, h3])
                                                                                                        hRecArg
                                                                                                    · by_cases h_str_substr : op = UserOp.str_substr
                                                                                                      · subst op
                                                                                                        exact substFalse_eval_ternary_op UserOp.str_substr x0 x1 a xs ss bvs
                                                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                          hFTrans hSubstTrans
                                                                                                          (substitute_simul_rec_uop_eq_self UserOp.str_substr xs ss bvs
                                                                                                            hXsEnv hBvsEnv hSsTrans)
                                                                                                          (fun {x y z} h =>
                                                                                                            apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
                                                                                                              (eoOp := UserOp.str_substr) (smtOp := SmtTerm.str_substr)
                                                                                                              (by rfl) str_substr_args_have_smt_translation_of_non_none h)
                                                                                                          (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                                                                            show __smtx_model_eval M
                                                                                                                (SmtTerm.str_substr (__eo_to_smt X1) (__eo_to_smt X2)
                                                                                                                  (__eo_to_smt X3)) =
                                                                                                              __smtx_model_eval N
                                                                                                                (SmtTerm.str_substr (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                                                                                  (__eo_to_smt Y3))
                                                                                                            simp only [__smtx_model_eval]
                                                                                                            rw [h1, h2, h3])
                                                                                                          hRecArg
                                                                                                      · by_cases h_str_indexof : op = UserOp.str_indexof
                                                                                                        · subst op
                                                                                                          exact substFalse_eval_ternary_op UserOp.str_indexof x0 x1 a xs ss bvs
                                                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                            hFTrans hSubstTrans
                                                                                                            (substitute_simul_rec_uop_eq_self UserOp.str_indexof xs ss bvs
                                                                                                              hXsEnv hBvsEnv hSsTrans)
                                                                                                            (fun {x y z} h =>
                                                                                                              apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
                                                                                                                (eoOp := UserOp.str_indexof) (smtOp := SmtTerm.str_indexof)
                                                                                                                (by rfl) str_indexof_args_have_smt_translation_of_non_none h)
                                                                                                            (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                                                                              show __smtx_model_eval M
                                                                                                                  (SmtTerm.str_indexof (__eo_to_smt X1) (__eo_to_smt X2)
                                                                                                                    (__eo_to_smt X3)) =
                                                                                                                __smtx_model_eval N
                                                                                                                  (SmtTerm.str_indexof (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                                                                                    (__eo_to_smt Y3))
                                                                                                              simp only [__smtx_model_eval]
                                                                                                              rw [h1, h2, h3])
                                                                                                            hRecArg
                                                                                                        · by_cases h_str_update : op = UserOp.str_update
                                                                                                          · subst op
                                                                                                            exact substFalse_eval_ternary_op UserOp.str_update x0 x1 a xs ss bvs
                                                                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                              hFTrans hSubstTrans
                                                                                                              (substitute_simul_rec_uop_eq_self UserOp.str_update xs ss bvs
                                                                                                                hXsEnv hBvsEnv hSsTrans)
                                                                                                              (fun {x y z} h =>
                                                                                                                apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
                                                                                                                  (eoOp := UserOp.str_update) (smtOp := SmtTerm.str_update)
                                                                                                                  (by rfl) str_update_args_have_smt_translation_of_non_none h)
                                                                                                              (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                                                                                show __smtx_model_eval M
                                                                                                                    (SmtTerm.str_update (__eo_to_smt X1) (__eo_to_smt X2)
                                                                                                                      (__eo_to_smt X3)) =
                                                                                                                  __smtx_model_eval N
                                                                                                                    (SmtTerm.str_update (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                                                                                      (__eo_to_smt Y3))
                                                                                                                simp only [__smtx_model_eval]
                                                                                                                rw [h1, h2, h3])
                                                                                                              hRecArg
                                                                                                          · by_cases h_str_replace : op = UserOp.str_replace
                                                                                                            · subst op
                                                                                                              exact substFalse_eval_ternary_op UserOp.str_replace x0 x1 a xs ss bvs
                                                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                hFTrans hSubstTrans
                                                                                                                (substitute_simul_rec_uop_eq_self UserOp.str_replace xs ss bvs
                                                                                                                  hXsEnv hBvsEnv hSsTrans)
                                                                                                                (fun {x y z} h =>
                                                                                                                  apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
                                                                                                                    (eoOp := UserOp.str_replace) (smtOp := SmtTerm.str_replace)
                                                                                                                    (by rfl)
                                                                                                                    (fun hNN =>
                                                                                                                      seq_triop_args_have_smt_translation_of_non_none
                                                                                                                        (typeof_str_replace_eq (__eo_to_smt x) (__eo_to_smt y)
                                                                                                                          (__eo_to_smt z)) hNN)
                                                                                                                    h)
                                                                                                                (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                                                                                  show __smtx_model_eval M
                                                                                                                      (SmtTerm.str_replace (__eo_to_smt X1) (__eo_to_smt X2)
                                                                                                                        (__eo_to_smt X3)) =
                                                                                                                    __smtx_model_eval N
                                                                                                                      (SmtTerm.str_replace (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                                                                                        (__eo_to_smt Y3))
                                                                                                                  simp only [__smtx_model_eval]
                                                                                                                  rw [h1, h2, h3])
                                                                                                                hRecArg
                                                                                                            · by_cases h_str_replace_all : op = UserOp.str_replace_all
                                                                                                              · subst op
                                                                                                                exact substFalse_eval_ternary_op UserOp.str_replace_all x0 x1 a xs ss bvs
                                                                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                  hFTrans hSubstTrans
                                                                                                                  (substitute_simul_rec_uop_eq_self UserOp.str_replace_all xs ss bvs
                                                                                                                    hXsEnv hBvsEnv hSsTrans)
                                                                                                                  (fun {x y z} h =>
                                                                                                                    apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
                                                                                                                      (eoOp := UserOp.str_replace_all) (smtOp := SmtTerm.str_replace_all)
                                                                                                                      (by rfl)
                                                                                                                      (fun hNN =>
                                                                                                                        seq_triop_args_have_smt_translation_of_non_none
                                                                                                                          (typeof_str_replace_all_eq (__eo_to_smt x) (__eo_to_smt y)
                                                                                                                            (__eo_to_smt z)) hNN)
                                                                                                                      h)
                                                                                                                  (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                                                                                    show __smtx_model_eval M
                                                                                                                        (SmtTerm.str_replace_all (__eo_to_smt X1) (__eo_to_smt X2)
                                                                                                                          (__eo_to_smt X3)) =
                                                                                                                      __smtx_model_eval N
                                                                                                                        (SmtTerm.str_replace_all (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                                                                                          (__eo_to_smt Y3))
                                                                                                                    simp only [__smtx_model_eval]
                                                                                                                    rw [h1, h2, h3])
                                                                                                                  hRecArg
                                                                                                              · by_cases h_str_replace_re : op = UserOp.str_replace_re
                                                                                                                · subst op
                                                                                                                  exact substFalse_eval_ternary_op UserOp.str_replace_re x0 x1 a xs ss bvs
                                                                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                    hFTrans hSubstTrans
                                                                                                                    (substitute_simul_rec_uop_eq_self UserOp.str_replace_re xs ss bvs
                                                                                                                      hXsEnv hBvsEnv hSsTrans)
                                                                                                                    (fun {x y z} h =>
                                                                                                                      apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
                                                                                                                        (eoOp := UserOp.str_replace_re) (smtOp := SmtTerm.str_replace_re)
                                                                                                                        (by rfl)
                                                                                                                        (fun hNN =>
                                                                                                                          str_replace_re_args_have_smt_translation_of_non_none
                                                                                                                            (typeof_str_replace_re_eq (__eo_to_smt x) (__eo_to_smt y)
                                                                                                                              (__eo_to_smt z)) hNN)
                                                                                                                        h)
                                                                                                                    (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                                                                                      show __smtx_model_eval M
                                                                                                                          (SmtTerm.str_replace_re (__eo_to_smt X1) (__eo_to_smt X2)
                                                                                                                            (__eo_to_smt X3)) =
                                                                                                                        __smtx_model_eval N
                                                                                                                          (SmtTerm.str_replace_re (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                                                                                            (__eo_to_smt Y3))
                                                                                                                      simp only [__smtx_model_eval]
                                                                                                                      rw [h1, h2, h3])
                                                                                                                    hRecArg
                                                                                                                · by_cases h_str_replace_re_all : op = UserOp.str_replace_re_all
                                                                                                                  · subst op
                                                                                                                    exact substFalse_eval_ternary_op UserOp.str_replace_re_all x0 x1 a xs ss bvs
                                                                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                      hFTrans hSubstTrans
                                                                                                                      (substitute_simul_rec_uop_eq_self UserOp.str_replace_re_all xs ss bvs
                                                                                                                        hXsEnv hBvsEnv hSsTrans)
                                                                                                                      (fun {x y z} h =>
                                                                                                                        apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
                                                                                                                          (eoOp := UserOp.str_replace_re_all) (smtOp := SmtTerm.str_replace_re_all)
                                                                                                                          (by rfl)
                                                                                                                          (fun hNN =>
                                                                                                                            str_replace_re_args_have_smt_translation_of_non_none
                                                                                                                              (typeof_str_replace_re_all_eq (__eo_to_smt x) (__eo_to_smt y)
                                                                                                                                (__eo_to_smt z)) hNN)
                                                                                                                          h)
                                                                                                                      (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                                                                                        show __smtx_model_eval M
                                                                                                                            (SmtTerm.str_replace_re_all (__eo_to_smt X1) (__eo_to_smt X2)
                                                                                                                              (__eo_to_smt X3)) =
                                                                                                                          __smtx_model_eval N
                                                                                                                            (SmtTerm.str_replace_re_all (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                                                                                              (__eo_to_smt Y3))
                                                                                                                        simp only [__smtx_model_eval]
                                                                                                                        rw [h1, h2, h3])
                                                                                                                      hRecArg
                                                                                                                  · by_cases h_str_indexof_re : op = UserOp.str_indexof_re
                                                                                                                    · subst op
                                                                                                                      exact substFalse_eval_ternary_op UserOp.str_indexof_re x0 x1 a xs ss bvs
                                                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                        hFTrans hSubstTrans
                                                                                                                        (substitute_simul_rec_uop_eq_self UserOp.str_indexof_re xs ss bvs
                                                                                                                          hXsEnv hBvsEnv hSsTrans)
                                                                                                                        (fun {x y z} h =>
                                                                                                                          apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
                                                                                                                            (eoOp := UserOp.str_indexof_re) (smtOp := SmtTerm.str_indexof_re)
                                                                                                                            (by rfl) str_indexof_re_args_have_smt_translation_of_non_none h)
                                                                                                                        (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                                                                                          show __smtx_model_eval M
                                                                                                                              (SmtTerm.str_indexof_re (__eo_to_smt X1) (__eo_to_smt X2)
                                                                                                                                (__eo_to_smt X3)) =
                                                                                                                            __smtx_model_eval N
                                                                                                                              (SmtTerm.str_indexof_re (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                                                                                                (__eo_to_smt Y3))
                                                                                                                          simp only [__smtx_model_eval]
                                                                                                                          rw [h1, h2, h3])
                                                                                                                        hRecArg
                                                                                                                    · by_cases h_strings_occur_index : op = UserOp._at_strings_occur_index
                                                                                                                      · subst op
                                                                                                                        exact substFalse_eval_ternary_op UserOp._at_strings_occur_index x0 x1 a xs ss bvs
                                                                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                          hFTrans hSubstTrans
                                                                                                                          (substitute_simul_rec_uop_eq_self UserOp._at_strings_occur_index xs ss bvs
                                                                                                                            hXsEnv hBvsEnv hSsTrans)
                                                                                                                          (fun {x y z} h =>
                                                                                                                            strings_occur_index_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                          (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                                                                                            show __smtx_model_eval M
                                                                                                                                (SmtTerm._at_strings_occur_index
                                                                                                                                  (__eo_to_smt X1) (__eo_to_smt X2) (__eo_to_smt X3)) =
                                                                                                                              __smtx_model_eval N
                                                                                                                                (SmtTerm._at_strings_occur_index
                                                                                                                                  (__eo_to_smt Y1) (__eo_to_smt Y2) (__eo_to_smt Y3))
                                                                                                                            simp only [__smtx_model_eval]
                                                                                                                            rw [h1, h2, h3])
                                                                                                                          hRecArg
                                                                                                                      · by_cases h_strings_occur_index_re : op = UserOp._at_strings_occur_index_re
                                                                                                                        · subst op
                                                                                                                          exact substFalse_eval_ternary_op UserOp._at_strings_occur_index_re x0 x1 a xs ss bvs
                                                                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                            hFTrans hSubstTrans
                                                                                                                            (substitute_simul_rec_uop_eq_self UserOp._at_strings_occur_index_re xs ss bvs
                                                                                                                              hXsEnv hBvsEnv hSsTrans)
                                                                                                                            (fun {x y z} h =>
                                                                                                                              strings_occur_index_re_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                            (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                                                                                              show __smtx_model_eval M
                                                                                                                                  (SmtTerm._at_strings_occur_index_re
                                                                                                                                    (__eo_to_smt X1) (__eo_to_smt X2) (__eo_to_smt X3)) =
                                                                                                                                __smtx_model_eval N
                                                                                                                                  (SmtTerm._at_strings_occur_index_re
                                                                                                                                    (__eo_to_smt Y1) (__eo_to_smt Y2) (__eo_to_smt Y3))
                                                                                                                              simp only [__smtx_model_eval]
                                                                                                                              rw [h1, h2, h3])
                                                                                                                            hRecArg
                                                                                                                        · exact substFalse_eval_ternary_uop_generic_apply op x0 x1 a xs ss bvs
                                                                                                                            hisr hxs hss hbvs
                                                                                                                            (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                            (eo_to_smt_apply_apply_apply_uop_generic_of_not_smt_triop
                                                                                                                              h_ite h_store h_bvite h_str_substr h_str_indexof
                                                                                                                              h_str_update h_str_replace h_str_replace_all
                                                                                                                              h_str_replace_re h_str_replace_re_all h_str_indexof_re
                                                                                                                              h_strings_occur_index
                                                                                                                              h_strings_occur_index_re)
                                                                                                                            (eo_to_smt_apply_apply_apply_uop_generic_of_not_smt_triop
                                                                                                                              h_ite h_store h_bvite h_str_substr h_str_indexof
                                                                                                                              h_str_update h_str_replace h_str_replace_all
                                                                                                                              h_str_replace_re h_str_replace_re_all h_str_indexof_re
                                                                                                                              h_strings_occur_index
                                                                                                                              h_strings_occur_index_re)
                                                                                                                            hFTrans hSubstTrans
                                                                                                                            (substitute_simul_rec_uop_eq_self op xs ss bvs
                                                                                                                              hXsEnv hBvsEnv hSsTrans)
                                                                                                                            hGlobals
                                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                            | Var name S =>
                                                                                                exact
                                                                                                  substFalse_eval_ternary_var_head_generic_apply
                                                                                                    name S x0 x1 a xs ss bvs
                                                                                                    hXsEnv hBvsEnv hSsTrans
                                                                                                    hisr hxs hss hbvs
                                                                                                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                    hFTrans hSubstTrans hGlobals
                                                                                                    hRecArg
                                                                                            | Stuck =>
                                                                                                exact False.elim (by
                                                                                                  apply hFTrans
                                                                                                  change
                                                                                                    __smtx_typeof
                                                                                                        (SmtTerm.Apply
                                                                                                          (SmtTerm.Apply
                                                                                                            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x0))
                                                                                                            (__eo_to_smt x1))
                                                                                                          (__eo_to_smt a)) =
                                                                                                      SmtType.None
                                                                                                  simp [__smtx_typeof, __smtx_typeof_apply])
                                                                                            | UOp1 op idx =>
                                                                                                exact
                                                                                                  substFalse_eval_ternary_uop1_head_generic_apply
                                                                                                    op idx x0 x1 a xs ss bvs
                                                                                                    hM hN hisr hxs hss hbvs
                                                                                                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                    hFTrans hSubstTrans
                                                                                                    (substitute_simul_rec_uop1_eq_self op idx xs ss bvs
                                                                                                      hXsEnv hBvsEnv hSsTrans)
                                                                                                    hGlobals
                                                                                                    hRecArg
                                                                                            | UOp2 op i j =>
                                                                                                exact
                                                                                                  substFalse_eval_ternary_atom_head_generic_apply
                                                                                                    (Term.UOp2 op i j) x0 x1 a xs ss bvs
                                                                                                    hXsEnv hBvsEnv hSsTrans
                                                                                                    hisr hxs hss hbvs
                                                                                                    (by intro op' hEq; cases hEq)
                                                                                                    (by intro op' idx hEq; cases hEq)
                                                                                                    (by intro f a hEq; cases hEq)
                                                                                                    (by intro s S hEq; cases hEq)
                                                                                                    (by intro hEq; cases hEq)
                                                                                                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                    hFTrans hSubstTrans
                                                                                                    hGlobals
                                                                                                    hRecArg
                                                                                            | UOp3 op i j k =>
                                                                                                exact
                                                                                                  substFalse_eval_ternary_atom_head_generic_apply
                                                                                                    (Term.UOp3 op i j k) x0 x1 a xs ss bvs
                                                                                                    hXsEnv hBvsEnv hSsTrans
                                                                                                    hisr hxs hss hbvs
                                                                                                    (by intro op' hEq; cases hEq)
                                                                                                    (by intro op' idx hEq; cases hEq)
                                                                                                    (by intro f a hEq; cases hEq)
                                                                                                    (by intro s S hEq; cases hEq)
                                                                                                    (by intro hEq; cases hEq)
                                                                                                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                    hFTrans hSubstTrans
                                                                                                    hGlobals
                                                                                                    hRecArg
                                                                                            | Apply g y =>
                                                                                                by_cases h_strings_replace_all_result :
                                                                                                    g = Term.UOp UserOp._at_strings_replace_all_result
                                                                                                · subst g
                                                                                                  exact
                                                                                                    substFalse_eval_quaternary_op
                                                                                                      UserOp._at_strings_replace_all_result
                                                                                                      y x0 x1 a xs ss bvs
                                                                                                      hisr hxs hss hbvs
                                                                                                      (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                      hFTrans hSubstTrans
                                                                                                      (substitute_simul_rec_uop_eq_self
                                                                                                        UserOp._at_strings_replace_all_result
                                                                                                        xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                      (fun {w z y x} h =>
                                                                                                        strings_replace_all_result_args_have_smt_translation_of_has_smt_translation h)
                                                                                                      (fun X1 Y1 X2 Y2 X3 Y3 X4 Y4
                                                                                                          h1 h2 h3 h4 => by
                                                                                                        show
                                                                                                          __smtx_model_eval M
                                                                                                              (SmtTerm.str_replace_all
                                                                                                                (SmtTerm.str_substr
                                                                                                                  (__eo_to_smt X1)
                                                                                                                  (SmtTerm._at_strings_occur_index
                                                                                                                    (__eo_to_smt X1)
                                                                                                                    (__eo_to_smt X2)
                                                                                                                    (__eo_to_smt X4))
                                                                                                                  (SmtTerm.str_len
                                                                                                                    (__eo_to_smt X1)))
                                                                                                                (__eo_to_smt X2)
                                                                                                                (__eo_to_smt X3)) =
                                                                                                            __smtx_model_eval N
                                                                                                              (SmtTerm.str_replace_all
                                                                                                                (SmtTerm.str_substr
                                                                                                                  (__eo_to_smt Y1)
                                                                                                                  (SmtTerm._at_strings_occur_index
                                                                                                                    (__eo_to_smt Y1)
                                                                                                                    (__eo_to_smt Y2)
                                                                                                                    (__eo_to_smt Y4))
                                                                                                                  (SmtTerm.str_len
                                                                                                                    (__eo_to_smt Y1)))
                                                                                                                (__eo_to_smt Y2)
                                                                                                                (__eo_to_smt Y3))
                                                                                                        simp [__smtx_model_eval,
                                                                                                          h1, h2, h3, h4])
                                                                                                      hRecArg
                                                                                                · by_cases h_strings_replace_re_all_result :
                                                                                                      g = Term.UOp UserOp._at_strings_replace_re_all_result
                                                                                                  · subst g
                                                                                                    exact
                                                                                                      substFalse_eval_quaternary_op
                                                                                                        UserOp._at_strings_replace_re_all_result
                                                                                                        y x0 x1 a xs ss bvs
                                                                                                        hisr hxs hss hbvs
                                                                                                        (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                        hFTrans hSubstTrans
                                                                                                        (substitute_simul_rec_uop_eq_self
                                                                                                          UserOp._at_strings_replace_re_all_result
                                                                                                          xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                        (fun {w z y x} h =>
                                                                                                          strings_replace_re_all_result_args_have_smt_translation_of_has_smt_translation h)
                                                                                                        (fun X1 Y1 X2 Y2 X3 Y3 X4 Y4
                                                                                                            h1 h2 h3 h4 => by
                                                                                                          show
                                                                                                            __smtx_model_eval M
                                                                                                                (SmtTerm.str_replace_re_all
                                                                                                                  (SmtTerm.str_substr
                                                                                                                    (__eo_to_smt X1)
                                                                                                                    (SmtTerm._at_strings_occur_index_re
                                                                                                                      (__eo_to_smt X1)
                                                                                                                      (__eo_to_smt X2)
                                                                                                                      (__eo_to_smt X4))
                                                                                                                    (SmtTerm.str_len
                                                                                                                      (__eo_to_smt X1)))
                                                                                                                  (__eo_to_smt X2)
                                                                                                                  (__eo_to_smt X3)) =
                                                                                                              __smtx_model_eval N
                                                                                                                (SmtTerm.str_replace_re_all
                                                                                                                  (SmtTerm.str_substr
                                                                                                                    (__eo_to_smt Y1)
                                                                                                                    (SmtTerm._at_strings_occur_index_re
                                                                                                                      (__eo_to_smt Y1)
                                                                                                                      (__eo_to_smt Y2)
                                                                                                                      (__eo_to_smt Y4))
                                                                                                                    (SmtTerm.str_len
                                                                                                                      (__eo_to_smt Y1)))
                                                                                                                  (__eo_to_smt Y2)
                                                                                                                  (__eo_to_smt Y3))
                                                                                                          simp [__smtx_model_eval,
                                                                                                            h1, h2, h3, h4])
                                                                                                        hRecArg
                                                                                                  · exact
                                                                                                      substFalse_eval_quaternary_apply_head_generic_apply
                                                                                                        g y x0 x1 a xs ss bvs
                                                                                                        hXsEnv hBvsEnv hSsTrans
                                                                                                        hisr hxs hss hbvs
                                                                                                        h_strings_replace_all_result
                                                                                                        h_strings_replace_re_all_result
                                                                                                        (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                        hFTrans hSubstTrans
                                                                                                        hGlobals
                                                                                                        hRecArg
                                                                                            | _ =>
                                                                                                exact
                                                                                                  substFalse_eval_ternary_atom_head_generic_apply
                                                                                                    _ x0 x1 a xs ss bvs
                                                                                                    hXsEnv hBvsEnv hSsTrans
                                                                                                    hisr hxs hss hbvs
                                                                                                    (by intro op hEq; cases hEq)
                                                                                                    (by intro op idx hEq; cases hEq)
                                                                                                    (by intro f a hEq; cases hEq)
                                                                                                    (by intro s S hEq; cases hEq)
                                                                                                    (by intro hEq; cases hEq)
                                                                                                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                    hFTrans hSubstTrans
                                                                                                    hGlobals
                                                                                                    hRecArg
                                                                                        | UOp1 op idx =>
                                                                                            -- Indexed binary updater heads are special because
                                                                                            -- `__eo_to_smt_updater` evaluates datatype selectors
                                                                                            -- syntactically, not as ordinary applications.
                                                                                            by_cases hUpdate : op = UserOp1.update
                                                                                            · subst op
                                                                                              exact substFalse_eval_binary_uop1_update idx x1 a xs ss bvs
                                                                                                hisr hxs hss hbvs
                                                                                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                hFTrans hSubstTrans
                                                                                                (substitute_simul_rec_uop1_eq_self
                                                                                                  UserOp1.update idx xs ss bvs
                                                                                                  hXsEnv hBvsEnv hSsTrans)
                                                                                                hGlobals
                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                            · by_cases hTupleUpdate : op = UserOp1.tuple_update
                                                                                              · subst op
                                                                                                exact substFalse_eval_binary_uop1_tuple_update idx x1 a xs ss bvs
                                                                                                  hM hN hisr hxs hss hbvs
                                                                                                  (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                  hFTrans hSubstTrans
                                                                                                  (substitute_simul_rec_uop1_eq_self
                                                                                                    UserOp1.tuple_update idx xs ss bvs
                                                                                                    hXsEnv hBvsEnv hSsTrans)
                                                                                                  hGlobals
                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                              · exact substFalse_eval_binary_uop1_generic_apply
                                                                                                  op idx x1 a xs ss bvs hM hN
                                                                                                  hisr hxs hss hbvs hUpdate hTupleUpdate
                                                                                                  (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                  hFTrans hSubstTrans
                                                                                                  (substitute_simul_rec_uop1_eq_self op idx xs ss bvs
                                                                                                    hXsEnv hBvsEnv hSsTrans)
                                                                                                  hGlobals
                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                  (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                        | Var name S =>
                                                                                            exact
                                                                                              substFalse_eval_binary_var_head_generic_apply
                                                                                                name S x1 a xs ss bvs
                                                                                                hXsEnv hBvsEnv hSsTrans
                                                                                                hisr hxs hss hbvs
                                                                                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                hFTrans hSubstTrans hGlobals
                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                                (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                        | Stuck =>
                                                                                            exact False.elim (by
                                                                                              apply hFTrans
                                                                                              change
                                                                                                __smtx_typeof
                                                                                                    (SmtTerm.Apply
                                                                                                      (SmtTerm.Apply SmtTerm.None (__eo_to_smt x1))
                                                                                                      (__eo_to_smt a)) =
                                                                                                  SmtType.None
                                                                                              simp [__smtx_typeof, __smtx_typeof_apply])
                                                                                        | _ =>
                                                                                            exact substFalse_eval_binary_atom_head_generic_apply
                                                                                              _ x1 a xs ss bvs
                                                                                              hXsEnv hBvsEnv hSsTrans
                                                                                              hisr hxs hss hbvs
                                                                                              (by intro op hEq; cases hEq)
                                                                                              (by intro op idx hEq; cases hEq)
                                                                                              (by intro f a hEq; cases hEq)
                                                                                              (by intro s S hEq; cases hEq)
                                                                                              (by intro hEq; cases hEq)
                                                                                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                              hFTrans hSubstTrans
                                                                                              hGlobals
                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                              (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                    | UOp1 op idx =>
                                                                                        by_cases hTupleSelect : op = UserOp1.tuple_select
                                                                                        · subst op
                                                                                          exact substFalse_eval_unary_uop1_tuple_select
                                                                                            idx a xs ss bvs hM hN
                                                                                            hisr hxs hss hbvs hFTrans hSubstTrans
                                                                                            (substitute_simul_rec_uop1_eq_self
                                                                                              UserOp1.tuple_select idx xs ss bvs
                                                                                              hXsEnv hBvsEnv hSsTrans)
                                                                                            hGlobals
                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                        · exact substFalse_eval_unary_uop1_nontuple_select
                                                                                            op idx a xs ss bvs
                                                                                            hisr hxs hss hbvs hTupleSelect hFTrans hSubstTrans
                                                                                            (substitute_simul_rec_uop1_eq_self op idx xs ss bvs
                                                                                              hXsEnv hBvsEnv hSsTrans)
                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                    | UOp2 op i j =>
                                                                                        exact substFalse_eval_unary_uop2_any op i j a xs ss bvs
                                                                                          hisr hxs hss hbvs hFTrans hSubstTrans
                                                                                          (substitute_simul_rec_atom_head_eq_self_of_apply_subst_trans
                                                                                            (Term.UOp2 op i j) a xs ss bvs
                                                                                            hXsEnv hBvsEnv hSsTrans
                                                                                            (by intro q v vs hEq; cases hEq)
                                                                                            (by intro f a hEq; cases hEq)
                                                                                            (by intro s S hEq; cases hEq)
                                                                                            (by intro hEq; cases hEq)
                                                                                            hSubstTrans)
                                                                                          hGlobals
                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                    | UOp3 op i j k =>
                                                                                        exact substFalse_eval_unary_uop3_any op i j k a xs ss bvs
                                                                                          hisr hxs hss hbvs hFTrans hSubstTrans
                                                                                          (substitute_simul_rec_atom_head_eq_self_of_apply_subst_trans
                                                                                            (Term.UOp3 op i j k) a xs ss bvs
                                                                                            hXsEnv hBvsEnv hSsTrans
                                                                                            (by intro q v vs hEq; cases hEq)
                                                                                            (by intro f a hEq; cases hEq)
                                                                                            (by intro s S hEq; cases hEq)
                                                                                            (by intro hEq; cases hEq)
                                                                                            hSubstTrans)
                                                                                          hGlobals
                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                    | UOp op =>
                                                                                        by_cases hDistinctOp : op = UserOp.distinct
                                                                                        · subst op
                                                                                          exact
                                                                                            substFalse_eval_distinct a xs ss bvs
                                                                                              hXsEnv hBvsEnv hSsTrans
                                                                                              hisr hxs hss hbvs
                                                                                              hFTrans hSubstTrans
                                                                                              (substitute_simul_rec_uop_eq_self
                                                                                                UserOp.distinct xs ss bvs
                                                                                                hXsEnv hBvsEnv hSsTrans)
                                                                                              hRecArg
                                                                                        · exact False.elim (by
                                                                                            apply hFTrans
                                                                                            exact
                                                                                              instantiate_uop_apply_typeof_none_of_not_unary_special
                                                                                                op a
                                                                                                hNot hDistinctOp hToReal hToInt hIsInt
                                                                                                hAbs hUneg hPow2 hLog2 hPurify
                                                                                                hIntIspow2 hBvnot hBvneg hBvnego
                                                                                                hStrLen hStrRev hStrToInt hStrToRe
                                                                                                hReMult hSeqUnit hSetSingletonOp
                                                                                                hStrToLower hStrToUpper hStrToCode
                                                                                                hStrFromCode hStrIsDigit hStrFromInt
                                                                                                hRePlus hReOpt hReComp hUbvToInt
                                                                                                hSbvToInt hStringsStoiNonDigit
                                                                                                hIntDivByZero hModByZero hQdivByZero
                                                                                                hBvsize hBvredand hBvredor hSetChoose
                                                                                                hSetEmpty hSetIsSingleton)
                                                                                    | Var name S =>
                                                                                        exact
                                                                                          substFalse_eval_unary_var_head_apply
                                                                                            name S a xs ss bvs
                                                                                            hXsEnv hBvsEnv hSsTrans
                                                                                            hisr hxs hss hbvs
                                                                                            hFTrans hSubstTrans hGlobals
                                                                                            (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                            (fun ht hst =>
                                                                                              hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)
                                                                                    | Stuck =>
                                                                                        exact False.elim (by
                                                                                          apply hFTrans
                                                                                          change
                                                                                            __smtx_typeof
                                                                                                (SmtTerm.Apply SmtTerm.None
                                                                                                  (__eo_to_smt a)) =
                                                                                              SmtType.None
                                                                                          simp [__smtx_typeof, __smtx_typeof_apply])
                                                                                    | _ =>
                                                                                        exact substFalse_eval_unary_atom_head_apply
                                                                                          _ a xs ss bvs
                                                                                          hXsEnv hBvsEnv hSsTrans
                                                                                          hisr hxs hss hbvs
                                                                                          (by intro op hEq; cases hEq)
                                                                                          (by intro op idx hEq; cases hEq)
                                                                                          (by intro op i j hEq; cases hEq)
                                                                                          (by intro op i j k hEq; cases hEq)
                                                                                          (by intro f x hEq; cases hEq)
                                                                                          (by intro s S hEq; cases hEq)
                                                                                          (by intro hEq; cases hEq)
                                                                                          hFTrans hSubstTrans
                                                                                          hGlobals
                                                                                          (fun ht hst => hRecArg (by simp [IsNonbinderSubterm, hBinder]) (by simp; try omega) ht hst)

/--
General substitution–evaluation induction (substitution mode, `isr = false`),
generalised over the bound-variable accumulator `bvs` and an arbitrary model
`N` realising the substitution.

Evaluating the translation of `subst false F xs ss bvs` in `M` coincides with
evaluating the translation of `F` in any model `N` related to `M` by
`SubstFalseRel M N xs ss bvs` (variables bound by `bvs` or unmapped by `xs` are
interpreted identically; a free mapped variable is assigned by `N` the value of
its substitute evaluated in `M`).

Proved by well-founded recursion on `F`. The **variable**, **atom**, and
**`Stuck`** cases are discharged here by `SubstituteSupport.substFalse_eval_var`
/ `substFalse_eval_atom` and the translation hypotheses. The **application**
case (both the non-binder heads — which reduce, per SMT constructor, to the
subterm IHs via the evaluator's compositionality — and the binder/quantifier
case, which descends under the binder via `SubstituteSupport.substFalseRel_push`
and the capture-avoidance guard) remains: it mirrors the head-shape dispatch of
`smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped_lt`
(`Cpc/Proofs/Closed/ContainsAtomicTermListFree.lean`), but with the substitution
applied on the `M` side. -/
theorem substFalse_eval_gen_lt
    (n : Nat) (F xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    {M N : SmtModel}
    (hLt : sizeOf F < n)
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hEntryTrans :
      ∀ (s : native_String) (T : Term),
        __eo_is_neg (__eo_list_find Term.__eo_List_cons xs
          (Term.Var (Term.String s) T)) = Term.Boolean false ->
        eoHasSmtTranslation
          (__assoc_nil_nth Term.__eo_List_cons ss
            (__eo_list_find Term.__eo_List_cons xs
              (Term.Var (Term.String s) T))))
    (hMappedWf :
      ∀ (s : native_String) (T : Term),
        __eo_is_neg (__eo_list_find Term.__eo_List_cons xs
          (Term.Var (Term.String s) T)) = Term.Boolean false ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hSubstTrans : RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false) F xs ss bvs))
    (hM : model_wf M)
    (hN : model_wf N)
    (hRel : SubstituteSupport.SubstFalseRel M N xs ss bvs) :
    __smtx_model_eval M
        (__eo_to_smt (__substitute_simul_rec (Term.Boolean false) F xs ss bvs)) =
      __smtx_model_eval N (__eo_to_smt F) := by
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSsTrans
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  cases n with
  | zero => omega
  | succ n =>
      let hRec :
          ∀ {G bvs' : Term} {bvsVars' : List EoVarKey} {M' N' : SmtModel},
            sizeOf G < sizeOf F ->
            EoVarEnvPerm bvs' bvsVars' ->
            RuleProofs.eo_has_smt_translation G ->
            RuleProofs.eo_has_smt_translation
              (__substitute_simul_rec (Term.Boolean false) G xs ss bvs') ->
            model_wf M' ->
            model_wf N' ->
            SubstituteSupport.SubstFalseRel M' N' xs ss bvs' ->
            __smtx_model_eval M'
                (__eo_to_smt
                  (__substitute_simul_rec (Term.Boolean false) G xs ss bvs')) =
              __smtx_model_eval N' (__eo_to_smt G) :=
        fun {G bvs' bvsVars' M' N'} hGLt hBvsEnv' hGTrans hGSubstTrans
            hM' hN' hRel' =>
          substFalse_eval_gen_lt n G xs ss bvs' (by omega)
            hXsEnv hBvsEnv' hSsTrans hEntryTrans hMappedWf
            hGTrans hGSubstTrans hM' hN' hRel'
      cases F
      case Apply f a =>
          by_cases hBinder :
              ∃ q v vs,
                f =
                  Term.Apply q
                    (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
          · -- binder / quantifier: descends under the binder via
            -- `substFalseRel_push` (its `hNoCollide` is dischargeable from
            -- `__eo_to_smt_type` injectivity; see the file header) and the
            -- capture-avoidance guard, then the body IH.
            rcases hBinder with ⟨q, v, vs, rfl⟩
            let binder := Term.Apply (Term.Apply Term.__eo_List_cons v) vs
            let bodySub :=
              __substitute_simul_rec (Term.Boolean false) a xs ss
                (__eo_list_concat Term.__eo_List_cons binder bvs)
            have hOrigTrans :
                eoHasSmtTranslation
                  (Term.Apply (Term.Apply q binder) a) := by
              simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation,
                binder] using hFTrans
            have hQ :
                q = Term.UOp UserOp.forall ∨
                  q = Term.UOp UserOp.exists :=
              is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
                hOrigTrans
            rcases eo_var_env_of_list_branch_has_smt_translation hOrigTrans with
              ⟨binderVars, hBinderEnv⟩
            have hNoFree :
                __contains_atomic_term_list_free_rec ss binder Term.__eo_List_nil =
                  Term.Boolean false := by
              have hSubstNe :
                  __substitute_simul_rec (Term.Boolean false)
                      (Term.Apply (Term.Apply q binder) a) xs ss bvs ≠
                    Term.Stuck :=
                RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
              simpa [binder] using
                substitute_simul_quant_guard_false_of_ne_stuck
                  q v vs a xs ss bvs hxs hss hbvs hSubstNe
            have hSubstEq :
                __substitute_simul_rec (Term.Boolean false)
                    (Term.Apply (Term.Apply q binder) a) xs ss bvs =
                  __eo_mk_apply (Term.Apply q binder) bodySub := by
              have hSubstNe :
                  __substitute_simul_rec (Term.Boolean false)
                      (Term.Apply (Term.Apply q binder) a) xs ss bvs ≠
                    Term.Stuck :=
                RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
              simpa [binder, bodySub] using
                substitute_simul_quant_eq_of_ne_stuck
                  q v vs a xs ss bvs hxs hss hbvs hSubstNe
            have hMkNe :
                __eo_mk_apply (Term.Apply q binder) bodySub ≠ Term.Stuck := by
              rw [← hSubstEq]
              exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
            have hMk :
                __eo_mk_apply (Term.Apply q binder) bodySub =
                  Term.Apply (Term.Apply q binder) bodySub :=
              instantiate_eo_mk_apply_eq_apply_of_ne_stuck
                (Term.Apply q binder) bodySub hMkNe
            have hSubstQuantTrans :
                eoHasSmtTranslation
                  (Term.Apply (Term.Apply q binder) bodySub) := by
              have hTmp := hSubstTrans
              rw [hSubstEq, hMk] at hTmp
              simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                using hTmp
            have hBodyTrans :
                RuleProofs.eo_has_smt_translation a := by
              simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                using
                  body_has_smt_translation_of_list_branch_has_smt_translation
                    hOrigTrans
            have hBodySubTrans :
                RuleProofs.eo_has_smt_translation bodySub := by
              simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                using
                  body_has_smt_translation_of_list_branch_has_smt_translation
                    hSubstQuantTrans
            have hFullBvsEnv :
                EoVarEnvPerm
                  (__eo_list_concat Term.__eo_List_cons binder bvs)
                  (binderVars.reverse ++ bvsVars) := by
              simpa [binder] using
                EoVarEnvPerm.concat_rev hBinderEnv hBvsEnv
            have hBinderWf :
                ∀ s T, (s, T) ∈ binderVars ->
                  __smtx_type_wf (__eo_to_smt_type T) = true :=
              quant_binder_types_wf_of_has_smt_translation
                hQ
                (by
                  simpa [binder] using hFTrans)
                hBinderEnv
            rw [hSubstEq, hMk]
            rcases hQ with hForall | hExists
            · subst q
              have hExistsEq :
                  __smtx_model_eval M
                      (__eo_to_smt_exists binder
                        (SmtTerm.not (__eo_to_smt bodySub))) =
                    __smtx_model_eval N
                      (__eo_to_smt_exists binder
                        (SmtTerm.not (__eo_to_smt a))) :=
                substFalse_eval_eo_to_smt_exists_diff_rel
                  binder xs ss bvs
                  (__eo_list_concat Term.__eo_List_cons binder bvs)
                  binder
                  hBinderEnv hXsEnv hBvsEnv hFullBvsEnv
                  (EoVarEnvPerm.of_exact hBinderEnv)
                  (fun key hMem => hMem)
                  hBinderWf hNoFree hSsTrans hEntryTrans hMappedWf
                  hM hN hRel
                  (fun {M' N'} hM' hN' hRel' => by
                    have hBodyEq :
                        __smtx_model_eval M'
                            (__eo_to_smt
                              (__substitute_simul_rec (Term.Boolean false) a xs ss
                                (__eo_list_concat Term.__eo_List_cons binder bvs))) =
                          __smtx_model_eval N' (__eo_to_smt a) :=
                      hRec
                        (G := a)
                        (bvs' := __eo_list_concat Term.__eo_List_cons binder bvs)
                        (by simp; omega)
                        hFullBvsEnv hBodyTrans hBodySubTrans
                        hM' hN' hRel'
                    simp [bodySub, __smtx_model_eval, hBodyEq])
              change
                __smtx_model_eval M
                    (SmtTerm.not
                      (__eo_to_smt_exists binder
                        (SmtTerm.not (__eo_to_smt bodySub)))) =
                  __smtx_model_eval N
                    (SmtTerm.not
                      (__eo_to_smt_exists binder
                        (SmtTerm.not (__eo_to_smt a))))
              simp [__smtx_model_eval, hExistsEq]
            · subst q
              change
                __smtx_model_eval M
                    (__eo_to_smt_exists binder (__eo_to_smt bodySub)) =
                  __smtx_model_eval N
                    (__eo_to_smt_exists binder (__eo_to_smt a))
              exact
                substFalse_eval_eo_to_smt_exists_diff_rel
                  binder xs ss bvs
                  (__eo_list_concat Term.__eo_List_cons binder bvs)
                  binder
                  hBinderEnv hXsEnv hBvsEnv hFullBvsEnv
                  (EoVarEnvPerm.of_exact hBinderEnv)
                  (fun key hMem => hMem)
                  hBinderWf hNoFree hSsTrans hEntryTrans hMappedWf
                  hM hN hRel
                  (fun {M' N'} hM' hN' hRel' =>
                    hRec
                      (G := a)
                      (bvs' := __eo_list_concat Term.__eo_List_cons binder bvs)
                      (by simp; omega)
                      hFullBvsEnv hBodyTrans hBodySubTrans
                      hM' hN' hRel')
          · -- The argument IH provider, shared by every non-binder head: the
            -- substitution keeps the operator head fixed, so each head reduces
            -- to the subterm IHs via `substFalse_eval_unary_op`.
            have hRecArg :
                ∀ {b : Term},
                  IsNonbinderSubterm b (Term.Apply f a) →
                  sizeOf b < sizeOf (Term.Apply f a) →
                  eoHasSmtTranslation b →
                  eoHasSmtTranslation
                    (__substitute_simul_rec (Term.Boolean false) b xs ss bvs) →
                  __smtx_model_eval M
                      (__eo_to_smt
                        (__substitute_simul_rec (Term.Boolean false) b xs ss bvs)) =
                    __smtx_model_eval N (__eo_to_smt b) :=
              fun {b} _hSubterm hb ht hst =>
                hRec hb hBvsEnv ht hst hM hN hRel
            exact substitute_simul_eval_nonbinder f a xs ss bvs
              hXsEnv hBvsEnv hSsTrans hBinder hFTrans hSubstTrans
              hM hN hRel.globals hRecArg
      case Var name S =>
          by_cases hString : ∃ s, name = Term.String s
          · rcases hString with ⟨s, rfl⟩
            exact SubstituteSupport.substFalse_eval_var M N s S xs ss bvs
              hXsEnv hBvsEnv hss hRel
          · exact false_of_non_string_var_has_smt_translation
              (fun s hEq => hString ⟨s, hEq⟩) hFTrans
      case Stuck =>
          exact False.elim
            (RuleProofs.term_ne_stuck_of_has_smt_translation Term.Stuck hFTrans rfl)
      all_goals
          exact SubstituteSupport.substFalse_eval_atom M N _ xs ss bvs
            hxs hss hbvs
            (by intro f a h; cases h)
            (by intro s S h; cases h)
            (by intro h; cases h)
            hFTrans hSubstTrans hRel.globals

/--
**Substitution–evaluation lemma (crux).**

Evaluating the SMT translation of the simultaneously-substituted body in `M`
coincides with evaluating the translation of `F` in the extended model
`pushSubstModel M xs ts`.

This is stated for the top-level `bvs = nil`; it is proved by structural
induction on `F` after generalising over an accumulator `bvs` of locally bound
variables (the third recursion argument of `__substitute_simul_rec`). The
generalised invariant is: variables occurring in `bvs` are *not* substituted
(they are bound by an inner quantifier) and remain interpreted by the ambient
model, while variables in `xs \ bvs` are replaced.

Induction cases (following `__substitute_simul_rec`, `Cpc/Logos.lean:2298`):

* **Application `Apply f a`** — translation is structural (`SmtTerm` mirrors the
  EO head), so `eval` commutes with the recursive substitutions on `f` and `a`.
* **Quantifier `Apply (Apply q (cons v vs)) a`** — the capture-avoidance
  side-condition `__contains_atomic_term_list_free_rec ts (cons v vs) = false`
  guarantees the substituted terms have no free occurrence of the bound `v`, so
  pushing `v` and substituting commute (the `bvs` accumulator gains `v`). Uses
  the `native_model_push` commutation lemmas in `Cpc/Proofs/Closed/Support.lean`.
* **Variable `Var s S`** — if `s ∈ bvs` it is kept (bound); otherwise it is
  looked up in `xs` and either replaced by the matching `ts` entry (whose value
  is exactly what `pushSubstModel` assigns) or kept if absent.
* **Closed atom (default)** — `__is_closed_rec` holds, the term is unchanged and
  ground, so its evaluation is model-independent.

The general induction (over an arbitrary `bvs` accumulator and a model `N`
related by `SubstFalseRel`) is factored into `substFalse_eval_gen_lt`, whose
variable / atom / `Stuck` cases are proved; only its application case remains.
Reducing this top-level `bvs = nil` statement to that lemma additionally needs
the base relation `SubstFalseRel M (pushSubstModel M xs ts) xs ts nil` (the
mapped field of which relates `pushSubstModel`'s push order to `assoc_nil_nth`
by `find`-index, and needs binder-key distinctness — the same collision subtlety
as `substFalseRel_push`'s `hNoCollide`).

Side hypotheses still to be threaded through from the rule context:
* `F` has an SMT translation and is `Bool`-typed under the binders;
* `ts` is a translatable value list matching `xs` (`__is_instantiation`).
-/
theorem substitute_simul_eval
    (M : SmtModel) (hM : model_wf M)
    (F xs ts : Term)
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hActuals : SubstActualsHaveSmtTypes xs ts)
    (hSubstTrans : RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil)) :
    __smtx_model_eval M
        (__eo_to_smt (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil)) =
      __smtx_model_eval (pushSubstModel M xs ts) (__eo_to_smt F) := by
  rcases SubstActualsHaveSmtTypes.env hActuals with ⟨xsVars, hXsEnv⟩
  exact
    substFalse_eval_gen_lt (sizeOf F + 1) F xs ts Term.__eo_List_nil
      (M := M) (N := pushSubstModel M xs ts)
      (by omega)
      (EoVarEnvPerm.of_exact hXsEnv)
      (EoVarEnvPerm.of_exact EoVarEnv.nil)
      hTs
      (SubstActualsHaveSmtTypes.entry_has_smt_translation hActuals)
      (SubstActualsHaveSmtTypes.wf_of_find_neg_false hActuals)
      hFTrans hSubstTrans hM
      (pushSubstModel_total_typed_of_smt_typed_actuals M hM hActuals)
      (substFalseRel_pushSubstModel M hM hActuals)
end InstantiateRule
