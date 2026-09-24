module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.CongSupport
import all Cpc.Proofs.RuleSupport.CongSupport
public import Cpc.Proofs.RuleSupport.InstantiateSupport
import all Cpc.Proofs.RuleSupport.InstantiateSupport

public section

/-!
# Rel-coincidence: evaluation respects extensional model equivalence

Two total-typed models that agree on globals and whose variable assignments
are pointwise `smt_value_rel`-related (equal, except possibly extensionally
equal `RegLan` values) evaluate every non-`None`-typed term to
`smt_value_rel`-related values.

This is the congruence ("cong") core needed by `quant-var-elim-eq`: the
quantifier semantics ranges over canonical values, and two canonical `RegLan`
values can be extensionally equal without being syntactically equal, so the
substitution model and the quantifier-witness model are only rel-related.

The development mirrors the eq-coincidence walk
(`smt_model_eval_eq_of_closedIn_lt` in `Cpc.Proofs.Closed.Support`), with two
new ingredients:

* a `RegLan`-blindness argument discharging every operator that simply
  rejects `RegLan` inputs (rel-related values are equal unless both are
  `RegLan`, and such operators cannot observe the difference), and
* a "clean type" invariant (`typeof` produces no `None`/`RegLan` components
  in `Map`/`Set`/`Seq`/function positions), which rules out the degenerate
  key types that would let map/set lookups observe extensional differences.
-/

open Eo
open SmtEval
open Smtm
open CongSupport

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RelCoincidence

/-! ## Basic `smt_value_rel` helpers -/

private theorem rel_of_eq {a b : SmtValue} (h : a = b) :
    RuleProofs.smt_value_rel a b := by
  rw [h]
  exact RuleProofs.smt_value_rel_refl b

/-- Rel-related values with a common non-`RegLan` type are equal. -/
private theorem eval_eq_of_rel_of_ty_ne_reglan
    {M N : SmtModel} (hM : model_wf M) (hN : model_wf N)
    {x : SmtTerm}
    (hRel : RuleProofs.smt_value_rel (__smtx_model_eval M x)
      (__smtx_model_eval N x))
    (hTy : term_has_non_none_type x)
    (hNe : __smtx_typeof x ≠ SmtType.RegLan) :
    __smtx_model_eval M x = __smtx_model_eval N x :=
  RuleProofs.smt_value_rel_eq_of_type_ne_reglan
    (smt_model_eval_preserves_type_of_non_none M hM x hTy)
    (smt_model_eval_preserves_type_of_non_none N hN x hTy) hNe hRel

/-! ## `RegLan`-blind operators

Rel-related values are equal unless both are `RegLan` values.  An operator
that cannot distinguish two `RegLan` inputs therefore maps rel-related
argument tuples to equal results.
-/

/-! ## Clean types

`cleanType T` records that the immediate element/domain components of
container types inside `T` are neither `None` nor `RegLan` (and recursively
clean), and that function/constructor-application result components are
clean.  This is what the walk needs at `select`/`store`/`set_member` (to rule
out `RegLan`-keyed lookups) and at `Apply` (to type the result).  Every
non-`None` `__smtx_typeof` is clean, because every type-introducing operator
guards well-formedness.
-/

private def cleanType : SmtType -> Prop
  | SmtType.Map A B =>
      (A ≠ SmtType.None ∧ A ≠ SmtType.RegLan ∧ cleanType A) ∧
      (B ≠ SmtType.None ∧ B ≠ SmtType.RegLan ∧ cleanType B)
  | SmtType.Set A => A ≠ SmtType.None ∧ A ≠ SmtType.RegLan ∧ cleanType A
  | SmtType.Seq A => A ≠ SmtType.None ∧ A ≠ SmtType.RegLan ∧ cleanType A
  | SmtType.FunType _ B => B = SmtType.None ∨ cleanType B
  | SmtType.DtcAppType _ B => B = SmtType.None ∨ cleanType B
  | _ => True

/-- `__smtx_type_wf_rec U = true` forces the container components of `U`
to be clean. -/
private theorem cleanType_of_wf_rec :
    ∀ U : SmtType, __smtx_type_wf_rec U = true -> cleanType U
  | SmtType.None, h => by
      simp [__smtx_type_wf_rec] at h
  | SmtType.Bool, _ => True.intro
  | SmtType.Int, _ => True.intro
  | SmtType.Real, _ => True.intro
  | SmtType.RegLan, h => by
      simp [__smtx_type_wf_rec] at h
  | SmtType.BitVec _, _ => True.intro
  | SmtType.Char, _ => True.intro
  | SmtType.Datatype _ _, _ => True.intro
  | SmtType.TypeRef _, h => by
      simp [__smtx_type_wf_rec] at h
  | SmtType.USort _, _ => True.intro
  | SmtType.FunType _ _, h => by
      simp [__smtx_type_wf_rec] at h
  | SmtType.DtcAppType _ _, h => by
      simp [__smtx_type_wf_rec] at h
  | SmtType.Seq A, h => by
      have hA : __smtx_type_wf_rec A = true := by
        simp [__smtx_type_wf_rec, SmtEval.native_and] at h
        exact h.2
      refine ⟨?_, ?_, cleanType_of_wf_rec A hA⟩
      · intro hEq
        subst hEq
        simp [__smtx_type_wf_rec] at hA
      · intro hEq
        subst hEq
        simp [__smtx_type_wf_rec] at hA
  | SmtType.Set A, h => by
      have hA : __smtx_type_wf_rec A = true := by
        simp [__smtx_type_wf_rec, SmtEval.native_and] at h
        exact h.2
      refine ⟨?_, ?_, cleanType_of_wf_rec A hA⟩
      · intro hEq
        subst hEq
        simp [__smtx_type_wf_rec] at hA
      · intro hEq
        subst hEq
        simp [__smtx_type_wf_rec] at hA
  | SmtType.Map A B, h => by
      have hAB : __smtx_type_wf_rec A = true ∧
          __smtx_type_wf_rec B = true := by
        simp [__smtx_type_wf_rec, SmtEval.native_and] at h
        exact ⟨h.1.2, h.2.2⟩
      refine ⟨⟨?_, ?_, cleanType_of_wf_rec A hAB.1⟩,
        ⟨?_, ?_, cleanType_of_wf_rec B hAB.2⟩⟩
      · intro hEq
        subst hEq
        have := hAB.1
        simp [__smtx_type_wf_rec] at this
      · intro hEq
        subst hEq
        have := hAB.1
        simp [__smtx_type_wf_rec] at this
      · intro hEq
        subst hEq
        have := hAB.2
        simp [__smtx_type_wf_rec] at this
      · intro hEq
        subst hEq
        have := hAB.2
        simp [__smtx_type_wf_rec] at this

private theorem cleanType_of_wf_component {T : SmtType}
    (h : __smtx_type_wf_component T = true) : cleanType T := by
  have hRec : __smtx_type_wf_rec T = true := by
    unfold __smtx_type_wf_component at h
    simp [SmtEval.native_and] at h
    exact h.2
  exact cleanType_of_wf_rec T hRec

private theorem ne_none_of_wf_component {T : SmtType}
    (h : __smtx_type_wf_component T = true) : T ≠ SmtType.None := by
  intro hEq
  subst hEq
  unfold __smtx_type_wf_component at h
  simp [SmtEval.native_and, __smtx_type_wf_rec] at h

/-- Well-formed types are clean. -/
private theorem cleanType_of_wf :
    ∀ {T : SmtType}, __smtx_type_wf T = true -> cleanType T
  | SmtType.RegLan, _ => True.intro
  | SmtType.FunType A B, h => by
      have hAB : __smtx_type_wf_component A = true ∧
          __smtx_type_wf B = true := by
        simpa [__smtx_type_wf, SmtEval.native_and] using h
      exact Or.inr (cleanType_of_wf hAB.2)
  | SmtType.Map A B, h => cleanType_of_wf_component h
  | SmtType.Set A, h => cleanType_of_wf_component h
  | SmtType.Seq A, h => cleanType_of_wf_component h
  | SmtType.DtcAppType A B, h => by
      -- not well-formed: `wf_rec _ (DtcAppType _ _) = false`
      exfalso
      unfold __smtx_type_wf __smtx_type_wf_component at h
      simp [SmtEval.native_and, __smtx_type_wf_rec] at h
  | SmtType.None, _ => True.intro
  | SmtType.Bool, _ => True.intro
  | SmtType.Int, _ => True.intro
  | SmtType.Real, _ => True.intro
  | SmtType.BitVec _, _ => True.intro
  | SmtType.Char, _ => True.intro
  | SmtType.Datatype _ _, _ => True.intro
  | SmtType.TypeRef _, _ => True.intro
  | SmtType.USort _, _ => True.intro

/-! ### Clean-or-`None` composition helpers -/

private def cleanOrNone (T : SmtType) : Prop :=
  T = SmtType.None ∨ cleanType T

private theorem cleanOrNone_guard' {g : native_Bool} {C : SmtType}
    (hC : cleanOrNone C) :
    cleanOrNone (native_ite g C SmtType.None) := by
  cases g
  · exact Or.inl rfl
  · exact hC

private theorem cleanOrNone_typeof_guard {T U : SmtType}
    (hU : cleanOrNone U) : cleanOrNone (__smtx_typeof_guard T U) := by
  unfold __smtx_typeof_guard
  cases hg : native_Teq T SmtType.None
  · simpa [native_ite] using hU
  · simp [native_ite]
    exact Or.inl rfl

private theorem cleanOrNone_typeof_guard_wf {T U : SmtType}
    (hU : __smtx_type_wf T = true -> cleanOrNone U) :
    cleanOrNone (__smtx_typeof_guard_wf T U) := by
  unfold __smtx_typeof_guard_wf
  cases hw : __smtx_type_wf T
  · exact Or.inl (by simp [native_ite])
  · simpa [native_ite] using hU hw

private theorem cleanOrNone_typeof_guard_wf_self (T : SmtType) :
    cleanOrNone (__smtx_typeof_guard_wf T T) :=
  cleanOrNone_typeof_guard_wf (fun hw => Or.inr (cleanType_of_wf hw))

/-! ## Typing extraction helpers -/

private theorem teq_eq {A B : SmtType} (h : native_Teq A B = true) : A = B := by
  simpa [native_Teq] using h

private theorem ite_cond_true_of_ne_none {g : native_Bool} {C : SmtType}
    (h : native_ite g C SmtType.None ≠ SmtType.None) : g = true := by
  cases g
  · exact absurd rfl h
  · rfl

private theorem ite_branch_of_ne_none {g : native_Bool} {C : SmtType}
    (h : native_ite g C SmtType.None ≠ SmtType.None) :
    native_ite g C SmtType.None = C := by
  rw [ite_cond_true_of_ne_none h]
  simp [native_ite]

private theorem guard1_arg {A c ret : SmtType}
    (h : native_ite (native_Teq A c) ret SmtType.None ≠ SmtType.None) :
    A = c :=
  teq_eq (ite_cond_true_of_ne_none h)

private theorem guard2_args {A B c1 c2 ret : SmtType}
    (h : native_ite (native_Teq A c1)
        (native_ite (native_Teq B c2) ret SmtType.None) SmtType.None ≠
      SmtType.None) :
    A = c1 ∧ B = c2 := by
  have h1 := ite_cond_true_of_ne_none h
  have h2 : native_ite (native_Teq B c2) ret SmtType.None ≠ SmtType.None := by
    rw [h1] at h
    simpa [native_ite] using h
  exact ⟨teq_eq h1, teq_eq (ite_cond_true_of_ne_none h2)⟩

private theorem guard3_args {A B C c1 c2 c3 ret : SmtType}
    (h : native_ite (native_Teq A c1)
        (native_ite (native_Teq B c2)
          (native_ite (native_Teq C c3) ret SmtType.None) SmtType.None)
        SmtType.None ≠ SmtType.None) :
    A = c1 ∧ B = c2 ∧ C = c3 := by
  have h1 := ite_cond_true_of_ne_none h
  have h2 : native_ite (native_Teq B c2)
      (native_ite (native_Teq C c3) ret SmtType.None) SmtType.None ≠
      SmtType.None := by
    rw [h1] at h
    simpa [native_ite] using h
  exact ⟨teq_eq h1, guard2_args h2⟩

private theorem to_real_arg {A : SmtType}
    (h : native_ite (native_Teq A SmtType.Int) SmtType.Real SmtType.None ≠
      SmtType.None) :
    A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  by_cases h1 : A = SmtType.Int
  · subst h1
    exact ⟨by simp, by simp⟩
  · exfalso
    have hg1 : native_Teq A SmtType.Int = false := by
      simp [native_Teq, h1]
    rw [hg1] at h
    simp [native_ite] at h

private theorem arith2_args {A B : SmtType}
    (h : __smtx_typeof_arith_overload_op_2 A B ≠ SmtType.None) :
    (A ≠ SmtType.None ∧ A ≠ SmtType.RegLan) ∧
      (B ≠ SmtType.None ∧ B ≠ SmtType.RegLan) := by
  unfold __smtx_typeof_arith_overload_op_2 at h
  split at h
  · exact ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩
  · exact ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩
  · exact absurd rfl h

private theorem arith2_ret_args {A B T : SmtType}
    (h : __smtx_typeof_arith_overload_op_2_ret A B T ≠ SmtType.None) :
    (A ≠ SmtType.None ∧ A ≠ SmtType.RegLan) ∧
      (B ≠ SmtType.None ∧ B ≠ SmtType.RegLan) := by
  unfold __smtx_typeof_arith_overload_op_2_ret at h
  split at h
  · exact ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩
  · exact ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩
  · exact absurd rfl h

private theorem arith1_arg {A : SmtType}
    (h : __smtx_typeof_arith_overload_op_1 A ≠ SmtType.None) :
    A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  unfold __smtx_typeof_arith_overload_op_1 at h
  split at h
  · exact ⟨by simp, by simp⟩
  · exact ⟨by simp, by simp⟩
  · exact absurd rfl h

private theorem bv1_arg {A : SmtType}
    (h : __smtx_typeof_bv_op_1 A ≠ SmtType.None) :
    A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  unfold __smtx_typeof_bv_op_1 at h
  split at h
  · exact ⟨by simp, by simp⟩
  · exact absurd rfl h

private theorem bv1_ret_arg {A T : SmtType}
    (h : __smtx_typeof_bv_op_1_ret A T ≠ SmtType.None) :
    A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  unfold __smtx_typeof_bv_op_1_ret at h
  split at h
  · exact ⟨by simp, by simp⟩
  · exact absurd rfl h

private theorem bv2_args {A B : SmtType}
    (h : __smtx_typeof_bv_op_2 A B ≠ SmtType.None) :
    (A ≠ SmtType.None ∧ A ≠ SmtType.RegLan) ∧
      (B ≠ SmtType.None ∧ B ≠ SmtType.RegLan) := by
  unfold __smtx_typeof_bv_op_2 at h
  split at h
  · exact ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩
  · exact absurd rfl h

private theorem bv2_ret_args {A B T : SmtType}
    (h : __smtx_typeof_bv_op_2_ret A B T ≠ SmtType.None) :
    (A ≠ SmtType.None ∧ A ≠ SmtType.RegLan) ∧
      (B ≠ SmtType.None ∧ B ≠ SmtType.RegLan) := by
  unfold __smtx_typeof_bv_op_2_ret at h
  split at h
  · exact ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩
  · exact absurd rfl h

private theorem seq1_arg {A : SmtType}
    (h : __smtx_typeof_seq_op_1 A ≠ SmtType.None) :
    A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  unfold __smtx_typeof_seq_op_1 at h
  split at h
  · exact ⟨by simp, by simp⟩
  · exact absurd rfl h

private theorem seq1_ret_arg {A T : SmtType}
    (h : __smtx_typeof_seq_op_1_ret A T ≠ SmtType.None) :
    A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  unfold __smtx_typeof_seq_op_1_ret at h
  split at h
  · exact ⟨by simp, by simp⟩
  · exact absurd rfl h

private theorem seq2_args {A B : SmtType}
    (h : __smtx_typeof_seq_op_2 A B ≠ SmtType.None) :
    (A ≠ SmtType.None ∧ A ≠ SmtType.RegLan) ∧
      (B ≠ SmtType.None ∧ B ≠ SmtType.RegLan) := by
  unfold __smtx_typeof_seq_op_2 at h
  split at h
  · exact ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩
  · exact absurd rfl h

private theorem seq2_ret_args {A B T : SmtType}
    (h : __smtx_typeof_seq_op_2_ret A B T ≠ SmtType.None) :
    (A ≠ SmtType.None ∧ A ≠ SmtType.RegLan) ∧
      (B ≠ SmtType.None ∧ B ≠ SmtType.RegLan) := by
  unfold __smtx_typeof_seq_op_2_ret at h
  split at h
  · exact ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩
  · exact absurd rfl h

private theorem seq3_args {A B C : SmtType}
    (h : __smtx_typeof_seq_op_3 A B C ≠ SmtType.None) :
    (A ≠ SmtType.None ∧ A ≠ SmtType.RegLan) ∧
      (B ≠ SmtType.None ∧ B ≠ SmtType.RegLan) ∧
      (C ≠ SmtType.None ∧ C ≠ SmtType.RegLan) := by
  unfold __smtx_typeof_seq_op_3 at h
  split at h
  · exact ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩
  · exact absurd rfl h

private theorem str_substr_args {A B C : SmtType}
    (h : __smtx_typeof_str_substr A B C ≠ SmtType.None) :
    (A ≠ SmtType.None ∧ A ≠ SmtType.RegLan) ∧
      B = SmtType.Int ∧ C = SmtType.Int := by
  unfold __smtx_typeof_str_substr at h
  split at h
  · exact ⟨⟨by simp, by simp⟩, rfl, rfl⟩
  · exact absurd rfl h

private theorem str_indexof_args {A B C : SmtType}
    (h : __smtx_typeof_str_indexof A B C ≠ SmtType.None) :
    (A ≠ SmtType.None ∧ A ≠ SmtType.RegLan) ∧
      (B ≠ SmtType.None ∧ B ≠ SmtType.RegLan) ∧ C = SmtType.Int := by
  unfold __smtx_typeof_str_indexof at h
  split at h
  · exact ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩, rfl⟩
  · exact absurd rfl h

private theorem str_at_args {A B : SmtType}
    (h : __smtx_typeof_str_at A B ≠ SmtType.None) :
    (A ≠ SmtType.None ∧ A ≠ SmtType.RegLan) ∧ B = SmtType.Int := by
  unfold __smtx_typeof_str_at at h
  split at h
  · exact ⟨⟨by simp, by simp⟩, rfl⟩
  · exact absurd rfl h

private theorem str_update_args {A B C : SmtType}
    (h : __smtx_typeof_str_update A B C ≠ SmtType.None) :
    (A ≠ SmtType.None ∧ A ≠ SmtType.RegLan) ∧
      B = SmtType.Int ∧ (C ≠ SmtType.None ∧ C ≠ SmtType.RegLan) := by
  unfold __smtx_typeof_str_update at h
  split at h
  · exact ⟨⟨by simp, by simp⟩, rfl, ⟨by simp, by simp⟩⟩
  · exact absurd rfl h

private theorem sets2_args {A B : SmtType}
    (h : __smtx_typeof_sets_op_2 A B ≠ SmtType.None) :
    (A ≠ SmtType.None ∧ A ≠ SmtType.RegLan) ∧
      (B ≠ SmtType.None ∧ B ≠ SmtType.RegLan) := by
  unfold __smtx_typeof_sets_op_2 at h
  split at h
  · exact ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩
  · exact absurd rfl h

private theorem sets2_ret_args {A B T : SmtType}
    (h : __smtx_typeof_sets_op_2_ret A B T ≠ SmtType.None) :
    (A ≠ SmtType.None ∧ A ≠ SmtType.RegLan) ∧
      (B ≠ SmtType.None ∧ B ≠ SmtType.RegLan) := by
  unfold __smtx_typeof_sets_op_2_ret at h
  split at h
  · exact ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩
  · exact absurd rfl h

private theorem map_diff_args {A B : SmtType}
    (h : __smtx_typeof_map_diff A B ≠ SmtType.None) :
    (A ≠ SmtType.None ∧ A ≠ SmtType.RegLan) ∧
      (B ≠ SmtType.None ∧ B ≠ SmtType.RegLan) := by
  unfold __smtx_typeof_map_diff at h
  split at h
  · exact ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩
  · exact ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩
  · exact absurd rfl h

private theorem seq_diff_args {A B : SmtType}
    (h : __smtx_typeof_seq_diff A B ≠ SmtType.None) :
    (A ≠ SmtType.None ∧ A ≠ SmtType.RegLan) ∧
      (B ≠ SmtType.None ∧ B ≠ SmtType.RegLan) := by
  unfold __smtx_typeof_seq_diff at h
  split at h
  · exact ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩
  · exact absurd rfl h

private theorem concat_args {A B : SmtType}
    (h : __smtx_typeof_concat A B ≠ SmtType.None) :
    (A ≠ SmtType.None ∧ A ≠ SmtType.RegLan) ∧
      (B ≠ SmtType.None ∧ B ≠ SmtType.RegLan) := by
  unfold __smtx_typeof_concat at h
  split at h
  · exact ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩
  · exact absurd rfl h

private theorem select_types {A B : SmtType}
    (h : __smtx_typeof_select A B ≠ SmtType.None) :
    ∃ K V, A = SmtType.Map K V ∧ B = K := by
  unfold __smtx_typeof_select at h
  split at h
  · rename_i K V
    exact ⟨K, V, rfl, (teq_eq (ite_cond_true_of_ne_none h)).symm⟩
  · exact absurd rfl h

private theorem store_types {A B C : SmtType}
    (h : __smtx_typeof_store A B C ≠ SmtType.None) :
    ∃ K V, A = SmtType.Map K V ∧ B = K ∧ C = V := by
  unfold __smtx_typeof_store at h
  split at h
  · rename_i K V
    obtain ⟨h1, h2⟩ := guard2_args h
    exact ⟨K, V, rfl, h1.symm, h2.symm⟩
  · exact absurd rfl h

private theorem set_member_types {A B : SmtType}
    (h : __smtx_typeof_set_member A B ≠ SmtType.None) :
    ∃ E, B = SmtType.Set E ∧ A = E := by
  unfold __smtx_typeof_set_member at h
  split at h
  · rename_i E
    exact ⟨E, rfl, teq_eq (ite_cond_true_of_ne_none h)⟩
  · exact absurd rfl h

private theorem seq_nth_types {A B : SmtType}
    (h : __smtx_typeof_seq_nth A B ≠ SmtType.None) :
    (A ≠ SmtType.None ∧ A ≠ SmtType.RegLan) ∧ B = SmtType.Int := by
  unfold __smtx_typeof_seq_nth at h
  split at h
  · exact ⟨⟨by simp, by simp⟩, rfl⟩
  · exact absurd rfl h

private theorem ite_types {A B C : SmtType}
    (h : __smtx_typeof_ite A B C ≠ SmtType.None) :
    A = SmtType.Bool ∧ C = B ∧ B ≠ SmtType.None := by
  unfold __smtx_typeof_ite at h
  split at h
  · have hBC : B = C := teq_eq (ite_cond_true_of_ne_none h)
    refine ⟨rfl, hBC.symm, ?_⟩
    intro hEq
    rw [ite_branch_of_ne_none h] at h
    exact h hEq
  · exact absurd rfl h

private theorem guard_ne_none_parts {T U : SmtType}
    (h : __smtx_typeof_guard T U ≠ SmtType.None) :
    T ≠ SmtType.None ∧ U ≠ SmtType.None := by
  unfold __smtx_typeof_guard at h
  cases hg : native_Teq T SmtType.None
  · rw [hg] at h
    refine ⟨?_, by simpa [native_ite] using h⟩
    intro hEq
    rw [hEq] at hg
    simp [native_Teq] at hg
  · rw [hg] at h
    simp [native_ite] at h

private theorem guard_inner_ne_none {T U : SmtType}
    (h : __smtx_typeof_guard T U ≠ SmtType.None) :
    U ≠ SmtType.None := (guard_ne_none_parts h).2

private theorem eq_types {A B : SmtType}
    (h : __smtx_typeof_eq A B ≠ SmtType.None) :
    A ≠ SmtType.None ∧ B = A := by
  unfold __smtx_typeof_eq at h
  obtain ⟨hA, hIte⟩ := guard_ne_none_parts h
  exact ⟨hA, (teq_eq (ite_cond_true_of_ne_none hIte)).symm⟩

private theorem apply_arg_types {F V : SmtType}
    (h : __smtx_typeof_apply F V ≠ SmtType.None) :
    F ≠ SmtType.None ∧ V ≠ SmtType.None := by
  unfold __smtx_typeof_apply at h
  split at h
  · rename_i T U
    obtain ⟨hT, hIte⟩ := guard_ne_none_parts h
    have hTV : T = V := teq_eq (ite_cond_true_of_ne_none hIte)
    exact ⟨by simp, by rw [← hTV]; exact hT⟩
  · rename_i T U
    obtain ⟨hT, hIte⟩ := guard_ne_none_parts h
    have hTV : T = V := teq_eq (ite_cond_true_of_ne_none hIte)
    exact ⟨by simp, by rw [← hTV]; exact hT⟩
  · exact absurd rfl h

private theorem quant_types {A T : SmtType}
    (h : native_ite (native_Teq A SmtType.Bool)
        (__smtx_typeof_guard_wf T SmtType.Bool) SmtType.None ≠
      SmtType.None) :
    A = SmtType.Bool ∧ __smtx_type_wf T = true := by
  have h1 := ite_cond_true_of_ne_none h
  have h2 : __smtx_typeof_guard_wf T SmtType.Bool ≠ SmtType.None := by
    rw [h1] at h
    simpa [native_ite] using h
  unfold __smtx_typeof_guard_wf at h2
  exact ⟨teq_eq h1, ite_cond_true_of_ne_none h2⟩

private theorem choice_types {A T : SmtType}
    (h : native_ite (native_Teq A SmtType.Bool)
        (__smtx_typeof_guard_wf T T) SmtType.None ≠
      SmtType.None) :
    A = SmtType.Bool ∧ __smtx_type_wf T = true := by
  have h1 := ite_cond_true_of_ne_none h
  have h2 : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    rw [h1] at h
    simpa [native_ite] using h
  unfold __smtx_typeof_guard_wf at h2
  exact ⟨teq_eq h1, ite_cond_true_of_ne_none h2⟩

private theorem bind_types {A B : SmtType} {T : SmtType}
    (h : native_ite (native_Teq A T)
        (__smtx_typeof_guard_wf T B) SmtType.None ≠ SmtType.None) :
    A = T ∧ __smtx_type_wf T = true ∧ B ≠ SmtType.None := by
  have h1 := ite_cond_true_of_ne_none h
  have h2 : __smtx_typeof_guard_wf T B ≠ SmtType.None := by
    rw [h1] at h
    simpa [native_ite] using h
  unfold __smtx_typeof_guard_wf at h2
  have hw := ite_cond_true_of_ne_none h2
  refine ⟨teq_eq h1, hw, ?_⟩
  intro hEq
  rw [hw, hEq] at h2
  simp [native_ite] at h2

private theorem guard_wf_self_types {T : SmtType}
    (h : __smtx_typeof_guard_wf T T ≠ SmtType.None) :
    __smtx_type_wf T = true := by
  unfold __smtx_typeof_guard_wf at h
  exact ite_cond_true_of_ne_none h

/-! ## Model relations -/

/-- Pointwise semantic relatedness of two models' variable assignments. -/
def ModelVarRel (M N : SmtModel) : Prop :=
  ∀ s T, RuleProofs.smt_value_rel (native_model_var_lookup M s T)
    (native_model_var_lookup N s T)

private theorem modelVarRel_push_rel {M N : SmtModel} (h : ModelVarRel M N)
    (s : native_String) (T : SmtType) {v w : SmtValue}
    (hvw : RuleProofs.smt_value_rel v w) :
    ModelVarRel (native_model_push M s T v) (native_model_push N s T w) := by
  intro s' T'
  simp only [native_model_var_lookup, native_model_push]
  split
  · exact hvw
  · exact h s' T'

private theorem modelVarRel_push_same {M N : SmtModel} (h : ModelVarRel M N)
    (s : native_String) (T : SmtType) (v : SmtValue) :
    ModelVarRel (native_model_push M s T v) (native_model_push N s T v) :=
  modelVarRel_push_rel h s T (RuleProofs.smt_value_rel_refl v)

private theorem globals_push_push {M N : SmtModel}
    (h : model_agrees_on_globals M N)
    (s : native_String) (T : SmtType) (v w : SmtValue) :
    model_agrees_on_globals (native_model_push M s T v)
      (native_model_push N s T w) := by
  constructor
  · intro s' T'
    exact ((model_agrees_on_globals_push M s T v).1 s' T').symm.trans
      ((h.1 s' T').trans ((model_agrees_on_globals_push N s T w).1 s' T'))
  · intro fid A B
    exact ((model_agrees_on_globals_push M s T v).2 fid A B).symm.trans
      ((h.2 fid A B).trans ((model_agrees_on_globals_push N s T w).2 fid A B))

/-! ## Typed body congruence for `choice` -/

private theorem choose_eq_of_pred_eq {p q : SmtValue -> Prop}
    (hp : ∃ v, p v) (hq : ∃ v, q v) (hpq : p = q) :
    Classical.choose hp = Classical.choose hq := by
  subst hpq
  rfl

private theorem native_eval_tchoice_eq_of_body_eval_eq_typed
    {M N : SmtModel} {s : native_String} {T : SmtType} {body : SmtTerm}
    (hBody : ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
      __smtx_value_canonical v = true ->
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval (native_model_push N s T v) body) :
    native_eval_choice M s T body = native_eval_choice N s T body := by
  classical
  have hPred : (fun v : SmtValue =>
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push M s T v) body =
          SmtValue.Boolean true) =
    (fun v : SmtValue =>
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push N s T v) body =
          SmtValue.Boolean true) := by
    funext v
    apply propext
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by rw [← hBody v h1 h2]; exact h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by rw [hBody v h1 h2]; exact h3⟩
  by_cases hSatM : ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical v = true ∧
        __smtx_model_eval (native_model_push M s T v) body =
          SmtValue.Boolean true
  · have hSatN : ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical v = true ∧
          __smtx_model_eval (native_model_push N s T v) body =
            SmtValue.Boolean true := by
      rw [show (∃ v : SmtValue,
          __smtx_typeof_value v = T ∧
            __smtx_value_canonical v = true ∧
            __smtx_model_eval (native_model_push N s T v) body =
              SmtValue.Boolean true) = ∃ v : SmtValue,
          __smtx_typeof_value v = T ∧
            __smtx_value_canonical v = true ∧
            __smtx_model_eval (native_model_push M s T v) body =
              SmtValue.Boolean true from by rw [hPred]]
      exact hSatM
    rw [dif_pos hSatM, dif_pos hSatN]
    exact choose_eq_of_pred_eq hSatM hSatN hPred
  · have hSatN : ¬ ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical v = true ∧
          __smtx_model_eval (native_model_push N s T v) body =
            SmtValue.Boolean true := by
      intro hN
      apply hSatM
      rw [show (∃ v : SmtValue,
          __smtx_typeof_value v = T ∧
            __smtx_value_canonical v = true ∧
            __smtx_model_eval (native_model_push M s T v) body =
              SmtValue.Boolean true) = ∃ v : SmtValue,
          __smtx_typeof_value v = T ∧
            __smtx_value_canonical v = true ∧
            __smtx_model_eval (native_model_push N s T v) body =
              SmtValue.Boolean true from by rw [hPred]]
      exact hN
    rw [dif_neg hSatM, dif_neg hSatN]

/-! ## Clean-or-`None` facts for the typeof helper families -/

private theorem cleanOrNone_arith2 (A B : SmtType) :
    cleanOrNone (__smtx_typeof_arith_overload_op_2 A B) := by
  unfold __smtx_typeof_arith_overload_op_2
  split
  · exact Or.inr True.intro
  · exact Or.inr True.intro
  · exact Or.inl rfl

private theorem cleanOrNone_arith2_ret (A B : SmtType) {T : SmtType}
    (hT : cleanOrNone T) :
    cleanOrNone (__smtx_typeof_arith_overload_op_2_ret A B T) := by
  unfold __smtx_typeof_arith_overload_op_2_ret
  split
  · exact hT
  · exact hT
  · exact Or.inl rfl

private theorem cleanOrNone_arith1 (A : SmtType) :
    cleanOrNone (__smtx_typeof_arith_overload_op_1 A) := by
  unfold __smtx_typeof_arith_overload_op_1
  split
  · exact Or.inr True.intro
  · exact Or.inr True.intro
  · exact Or.inl rfl

private theorem cleanOrNone_bv1 (A : SmtType) :
    cleanOrNone (__smtx_typeof_bv_op_1 A) := by
  unfold __smtx_typeof_bv_op_1
  split
  · exact Or.inr True.intro
  · exact Or.inl rfl

private theorem cleanOrNone_bv1_ret (A : SmtType) {T : SmtType}
    (hT : cleanOrNone T) :
    cleanOrNone (__smtx_typeof_bv_op_1_ret A T) := by
  unfold __smtx_typeof_bv_op_1_ret
  split
  · exact hT
  · exact Or.inl rfl

private theorem cleanOrNone_bv2 (A B : SmtType) :
    cleanOrNone (__smtx_typeof_bv_op_2 A B) := by
  unfold __smtx_typeof_bv_op_2
  split
  · exact cleanOrNone_guard' (Or.inr True.intro)
  · exact Or.inl rfl

private theorem cleanOrNone_bv2_ret (A B : SmtType) {T : SmtType}
    (hT : cleanOrNone T) :
    cleanOrNone (__smtx_typeof_bv_op_2_ret A B T) := by
  unfold __smtx_typeof_bv_op_2_ret
  split
  · exact cleanOrNone_guard' hT
  · exact Or.inl rfl

private theorem cleanOrNone_seq1 {A : SmtType} (hA : cleanOrNone A) :
    cleanOrNone (__smtx_typeof_seq_op_1 A) := by
  unfold __smtx_typeof_seq_op_1
  split
  · exact hA
  · exact Or.inl rfl

private theorem cleanOrNone_seq1_ret (A : SmtType) {T : SmtType}
    (hT : cleanOrNone T) :
    cleanOrNone (__smtx_typeof_seq_op_1_ret A T) := by
  unfold __smtx_typeof_seq_op_1_ret
  split
  · exact hT
  · exact Or.inl rfl

private theorem cleanOrNone_seq2 {A : SmtType} (B : SmtType)
    (hA : cleanOrNone A) :
    cleanOrNone (__smtx_typeof_seq_op_2 A B) := by
  unfold __smtx_typeof_seq_op_2
  split
  · rename_i a b
    exact cleanOrNone_guard' hA
  · exact Or.inl rfl

private theorem cleanOrNone_seq2_ret (A B : SmtType) {T : SmtType}
    (hT : cleanOrNone T) :
    cleanOrNone (__smtx_typeof_seq_op_2_ret A B T) := by
  unfold __smtx_typeof_seq_op_2_ret
  split
  · exact cleanOrNone_guard' hT
  · exact Or.inl rfl

private theorem cleanOrNone_seq3 {A : SmtType} (B C : SmtType)
    (hA : cleanOrNone A) :
    cleanOrNone (__smtx_typeof_seq_op_3 A B C) := by
  unfold __smtx_typeof_seq_op_3
  split
  · exact cleanOrNone_guard' (cleanOrNone_guard' hA)
  · exact Or.inl rfl

private theorem cleanOrNone_str_substr {A : SmtType} (B C : SmtType)
    (hA : cleanOrNone A) :
    cleanOrNone (__smtx_typeof_str_substr A B C) := by
  unfold __smtx_typeof_str_substr
  split
  · exact hA
  · exact Or.inl rfl

private theorem cleanOrNone_str_indexof (A B C : SmtType) :
    cleanOrNone (__smtx_typeof_str_indexof A B C) := by
  unfold __smtx_typeof_str_indexof
  split
  · exact cleanOrNone_guard' (Or.inr True.intro)
  · exact Or.inl rfl

private theorem cleanOrNone_str_at {A : SmtType} (B : SmtType)
    (hA : cleanOrNone A) :
    cleanOrNone (__smtx_typeof_str_at A B) := by
  unfold __smtx_typeof_str_at
  split
  · exact hA
  · exact Or.inl rfl

private theorem cleanOrNone_str_update {A : SmtType} (B C : SmtType)
    (hA : cleanOrNone A) :
    cleanOrNone (__smtx_typeof_str_update A B C) := by
  unfold __smtx_typeof_str_update
  split
  · exact cleanOrNone_guard' hA
  · exact Or.inl rfl

private theorem cleanOrNone_sets2 {A : SmtType} (B : SmtType)
    (hA : cleanOrNone A) :
    cleanOrNone (__smtx_typeof_sets_op_2 A B) := by
  unfold __smtx_typeof_sets_op_2
  split
  · exact cleanOrNone_guard' hA
  · exact Or.inl rfl

private theorem cleanOrNone_sets2_ret (A B : SmtType) {T : SmtType}
    (hT : cleanOrNone T) :
    cleanOrNone (__smtx_typeof_sets_op_2_ret A B T) := by
  unfold __smtx_typeof_sets_op_2_ret
  split
  · exact cleanOrNone_guard' hT
  · exact Or.inl rfl

private theorem cleanOrNone_set_member (A B : SmtType) :
    cleanOrNone (__smtx_typeof_set_member A B) := by
  unfold __smtx_typeof_set_member
  split
  · exact cleanOrNone_guard' (Or.inr True.intro)
  · exact Or.inl rfl

private theorem cleanOrNone_seq_nth (A B : SmtType) :
    cleanOrNone (__smtx_typeof_seq_nth A B) := by
  unfold __smtx_typeof_seq_nth
  split
  · exact cleanOrNone_typeof_guard_wf_self _
  · exact Or.inl rfl

private theorem cleanOrNone_map_diff {A : SmtType} (B : SmtType)
    (hA : cleanOrNone A) :
    cleanOrNone (__smtx_typeof_map_diff A B) := by
  unfold __smtx_typeof_map_diff
  split
  · rename_i K V K2 V2
    rcases hA with hA | hA
    · cases hA
    · exact cleanOrNone_guard' (Or.inr hA.1.2.2)
  · rename_i E E2
    rcases hA with hA | hA
    · cases hA
    · exact cleanOrNone_guard' (Or.inr hA.2.2)
  · exact Or.inl rfl

private theorem cleanOrNone_seq_diff (A B : SmtType) :
    cleanOrNone (__smtx_typeof_seq_diff A B) := by
  unfold __smtx_typeof_seq_diff
  split
  · exact cleanOrNone_guard' (Or.inr True.intro)
  · exact Or.inl rfl

private theorem cleanOrNone_select {A : SmtType} (B : SmtType)
    (hA : cleanOrNone A) :
    cleanOrNone (__smtx_typeof_select A B) := by
  unfold __smtx_typeof_select
  split
  · rename_i K V
    rcases hA with hA | hA
    · cases hA
    · exact cleanOrNone_guard' (Or.inr hA.2.2.2)
  · exact Or.inl rfl

private theorem cleanOrNone_store {A : SmtType} (B C : SmtType)
    (hA : cleanOrNone A) :
    cleanOrNone (__smtx_typeof_store A B C) := by
  unfold __smtx_typeof_store
  split
  · exact cleanOrNone_guard' (cleanOrNone_guard' hA)
  · exact Or.inl rfl

private theorem cleanOrNone_concat (A B : SmtType) :
    cleanOrNone (__smtx_typeof_concat A B) := by
  unfold __smtx_typeof_concat
  split
  · exact Or.inr True.intro
  · exact Or.inl rfl

private theorem cleanOrNone_extract (i j : SmtTerm) (C : SmtType) :
    cleanOrNone (__smtx_typeof_extract i j C) := by
  unfold __smtx_typeof_extract
  split
  · exact cleanOrNone_guard' (cleanOrNone_guard' (cleanOrNone_guard'
      (Or.inr True.intro)))
  · exact Or.inl rfl

private theorem cleanOrNone_repeat (i : SmtTerm) (C : SmtType) :
    cleanOrNone (__smtx_typeof_repeat i C) := by
  unfold __smtx_typeof_repeat
  split
  · exact cleanOrNone_guard' (Or.inr True.intro)
  · exact Or.inl rfl

private theorem cleanOrNone_zero_extend (i : SmtTerm) (C : SmtType) :
    cleanOrNone (__smtx_typeof_zero_extend i C) := by
  unfold __smtx_typeof_zero_extend
  split
  · exact cleanOrNone_guard' (Or.inr True.intro)
  · exact Or.inl rfl

private theorem cleanOrNone_sign_extend (i : SmtTerm) (C : SmtType) :
    cleanOrNone (__smtx_typeof_sign_extend i C) := by
  unfold __smtx_typeof_sign_extend
  split
  · exact cleanOrNone_guard' (Or.inr True.intro)
  · exact Or.inl rfl

private theorem cleanOrNone_rotate_left (i : SmtTerm) (C : SmtType) :
    cleanOrNone (__smtx_typeof_rotate_left i C) := by
  unfold __smtx_typeof_rotate_left
  split
  · exact cleanOrNone_guard' (Or.inr True.intro)
  · exact Or.inl rfl

private theorem cleanOrNone_rotate_right (i : SmtTerm) (C : SmtType) :
    cleanOrNone (__smtx_typeof_rotate_right i C) := by
  unfold __smtx_typeof_rotate_right
  split
  · exact cleanOrNone_guard' (Or.inr True.intro)
  · exact Or.inl rfl

private theorem cleanOrNone_int_to_bv (i : SmtTerm) (C : SmtType) :
    cleanOrNone (__smtx_typeof_int_to_bv i C) := by
  unfold __smtx_typeof_int_to_bv
  split
  · exact cleanOrNone_guard' (Or.inr True.intro)
  · exact Or.inl rfl

private theorem cleanOrNone_re_exp (i : SmtTerm) (C : SmtType) :
    cleanOrNone (__smtx_typeof_re_exp i C) := by
  unfold __smtx_typeof_re_exp
  split
  · exact cleanOrNone_guard' (Or.inr True.intro)
  · exact Or.inl rfl

private theorem cleanOrNone_re_loop (i j : SmtTerm) (C : SmtType) :
    cleanOrNone (__smtx_typeof_re_loop i j C) := by
  unfold __smtx_typeof_re_loop
  split
  · exact cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro))
  · exact Or.inl rfl

private theorem cleanOrNone_ite {B : SmtType} (A C : SmtType)
    (hB : cleanOrNone B) :
    cleanOrNone (__smtx_typeof_ite A B C) := by
  unfold __smtx_typeof_ite
  split
  · exact cleanOrNone_guard' hB
  · exact Or.inl rfl

private theorem cleanOrNone_eq (A B : SmtType) :
    cleanOrNone (__smtx_typeof_eq A B) := by
  unfold __smtx_typeof_eq
  exact cleanOrNone_typeof_guard (cleanOrNone_guard' (Or.inr True.intro))

private theorem cleanOrNone_apply {F : SmtType} (V : SmtType)
    (hF : cleanOrNone F) :
    cleanOrNone (__smtx_typeof_apply F V) := by
  unfold __smtx_typeof_apply
  split
  · rename_i T U
    rcases hF with hF | hF
    · cases hF
    · exact cleanOrNone_typeof_guard (cleanOrNone_guard' hF)
  · rename_i T U
    rcases hF with hF | hF
    · cases hF
    · exact cleanOrNone_typeof_guard (cleanOrNone_guard' hF)
  · exact Or.inl rfl

private theorem cleanOrNone_dt_cons_rec_zero (T0 : SmtType)
    (hT0 : cleanType T0) :
    ∀ (c : SmtDatatypeCons) (d : SmtDatatype),
      cleanOrNone (__smtx_typeof_dt_cons_rec T0 (SmtDatatype.sum c d) 0)
  | SmtDatatypeCons.unit, d => by
      rw [show __smtx_typeof_dt_cons_rec T0
          (SmtDatatype.sum SmtDatatypeCons.unit d) 0 = T0 from by
        simp [__smtx_typeof_dt_cons_rec]]
      exact Or.inr hT0
  | SmtDatatypeCons.cons U c, d => by
      rw [show __smtx_typeof_dt_cons_rec T0
          (SmtDatatype.sum (SmtDatatypeCons.cons U c) d) 0 =
          SmtType.DtcAppType U
            (__smtx_typeof_dt_cons_rec T0 (SmtDatatype.sum c d) 0) from by
        simp [__smtx_typeof_dt_cons_rec]]
      exact Or.inr (cleanOrNone_dt_cons_rec_zero T0 hT0 c d)

private theorem cleanOrNone_dt_cons_rec (T0 : SmtType) (hT0 : cleanType T0) :
    ∀ (d : SmtDatatype) (i : native_Nat),
      cleanOrNone (__smtx_typeof_dt_cons_rec T0 d i)
  | SmtDatatype.null, i => by
      rw [show __smtx_typeof_dt_cons_rec T0 SmtDatatype.null i =
          SmtType.None from by
        cases i <;> simp [__smtx_typeof_dt_cons_rec]]
      exact Or.inl rfl
  | SmtDatatype.sum c d, 0 => cleanOrNone_dt_cons_rec_zero T0 hT0 c d
  | SmtDatatype.sum c d, (n+1) => by
      rw [show __smtx_typeof_dt_cons_rec T0 (SmtDatatype.sum c d) (n+1) =
          __smtx_typeof_dt_cons_rec T0 d n from by
        cases c <;> simp [__smtx_typeof_dt_cons_rec]]
      exact cleanOrNone_dt_cons_rec T0 hT0 d n

private theorem cleanSeqChar : cleanType (SmtType.Seq SmtType.Char) :=
  ⟨by simp, by simp, True.intro⟩

private theorem cleanOrNone_to_real (A : SmtType) :
    cleanOrNone (native_ite (native_Teq A SmtType.Int) SmtType.Real SmtType.None) := by
  cases native_Teq A SmtType.Int
  · exact Or.inl rfl
  · exact Or.inr True.intro

/-- Every non-`None` `__smtx_typeof` is a clean type. -/
private theorem typeof_cleanOrNone :
    ∀ (t : SmtTerm), cleanOrNone (__smtx_typeof t)
  | SmtTerm.None => Or.inl rfl
  | SmtTerm.Boolean _ => Or.inr True.intro
  | SmtTerm.Numeral _ => Or.inr True.intro
  | SmtTerm.Rational _ => Or.inr True.intro
  | SmtTerm.String _ => cleanOrNone_guard' (Or.inr cleanSeqChar)
  | SmtTerm.Binary _ _ => cleanOrNone_guard' (Or.inr True.intro)
  | SmtTerm.Apply (SmtTerm.DtSel s d i j) x1 =>
      cleanOrNone_typeof_guard_wf
        (fun hw => cleanOrNone_apply _ (Or.inr (Or.inr (cleanType_of_wf hw))))
  | SmtTerm.Apply (SmtTerm.DtTester s d i) x1 =>
      cleanOrNone_typeof_guard
        (cleanOrNone_apply _ (Or.inr (Or.inr True.intro)))
  | SmtTerm.Apply (SmtTerm.None) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone SmtTerm.None)
  | SmtTerm.Apply (SmtTerm.Boolean b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.Boolean b))
  | SmtTerm.Apply (SmtTerm.Numeral n) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.Numeral n))
  | SmtTerm.Apply (SmtTerm.Rational q) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.Rational q))
  | SmtTerm.Apply (SmtTerm.String s) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.String s))
  | SmtTerm.Apply (SmtTerm.Binary w n) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.Binary w n))
  | SmtTerm.Apply (SmtTerm.Apply f y) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.Apply f y))
  | SmtTerm.Apply (SmtTerm.Var s T) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.Var s T))
  | SmtTerm.Apply (SmtTerm.ite c a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.ite c a b))
  | SmtTerm.Apply (SmtTerm.eq a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.eq a b))
  | SmtTerm.Apply (SmtTerm.exists s T b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.exists s T b))
  | SmtTerm.Apply (SmtTerm.forall s T b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.forall s T b))
  | SmtTerm.Apply (SmtTerm.choice s T b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.choice s T b))
  | SmtTerm.Apply (SmtTerm.bind s T a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bind s T a b))
  | SmtTerm.Apply (SmtTerm.map_diff a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.map_diff a b))
  | SmtTerm.Apply (SmtTerm.seq_diff a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.seq_diff a b))
  | SmtTerm.Apply (SmtTerm.DtCons s d i) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.DtCons s d i))
  | SmtTerm.Apply (SmtTerm.UConst s T) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.UConst s T))
  | SmtTerm.Apply (SmtTerm.not a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.not a))
  | SmtTerm.Apply (SmtTerm.or a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.or a b))
  | SmtTerm.Apply (SmtTerm.and a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.and a b))
  | SmtTerm.Apply (SmtTerm.imp a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.imp a b))
  | SmtTerm.Apply (SmtTerm.xor a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.xor a b))
  | SmtTerm.Apply (SmtTerm._at_purify a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm._at_purify a))
  | SmtTerm.Apply (SmtTerm.plus a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.plus a b))
  | SmtTerm.Apply (SmtTerm.neg a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.neg a b))
  | SmtTerm.Apply (SmtTerm.mult a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.mult a b))
  | SmtTerm.Apply (SmtTerm.lt a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.lt a b))
  | SmtTerm.Apply (SmtTerm.leq a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.leq a b))
  | SmtTerm.Apply (SmtTerm.gt a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.gt a b))
  | SmtTerm.Apply (SmtTerm.geq a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.geq a b))
  | SmtTerm.Apply (SmtTerm.to_real a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.to_real a))
  | SmtTerm.Apply (SmtTerm.to_int a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.to_int a))
  | SmtTerm.Apply (SmtTerm.is_int a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.is_int a))
  | SmtTerm.Apply (SmtTerm.abs a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.abs a))
  | SmtTerm.Apply (SmtTerm.uneg a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.uneg a))
  | SmtTerm.Apply (SmtTerm.div a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.div a b))
  | SmtTerm.Apply (SmtTerm.mod a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.mod a b))
  | SmtTerm.Apply (SmtTerm.divisible a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.divisible a b))
  | SmtTerm.Apply (SmtTerm.int_pow2 a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.int_pow2 a))
  | SmtTerm.Apply (SmtTerm.int_log2 a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.int_log2 a))
  | SmtTerm.Apply (SmtTerm.div_total a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.div_total a b))
  | SmtTerm.Apply (SmtTerm.mod_total a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.mod_total a b))
  | SmtTerm.Apply (SmtTerm.select a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.select a b))
  | SmtTerm.Apply (SmtTerm.store a b c) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.store a b c))
  | SmtTerm.Apply (SmtTerm.concat a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.concat a b))
  | SmtTerm.Apply (SmtTerm.extract a b c) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.extract a b c))
  | SmtTerm.Apply (SmtTerm.repeat a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.repeat a b))
  | SmtTerm.Apply (SmtTerm.bvnot a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvnot a))
  | SmtTerm.Apply (SmtTerm.bvand a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvand a b))
  | SmtTerm.Apply (SmtTerm.bvor a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvor a b))
  | SmtTerm.Apply (SmtTerm.bvnand a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvnand a b))
  | SmtTerm.Apply (SmtTerm.bvnor a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvnor a b))
  | SmtTerm.Apply (SmtTerm.bvxor a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvxor a b))
  | SmtTerm.Apply (SmtTerm.bvxnor a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvxnor a b))
  | SmtTerm.Apply (SmtTerm.bvcomp a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvcomp a b))
  | SmtTerm.Apply (SmtTerm.bvneg a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvneg a))
  | SmtTerm.Apply (SmtTerm.bvadd a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvadd a b))
  | SmtTerm.Apply (SmtTerm.bvmul a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvmul a b))
  | SmtTerm.Apply (SmtTerm.bvudiv a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvudiv a b))
  | SmtTerm.Apply (SmtTerm.bvurem a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvurem a b))
  | SmtTerm.Apply (SmtTerm.bvsub a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvsub a b))
  | SmtTerm.Apply (SmtTerm.bvsdiv a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvsdiv a b))
  | SmtTerm.Apply (SmtTerm.bvsrem a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvsrem a b))
  | SmtTerm.Apply (SmtTerm.bvsmod a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvsmod a b))
  | SmtTerm.Apply (SmtTerm.bvult a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvult a b))
  | SmtTerm.Apply (SmtTerm.bvule a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvule a b))
  | SmtTerm.Apply (SmtTerm.bvugt a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvugt a b))
  | SmtTerm.Apply (SmtTerm.bvuge a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvuge a b))
  | SmtTerm.Apply (SmtTerm.bvslt a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvslt a b))
  | SmtTerm.Apply (SmtTerm.bvsle a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvsle a b))
  | SmtTerm.Apply (SmtTerm.bvsgt a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvsgt a b))
  | SmtTerm.Apply (SmtTerm.bvsge a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvsge a b))
  | SmtTerm.Apply (SmtTerm.bvshl a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvshl a b))
  | SmtTerm.Apply (SmtTerm.bvlshr a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvlshr a b))
  | SmtTerm.Apply (SmtTerm.bvashr a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvashr a b))
  | SmtTerm.Apply (SmtTerm.zero_extend a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.zero_extend a b))
  | SmtTerm.Apply (SmtTerm.sign_extend a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.sign_extend a b))
  | SmtTerm.Apply (SmtTerm.rotate_left a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.rotate_left a b))
  | SmtTerm.Apply (SmtTerm.rotate_right a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.rotate_right a b))
  | SmtTerm.Apply (SmtTerm.bvuaddo a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvuaddo a b))
  | SmtTerm.Apply (SmtTerm.bvnego a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvnego a))
  | SmtTerm.Apply (SmtTerm.bvsaddo a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvsaddo a b))
  | SmtTerm.Apply (SmtTerm.bvumulo a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvumulo a b))
  | SmtTerm.Apply (SmtTerm.bvsmulo a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvsmulo a b))
  | SmtTerm.Apply (SmtTerm.bvusubo a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvusubo a b))
  | SmtTerm.Apply (SmtTerm.bvssubo a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvssubo a b))
  | SmtTerm.Apply (SmtTerm.bvsdivo a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.bvsdivo a b))
  | SmtTerm.Apply (SmtTerm.seq_empty T) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.seq_empty T))
  | SmtTerm.Apply (SmtTerm.str_len a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_len a))
  | SmtTerm.Apply (SmtTerm.str_concat a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_concat a b))
  | SmtTerm.Apply (SmtTerm.str_substr a b c) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_substr a b c))
  | SmtTerm.Apply (SmtTerm.str_contains a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_contains a b))
  | SmtTerm.Apply (SmtTerm.str_replace a b c) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_replace a b c))
  | SmtTerm.Apply (SmtTerm.str_indexof a b c) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_indexof a b c))
  | SmtTerm.Apply (SmtTerm._at_strings_occur_index a b c) x1 =>
      cleanOrNone_apply _
        (typeof_cleanOrNone (SmtTerm._at_strings_occur_index a b c))
  | SmtTerm.Apply (SmtTerm.str_at a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_at a b))
  | SmtTerm.Apply (SmtTerm.str_prefixof a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_prefixof a b))
  | SmtTerm.Apply (SmtTerm.str_suffixof a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_suffixof a b))
  | SmtTerm.Apply (SmtTerm.str_rev a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_rev a))
  | SmtTerm.Apply (SmtTerm.str_update a b c) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_update a b c))
  | SmtTerm.Apply (SmtTerm.str_to_lower a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_to_lower a))
  | SmtTerm.Apply (SmtTerm.str_to_upper a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_to_upper a))
  | SmtTerm.Apply (SmtTerm.str_to_code a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_to_code a))
  | SmtTerm.Apply (SmtTerm.str_from_code a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_from_code a))
  | SmtTerm.Apply (SmtTerm.str_is_digit a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_is_digit a))
  | SmtTerm.Apply (SmtTerm.str_to_int a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_to_int a))
  | SmtTerm.Apply (SmtTerm.str_from_int a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_from_int a))
  | SmtTerm.Apply (SmtTerm.str_lt a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_lt a b))
  | SmtTerm.Apply (SmtTerm.str_leq a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_leq a b))
  | SmtTerm.Apply (SmtTerm.str_replace_all a b c) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_replace_all a b c))
  | SmtTerm.Apply (SmtTerm.str_replace_re a b c) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_replace_re a b c))
  | SmtTerm.Apply (SmtTerm.str_replace_re_all a b c) x1 =>
      cleanOrNone_apply _
        (typeof_cleanOrNone (SmtTerm.str_replace_re_all a b c))
  | SmtTerm.Apply (SmtTerm.str_indexof_re a b c) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_indexof_re a b c))
  | SmtTerm.Apply (SmtTerm._at_strings_occur_index_re a b c) x1 =>
      cleanOrNone_apply _
        (typeof_cleanOrNone (SmtTerm._at_strings_occur_index_re a b c))
  | SmtTerm.Apply SmtTerm.re_allchar x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone SmtTerm.re_allchar)
  | SmtTerm.Apply SmtTerm.re_none x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone SmtTerm.re_none)
  | SmtTerm.Apply SmtTerm.re_all x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone SmtTerm.re_all)
  | SmtTerm.Apply (SmtTerm.str_to_re a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_to_re a))
  | SmtTerm.Apply (SmtTerm.re_mult a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.re_mult a))
  | SmtTerm.Apply (SmtTerm.re_plus a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.re_plus a))
  | SmtTerm.Apply (SmtTerm.re_exp a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.re_exp a b))
  | SmtTerm.Apply (SmtTerm.re_opt a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.re_opt a))
  | SmtTerm.Apply (SmtTerm.re_comp a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.re_comp a))
  | SmtTerm.Apply (SmtTerm.re_range a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.re_range a b))
  | SmtTerm.Apply (SmtTerm.re_concat a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.re_concat a b))
  | SmtTerm.Apply (SmtTerm.re_inter a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.re_inter a b))
  | SmtTerm.Apply (SmtTerm.re_union a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.re_union a b))
  | SmtTerm.Apply (SmtTerm.re_diff a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.re_diff a b))
  | SmtTerm.Apply (SmtTerm.re_loop a b c) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.re_loop a b c))
  | SmtTerm.Apply (SmtTerm.str_in_re a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.str_in_re a b))
  | SmtTerm.Apply (SmtTerm.str_indexof_re_split a b c) x1 =>
      cleanOrNone_apply _
        (typeof_cleanOrNone (SmtTerm.str_indexof_re_split a b c))
  | SmtTerm.Apply (SmtTerm.seq_unit a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.seq_unit a))
  | SmtTerm.Apply (SmtTerm.seq_nth a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.seq_nth a b))
  | SmtTerm.Apply (SmtTerm.set_empty T) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.set_empty T))
  | SmtTerm.Apply (SmtTerm.set_singleton a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.set_singleton a))
  | SmtTerm.Apply (SmtTerm.set_union a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.set_union a b))
  | SmtTerm.Apply (SmtTerm.set_inter a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.set_inter a b))
  | SmtTerm.Apply (SmtTerm.set_minus a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.set_minus a b))
  | SmtTerm.Apply (SmtTerm.set_member a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.set_member a b))
  | SmtTerm.Apply (SmtTerm.set_subset a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.set_subset a b))
  | SmtTerm.Apply (SmtTerm.qdiv a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.qdiv a b))
  | SmtTerm.Apply (SmtTerm.qdiv_total a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.qdiv_total a b))
  | SmtTerm.Apply (SmtTerm.int_to_bv a b) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.int_to_bv a b))
  | SmtTerm.Apply (SmtTerm.ubv_to_int a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.ubv_to_int a))
  | SmtTerm.Apply (SmtTerm.sbv_to_int a) x1 =>
      cleanOrNone_apply _ (typeof_cleanOrNone (SmtTerm.sbv_to_int a))
  | SmtTerm.Var _ T => cleanOrNone_typeof_guard_wf_self T
  | SmtTerm.ite c a b => cleanOrNone_ite _ _ (typeof_cleanOrNone a)
  | SmtTerm.eq a b => cleanOrNone_eq _ _
  | SmtTerm.exists s T b =>
      cleanOrNone_guard'
        (cleanOrNone_typeof_guard_wf (fun _ => Or.inr True.intro))
  | SmtTerm.forall s T b =>
      cleanOrNone_guard'
        (cleanOrNone_typeof_guard_wf (fun _ => Or.inr True.intro))
  | SmtTerm.choice s T b =>
      cleanOrNone_guard' (cleanOrNone_typeof_guard_wf_self T)
  | SmtTerm.bind s T a b =>
      cleanOrNone_guard'
        (cleanOrNone_typeof_guard_wf (fun _ => typeof_cleanOrNone b))
  | SmtTerm.map_diff a b => cleanOrNone_map_diff _ (typeof_cleanOrNone a)
  | SmtTerm.seq_diff a b => cleanOrNone_seq_diff _ _
  | SmtTerm.DtCons s d i =>
      cleanOrNone_typeof_guard_wf
        (fun _ => cleanOrNone_dt_cons_rec (SmtType.Datatype s d) True.intro
          (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i)
  | SmtTerm.DtSel _ _ _ _ => Or.inl rfl
  | SmtTerm.DtTester _ _ _ => Or.inl rfl
  | SmtTerm.UConst _ T => cleanOrNone_typeof_guard_wf_self T
  | SmtTerm.not a => cleanOrNone_guard' (Or.inr True.intro)
  | SmtTerm.or a b =>
      cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro))
  | SmtTerm.and a b =>
      cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro))
  | SmtTerm.imp a b =>
      cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro))
  | SmtTerm.xor a b =>
      cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro))
  | SmtTerm._at_purify a => typeof_cleanOrNone a
  | SmtTerm.plus a b => cleanOrNone_arith2 _ _
  | SmtTerm.neg a b => cleanOrNone_arith2 _ _
  | SmtTerm.mult a b => cleanOrNone_arith2 _ _
  | SmtTerm.lt a b => cleanOrNone_arith2_ret _ _ (Or.inr True.intro)
  | SmtTerm.leq a b => cleanOrNone_arith2_ret _ _ (Or.inr True.intro)
  | SmtTerm.gt a b => cleanOrNone_arith2_ret _ _ (Or.inr True.intro)
  | SmtTerm.geq a b => cleanOrNone_arith2_ret _ _ (Or.inr True.intro)
  | SmtTerm.to_real a => cleanOrNone_to_real _
  | SmtTerm.to_int a => cleanOrNone_guard' (Or.inr True.intro)
  | SmtTerm.is_int a => cleanOrNone_guard' (Or.inr True.intro)
  | SmtTerm.abs a => cleanOrNone_arith1 _
  | SmtTerm.uneg a => cleanOrNone_arith1 _
  | SmtTerm.div a b =>
      cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro))
  | SmtTerm.mod a b =>
      cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro))
  | SmtTerm.divisible a b =>
      cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro))
  | SmtTerm.int_pow2 a => cleanOrNone_guard' (Or.inr True.intro)
  | SmtTerm.int_log2 a => cleanOrNone_guard' (Or.inr True.intro)
  | SmtTerm.div_total a b =>
      cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro))
  | SmtTerm.mod_total a b =>
      cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro))
  | SmtTerm.select a b => cleanOrNone_select _ (typeof_cleanOrNone a)
  | SmtTerm.store a b c => cleanOrNone_store _ _ (typeof_cleanOrNone a)
  | SmtTerm.concat a b => cleanOrNone_concat _ _
  | SmtTerm.extract a b c => cleanOrNone_extract _ _ _
  | SmtTerm.repeat a b => cleanOrNone_repeat _ _
  | SmtTerm.bvnot a => cleanOrNone_bv1 _
  | SmtTerm.bvand a b => cleanOrNone_bv2 _ _
  | SmtTerm.bvor a b => cleanOrNone_bv2 _ _
  | SmtTerm.bvnand a b => cleanOrNone_bv2 _ _
  | SmtTerm.bvnor a b => cleanOrNone_bv2 _ _
  | SmtTerm.bvxor a b => cleanOrNone_bv2 _ _
  | SmtTerm.bvxnor a b => cleanOrNone_bv2 _ _
  | SmtTerm.bvcomp a b => cleanOrNone_bv2_ret _ _ (Or.inr True.intro)
  | SmtTerm.bvneg a => cleanOrNone_bv1 _
  | SmtTerm.bvadd a b => cleanOrNone_bv2 _ _
  | SmtTerm.bvmul a b => cleanOrNone_bv2 _ _
  | SmtTerm.bvudiv a b => cleanOrNone_bv2 _ _
  | SmtTerm.bvurem a b => cleanOrNone_bv2 _ _
  | SmtTerm.bvsub a b => cleanOrNone_bv2 _ _
  | SmtTerm.bvsdiv a b => cleanOrNone_bv2 _ _
  | SmtTerm.bvsrem a b => cleanOrNone_bv2 _ _
  | SmtTerm.bvsmod a b => cleanOrNone_bv2 _ _
  | SmtTerm.bvult a b => cleanOrNone_bv2_ret _ _ (Or.inr True.intro)
  | SmtTerm.bvule a b => cleanOrNone_bv2_ret _ _ (Or.inr True.intro)
  | SmtTerm.bvugt a b => cleanOrNone_bv2_ret _ _ (Or.inr True.intro)
  | SmtTerm.bvuge a b => cleanOrNone_bv2_ret _ _ (Or.inr True.intro)
  | SmtTerm.bvslt a b => cleanOrNone_bv2_ret _ _ (Or.inr True.intro)
  | SmtTerm.bvsle a b => cleanOrNone_bv2_ret _ _ (Or.inr True.intro)
  | SmtTerm.bvsgt a b => cleanOrNone_bv2_ret _ _ (Or.inr True.intro)
  | SmtTerm.bvsge a b => cleanOrNone_bv2_ret _ _ (Or.inr True.intro)
  | SmtTerm.bvshl a b => cleanOrNone_bv2 _ _
  | SmtTerm.bvlshr a b => cleanOrNone_bv2 _ _
  | SmtTerm.bvashr a b => cleanOrNone_bv2 _ _
  | SmtTerm.zero_extend a b => cleanOrNone_zero_extend _ _
  | SmtTerm.sign_extend a b => cleanOrNone_sign_extend _ _
  | SmtTerm.rotate_left a b => cleanOrNone_rotate_left _ _
  | SmtTerm.rotate_right a b => cleanOrNone_rotate_right _ _
  | SmtTerm.bvuaddo a b => cleanOrNone_bv2_ret _ _ (Or.inr True.intro)
  | SmtTerm.bvnego a => cleanOrNone_bv1_ret _ (Or.inr True.intro)
  | SmtTerm.bvsaddo a b => cleanOrNone_bv2_ret _ _ (Or.inr True.intro)
  | SmtTerm.bvumulo a b => cleanOrNone_bv2_ret _ _ (Or.inr True.intro)
  | SmtTerm.bvsmulo a b => cleanOrNone_bv2_ret _ _ (Or.inr True.intro)
  | SmtTerm.bvusubo a b => cleanOrNone_bv2_ret _ _ (Or.inr True.intro)
  | SmtTerm.bvssubo a b => cleanOrNone_bv2_ret _ _ (Or.inr True.intro)
  | SmtTerm.bvsdivo a b => cleanOrNone_bv2_ret _ _ (Or.inr True.intro)
  | SmtTerm.seq_empty T => cleanOrNone_typeof_guard_wf_self _
  | SmtTerm.str_len a => cleanOrNone_seq1_ret _ (Or.inr True.intro)
  | SmtTerm.str_concat a b => cleanOrNone_seq2 _ (typeof_cleanOrNone a)
  | SmtTerm.str_substr a b c =>
      cleanOrNone_str_substr _ _ (typeof_cleanOrNone a)
  | SmtTerm.str_contains a b =>
      cleanOrNone_seq2_ret _ _ (Or.inr True.intro)
  | SmtTerm.str_replace a b c => cleanOrNone_seq3 _ _ (typeof_cleanOrNone a)
  | SmtTerm.str_indexof a b c => cleanOrNone_str_indexof _ _ _
  | SmtTerm._at_strings_occur_index a b c => cleanOrNone_str_indexof _ _ _
  | SmtTerm.str_at a b => cleanOrNone_str_at _ (typeof_cleanOrNone a)
  | SmtTerm.str_prefixof a b => cleanOrNone_seq2_ret _ _ (Or.inr True.intro)
  | SmtTerm.str_suffixof a b => cleanOrNone_seq2_ret _ _ (Or.inr True.intro)
  | SmtTerm.str_rev a => cleanOrNone_seq1 (typeof_cleanOrNone a)
  | SmtTerm.str_update a b c =>
      cleanOrNone_str_update _ _ (typeof_cleanOrNone a)
  | SmtTerm.str_to_lower a => cleanOrNone_guard' (Or.inr cleanSeqChar)
  | SmtTerm.str_to_upper a => cleanOrNone_guard' (Or.inr cleanSeqChar)
  | SmtTerm.str_to_code a => cleanOrNone_guard' (Or.inr True.intro)
  | SmtTerm.str_from_code a => cleanOrNone_guard' (Or.inr cleanSeqChar)
  | SmtTerm.str_is_digit a => cleanOrNone_guard' (Or.inr True.intro)
  | SmtTerm.str_to_int a => cleanOrNone_guard' (Or.inr True.intro)
  | SmtTerm.str_from_int a => cleanOrNone_guard' (Or.inr cleanSeqChar)
  | SmtTerm.str_lt a b =>
      cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro))
  | SmtTerm.str_leq a b =>
      cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro))
  | SmtTerm.str_replace_all a b c =>
      cleanOrNone_seq3 _ _ (typeof_cleanOrNone a)
  | SmtTerm.str_replace_re a b c =>
      cleanOrNone_guard'
        (cleanOrNone_guard' (cleanOrNone_guard' (Or.inr cleanSeqChar)))
  | SmtTerm.str_replace_re_all a b c =>
      cleanOrNone_guard'
        (cleanOrNone_guard' (cleanOrNone_guard' (Or.inr cleanSeqChar)))
  | SmtTerm.str_indexof_re a b c =>
      cleanOrNone_guard'
        (cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro)))
  | SmtTerm._at_strings_occur_index_re a b c =>
      cleanOrNone_guard'
        (cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro)))
  | SmtTerm.re_allchar => Or.inr True.intro
  | SmtTerm.re_none => Or.inr True.intro
  | SmtTerm.re_all => Or.inr True.intro
  | SmtTerm.str_to_re a => cleanOrNone_guard' (Or.inr True.intro)
  | SmtTerm.re_mult a => cleanOrNone_guard' (Or.inr True.intro)
  | SmtTerm.re_plus a => cleanOrNone_guard' (Or.inr True.intro)
  | SmtTerm.re_exp a b => cleanOrNone_re_exp _ _
  | SmtTerm.re_opt a => cleanOrNone_guard' (Or.inr True.intro)
  | SmtTerm.re_comp a => cleanOrNone_guard' (Or.inr True.intro)
  | SmtTerm.re_range a b =>
      cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro))
  | SmtTerm.re_concat a b =>
      cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro))
  | SmtTerm.re_inter a b =>
      cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro))
  | SmtTerm.re_union a b =>
      cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro))
  | SmtTerm.re_diff a b =>
      cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro))
  | SmtTerm.re_loop a b c => cleanOrNone_re_loop _ _ _
  | SmtTerm.str_in_re a b =>
      cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro))
  | SmtTerm.str_indexof_re_split a b c =>
      cleanOrNone_guard'
        (cleanOrNone_guard' (cleanOrNone_guard' (Or.inr True.intro)))
  | SmtTerm.seq_unit a => cleanOrNone_typeof_guard_wf_self _
  | SmtTerm.seq_nth a b => cleanOrNone_seq_nth _ _
  | SmtTerm.set_empty T => cleanOrNone_typeof_guard_wf_self _
  | SmtTerm.set_singleton a => cleanOrNone_typeof_guard_wf_self _
  | SmtTerm.set_union a b => cleanOrNone_sets2 _ (typeof_cleanOrNone a)
  | SmtTerm.set_inter a b => cleanOrNone_sets2 _ (typeof_cleanOrNone a)
  | SmtTerm.set_minus a b => cleanOrNone_sets2 _ (typeof_cleanOrNone a)
  | SmtTerm.set_member a b => cleanOrNone_set_member _ _
  | SmtTerm.set_subset a b => cleanOrNone_sets2_ret _ _ (Or.inr True.intro)
  | SmtTerm.qdiv a b => cleanOrNone_arith2_ret _ _ (Or.inr True.intro)
  | SmtTerm.qdiv_total a b => cleanOrNone_arith2_ret _ _ (Or.inr True.intro)
  | SmtTerm.int_to_bv a b => cleanOrNone_int_to_bv _ _
  | SmtTerm.ubv_to_int a => cleanOrNone_bv1_ret _ (Or.inr True.intro)
  | SmtTerm.sbv_to_int a => cleanOrNone_bv1_ret _ (Or.inr True.intro)

/-! ## Remaining helpers for the master walk -/

private theorem tnn_of_typeof_eq {x : SmtTerm} {c : SmtType}
    (h : __smtx_typeof x = c) (hc : c ≠ SmtType.None) :
    term_has_non_none_type x := by
  unfold term_has_non_none_type
  rw [h]
  exact hc

private theorem ne_none_of_wf {T : SmtType}
    (h : __smtx_type_wf T = true) : T ≠ SmtType.None := by
  intro hEq
  subst hEq
  unfold __smtx_type_wf at h
  exact ne_none_of_wf_component h rfl

private theorem extract_term_args {i j : SmtTerm} {C : SmtType}
    (h : __smtx_typeof_extract i j C ≠ SmtType.None) :
    (∃ a, i = SmtTerm.Numeral a) ∧ (∃ b, j = SmtTerm.Numeral b) ∧
      (C ≠ SmtType.None ∧ C ≠ SmtType.RegLan) := by
  unfold __smtx_typeof_extract at h
  split at h
  · exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩, by simp, by simp⟩
  · exact absurd rfl h

private theorem repeat_term_args {i : SmtTerm} {C : SmtType}
    (h : __smtx_typeof_repeat i C ≠ SmtType.None) :
    (∃ a, i = SmtTerm.Numeral a) ∧ (C ≠ SmtType.None ∧ C ≠ SmtType.RegLan) := by
  unfold __smtx_typeof_repeat at h
  split at h
  · exact ⟨⟨_, rfl⟩, by simp, by simp⟩
  · exact absurd rfl h

private theorem zero_extend_term_args {i : SmtTerm} {C : SmtType}
    (h : __smtx_typeof_zero_extend i C ≠ SmtType.None) :
    (∃ a, i = SmtTerm.Numeral a) ∧ (C ≠ SmtType.None ∧ C ≠ SmtType.RegLan) := by
  unfold __smtx_typeof_zero_extend at h
  split at h
  · exact ⟨⟨_, rfl⟩, by simp, by simp⟩
  · exact absurd rfl h

private theorem sign_extend_term_args {i : SmtTerm} {C : SmtType}
    (h : __smtx_typeof_sign_extend i C ≠ SmtType.None) :
    (∃ a, i = SmtTerm.Numeral a) ∧ (C ≠ SmtType.None ∧ C ≠ SmtType.RegLan) := by
  unfold __smtx_typeof_sign_extend at h
  split at h
  · exact ⟨⟨_, rfl⟩, by simp, by simp⟩
  · exact absurd rfl h

private theorem rotate_left_term_args {i : SmtTerm} {C : SmtType}
    (h : __smtx_typeof_rotate_left i C ≠ SmtType.None) :
    (∃ a, i = SmtTerm.Numeral a) ∧ (C ≠ SmtType.None ∧ C ≠ SmtType.RegLan) := by
  unfold __smtx_typeof_rotate_left at h
  split at h
  · exact ⟨⟨_, rfl⟩, by simp, by simp⟩
  · exact absurd rfl h

private theorem rotate_right_term_args {i : SmtTerm} {C : SmtType}
    (h : __smtx_typeof_rotate_right i C ≠ SmtType.None) :
    (∃ a, i = SmtTerm.Numeral a) ∧ (C ≠ SmtType.None ∧ C ≠ SmtType.RegLan) := by
  unfold __smtx_typeof_rotate_right at h
  split at h
  · exact ⟨⟨_, rfl⟩, by simp, by simp⟩
  · exact absurd rfl h

private theorem int_to_bv_term_args {i : SmtTerm} {C : SmtType}
    (h : __smtx_typeof_int_to_bv i C ≠ SmtType.None) :
    (∃ a, i = SmtTerm.Numeral a) ∧ C = SmtType.Int := by
  unfold __smtx_typeof_int_to_bv at h
  split at h
  · exact ⟨⟨_, rfl⟩, rfl⟩
  · exact absurd rfl h

private theorem re_exp_term_args {i : SmtTerm} {C : SmtType}
    (h : __smtx_typeof_re_exp i C ≠ SmtType.None) :
    (∃ a, i = SmtTerm.Numeral a) ∧ C = SmtType.RegLan := by
  unfold __smtx_typeof_re_exp at h
  split at h
  · exact ⟨⟨_, rfl⟩, rfl⟩
  · exact absurd rfl h

private theorem re_loop_term_args {i j : SmtTerm} {C : SmtType}
    (h : __smtx_typeof_re_loop i j C ≠ SmtType.None) :
    (∃ a, i = SmtTerm.Numeral a) ∧ (∃ b, j = SmtTerm.Numeral b) ∧
      C = SmtType.RegLan := by
  unfold __smtx_typeof_re_loop at h
  split at h
  · exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩, rfl⟩
  · exact absurd rfl h

/-! ### Congruence for the composite regex value operators -/

private theorem rel_re_plus_congr {b d : SmtValue}
    (h : RuleProofs.smt_value_rel b d) :
    RuleProofs.smt_value_rel (__smtx_model_eval_re_plus b)
      (__smtx_model_eval_re_plus d) :=
  CongSupport.smt_value_rel_re_concat_congr h
    (CongSupport.smt_value_rel_re_mult_congr h)

private theorem rel_re_opt_congr {b d : SmtValue}
    (h : RuleProofs.smt_value_rel b d) :
    RuleProofs.smt_value_rel (__smtx_model_eval_re_opt b)
      (__smtx_model_eval_re_opt d) :=
  CongSupport.smt_value_rel_re_union_congr h (RuleProofs.smt_value_rel_refl _)

private theorem rel_re_exp_rec_congr :
    ∀ (n : native_Nat) {b d : SmtValue},
      RuleProofs.smt_value_rel b d ->
      RuleProofs.smt_value_rel (__smtx_re_exp_rec n b)
        (__smtx_re_exp_rec n d)
  | 0, b, d, h => RuleProofs.smt_value_rel_refl _
  | (n+1), b, d, h =>
      CongSupport.smt_value_rel_re_concat_congr
        (rel_re_exp_rec_congr n h) h

private theorem rel_re_exp_congr {v b d : SmtValue}
    (h : RuleProofs.smt_value_rel b d) :
    RuleProofs.smt_value_rel (__smtx_model_eval_re_exp v b)
      (__smtx_model_eval_re_exp v d) := by
  rcases CongSupport.smt_value_rel_cases h with rfl | ⟨r, r', rfl, rfl⟩
  · exact RuleProofs.smt_value_rel_refl _
  · cases v with
    | Numeral n0 => exact rel_re_exp_rec_congr (native_int_to_nat n0) h
    | _ => exact RuleProofs.smt_value_rel_refl _

private theorem rel_re_loop_rec_congr :
    ∀ (n : native_Nat) (v1 v2 : SmtValue) {b d : SmtValue},
      RuleProofs.smt_value_rel b d ->
      RuleProofs.smt_value_rel (__smtx_re_loop_rec n v1 v2 b)
        (__smtx_re_loop_rec n v1 v2 d)
  | 0, v1, v2, b, d, h => by
      cases v2 with
      | Numeral m => exact rel_re_exp_congr h
      | _ => exact RuleProofs.smt_value_rel_refl _
  | (n+1), v1, v2, b, d, h => by
      cases v2 with
      | Numeral m =>
          exact CongSupport.smt_value_rel_re_union_congr
            (rel_re_loop_rec_congr n v1
              (SmtValue.Numeral (native_zplus m (native_zneg 1))) h)
            (rel_re_exp_congr h)
      | _ => exact RuleProofs.smt_value_rel_refl _

private theorem rel_re_loop_congr {v1 v2 b d : SmtValue}
    (h : RuleProofs.smt_value_rel b d) :
    RuleProofs.smt_value_rel (__smtx_model_eval_re_loop v1 v2 b)
      (__smtx_model_eval_re_loop v1 v2 d) := by
  rcases CongSupport.smt_value_rel_cases h with rfl | ⟨r, r', rfl, rfl⟩
  · exact RuleProofs.smt_value_rel_refl _
  · cases v1 with
    | Numeral a =>
        cases v2 with
        | Numeral c =>
            exact CongSupport.smt_value_rel_ite_congr _ _ _ _ _ _
              (RuleProofs.smt_value_rel_refl _)
              (RuleProofs.smt_value_rel_refl _)
              (rel_re_loop_rec_congr _ _ _ h)
        | _ => exact RuleProofs.smt_value_rel_refl _
    | _ => exact RuleProofs.smt_value_rel_refl _

private theorem rel_strings_occur_index_re_congr {a b b' c : SmtValue}
    (hATy : __smtx_typeof_value a = SmtType.Seq SmtType.Char)
    (h : RuleProofs.smt_value_rel b b') :
    RuleProofs.smt_value_rel
      (__smtx_model_eval__at_strings_occur_index_re a b c)
      (__smtx_model_eval__at_strings_occur_index_re a b' c) := by
  rcases CongSupport.smt_value_rel_cases h with rfl | ⟨r, r', rfl, rfl⟩
  · exact RuleProofs.smt_value_rel_refl _
  · apply rel_of_eq
    have hExt := CongSupport.reglan_valid_ext_of_rel h
    cases a with
    | Seq s =>
        have hSTy :
            __smtx_typeof_seq_value s = SmtType.Seq SmtType.Char := by
          simpa [__smtx_typeof_value] using hATy
        have hUnpack :=
          native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSTy
        have hValid :=
          native_unpack_string_valid_of_typeof_seq_char hSTy
        cases c with
        | Numeral i =>
            change
              SmtValue.Numeral
                  (native_str_occur_index_re (native_unpack_seq s) r i) =
                SmtValue.Numeral
                  (native_str_occur_index_re (native_unpack_seq s) r' i)
            rw [hUnpack]
            rw [CongSupport.native_str_occur_index_re_congr
              (native_unpack_string s) r r' i hValid hExt]
        | _ => rfl
    | _ => rfl

/-! ### The `Apply` case -/

private theorem apply_rel {M N : SmtModel}
    (hM : model_wf M) (hN : model_wf N)
    (hGlobals : model_agrees_on_globals M N)
    {f x : SmtTerm}
    (hTy : term_has_non_none_type (SmtTerm.Apply f x))
    (hF : term_has_non_none_type f ->
      RuleProofs.smt_value_rel (__smtx_model_eval M f) (__smtx_model_eval N f))
    (hX : term_has_non_none_type x ->
      RuleProofs.smt_value_rel (__smtx_model_eval M x) (__smtx_model_eval N x))
    (hXeq : term_has_non_none_type x -> __smtx_typeof x ≠ SmtType.RegLan ->
      __smtx_model_eval M x = __smtx_model_eval N x) :
    RuleProofs.smt_value_rel (__smtx_model_eval M (SmtTerm.Apply f x))
      (__smtx_model_eval N (SmtTerm.Apply f x)) := by
  cases f with
  | DtSel s d i j =>
      have hInner : __smtx_typeof_apply
          (SmtType.FunType (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j))
          (__smtx_typeof x) ≠ SmtType.None := by
        have h1 : __smtx_typeof_guard_wf (__smtx_ret_typeof_sel s d i j)
            (__smtx_typeof_apply
              (SmtType.FunType (SmtType.Datatype s d)
                (__smtx_ret_typeof_sel s d i j))
              (__smtx_typeof x)) ≠ SmtType.None := hTy
        unfold __smtx_typeof_guard_wf at h1
        intro hEq
        rw [hEq] at h1
        cases hw : __smtx_type_wf (__smtx_ret_typeof_sel s d i j) <;>
          rw [hw] at h1 <;> simp [native_ite] at h1
      have hXTy : __smtx_typeof x = SmtType.Datatype s d := by
        have h2 := hInner
        unfold __smtx_typeof_apply at h2
        obtain ⟨_, hIte⟩ := guard_ne_none_parts h2
        exact (teq_eq (ite_cond_true_of_ne_none hIte)).symm
      have e := hXeq (tnn_of_typeof_eq hXTy (by simp)) (by rw [hXTy]; simp)
      simp only [__smtx_model_eval]
      rw [e, smtx_model_eval_dt_sel_eq_of_globals hGlobals]
      exact RuleProofs.smt_value_rel_refl _
  | DtTester s d i =>
      have hInner : __smtx_typeof_apply
          (SmtType.FunType (SmtType.Datatype s d) SmtType.Bool)
          (__smtx_typeof x) ≠ SmtType.None := by
        have h1 : __smtx_typeof_guard
            (__smtx_typeof_dt_cons_rec (SmtType.Datatype s d)
              (__smtx_dt_resolve (__smtx_dd_lookup s d) d) i)
            (__smtx_typeof_apply
              (SmtType.FunType (SmtType.Datatype s d) SmtType.Bool)
              (__smtx_typeof x)) ≠ SmtType.None := hTy
        exact guard_inner_ne_none h1
      have hXTy : __smtx_typeof x = SmtType.Datatype s d := by
        have h2 := hInner
        unfold __smtx_typeof_apply at h2
        obtain ⟨_, hIte⟩ := guard_ne_none_parts h2
        exact (teq_eq (ite_cond_true_of_ne_none hIte)).symm
      have e := hXeq (tnn_of_typeof_eq hXTy (by simp)) (by rw [hXTy]; simp)
      simp only [__smtx_model_eval]
      rw [e]
      exact RuleProofs.smt_value_rel_refl _
  | _ =>
      obtain ⟨hFN, hXN⟩ := apply_arg_types hTy
      simp only [__smtx_model_eval]
      exact CongSupport.smt_value_rel_model_eval_apply_of_rel_across_models
        M N hM hN hGlobals _ _ _ _ hTy rfl rfl (hF hFN) (hX hXN)

/-! ## The master rel-coincidence walk -/

/-- Two total-typed models agreeing on globals with pointwise rel-related
variable assignments evaluate every non-`None`-typed term to rel-related
values. -/
theorem smt_model_eval_rel_of_var_rel_lt
    (n : Nat) {t : SmtTerm} {M N : SmtModel}
    (hLt : sizeOf t < n)
    (hM : model_wf M) (hN : model_wf N)
    (hGlobals : model_agrees_on_globals M N)
    (hVars : ModelVarRel M N)
    (hTy : term_has_non_none_type t) :
    RuleProofs.smt_value_rel (__smtx_model_eval M t) (__smtx_model_eval N t) := by
  cases n with
  | zero => omega
  | succ n =>
      let hRec :
          ∀ {u : SmtTerm} {M' N' : SmtModel},
            sizeOf u < sizeOf t ->
              model_wf M' -> model_wf N' ->
              model_agrees_on_globals M' N' -> ModelVarRel M' N' ->
              term_has_non_none_type u ->
              RuleProofs.smt_value_rel (__smtx_model_eval M' u)
                (__smtx_model_eval N' u) :=
        fun {u M' N'} hULt hM' hN' hG' hV' hTy' =>
          smt_model_eval_rel_of_var_rel_lt
            n (t := u) (M := M') (N := N') (by omega) hM' hN' hG' hV' hTy'
      let ih :
          ∀ (u : SmtTerm), sizeOf u < sizeOf t ->
            term_has_non_none_type u ->
            RuleProofs.smt_value_rel (__smtx_model_eval M u)
              (__smtx_model_eval N u) :=
        fun u hU hTy' => hRec hU hM hN hGlobals hVars hTy'
      let ihEq :
          ∀ (u : SmtTerm), sizeOf u < sizeOf t ->
            term_has_non_none_type u ->
            __smtx_typeof u ≠ SmtType.RegLan ->
            __smtx_model_eval M u = __smtx_model_eval N u :=
        fun u hU hTy' hNe =>
          eval_eq_of_rel_of_ty_ne_reglan hM hN (ih u hU hTy') hTy' hNe
      cases t
      case None =>
        exact RuleProofs.smt_value_rel_refl _
      case Boolean b =>
        exact RuleProofs.smt_value_rel_refl _
      case Numeral n0 =>
        exact RuleProofs.smt_value_rel_refl _
      case Rational q =>
        exact RuleProofs.smt_value_rel_refl _
      case String s0 =>
        exact RuleProofs.smt_value_rel_refl _
      case Binary w n0 =>
        exact RuleProofs.smt_value_rel_refl _
      case DtCons s0 d0 i0 =>
        exact RuleProofs.smt_value_rel_refl _
      case DtSel s0 d0 i0 j0 =>
        exact RuleProofs.smt_value_rel_refl _
      case DtTester s0 d0 i0 =>
        exact RuleProofs.smt_value_rel_refl _
      case re_allchar =>
        exact RuleProofs.smt_value_rel_refl _
      case re_none =>
        exact RuleProofs.smt_value_rel_refl _
      case re_all =>
        exact RuleProofs.smt_value_rel_refl _
      case seq_empty T0 =>
        exact RuleProofs.smt_value_rel_refl _
      case set_empty T0 =>
        exact RuleProofs.smt_value_rel_refl _
      case to_int x1 =>
        have hA := guard1_arg hTy
        have e1 := ihEq x1 (by simp) (tnn_of_typeof_eq hA (by simp)) (by rw [hA]; simp)
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case is_int x1 =>
        have hA := guard1_arg hTy
        have e1 := ihEq x1 (by simp) (tnn_of_typeof_eq hA (by simp)) (by rw [hA]; simp)
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case int_pow2 x1 =>
        have hA := guard1_arg hTy
        have e1 := ihEq x1 (by simp) (tnn_of_typeof_eq hA (by simp)) (by rw [hA]; simp)
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case int_log2 x1 =>
        have hA := guard1_arg hTy
        have e1 := ihEq x1 (by simp) (tnn_of_typeof_eq hA (by simp)) (by rw [hA]; simp)
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case str_to_lower x1 =>
        have hA := guard1_arg hTy
        have e1 := ihEq x1 (by simp) (tnn_of_typeof_eq hA (by simp)) (by rw [hA]; simp)
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case str_to_upper x1 =>
        have hA := guard1_arg hTy
        have e1 := ihEq x1 (by simp) (tnn_of_typeof_eq hA (by simp)) (by rw [hA]; simp)
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case str_to_code x1 =>
        have hA := guard1_arg hTy
        have e1 := ihEq x1 (by simp) (tnn_of_typeof_eq hA (by simp)) (by rw [hA]; simp)
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case str_from_code x1 =>
        have hA := guard1_arg hTy
        have e1 := ihEq x1 (by simp) (tnn_of_typeof_eq hA (by simp)) (by rw [hA]; simp)
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case str_is_digit x1 =>
        have hA := guard1_arg hTy
        have e1 := ihEq x1 (by simp) (tnn_of_typeof_eq hA (by simp)) (by rw [hA]; simp)
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case str_to_int x1 =>
        have hA := guard1_arg hTy
        have e1 := ihEq x1 (by simp) (tnn_of_typeof_eq hA (by simp)) (by rw [hA]; simp)
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case str_from_int x1 =>
        have hA := guard1_arg hTy
        have e1 := ihEq x1 (by simp) (tnn_of_typeof_eq hA (by simp)) (by rw [hA]; simp)
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case str_to_re x1 =>
        have hA := guard1_arg hTy
        have e1 := ihEq x1 (by simp) (tnn_of_typeof_eq hA (by simp)) (by rw [hA]; simp)
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case not x1 =>
        have hA := guard1_arg hTy
        have e1 := ihEq x1 (by simp) (tnn_of_typeof_eq hA (by simp)) (by rw [hA]; simp)
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case to_real x1 =>
        have hA := to_real_arg hTy
        have e1 := ihEq x1 (by simp) hA.1 hA.2
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case abs x1 =>
        have hA := arith1_arg hTy
        have e1 := ihEq x1 (by simp) hA.1 hA.2
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case uneg x1 =>
        have hA := arith1_arg hTy
        have e1 := ihEq x1 (by simp) hA.1 hA.2
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case bvnot x1 =>
        have hA := bv1_arg hTy
        have e1 := ihEq x1 (by simp) hA.1 hA.2
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case bvneg x1 =>
        have hA := bv1_arg hTy
        have e1 := ihEq x1 (by simp) hA.1 hA.2
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case bvnego x1 =>
        have hA := bv1_ret_arg hTy
        have e1 := ihEq x1 (by simp) hA.1 hA.2
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case ubv_to_int x1 =>
        have hA := bv1_ret_arg hTy
        have e1 := ihEq x1 (by simp) hA.1 hA.2
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case sbv_to_int x1 =>
        have hA := bv1_ret_arg hTy
        have e1 := ihEq x1 (by simp) hA.1 hA.2
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case str_len x1 =>
        have hA := seq1_ret_arg hTy
        have e1 := ihEq x1 (by simp) hA.1 hA.2
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case str_rev x1 =>
        have hA := seq1_arg hTy
        have e1 := ihEq x1 (by simp) hA.1 hA.2
        simp only [__smtx_model_eval]
        rw [e1]
        exact RuleProofs.smt_value_rel_refl _
      case plus x1 x2 =>
        have hA := arith2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case neg x1 x2 =>
        have hA := arith2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case mult x1 x2 =>
        have hA := arith2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case lt x1 x2 =>
        have hA := arith2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case leq x1 x2 =>
        have hA := arith2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case gt x1 x2 =>
        have hA := arith2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case geq x1 x2 =>
        have hA := arith2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case qdiv_total x1 x2 =>
        have hA := arith2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case divisible x1 x2 =>
        have hA := guard2_args hTy
        have e1 := ihEq x1 (by simp; omega) (tnn_of_typeof_eq hA.1 (by simp)) (by rw [hA.1]; simp)
        have e2 := ihEq x2 (by simp; omega) (tnn_of_typeof_eq hA.2 (by simp)) (by rw [hA.2]; simp)
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case div_total x1 x2 =>
        have hA := guard2_args hTy
        have e1 := ihEq x1 (by simp; omega) (tnn_of_typeof_eq hA.1 (by simp)) (by rw [hA.1]; simp)
        have e2 := ihEq x2 (by simp; omega) (tnn_of_typeof_eq hA.2 (by simp)) (by rw [hA.2]; simp)
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case mod_total x1 x2 =>
        have hA := guard2_args hTy
        have e1 := ihEq x1 (by simp; omega) (tnn_of_typeof_eq hA.1 (by simp)) (by rw [hA.1]; simp)
        have e2 := ihEq x2 (by simp; omega) (tnn_of_typeof_eq hA.2 (by simp)) (by rw [hA.2]; simp)
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case str_lt x1 x2 =>
        have hA := guard2_args hTy
        have e1 := ihEq x1 (by simp; omega) (tnn_of_typeof_eq hA.1 (by simp)) (by rw [hA.1]; simp)
        have e2 := ihEq x2 (by simp; omega) (tnn_of_typeof_eq hA.2 (by simp)) (by rw [hA.2]; simp)
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case str_leq x1 x2 =>
        have hA := guard2_args hTy
        have e1 := ihEq x1 (by simp; omega) (tnn_of_typeof_eq hA.1 (by simp)) (by rw [hA.1]; simp)
        have e2 := ihEq x2 (by simp; omega) (tnn_of_typeof_eq hA.2 (by simp)) (by rw [hA.2]; simp)
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case or x1 x2 =>
        have hA := guard2_args hTy
        have e1 := ihEq x1 (by simp; omega) (tnn_of_typeof_eq hA.1 (by simp)) (by rw [hA.1]; simp)
        have e2 := ihEq x2 (by simp; omega) (tnn_of_typeof_eq hA.2 (by simp)) (by rw [hA.2]; simp)
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case and x1 x2 =>
        have hA := guard2_args hTy
        have e1 := ihEq x1 (by simp; omega) (tnn_of_typeof_eq hA.1 (by simp)) (by rw [hA.1]; simp)
        have e2 := ihEq x2 (by simp; omega) (tnn_of_typeof_eq hA.2 (by simp)) (by rw [hA.2]; simp)
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case imp x1 x2 =>
        have hA := guard2_args hTy
        have e1 := ihEq x1 (by simp; omega) (tnn_of_typeof_eq hA.1 (by simp)) (by rw [hA.1]; simp)
        have e2 := ihEq x2 (by simp; omega) (tnn_of_typeof_eq hA.2 (by simp)) (by rw [hA.2]; simp)
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case xor x1 x2 =>
        have hA := guard2_args hTy
        have e1 := ihEq x1 (by simp; omega) (tnn_of_typeof_eq hA.1 (by simp)) (by rw [hA.1]; simp)
        have e2 := ihEq x2 (by simp; omega) (tnn_of_typeof_eq hA.2 (by simp)) (by rw [hA.2]; simp)
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case concat x1 x2 =>
        have hA := concat_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case str_concat x1 x2 =>
        have hA := seq2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case str_contains x1 x2 =>
        have hA := seq2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case str_prefixof x1 x2 =>
        have hA := seq2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case str_suffixof x1 x2 =>
        have hA := seq2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case set_union x1 x2 =>
        have hA := sets2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case set_inter x1 x2 =>
        have hA := sets2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case set_minus x1 x2 =>
        have hA := sets2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case set_subset x1 x2 =>
        have hA := sets2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case map_diff x1 x2 =>
        have hA := map_diff_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case seq_diff x1 x2 =>
        have hA := seq_diff_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case str_at x1 x2 =>
        have hA := str_at_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) (tnn_of_typeof_eq hA.2 (by simp)) (by rw [hA.2]; simp)
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvand x1 x2 =>
        have hA := bv2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvor x1 x2 =>
        have hA := bv2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvnand x1 x2 =>
        have hA := bv2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvnor x1 x2 =>
        have hA := bv2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvxor x1 x2 =>
        have hA := bv2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvxnor x1 x2 =>
        have hA := bv2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvadd x1 x2 =>
        have hA := bv2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvmul x1 x2 =>
        have hA := bv2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvudiv x1 x2 =>
        have hA := bv2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvurem x1 x2 =>
        have hA := bv2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvsub x1 x2 =>
        have hA := bv2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvsdiv x1 x2 =>
        have hA := bv2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvsrem x1 x2 =>
        have hA := bv2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvsmod x1 x2 =>
        have hA := bv2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvshl x1 x2 =>
        have hA := bv2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvlshr x1 x2 =>
        have hA := bv2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvashr x1 x2 =>
        have hA := bv2_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvcomp x1 x2 =>
        have hA := bv2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvult x1 x2 =>
        have hA := bv2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvule x1 x2 =>
        have hA := bv2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvugt x1 x2 =>
        have hA := bv2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvuge x1 x2 =>
        have hA := bv2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvslt x1 x2 =>
        have hA := bv2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvsle x1 x2 =>
        have hA := bv2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvsgt x1 x2 =>
        have hA := bv2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvsge x1 x2 =>
        have hA := bv2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvuaddo x1 x2 =>
        have hA := bv2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvsaddo x1 x2 =>
        have hA := bv2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvumulo x1 x2 =>
        have hA := bv2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvsmulo x1 x2 =>
        have hA := bv2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvusubo x1 x2 =>
        have hA := bv2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvssubo x1 x2 =>
        have hA := bv2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case bvsdivo x1 x2 =>
        have hA := bv2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case str_substr x1 x2 x3 =>
        have hA := str_substr_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) (tnn_of_typeof_eq hA.2.1 (by simp)) (by rw [hA.2.1]; simp)
        have e3 := ihEq x3 (by simp; omega) (tnn_of_typeof_eq hA.2.2 (by simp)) (by rw [hA.2.2]; simp)
        simp only [__smtx_model_eval]
        rw [e1, e2, e3]
        exact RuleProofs.smt_value_rel_refl _
      case str_replace x1 x2 x3 =>
        have hA := seq3_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1.1 hA.2.1.2
        have e3 := ihEq x3 (by simp; omega) hA.2.2.1 hA.2.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2, e3]
        exact RuleProofs.smt_value_rel_refl _
      case str_replace_all x1 x2 x3 =>
        have hA := seq3_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1.1 hA.2.1.2
        have e3 := ihEq x3 (by simp; omega) hA.2.2.1 hA.2.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2, e3]
        exact RuleProofs.smt_value_rel_refl _
      case str_indexof x1 x2 x3 =>
        have hA := str_indexof_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1.1 hA.2.1.2
        have e3 := ihEq x3 (by simp; omega) (tnn_of_typeof_eq hA.2.2 (by simp)) (by rw [hA.2.2]; simp)
        simp only [__smtx_model_eval]
        rw [e1, e2, e3]
        exact RuleProofs.smt_value_rel_refl _
      case _at_strings_occur_index x1 x2 x3 =>
        have hA := str_indexof_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1.1 hA.2.1.2
        have e3 := ihEq x3 (by simp; omega)
          (tnn_of_typeof_eq hA.2.2 (by simp)) (by rw [hA.2.2]; simp)
        simp only [__smtx_model_eval]
        rw [e1, e2, e3]
        exact RuleProofs.smt_value_rel_refl _
      case str_update x1 x2 x3 =>
        have hA := str_update_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) (tnn_of_typeof_eq hA.2.1 (by simp)) (by rw [hA.2.1]; simp)
        have e3 := ihEq x3 (by simp; omega) hA.2.2.1 hA.2.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2, e3]
        exact RuleProofs.smt_value_rel_refl _
      case re_range x1 x2 =>
        have hA := guard2_args hTy
        have e1 := ihEq x1 (by simp; omega) (tnn_of_typeof_eq hA.1 (by simp)) (by rw [hA.1]; simp)
        have e2 := ihEq x2 (by simp; omega) (tnn_of_typeof_eq hA.2 (by simp)) (by rw [hA.2]; simp)
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case re_mult x1 =>
        have hA := guard1_arg hTy
        simp only [__smtx_model_eval]
        exact CongSupport.smt_value_rel_re_mult_congr
          (ih x1 (by simp) (tnn_of_typeof_eq hA (by simp)))
      case re_comp x1 =>
        have hA := guard1_arg hTy
        simp only [__smtx_model_eval]
        exact CongSupport.smt_value_rel_re_comp_congr
          (ih x1 (by simp) (tnn_of_typeof_eq hA (by simp)))
      case re_plus x1 =>
        have hA := guard1_arg hTy
        simp only [__smtx_model_eval]
        exact rel_re_plus_congr
          (ih x1 (by simp) (tnn_of_typeof_eq hA (by simp)))
      case re_opt x1 =>
        have hA := guard1_arg hTy
        simp only [__smtx_model_eval]
        exact rel_re_opt_congr
          (ih x1 (by simp) (tnn_of_typeof_eq hA (by simp)))
      case re_concat x1 x2 =>
        have hA := guard2_args hTy
        simp only [__smtx_model_eval]
        exact CongSupport.smt_value_rel_re_concat_congr
          (ih x1 (by simp; omega) (tnn_of_typeof_eq hA.1 (by simp)))
          (ih x2 (by simp; omega) (tnn_of_typeof_eq hA.2 (by simp)))
      case re_inter x1 x2 =>
        have hA := guard2_args hTy
        simp only [__smtx_model_eval]
        exact CongSupport.smt_value_rel_re_inter_congr
          (ih x1 (by simp; omega) (tnn_of_typeof_eq hA.1 (by simp)))
          (ih x2 (by simp; omega) (tnn_of_typeof_eq hA.2 (by simp)))
      case re_union x1 x2 =>
        have hA := guard2_args hTy
        simp only [__smtx_model_eval]
        exact CongSupport.smt_value_rel_re_union_congr
          (ih x1 (by simp; omega) (tnn_of_typeof_eq hA.1 (by simp)))
          (ih x2 (by simp; omega) (tnn_of_typeof_eq hA.2 (by simp)))
      case re_diff x1 x2 =>
        have hA := guard2_args hTy
        simp only [__smtx_model_eval]
        exact CongSupport.smt_value_rel_re_diff_congr
          (ih x1 (by simp; omega) (tnn_of_typeof_eq hA.1 (by simp)))
          (ih x2 (by simp; omega) (tnn_of_typeof_eq hA.2 (by simp)))
      case str_in_re x1 x2 =>
        have hA := guard2_args hTy
        simp only [__smtx_model_eval]
        exact CongSupport.smt_value_rel_str_in_re_congr
          (by
            have hp := smt_model_eval_preserves_type_of_non_none M hM x1
              (tnn_of_typeof_eq hA.1 (by simp))
            rw [hA.1] at hp
            exact hp)
          (ih x1 (by simp; omega) (tnn_of_typeof_eq hA.1 (by simp)))
          (ih x2 (by simp; omega) (tnn_of_typeof_eq hA.2 (by simp)))
      case str_replace_re x1 x2 x3 =>
        have hA := guard3_args hTy
        simp only [__smtx_model_eval]
        exact CongSupport.smt_value_rel_str_replace_re_congr
          (by
            have hp := smt_model_eval_preserves_type_of_non_none M hM x1
              (tnn_of_typeof_eq hA.1 (by simp))
            rw [hA.1] at hp
            exact hp)
          (by
            have hp := smt_model_eval_preserves_type_of_non_none M hM x3
              (tnn_of_typeof_eq hA.2.2 (by simp))
            rw [hA.2.2] at hp
            exact hp)
          (ih x1 (by simp; omega) (tnn_of_typeof_eq hA.1 (by simp)))
          (ih x2 (by simp; omega) (tnn_of_typeof_eq hA.2.1 (by simp)))
          (ih x3 (by simp; omega) (tnn_of_typeof_eq hA.2.2 (by simp)))
      case str_replace_re_all x1 x2 x3 =>
        have hA := guard3_args hTy
        simp only [__smtx_model_eval]
        exact CongSupport.smt_value_rel_str_replace_re_all_congr
          (by
            have hp := smt_model_eval_preserves_type_of_non_none M hM x1
              (tnn_of_typeof_eq hA.1 (by simp))
            rw [hA.1] at hp
            exact hp)
          (by
            have hp := smt_model_eval_preserves_type_of_non_none M hM x3
              (tnn_of_typeof_eq hA.2.2 (by simp))
            rw [hA.2.2] at hp
            exact hp)
          (ih x1 (by simp; omega) (tnn_of_typeof_eq hA.1 (by simp)))
          (ih x2 (by simp; omega) (tnn_of_typeof_eq hA.2.1 (by simp)))
          (ih x3 (by simp; omega) (tnn_of_typeof_eq hA.2.2 (by simp)))
      case str_indexof_re x1 x2 x3 =>
        have hA := guard3_args hTy
        simp only [__smtx_model_eval]
        exact CongSupport.smt_value_rel_str_indexof_re_congr
          (by
            have hp := smt_model_eval_preserves_type_of_non_none M hM x1
              (tnn_of_typeof_eq hA.1 (by simp))
            rw [hA.1] at hp
            exact hp)
          (ih x1 (by simp; omega) (tnn_of_typeof_eq hA.1 (by simp)))
          (ih x2 (by simp; omega) (tnn_of_typeof_eq hA.2.1 (by simp)))
          (ih x3 (by simp; omega) (tnn_of_typeof_eq hA.2.2 (by simp)))
      case _at_strings_occur_index_re x1 x2 x3 =>
        have hA := guard3_args hTy
        have hX1Tnn : term_has_non_none_type x1 :=
          tnn_of_typeof_eq hA.1 (by simp)
        have e1 := ihEq x1 (by simp; omega)
          hX1Tnn (by rw [hA.1]; simp)
        have e3 := ihEq x3 (by simp; omega)
          (tnn_of_typeof_eq hA.2.2 (by simp)) (by rw [hA.2.2]; simp)
        have hX1ValTy :
            __smtx_typeof_value (__smtx_model_eval N x1) =
              SmtType.Seq SmtType.Char := by
          rw [smt_model_eval_preserves_type_of_non_none N hN x1 hX1Tnn,
            hA.1]
        simp only [__smtx_model_eval]
        rw [e1, e3]
        exact rel_strings_occur_index_re_congr
          hX1ValTy
          (ih x2 (by simp; omega) (tnn_of_typeof_eq hA.2.1 (by simp)))
      case str_indexof_re_split x1 x2 x3 =>
        have hA := guard3_args hTy
        simp only [__smtx_model_eval]
        exact CongSupport.smt_value_rel_str_indexof_re_split_congr
          (by
            have hp := smt_model_eval_preserves_type_of_non_none M hM x1
              (tnn_of_typeof_eq hA.1 (by simp))
            rw [hA.1] at hp
            exact hp)
          (ih x1 (by simp; omega) (tnn_of_typeof_eq hA.1 (by simp)))
          (ih x2 (by simp; omega) (tnn_of_typeof_eq hA.2.1 (by simp)))
          (ih x3 (by simp; omega) (tnn_of_typeof_eq hA.2.2 (by simp)))

      case Var s0 T0 =>
        exact hVars s0 T0
      case UConst s0 T0 =>
        exact rel_of_eq (hGlobals.1 s0 T0)
      case _at_purify x1 =>
        exact ih x1 (by simp) hTy
      case Apply f x1 =>
        exact apply_rel hM hN hGlobals hTy
          (fun hfn => ih f (by simp; omega) hfn)
          (fun hxn => ih x1 (by simp; omega) hxn)
          (fun hxn hne => ihEq x1 (by simp; omega) hxn hne)
      case div x1 x2 =>
        have hA := guard2_args hTy
        have e1 := ihEq x1 (by simp; omega)
          (tnn_of_typeof_eq hA.1 (by simp)) (by rw [hA.1]; simp)
        have e2 := ihEq x2 (by simp; omega)
          (tnn_of_typeof_eq hA.2 (by simp)) (by rw [hA.2]; simp)
        simp only [__smtx_model_eval]
        rw [e1, e2, hGlobals.1, smtx_model_eval_apply_eq_of_globals hGlobals]
        exact RuleProofs.smt_value_rel_refl _
      case mod x1 x2 =>
        have hA := guard2_args hTy
        have e1 := ihEq x1 (by simp; omega)
          (tnn_of_typeof_eq hA.1 (by simp)) (by rw [hA.1]; simp)
        have e2 := ihEq x2 (by simp; omega)
          (tnn_of_typeof_eq hA.2 (by simp)) (by rw [hA.2]; simp)
        simp only [__smtx_model_eval]
        rw [e1, e2, hGlobals.1, smtx_model_eval_apply_eq_of_globals hGlobals]
        exact RuleProofs.smt_value_rel_refl _
      case qdiv x1 x2 =>
        have hA := arith2_ret_args hTy
        have e1 := ihEq x1 (by simp; omega) hA.1.1 hA.1.2
        have e2 := ihEq x2 (by simp; omega) hA.2.1 hA.2.2
        simp only [__smtx_model_eval]
        rw [e1, e2, hGlobals.1, smtx_model_eval_apply_eq_of_globals hGlobals]
        exact RuleProofs.smt_value_rel_refl _
      case select x1 x2 =>
        obtain ⟨K, V, hMap, hKey⟩ := select_types hTy
        have hClean : cleanType (SmtType.Map K V) := by
          have h1 := typeof_cleanOrNone x1
          rw [hMap] at h1
          exact h1.resolve_left (by simp)
        have e1 := ihEq x1 (by simp; omega)
          (tnn_of_typeof_eq hMap (by simp)) (by rw [hMap]; simp)
        have e2 := ihEq x2 (by simp; omega)
          (tnn_of_typeof_eq hKey hClean.1.1) (by rw [hKey]; exact hClean.1.2.1)
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case store x1 x2 x3 =>
        obtain ⟨K, V, hMap, hKey, hVal⟩ := store_types hTy
        have hClean : cleanType (SmtType.Map K V) := by
          have h1 := typeof_cleanOrNone x1
          rw [hMap] at h1
          exact h1.resolve_left (by simp)
        have e1 := ihEq x1 (by simp; omega)
          (tnn_of_typeof_eq hMap (by simp)) (by rw [hMap]; simp)
        have e2 := ihEq x2 (by simp; omega)
          (tnn_of_typeof_eq hKey hClean.1.1) (by rw [hKey]; exact hClean.1.2.1)
        have e3 := ihEq x3 (by simp; omega)
          (tnn_of_typeof_eq hVal hClean.2.1) (by rw [hVal]; exact hClean.2.2.1)
        simp only [__smtx_model_eval]
        rw [e1, e2, e3]
        exact RuleProofs.smt_value_rel_refl _
      case set_member x1 x2 =>
        obtain ⟨E, hSet, hElem⟩ := set_member_types hTy
        have hClean : cleanType (SmtType.Set E) := by
          have h2 := typeof_cleanOrNone x2
          rw [hSet] at h2
          exact h2.resolve_left (by simp)
        have e1 := ihEq x1 (by simp; omega)
          (tnn_of_typeof_eq hElem hClean.1) (by rw [hElem]; exact hClean.2.1)
        have e2 := ihEq x2 (by simp; omega)
          (tnn_of_typeof_eq hSet (by simp)) (by rw [hSet]; simp)
        simp only [__smtx_model_eval]
        rw [e1, e2]
        exact RuleProofs.smt_value_rel_refl _
      case seq_nth x1 x2 =>
        obtain ⟨hA, hB⟩ := seq_nth_types hTy
        have e1 := ihEq x1 (by simp; omega) hA.1 hA.2
        have e2 := ihEq x2 (by simp; omega)
          (tnn_of_typeof_eq hB (by simp)) (by rw [hB]; simp)
        simp only [__smtx_model_eval]
        rw [e1, e2, smtx_seq_nth_eq_of_globals hGlobals]
        exact RuleProofs.smt_value_rel_refl _
      case seq_unit x1 =>
        have hwf := guard_wf_self_types (T := SmtType.Seq (__smtx_typeof x1)) hTy
        have hClean : cleanType (SmtType.Seq (__smtx_typeof x1)) :=
          cleanType_of_wf hwf
        have e := ihEq x1 (by simp) hClean.1 hClean.2.1
        simp only [__smtx_model_eval]
        rw [e]
        exact RuleProofs.smt_value_rel_refl _
      case set_singleton x1 =>
        have hwf := guard_wf_self_types (T := SmtType.Set (__smtx_typeof x1)) hTy
        have hClean : cleanType (SmtType.Set (__smtx_typeof x1)) :=
          cleanType_of_wf hwf
        have e := ihEq x1 (by simp) hClean.1 hClean.2.1
        simp only [__smtx_model_eval]
        rw [e]
        exact RuleProofs.smt_value_rel_refl _
      case extract x1 x2 x3 =>
        obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩, hC⟩ := extract_term_args hTy
        have e3 := ihEq x3 (by simp; omega) hC.1 hC.2
        simp only [__smtx_model_eval]
        rw [e3]
        exact RuleProofs.smt_value_rel_refl _
      case «repeat» x1 x2 =>
        obtain ⟨⟨a, rfl⟩, hC⟩ := repeat_term_args hTy
        have e2 := ihEq x2 (by simp; omega) hC.1 hC.2
        simp only [__smtx_model_eval]
        rw [e2]
        exact RuleProofs.smt_value_rel_refl _
      case zero_extend x1 x2 =>
        obtain ⟨⟨a, rfl⟩, hC⟩ := zero_extend_term_args hTy
        have e2 := ihEq x2 (by simp; omega) hC.1 hC.2
        simp only [__smtx_model_eval]
        rw [e2]
        exact RuleProofs.smt_value_rel_refl _
      case sign_extend x1 x2 =>
        obtain ⟨⟨a, rfl⟩, hC⟩ := sign_extend_term_args hTy
        have e2 := ihEq x2 (by simp; omega) hC.1 hC.2
        simp only [__smtx_model_eval]
        rw [e2]
        exact RuleProofs.smt_value_rel_refl _
      case rotate_left x1 x2 =>
        obtain ⟨⟨a, rfl⟩, hC⟩ := rotate_left_term_args hTy
        have e2 := ihEq x2 (by simp; omega) hC.1 hC.2
        simp only [__smtx_model_eval]
        rw [e2]
        exact RuleProofs.smt_value_rel_refl _
      case rotate_right x1 x2 =>
        obtain ⟨⟨a, rfl⟩, hC⟩ := rotate_right_term_args hTy
        have e2 := ihEq x2 (by simp; omega) hC.1 hC.2
        simp only [__smtx_model_eval]
        rw [e2]
        exact RuleProofs.smt_value_rel_refl _
      case int_to_bv x1 x2 =>
        obtain ⟨⟨a, rfl⟩, hC⟩ := int_to_bv_term_args hTy
        have e2 := ihEq x2 (by simp; omega)
          (tnn_of_typeof_eq hC (by simp)) (by rw [hC]; simp)
        simp only [__smtx_model_eval]
        rw [e2]
        exact RuleProofs.smt_value_rel_refl _
      case re_exp x1 x2 =>
        obtain ⟨⟨a, rfl⟩, hC⟩ := re_exp_term_args hTy
        simp only [__smtx_model_eval]
        exact rel_re_exp_congr
          (ih x2 (by simp; omega) (tnn_of_typeof_eq hC (by simp)))
      case re_loop x1 x2 x3 =>
        obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩, hC⟩ := re_loop_term_args hTy
        simp only [__smtx_model_eval]
        exact rel_re_loop_congr
          (ih x3 (by simp; omega) (tnn_of_typeof_eq hC (by simp)))
      case eq x1 x2 =>
        have hA := eq_types hTy
        simp only [__smtx_model_eval]
        exact CongSupport.smt_value_rel_eq_congr _ _ _ _
          (ih x1 (by simp; omega) hA.1)
          (ih x2 (by simp; omega) (tnn_of_typeof_eq hA.2 hA.1))
      case ite x1 x2 x3 =>
        have hA := ite_types hTy
        simp only [__smtx_model_eval]
        exact CongSupport.smt_value_rel_ite_congr _ _ _ _ _ _
          (ih x1 (by simp; omega) (tnn_of_typeof_eq hA.1 (by simp)))
          (ih x2 (by simp; omega) hA.2.2)
          (ih x3 (by simp; omega) (tnn_of_typeof_eq hA.2.1 hA.2.2))
      case «exists» s0 T0 body =>
        obtain ⟨hBTy, hTWf⟩ := quant_types hTy
        have hBtnn : term_has_non_none_type body :=
          tnn_of_typeof_eq hBTy (by simp)
        simp only [__smtx_model_eval]
        apply rel_of_eq
        apply InstantiateRule.native_eval_texists_eq_of_body_eval_eq_diff_typed
        intro v hvTy hvCanon
        have hPM := model_total_typed_push hM s0 T0 v hTWf hvTy
          (by simpa [value_canonical] using hvCanon)
        have hPN := model_total_typed_push hN s0 T0 v hTWf hvTy
          (by simpa [value_canonical] using hvCanon)
        exact eval_eq_of_rel_of_ty_ne_reglan hPM hPN
          (hRec (by simp; omega) hPM hPN (globals_push_push hGlobals s0 T0 v v)
            (modelVarRel_push_same hVars s0 T0 v) hBtnn)
          hBtnn (by rw [hBTy]; simp)
      case «forall» s0 T0 body =>
        obtain ⟨hBTy, hTWf⟩ := quant_types hTy
        have hBtnn : term_has_non_none_type body :=
          tnn_of_typeof_eq hBTy (by simp)
        simp only [__smtx_model_eval]
        apply rel_of_eq
        apply InstantiateRule.native_eval_tforall_eq_of_body_eval_eq_diff_typed
        intro v hvTy hvCanon
        have hPM := model_total_typed_push hM s0 T0 v hTWf hvTy
          (by simpa [value_canonical] using hvCanon)
        have hPN := model_total_typed_push hN s0 T0 v hTWf hvTy
          (by simpa [value_canonical] using hvCanon)
        exact eval_eq_of_rel_of_ty_ne_reglan hPM hPN
          (hRec (by simp; omega) hPM hPN (globals_push_push hGlobals s0 T0 v v)
            (modelVarRel_push_same hVars s0 T0 v) hBtnn)
          hBtnn (by rw [hBTy]; simp)
      case choice s0 T0 body =>
        obtain ⟨hBTy, hTWf⟩ := choice_types hTy
        have hBtnn : term_has_non_none_type body :=
          tnn_of_typeof_eq hBTy (by simp)
        simp only [__smtx_model_eval]
        apply rel_of_eq
        apply native_eval_tchoice_eq_of_body_eval_eq_typed
        intro v hvTy hvCanon
        have hPM := model_total_typed_push hM s0 T0 v hTWf hvTy
          (by simpa [value_canonical] using hvCanon)
        have hPN := model_total_typed_push hN s0 T0 v hTWf hvTy
          (by simpa [value_canonical] using hvCanon)
        exact eval_eq_of_rel_of_ty_ne_reglan hPM hPN
          (hRec (by simp; omega) hPM hPN (globals_push_push hGlobals s0 T0 v v)
            (modelVarRel_push_same hVars s0 T0 v) hBtnn)
          hBtnn (by rw [hBTy]; simp)
      case bind s0 T0 x1 x2 =>
        obtain ⟨hX1Ty, hTWf, hX2Ne⟩ := bind_types hTy
        have hX1tnn : term_has_non_none_type x1 :=
          tnn_of_typeof_eq hX1Ty (ne_none_of_wf hTWf)
        have hRelX1 := ih x1 (by simp; omega) hX1tnn
        have hVM : __smtx_typeof_value (__smtx_model_eval M x1) = T0 := by
          rw [smt_model_eval_preserves_type_of_non_none M hM x1 hX1tnn, hX1Ty]
        have hVN : __smtx_typeof_value (__smtx_model_eval N x1) = T0 := by
          rw [smt_model_eval_preserves_type_of_non_none N hN x1 hX1tnn, hX1Ty]
        have hPM := model_total_typed_push hM s0 T0 (__smtx_model_eval M x1)
          hTWf hVM (Smtm.model_eval_canonical M hM x1 hX1tnn)
        have hPN := model_total_typed_push hN s0 T0 (__smtx_model_eval N x1)
          hTWf hVN (Smtm.model_eval_canonical N hN x1 hX1tnn)
        simp only [__smtx_model_eval]
        exact hRec (by simp; omega) hPM hPN
          (globals_push_push hGlobals s0 T0 _ _)
          (modelVarRel_push_rel hVars s0 T0 hRelX1) hX2Ne
termination_by n
decreasing_by
  all_goals omega

/-! ## Public wrappers -/

/-- The rel-coincidence theorem without the fuel argument. -/
theorem smt_model_eval_rel_of_var_rel
    {t : SmtTerm} {M N : SmtModel}
    (hM : model_wf M) (hN : model_wf N)
    (hGlobals : model_agrees_on_globals M N)
    (hVars : ModelVarRel M N)
    (hTy : term_has_non_none_type t) :
    RuleProofs.smt_value_rel (__smtx_model_eval M t) (__smtx_model_eval N t) :=
  smt_model_eval_rel_of_var_rel_lt (sizeOf t + 1) (by omega)
    hM hN hGlobals hVars hTy

/-- Truth of a non-`None`-typed term is transported between pushes of two
rel-related values: the congruence core of `quant-var-elim-eq`. -/
theorem smt_model_eval_true_push_of_rel
    (M : SmtModel) (hM : model_wf M)
    (s : native_String) (ST : SmtType) (v w : SmtValue) (u : SmtTerm)
    (hSTWf : __smtx_type_wf ST = true)
    (hvTy : __smtx_typeof_value v = ST)
    (hwTy : __smtx_typeof_value w = ST)
    (hvCanon : __smtx_value_canonical v = true)
    (hwCanon : __smtx_value_canonical w = true)
    (hRel : RuleProofs.smt_value_rel v w)
    (hTy : term_has_non_none_type u)
    (hTrue : __smtx_model_eval (native_model_push M s ST w) u =
      SmtValue.Boolean true) :
    __smtx_model_eval (native_model_push M s ST v) u =
      SmtValue.Boolean true := by
  have hPM : model_wf (native_model_push M s ST v) :=
    model_total_typed_push hM s ST v hSTWf hvTy
      (by simpa [value_canonical] using hvCanon)
  have hPN : model_wf (native_model_push M s ST w) :=
    model_total_typed_push hM s ST w hSTWf hwTy
      (by simpa [value_canonical] using hwCanon)
  have hGlobals : model_agrees_on_globals
      (native_model_push M s ST v) (native_model_push M s ST w) :=
    globals_push_push (model_agrees_on_globals_refl M) s ST v w
  have hVars : ModelVarRel
      (native_model_push M s ST v) (native_model_push M s ST w) := by
    intro s' T'
    simp only [native_model_var_lookup, native_model_push]
    split
    · exact hRel
    · exact RuleProofs.smt_value_rel_refl _
  have hRelEval := smt_model_eval_rel_of_var_rel hPM hPN hGlobals hVars hTy
  rw [hTrue] at hRelEval
  rcases CongSupport.smt_value_rel_cases hRelEval with hEq | ⟨r, r', hr, hr'⟩
  · exact hEq
  · exact absurd hr' (by simp)

end RelCoincidence
