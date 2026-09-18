module

public import Cpc.Proofs.TermCompat
import all Cpc.Proofs.TermCompat
public import Cpc.Proofs.Translation
import all Cpc.Proofs.Translation
public import Cpc.Proofs.TypePreservation
import all Cpc.Proofs.TypePreservation
import all Cpc.Proofs.TypePreservation.Common

public section

open Eo
open SmtEval
open Smtm

/-- Proof-side bridge predicate: an SMT term is Boolean-typed and evaluates to `b`.
    Formerly defined in the model; now a proof-only helper after `smt_satisfiability`
    was simplified to refer to `__smtx_model_eval` directly. -/
inductive smt_interprets : SmtModel -> SmtTerm -> Bool -> Prop
  | intro_true  (M : SmtModel) (t : SmtTerm) :
      (__smtx_typeof t) = SmtType.Bool ->
      (__smtx_model_eval M t) = (SmtValue.Boolean true) ->
      (smt_interprets M t true)
  | intro_false (M : SmtModel) (t : SmtTerm) :
      (__smtx_typeof t) = SmtType.Bool ->
      (__smtx_model_eval M t) = (SmtValue.Boolean false)->
      smt_interprets M t false

/-- Proof-side EO interpretation after the core translation bridge was flattened. -/
def eo_interprets (M : SmtModel) (t : Term) (b : Bool) : Prop :=
  smt_interprets M (__eo_to_smt t) b

namespace RuleProofs

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-!
## Arms of the generated semantics, by name

`__smtx_typeof.eq_<n>` and `__smtx_model_eval.eq_<n>` are the arm numbering the
compiler happened to emit for one signature, and the numbering shifts when the
operator set does: the `and` arm of `__smtx_model_eval` is `eq_9` in `Cpc` and
`eq_7` in `CpcMini`.  A proof in the checker layer that names a number is
reusable only by accident, so the three arms this layer needs are named here
and the numbers are not used anywhere in it.
`scripts/check-proof-modularity.sh` keeps it that way.
-/

/-- The `Boolean` arm of the generated `__smtx_typeof`. -/
theorem typeof_boolean_eq (b : Bool) :
    __smtx_typeof (SmtTerm.Boolean b) = SmtType.Bool := by
  rfl

/-- The `None` arm of the generated `__smtx_typeof`. -/
theorem typeof_none_eq :
    __smtx_typeof SmtTerm.None = SmtType.None := by
  rfl

/-- The `Boolean` arm of the generated `__smtx_model_eval`. -/
theorem model_eval_boolean_eq (M : SmtModel) (b : Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rfl

/-- The `and` arm of the generated `__smtx_model_eval`. -/
theorem model_eval_and_eq (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.and a b) =
      __smtx_model_eval_and (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rfl

/-- Simplifies EO-to-SMT translation for `true`. -/
private theorem eo_to_smt_true_eq :
    __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true := by
  rfl

/-- Simplifies EO-to-SMT translation for `stuck`. -/
private theorem eo_to_smt_stuck_eq :
    __eo_to_smt Term.Stuck = SmtTerm.None := by
  rfl

/-- Simplifies EO-to-SMT translation for `and`. -/
private theorem eo_to_smt_and_eq (A B : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) =
      SmtTerm.and (__eo_to_smt A) (__eo_to_smt B) := by
  rfl

/-- Characterizes EO interpretation in terms of the translated SMT interpretation. -/
theorem eo_interprets_iff_smt_interprets (M : SmtModel) (t : Term) (b : Bool) :
  eo_interprets M t b ↔ smt_interprets M (__eo_to_smt t) b := by
  rfl

/-- Shows that the EO term `true` is interpreted as `true` in every model. -/
theorem eo_interprets_true (M : SmtModel) :
  eo_interprets M (Term.Boolean true) true := by
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_true_eq]
  have hTy : __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool := by
    rw [typeof_boolean_eq]
  have hEval : __smtx_model_eval M (SmtTerm.Boolean true) = SmtValue.Boolean true := by
    rw [model_eval_boolean_eq]
  exact smt_interprets.intro_true M (SmtTerm.Boolean true) hTy hEval

/-- Predicate asserting that translating an EO term yields a non-`None` SMT term. -/
def eo_has_smt_translation (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) ≠ SmtType.None

/-- Predicate asserting that an EO term translates to SMT Boolean type. -/
def eo_has_bool_type (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) = SmtType.Bool

/-- Shows that `Term.Boolean true` has an SMT translation. -/
theorem eo_has_smt_translation_true :
  eo_has_smt_translation (Term.Boolean true) := by
  rw [eo_has_smt_translation, eo_to_smt_true_eq, typeof_boolean_eq]
  decide

/-- Shows that `Term.Boolean true` has translated SMT Boolean type. -/
theorem eo_has_bool_type_true :
  eo_has_bool_type (Term.Boolean true) := by
  rw [eo_has_bool_type, eo_to_smt_true_eq, typeof_boolean_eq]

/-- Derives `eo_has_bool_type` from `interprets_true`. -/
theorem eo_has_bool_type_of_interprets_true (M : SmtModel) (t : Term) :
  eo_interprets M t true ->
  eo_has_bool_type t := by
  rw [eo_interprets_iff_smt_interprets]
  intro h
  cases h with
  | intro_true hTy _ =>
      simpa [eo_has_bool_type] using hTy

/-- Derives `eo_has_bool_type` from `interprets_false`. -/
theorem eo_has_bool_type_of_interprets_false (M : SmtModel) (t : Term) :
  eo_interprets M t false ->
  eo_has_bool_type t := by
  rw [eo_interprets_iff_smt_interprets]
  intro h
  cases h with
  | intro_false hTy _ =>
      simpa [eo_has_bool_type] using hTy

/-- Shows that `eo_typeof_bool` implies `has_bool_type`. -/
theorem eo_typeof_bool_implies_has_bool_type
    (t : Term) :
  eo_has_smt_translation t ->
  __eo_typeof t = Term.Bool ->
  eo_has_bool_type t := by
  intro hTrans hTy
  exact eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    t (__eo_to_smt t) rfl hTrans hTy

/-- Derives `eo_has_smt_translation` from `has_bool_type`. -/
theorem eo_has_smt_translation_of_has_bool_type (t : Term) :
  eo_has_bool_type t ->
  eo_has_smt_translation t := by
  intro hTy
  intro hNone
  rw [eo_has_bool_type] at hTy
  rw [hNone] at hTy
  cases hTy

/-- Derives `term_ne_stuck` from `has_smt_translation`. -/
theorem term_ne_stuck_of_has_smt_translation (t : Term) :
  eo_has_smt_translation t -> t ≠ Term.Stuck := by
  intro hTy hStuck
  subst hStuck
  rw [eo_has_smt_translation, eo_to_smt_stuck_eq] at hTy
  exact hTy TranslationProofs.smtx_typeof_none

/-- Derives `eo_has_bool_type_and` from `bool_args`. -/
theorem eo_has_bool_type_and_of_bool_args (A B : Term) :
  eo_has_bool_type A ->
  eo_has_bool_type B ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) := by
  intro hA hB
  unfold eo_has_bool_type at hA hB ⊢
  rw [eo_to_smt_and_eq A B, typeof_and_eq]
  simp [hA, hB, native_ite, native_Teq]

/-- Left-projection lemma for `eo_has_bool_type_and`. -/
theorem eo_has_bool_type_and_left (A B : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) ->
  eo_has_bool_type A := by
  intro hTy
  unfold eo_has_bool_type at hTy ⊢
  rw [eo_to_smt_and_eq A B] at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
    (typeof_and_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).1

/-- Right-projection lemma for `eo_has_bool_type_and`. -/
theorem eo_has_bool_type_and_right (A B : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) ->
  eo_has_bool_type B := by
  intro hTy
  unfold eo_has_bool_type at hTy ⊢
  rw [eo_to_smt_and_eq A B] at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
    (typeof_and_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).2

/-- Derives `eo_interprets` from `bool_eval`. -/
theorem eo_interprets_of_bool_eval
    (M : SmtModel) (t : Term) (b : Bool) :
  eo_has_bool_type t ->
  __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean b ->
  eo_interprets M t b := by
  intro hTy hEval
  rw [eo_interprets_iff_smt_interprets]
  cases b with
  | false =>
      exact smt_interprets.intro_false M (__eo_to_smt t) hTy hEval
  | true =>
      exact smt_interprets.intro_true M (__eo_to_smt t) hTy hEval

/-- Derives `eo_eval_is_boolean` from `has_bool_type`. -/
theorem eo_eval_is_boolean_of_has_bool_type
    (M : SmtModel) (hM : model_wf M) (t : Term) :
  eo_has_bool_type t ->
  ∃ b : Bool, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean b := by
  intro hTy
  exact smt_model_eval_bool_is_boolean M hM (__eo_to_smt t) hTy

/-- A Boolean-typed term with no `true` interpretation is false in every model. -/
theorem smt_satisfiability_false_of_no_true (t : Term)
    (hTy : eo_has_bool_type t)
    (h : ∀ M : SmtModel, model_wf M -> ¬ eo_interprets M t true) :
    smt_satisfiability (__eo_to_smt t) false := by
  apply smt_satisfiability.intro_false
  intro M hM
  rcases eo_eval_is_boolean_of_has_bool_type M hM t hTy with ⟨b, hb⟩
  cases b with
  | true =>
      exact absurd (eo_interprets_of_bool_eval M t true hTy hb) (h M hM)
  | false =>
      exact hb

/-- Shows that an EO term cannot be interpreted as both `true` and `false`. -/
theorem eo_interprets_true_not_false (M : SmtModel) (t : Term) :
  eo_interprets M t true -> ¬ eo_interprets M t false := by
  intro hTrue hFalse
  rw [eo_interprets_iff_smt_interprets] at hTrue hFalse
  cases hTrue with
  | intro_true hTyTrue hEvalTrue =>
      cases hFalse with
      | intro_false hTyFalse hEvalFalse =>
          rw [hEvalTrue] at hEvalFalse
          cases hEvalFalse

/-- Left-projection lemma for `eo_interprets_and`. -/
theorem eo_interprets_and_left (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) true ->
  eo_interprets M A true := by
  intro h
  rw [eo_interprets_iff_smt_interprets] at h ⊢
  rw [eo_to_smt_and_eq A B] at h
  cases h with
  | intro_true hty hEval =>
      have htyA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool := by
        have hNN : term_has_non_none_type
            (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) := by
          unfold term_has_non_none_type
          rw [hty]
          simp
        exact (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
          (typeof_and_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).1
      have hEvalA : __smtx_model_eval M (__eo_to_smt A) = SmtValue.Boolean true := by
        rw [model_eval_and_eq] at hEval
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [hAeval, hBeval, __smtx_model_eval_and] at hEval
        case Boolean.Boolean a b =>
          cases a <;> cases b <;> simp [SmtEval.native_and] at hEval
          simp
      exact smt_interprets.intro_true M (__eo_to_smt A) htyA hEvalA

/-- Right-projection lemma for `eo_interprets_and`. -/
theorem eo_interprets_and_right (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) true ->
  eo_interprets M B true := by
  intro h
  rw [eo_interprets_iff_smt_interprets] at h ⊢
  rw [eo_to_smt_and_eq A B] at h
  cases h with
  | intro_true hty hEval =>
      have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
        have hNN : term_has_non_none_type
            (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) := by
          unfold term_has_non_none_type
          rw [hty]
          simp
        exact (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
          (typeof_and_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).2
      have hEvalB : __smtx_model_eval M (__eo_to_smt B) = SmtValue.Boolean true := by
        rw [model_eval_and_eq] at hEval
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [hAeval, hBeval, __smtx_model_eval_and] at hEval
        case Boolean.Boolean a b =>
          cases a <;> cases b <;> simp [SmtEval.native_and] at hEval
          simp
      exact smt_interprets.intro_true M (__eo_to_smt B) htyB hEvalB

/-- Introduction lemma for `eo_interprets_and`. -/
theorem eo_interprets_and_intro (M : SmtModel) (A B : Term) :
  eo_interprets M A true ->
  eo_interprets M B true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) true := by
  intro hA hB
  rw [eo_interprets_iff_smt_interprets] at hA hB ⊢
  rw [eo_to_smt_and_eq A B]
  cases hA with
  | intro_true htyA hEvalA =>
      cases hB with
      | intro_true htyB hEvalB =>
          apply smt_interprets.intro_true
          · rw [typeof_and_eq]
            simp [htyA, htyB, native_Teq, native_ite]
          · rw [model_eval_and_eq]
            rw [hEvalA, hEvalB]
            simp [__smtx_model_eval_and, SmtEval.native_and]

/-- Semantic equality relation on SMT values, defined by evaluation of SMT equality. -/
def smt_value_rel (v1 v2 : SmtValue) : Prop :=
  __smtx_model_eval_eq v1 v2 = SmtValue.Boolean true

/-- Semantic equality relation on SMT sequences, lifted through `SmtValue.Seq`. -/
def smt_seq_rel (s1 s2 : SmtSeq) : Prop :=
  __smtx_model_eval_eq (SmtValue.Seq s1) (SmtValue.Seq s2) = SmtValue.Boolean true

/-- Relates non-regex SMT equality evaluation to Lean equality of values. -/
private theorem smtx_model_eval_eq_true_iff_of_not_reglan_pair {v1 v2 : SmtValue}
    (hReg :
      ¬ ∃ r1 r2, v1 = SmtValue.RegLan r1 ∧ v2 = SmtValue.RegLan r2) :
    __smtx_model_eval_eq v1 v2 = SmtValue.Boolean true ↔ v1 = v2 := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_eq, native_veq] at hReg ⊢

/-- Relates SMT equality evaluation to Lean equality of sequences. -/
private theorem smtx_model_eval_seq_eq_true_iff {s1 s2 : SmtSeq} :
    __smtx_model_eval_eq (SmtValue.Seq s1) (SmtValue.Seq s2) = SmtValue.Boolean true ↔
      s1 = s2 := by
  simp [__smtx_model_eval_eq, native_veq]

/-- Stable rewrite for evaluating SMT equality terms. -/
private theorem smtx_model_eval_eq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.eq x y) =
      __smtx_model_eval_eq (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Establishes an equality relating `smtx_model_eval` and `refl_aux`. -/
private theorem smtx_model_eval_eq_refl_aux
    (v : SmtValue) :
    __smtx_model_eval_eq v v = SmtValue.Boolean true := by
  cases v <;> simp [__smtx_model_eval_eq, native_veq]

/-- Establishes an equality relating `smtx_model_eval_seq` and `refl_aux`. -/
private theorem smtx_model_eval_seq_eq_refl_aux
    (s : SmtSeq) :
    __smtx_model_eval_eq (SmtValue.Seq s) (SmtValue.Seq s) = SmtValue.Boolean true :=
  smtx_model_eval_seq_eq_true_iff.2 rfl

/-- Establishes an equality relating `smtx_model_eval` and `true_symm`. -/
private theorem smtx_model_eval_eq_true_symm
    {v1 v2 : SmtValue}
    (h : __smtx_model_eval_eq v1 v2 = SmtValue.Boolean true) :
    __smtx_model_eval_eq v2 v1 = SmtValue.Boolean true := by
  by_cases hReg :
      ∃ r1 r2, v1 = SmtValue.RegLan r1 ∧ v2 = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    change SmtValue.Boolean (native_re_ext_eq r2 r1) = SmtValue.Boolean true
    change SmtValue.Boolean (native_re_ext_eq r1 r2) = SmtValue.Boolean true at h
    simp at h ⊢
    by_cases hExt12 :
        ∀ s : native_String,
          native_string_valid s = true ->
            native_str_in_re (impl_native_string_to_values s) r1 =
              native_str_in_re (impl_native_string_to_values s) r2
    · have hExt21 :
          ∀ s : native_String,
            native_string_valid s = true ->
              native_str_in_re (impl_native_string_to_values s) r2 =
                native_str_in_re (impl_native_string_to_values s) r1 := by
        intro s hs
        exact (hExt12 s hs).symm
      simpa [hExt21]
    · simp [hExt12] at h
  · have hEq : v1 = v2 :=
      (smtx_model_eval_eq_true_iff_of_not_reglan_pair hReg).1 h
    subst v2
    exact smtx_model_eval_eq_refl_aux v1

/-- Establishes an equality relating `smtx_model_eval_seq` and `true_symm`. -/
private theorem smtx_model_eval_seq_eq_true_symm
    {s1 s2 : SmtSeq}
    (h : __smtx_model_eval_eq (SmtValue.Seq s1) (SmtValue.Seq s2) = SmtValue.Boolean true) :
    __smtx_model_eval_eq (SmtValue.Seq s2) (SmtValue.Seq s1) = SmtValue.Boolean true :=
  smtx_model_eval_seq_eq_true_iff.2 (smtx_model_eval_seq_eq_true_iff.1 h).symm

/-- Establishes an equality relating `smtx_model_eval` and `true_trans`. -/
private theorem smtx_model_eval_eq_true_trans
    {v1 v2 v3 : SmtValue}
    (h12 : __smtx_model_eval_eq v1 v2 = SmtValue.Boolean true)
    (h23 : __smtx_model_eval_eq v2 v3 = SmtValue.Boolean true) :
    __smtx_model_eval_eq v1 v3 = SmtValue.Boolean true := by
  cases v1 <;> cases v2 <;> cases v3 <;>
    simp [__smtx_model_eval_eq, native_veq] at h12 h23 ⊢
  all_goals
    first
    | intro s
      exact (h12 s).trans (h23 s)
    | simp_all

/-- Establishes an equality relating `smtx_model_eval_seq` and `true_trans`. -/
private theorem smtx_model_eval_seq_eq_true_trans
    {s1 s2 s3 : SmtSeq}
    (h12 : __smtx_model_eval_eq (SmtValue.Seq s1) (SmtValue.Seq s2) = SmtValue.Boolean true)
    (h23 : __smtx_model_eval_eq (SmtValue.Seq s2) (SmtValue.Seq s3) = SmtValue.Boolean true) :
    __smtx_model_eval_eq (SmtValue.Seq s1) (SmtValue.Seq s3) = SmtValue.Boolean true :=
  smtx_model_eval_seq_eq_true_iff.2
    ((smtx_model_eval_seq_eq_true_iff.1 h12).trans
      (smtx_model_eval_seq_eq_true_iff.1 h23))

/-- Reflexivity lemma for `smt_value_rel`. -/
theorem smt_value_rel_refl (v : SmtValue) : smt_value_rel v v :=
  smtx_model_eval_eq_refl_aux v

/-- Reflexivity lemma for `smt_seq_rel`. -/
theorem smt_seq_rel_refl (s : SmtSeq) : smt_seq_rel s s :=
  smtx_model_eval_seq_eq_refl_aux s

/-- Symmetry lemma for `smt_value_rel`. -/
theorem smt_value_rel_symm (v1 v2 : SmtValue) :
    smt_value_rel v1 v2 ->
    smt_value_rel v2 v1 :=
  smtx_model_eval_eq_true_symm

/-- Symmetry lemma for `smt_seq_rel`. -/
theorem smt_seq_rel_symm (s1 s2 : SmtSeq) :
    smt_seq_rel s1 s2 ->
    smt_seq_rel s2 s1 :=
  smtx_model_eval_seq_eq_true_symm

/-- Transitivity lemma for `smt_value_rel`. -/
theorem smt_value_rel_trans (v1 v2 v3 : SmtValue) :
    smt_value_rel v1 v2 ->
    smt_value_rel v2 v3 ->
    smt_value_rel v1 v3 :=
  smtx_model_eval_eq_true_trans

/-- Transitivity lemma for `smt_seq_rel`. -/
theorem smt_seq_rel_trans (s1 s2 s3 : SmtSeq) :
    smt_seq_rel s1 s2 ->
    smt_seq_rel s2 s3 ->
    smt_seq_rel s1 s3 :=
  smtx_model_eval_seq_eq_true_trans

/-- Characterizes `smt_value_rel` in terms of `model_eval_eq_true`. -/
theorem smt_value_rel_iff_model_eval_eq_true
    (v1 : SmtValue) (v2 : SmtValue) :
    smt_value_rel v1 v2 ↔ __smtx_model_eval_eq v1 v2 = SmtValue.Boolean true :=
  Iff.rfl

/-- Characterizes `smt_seq_rel` in terms of `model_eval_eq_true`. -/
theorem smt_seq_rel_iff_model_eval_eq_true
    (s1 : SmtSeq) (s2 : SmtSeq) :
    smt_seq_rel s1 s2 ↔
      __smtx_model_eval_eq (SmtValue.Seq s1) (SmtValue.Seq s2) = SmtValue.Boolean true :=
  Iff.rfl

/-- Characterizes `smt_value_rel` under constructor equality outside regex pairs. -/
theorem smt_value_rel_iff_eq (v1 : SmtValue) (v2 : SmtValue)
    (hReg :
      ¬ ∃ r1 r2, v1 = SmtValue.RegLan r1 ∧ v2 = SmtValue.RegLan r2) :
    smt_value_rel v1 v2 ↔ v1 = v2 :=
  smtx_model_eval_eq_true_iff_of_not_reglan_pair hReg

/-- Values of the same non-`RegLan` type are semantically related iff they are equal. -/
theorem smt_value_rel_iff_eq_of_type_ne_reglan
    {v1 v2 : SmtValue} {T : SmtType}
    (hTy1 : __smtx_typeof_value v1 = T)
    (hTy2 : __smtx_typeof_value v2 = T)
    (hT : T ≠ SmtType.RegLan) :
    smt_value_rel v1 v2 ↔ v1 = v2 := by
  exact smt_value_rel_iff_eq v1 v2 (by
    rintro ⟨r1, r2, hV1, hV2⟩
    have hTReg : T = SmtType.RegLan := by
      rw [← hTy1, hV1]
      rfl
    exact hT hTReg)

/-- Values of the same non-`RegLan` type that are semantically related are equal. -/
theorem smt_value_rel_eq_of_type_ne_reglan
    {v1 v2 : SmtValue} {T : SmtType}
    (hTy1 : __smtx_typeof_value v1 = T)
    (hTy2 : __smtx_typeof_value v2 = T)
    (hT : T ≠ SmtType.RegLan)
    (hRel : smt_value_rel v1 v2) :
    v1 = v2 :=
  (smt_value_rel_iff_eq_of_type_ne_reglan hTy1 hTy2 hT).mp hRel

/-- Characterizes `smt_seq_rel` under canonical value equality. -/
theorem smt_seq_rel_iff_eq (s1 : SmtSeq) (s2 : SmtSeq) :
    smt_seq_rel s1 s2 ↔ s1 = s2 :=
  smtx_model_eval_seq_eq_true_iff

/-- Derives `term_ne_stuck` from `interprets_true`. -/
theorem term_ne_stuck_of_interprets_true (M : SmtModel) (t : Term) :
  eo_interprets M t true -> t ≠ Term.Stuck := by
  intro h hStuck
  subst hStuck
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_stuck_eq] at h
  cases h with
  | intro_true hTy _ =>
      simp [TranslationProofs.smtx_typeof_none] at hTy

/-- Derives `term_ne_stuck` from `interprets_false`. -/
theorem term_ne_stuck_of_interprets_false (M : SmtModel) (t : Term) :
  eo_interprets M t false -> t ≠ Term.Stuck := by
  intro h hStuck
  subst hStuck
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_stuck_eq] at h
  cases h with
  | intro_false hTy _ =>
      simp [TranslationProofs.smtx_typeof_none] at hTy

/-- Derives `term_ne_stuck` from `has_bool_type`. -/
theorem term_ne_stuck_of_has_bool_type (t : Term) :
  eo_has_bool_type t -> t ≠ Term.Stuck := by
  intro hTy hStuck
  subst hStuck
  rw [eo_has_bool_type, eo_to_smt_stuck_eq] at hTy
  simp [TranslationProofs.smtx_typeof_none] at hTy

/-- Establishes an equality relating `smtx_typeof` and `refl`. -/
theorem smtx_typeof_eq_refl (T : SmtType) :
  T ≠ SmtType.None -> __smtx_typeof_eq T T = SmtType.Bool := by
  intro hT
  unfold __smtx_typeof_eq __smtx_typeof_guard
  simp [native_ite, native_Teq, hT]

/-- Establishes an equality relating `smtx_model_eval` and `refl`. -/
theorem smtx_model_eval_eq_refl (v : SmtValue) :
  __smtx_model_eval_eq v v = SmtValue.Boolean true := by
  exact (smt_value_rel_iff_model_eval_eq_true v v).mp (smt_value_rel_refl v)

end RuleProofs
