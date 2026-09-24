module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.ReConcatStarSupport
import all Cpc.Proofs.RuleSupport.ReConcatStarSupport
public import Cpc.Proofs.Closed.IsClosedRec
import all Cpc.Proofs.Closed.IsClosedRec

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

/-- `native_re_ext_eq`, elaborated outside `RuleProofs` so that
`native_str_in_re` still denotes the model-level operator on value sequences
rather than the string-view proxy `RuleProofs.native_str_in_re`. -/
private noncomputable def nativeReExtEq (r1 r2 : SmtRegLan) : native_Bool :=
  native_re_ext_eq r1 r2

private theorem nativeReExtEq_eq_true_iff (r1 r2 : SmtRegLan) :
    nativeReExtEq r1 r2 = true ↔
      ∀ s : native_String, native_string_valid s = true ->
        native_str_in_re (impl_native_string_to_values s) r1 =
          native_str_in_re (impl_native_string_to_values s) r2 := by
  classical
  unfold nativeReExtEq
  constructor
  · intro h
    by_cases hP :
        ∀ s : native_String, native_string_valid s = true ->
          native_str_in_re (impl_native_string_to_values s) r1 =
            native_str_in_re (impl_native_string_to_values s) r2
    · exact hP
    · rw [dif_neg hP] at h
      exact absurd h (by decide)
  · intro hP
    exact dif_pos hP

namespace RuleProofs

/-! ## Term-structure abbreviations for `re_eq_elim`

The rule `__eo_prog_re_eq_elim` rewrites `(= (= r1 r2) Q)` to `(= (= r1 r2) Q)`
under the guards that `(= r1 r2)` is closed and that `Q` is syntactically the
extensionality formula `∀ x:(Seq Char). (str_in_re x r1) = (str_in_re x r2)`.
-/

private abbrev reqName : native_String :=
  native_string_lit "@var.re_eq"

private abbrev seqCharTy : Term :=
  Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)

private abbrev reqVar : Term :=
  Term.Var (Term.String reqName) seqCharTy

private abbrev reqList : Term :=
  Term.Apply (Term.Apply Term.__eo_List_cons reqVar) Term.__eo_List_nil

private abbrev mkEqT (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

private abbrev mkStrInReT (s r : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r

/-- The extensionality body `(= (str_in_re x r1) (str_in_re x r2))`. -/
private abbrev reEqBody (r1 r2 : Term) : Term :=
  mkEqT (mkStrInReT reqVar r1) (mkStrInReT reqVar r2)

/-- The extensionality formula `Q`, i.e. `∀ x. (str_in_re x r1) = (str_in_re x r2)`. -/
private abbrev reEqForall (r1 r2 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.forall) reqList) (reEqBody r1 r2)

/-! ## `__eo_requires` extraction helpers (mirrors `Re_loop_elim`). -/

private theorem eo_requires_eq_result_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    __eo_requires x y z = z := by
  intro h
  by_cases hxy : x = y
  · subst y
    by_cases hx : x = Term.Stuck
    · subst x
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at h
    · simp [__eo_requires, hx, native_ite, native_teq, native_not,
        SmtEval.native_not]
  · simp [__eo_requires, hxy, native_ite, native_teq] at h

private theorem eo_requires_arg_eq_of_ne_stuck
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · have hStuck : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, native_ite, hxy]
    exact False.elim (hReq hStuck)

private theorem eo_requires_result_ne_stuck_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    z ≠ Term.Stuck := by
  intro h hz
  have hReq : __eo_requires x y z = z :=
    eo_requires_eq_result_of_ne_stuck x y z h
  exact h (by rw [hReq, hz])

/-! ## Shape extraction.

If `__eo_prog_re_eq_elim a1` is not `Stuck`, then `a1` is `(= (= r1 r2) Q)`,
the closedness guard holds, `Q` is the extensionality formula, and the result is
`(= (= r1 r2) Q)`. -/

private theorem re_eq_elim_nonstuck_shape (a1 : Term) :
    __eo_prog_re_eq_elim a1 ≠ Term.Stuck ->
    ∃ r1 r2 Q,
      a1 = mkEqT (mkEqT r1 r2) Q ∧
      __is_closed_rec (mkEqT r1 r2) Term.__eo_List_nil = Term.Boolean true ∧
      Q = reEqForall r1 r2 ∧
      __eo_prog_re_eq_elim a1 = mkEqT (mkEqT r1 r2) Q := by
  intro hNe
  -- Only the matching shape avoids the `Term.Stuck` fall-through.
  match a1, hNe with
  | (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) r1) r2)) Q), hNe =>
    refine ⟨r1, r2, Q, rfl, ?_, ?_, ?_⟩
    · -- closedness guard
      have hProg :
          __eo_prog_re_eq_elim (mkEqT (mkEqT r1 r2) Q) =
            __eo_requires
              (__is_closed_rec (mkEqT r1 r2) Term.__eo_List_nil)
              (Term.Boolean true)
              (__eo_requires Q (reEqForall r1 r2)
                (mkEqT (mkEqT r1 r2) Q)) := rfl
      rw [hProg] at hNe
      exact eo_requires_arg_eq_of_ne_stuck hNe
    · -- Q equals the extensionality formula
      have hProg :
          __eo_prog_re_eq_elim (mkEqT (mkEqT r1 r2) Q) =
            __eo_requires
              (__is_closed_rec (mkEqT r1 r2) Term.__eo_List_nil)
              (Term.Boolean true)
              (__eo_requires Q (reEqForall r1 r2)
                (mkEqT (mkEqT r1 r2) Q)) := rfl
      rw [hProg] at hNe
      have hInner :
          __eo_requires Q (reEqForall r1 r2) (mkEqT (mkEqT r1 r2) Q) ≠
            Term.Stuck :=
        eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hNe
      exact eo_requires_arg_eq_of_ne_stuck hInner
    · -- the produced term
      have hProg :
          __eo_prog_re_eq_elim (mkEqT (mkEqT r1 r2) Q) =
            __eo_requires
              (__is_closed_rec (mkEqT r1 r2) Term.__eo_List_nil)
              (Term.Boolean true)
              (__eo_requires Q (reEqForall r1 r2)
                (mkEqT (mkEqT r1 r2) Q)) := rfl
      rw [hProg]
      rw [hProg] at hNe
      rw [eo_requires_eq_result_of_ne_stuck _ _ _ hNe]
      exact eo_requires_eq_result_of_ne_stuck _ _ _
        (eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hNe)

/-! ## Typing: the regex operands have `RegLan` type.

From `eo_has_bool_type (= (= r1 r2) Q)` with `Q` the extensionality formula, the
operands `r1`, `r2` translate to `RegLan`. -/

/-- If `ite c A None ≠ None`, the guard held and the `then`-branch is non-`None`. -/
private theorem ite_then_of_ne_none {c : native_Bool} {A : SmtType}
    (h : native_ite c A SmtType.None ≠ SmtType.None) :
    c = true ∧ A ≠ SmtType.None := by
  cases c with
  | true => exact ⟨rfl, by simpa [native_ite] using h⟩
  | false => exact absurd (by simp [native_ite]) h

private theorem eq_of_teq_true {X Y : SmtType}
    (h : native_Teq X Y = true) : X = Y :=
  of_decide_eq_true h

/-- The smt translation of the extensionality formula. -/
private theorem re_eq_forall_smt (r1 r2 : Term) :
    __eo_to_smt (reEqForall r1 r2) =
      SmtTerm.not
        (SmtTerm.exists reqName (__eo_to_smt_type seqCharTy)
          (SmtTerm.not (__eo_to_smt (reEqBody r1 r2)))) := rfl

private theorem re_eq_forall_args_reglan (r1 r2 : Term)
    (hBool : eo_has_bool_type (mkEqT (mkEqT r1 r2) (reEqForall r1 r2))) :
    __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan := by
  -- The forall operand has a non-`None` smt type.
  rcases eo_eq_operands_same_smt_type_of_has_bool_type
      (mkEqT r1 r2) (reEqForall r1 r2) hBool with ⟨hSame, hLeftNN⟩
  have hQNN : __smtx_typeof (__eo_to_smt (reEqForall r1 r2)) ≠ SmtType.None :=
    hSame ▸ hLeftNN
  rw [re_eq_forall_smt, typeof_not_eq] at hQNN
  -- Peel `not`: the inner `exists` has Bool type.
  have hExBool := (ite_then_of_ne_none hQNN).1
  have hExEq : __smtx_typeof
      (SmtTerm.exists reqName (__eo_to_smt_type seqCharTy)
        (SmtTerm.not (__eo_to_smt (reEqBody r1 r2)))) = SmtType.Bool :=
    eq_of_teq_true hExBool
  rw [smtx_typeof_exists_term_eq] at hExEq
  -- Peel `exists`: the `not body` has Bool type.
  have hNotBodyTeq :=
    (ite_then_of_ne_none (A := __smtx_typeof_guard_wf
      (__eo_to_smt_type seqCharTy) SmtType.Bool)
      (by rw [hExEq]; exact (by decide))).1
  have hNotBodyEq :
      __smtx_typeof (SmtTerm.not (__eo_to_smt (reEqBody r1 r2))) =
        SmtType.Bool :=
    eq_of_teq_true hNotBodyTeq
  rw [typeof_not_eq] at hNotBodyEq
  -- Peel `not`: the body has Bool type.
  have hBodyTeq := (ite_then_of_ne_none (A := SmtType.Bool)
    (by rw [hNotBodyEq]; exact (by decide))).1
  have hBodyBool : eo_has_bool_type (reEqBody r1 r2) := by
    unfold eo_has_bool_type
    exact eq_of_teq_true hBodyTeq
  -- The body is `(= (str_in_re x r1) (str_in_re x r2))`; both operands non-`None`.
  rcases eo_eq_operands_same_smt_type_of_has_bool_type
      (mkStrInReT reqVar r1) (mkStrInReT reqVar r2) hBodyBool with
    ⟨hSameB, hLeftBNN⟩
  have hRightBNN :
      __smtx_typeof (__eo_to_smt (mkStrInReT reqVar r2)) ≠ SmtType.None :=
    hSameB ▸ hLeftBNN
  -- Extract `RegLan` from each `str_in_re` operand.
  have hStr1 :
      __eo_to_smt (mkStrInReT reqVar r1) =
        SmtTerm.str_in_re (__eo_to_smt reqVar) (__eo_to_smt r1) := rfl
  have hStr2 :
      __eo_to_smt (mkStrInReT reqVar r2) =
        SmtTerm.str_in_re (__eo_to_smt reqVar) (__eo_to_smt r2) := rfl
  rw [hStr1, typeof_str_in_re_eq] at hLeftBNN
  rw [hStr2, typeof_str_in_re_eq] at hRightBNN
  refine ⟨?_, ?_⟩
  · exact eq_of_teq_true (ite_then_of_ne_none
      ((ite_then_of_ne_none hLeftBNN).2)).1
  · exact eq_of_teq_true (ite_then_of_ne_none
      ((ite_then_of_ne_none hRightBNN).2)).1

/-! ## Core: the produced equation evaluates true.

`(= r1 r2)` (regex extensional equality) and the extensionality formula `Q`
evaluate to the same Boolean in `M`. -/

private theorem unpack_pack_seq (T : SmtType) :
    ∀ xs : List SmtValue, native_unpack_seq (native_pack_seq T xs) = xs
  | [] => rfl
  | _ :: xs => by
      simp [native_pack_seq, native_unpack_seq, unpack_pack_seq T xs]

/-- Round-trip: unpacking a packed native string is the identity. -/
private theorem native_unpack_string_pack_string (s : native_String) :
    native_unpack_string (native_pack_string s) = s := by
  unfold native_unpack_string native_pack_string
  rw [unpack_pack_seq, List.map_map]
  have hid : (impl_native_ssm_char_of_value ∘ SmtValue.Char) = id := by
    funext x; rfl
  rw [hid, List.map_id]

/-- A valid native string packs to a canonical SMT sequence value. -/
private theorem seq_canonical_pack_string :
    ∀ s : native_String, native_string_valid s = true ->
      __smtx_seq_canonical (native_pack_string s) = true
  | [], _ => rfl
  | c :: cs, hValid => by
      have hc : native_char_valid c = true := by
        rw [native_string_valid, List.all_eq_true] at hValid
        exact hValid c (by simp)
      have hcs : native_string_valid cs = true := by
        rw [native_string_valid, List.all_eq_true] at hValid ⊢
        intro d hd
        exact hValid d (by simp [hd])
      have ih := seq_canonical_pack_string cs hcs
      change
        __smtx_seq_canonical
          (native_pack_seq SmtType.Char ((c :: cs).map SmtValue.Char)) = true
      rw [List.map_cons]
      change
        native_and (__smtx_value_canonical (SmtValue.Char c))
          (__smtx_seq_canonical
            (native_pack_seq SmtType.Char (cs.map SmtValue.Char))) = true
      have ih' :
          __smtx_seq_canonical (native_pack_seq SmtType.Char (cs.map SmtValue.Char)) =
            true := ih
      change native_and (native_char_valid c) _ = true
      rw [ih', hc]
      rfl

/-- Evaluation of a `RegLan`-typed term yields a `RegLan` value. -/
private theorem smt_eval_reglan_of_smt_type_reglan
    (M : SmtModel) (hM : model_wf M) (t : SmtTerm) :
    __smtx_typeof t = SmtType.RegLan ->
    ∃ r, __smtx_model_eval M t = SmtValue.RegLan r := by
  intro hTy
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type; rw [hTy]; simp
  have hValTy : __smtx_typeof_value (__smtx_model_eval M t) = SmtType.RegLan := by
    simpa [hTy] using smt_model_eval_preserves_type_of_non_none M hM t hNN
  exact reglan_value_canonical hValTy

/-
Core: `(= r1 r2)` (regex extensional equality) and the extensionality formula
evaluate to the same Boolean in `M`.  Proof outline:

Let `R1 := eval M (smt r1)`, `R2 := eval M (smt r2)` (both `RegLan` by `hr1`/`hr2`
via `smt_eval_reglan_of_smt_type_reglan`).

1. LHS: `eval M (smt (= r1 r2)) = __smtx_model_eval_eq (RegLan R1) (RegLan R2)
   = Boolean (native_re_ext_eq R1 R2)` (SmtModel.lean:872).  And
   `native_re_ext_eq R1 R2 = true ↔ ∀ s, native_string_valid s →
   native_str_in_re s R1 = native_str_in_re s R2` (definitional, SmtModel.lean:567).

2. Freshness: from `hClosed` + `hTrans`, derive `SmtTermClosedIn [] (smt r1)` and
   `(smt r2)`:
     `is_closed_rec_eq_eo_is_closed_of_has_smt_translation` (needs
     `eoHasSmtTranslation (= r1 r2)`, = `hTrans` modulo the `eoHasSmtTranslation`
     / `eo_has_smt_translation` defeq) gives `__is_closed_rec (= r1 r2) [] =
     __eo_is_closed (= r1 r2)`; with `hClosed` ⟹ `__eo_is_closed (= r1 r2) = true`;
     `smtTermClosedIn_of_eo_is_closed` ⟹ `SmtTermClosedIn [] (eq (smt r1) (smt r2))`,
     which unfolds to closedness of `smt r1` and `smt r2`.
   Hence for every `v`, `eval (native_model_push M reqName T v) (smt r_i) =
   eval M (smt r_i)` via `smt_model_eval_eq_of_eo_smt_closed` +
   `model_agrees_on_globals_push`.

3. RHS: `smt (reEqForall r1 r2) = not (exists reqName T (not (smt body)))`
   (`re_eq_forall_smt`), so `eval RHS = __smtx_model_eval_not
   (native_eval_exists M reqName T (not (smt body)))` (SmtModel.lean:2147,2293).
   With the freshness from (2), for a value `v = Seq ss`:
     `eval (push) (smt body) =
       Boolean (decide (native_str_in_re (native_unpack_string ss) R1 =
                        native_str_in_re (native_unpack_string ss) R2))`
   (str_in_re eval SmtModel.lean:1497; eq of two Booleans).  Using `hM`
   (canonical Bool), `eval RHS = Boolean true ↔ ∀ canonical Seq-Char `v=Seq ss`,
   `native_str_in_re (unpack ss) R1 = native_str_in_re (unpack ss) R2`.

4. Domain match (`T = __eo_to_smt_type seqCharTy = Seq Char`):
   - (⟸) every valid string `s` gives a canonical value `Seq (native_pack_string s)`
     with `typeof_value = Seq Char` (`typeof_pack_string`),
     `unpack (pack_string s) = s` (roundtrip — `native_unpack_string_pack_string`,
     copyable from e.g. Str_to_upper_lower.lean:105) and `canonical_bool = true`
     (i.e. `__smtx_seq_canonical (native_pack_string s) = true` for valid `s` —
     the ONE sub-lemma with no ready-made version; prove from `native_string_valid`
     ⟹ all chars valid); so the `∀`-over-values implies the `∀`-over-valid-strings.
   - (⟹) every canonical Seq-Char value is `Seq ss` (`seq_value_canonical`) with
     `unpack ss` valid (`native_unpack_string_valid_of_typeof_seq_char`).
   Hence the two booleans of (1) and (3) coincide.

5. `rw` both evals to `Boolean (native_re_ext_eq R1 R2)` and close with
   `smt_value_rel_refl`.
-/
private theorem re_eq_elim_smt_value_rel
    (M : SmtModel) (hM : model_wf M) (r1 r2 : Term)
    (hClosed :
      __is_closed_rec (mkEqT r1 r2) Term.__eo_List_nil = Term.Boolean true)
    (hTrans : eo_has_smt_translation (mkEqT r1 r2))
    (hr1 : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hr2 : __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan) :
    smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkEqT r1 r2)))
      (__smtx_model_eval M (__eo_to_smt (reEqForall r1 r2))) := by
  classical
  obtain ⟨R1, hR1⟩ :=
    smt_eval_reglan_of_smt_type_reglan M hM (__eo_to_smt r1) hr1
  obtain ⟨R2, hR2⟩ :=
    smt_eval_reglan_of_smt_type_reglan M hM (__eo_to_smt r2) hr2
  have hT : __eo_to_smt_type seqCharTy = SmtType.Seq SmtType.Char := rfl
  -- LHS value
  have hLHS :
      __smtx_model_eval M (__eo_to_smt (mkEqT r1 r2)) =
        SmtValue.Boolean (nativeReExtEq R1 R2) := by
    have h1 : __eo_to_smt (mkEqT r1 r2) =
        SmtTerm.eq (__eo_to_smt r1) (__eo_to_smt r2) := rfl
    rw [h1]
    simp only [__smtx_model_eval]
    rw [hR1, hR2]
    rfl
  -- closedness of the operands → push-invariance (freshness)
  have hEoTrans : eoHasSmtTranslation (mkEqT r1 r2) := by
    simpa [eoHasSmtTranslation, eo_has_smt_translation] using hTrans
  have hEoClosed : __eo_is_closed (mkEqT r1 r2) = Term.Boolean true := by
    rw [← is_closed_rec_eq_eo_is_closed_of_has_smt_translation hEoTrans]
    exact hClosed
  have hClosedEq :
      SmtTermClosedIn [] (SmtTerm.eq (__eo_to_smt r1) (__eo_to_smt r2)) :=
    smtTermClosedIn_of_eo_is_closed _ hEoClosed
  have hC1 : SmtTermClosedIn [] (__eo_to_smt r1) := hClosedEq.1
  have hC2 : SmtTermClosedIn [] (__eo_to_smt r2) := hClosedEq.2
  have hFresh1 : ∀ v : SmtValue,
      __smtx_model_eval
        (native_model_push M reqName (__eo_to_smt_type seqCharTy) v)
        (__eo_to_smt r1) = SmtValue.RegLan R1 := by
    intro v
    have h := smt_model_eval_eq_of_eo_smt_closed (P := r1) hC1
      (model_agrees_on_globals_push M reqName (__eo_to_smt_type seqCharTy) v)
    rw [← h]; exact hR1
  have hFresh2 : ∀ v : SmtValue,
      __smtx_model_eval
        (native_model_push M reqName (__eo_to_smt_type seqCharTy) v)
        (__eo_to_smt r2) = SmtValue.RegLan R2 := by
    intro v
    have h := smt_model_eval_eq_of_eo_smt_closed (P := r2) hC2
      (model_agrees_on_globals_push M reqName (__eo_to_smt_type seqCharTy) v)
    rw [← h]; exact hR2
  have hReqVar : ∀ v : SmtValue,
      __smtx_model_eval
        (native_model_push M reqName (__eo_to_smt_type seqCharTy) v)
        (__eo_to_smt reqVar) = v := by
    intro v
    have h1 : __eo_to_smt reqVar =
        SmtTerm.Var reqName (__eo_to_smt_type seqCharTy) := rfl
    rw [h1]
    simp only [__smtx_model_eval]
    simp [native_model_var_lookup, native_model_push]
  -- the body evaluated at a `Seq` value
  have hBodyEval : ∀ ss : SmtSeq,
      __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char ->
      __smtx_model_eval
        (native_model_push M reqName (__eo_to_smt_type seqCharTy)
          (SmtValue.Seq ss))
        (__eo_to_smt (reEqBody r1 r2)) =
        SmtValue.Boolean
          (decide (native_str_in_re (native_unpack_string ss) R1 =
                   native_str_in_re (native_unpack_string ss) R2)) := by
    intro ss hssTy
    have h1 : __eo_to_smt (reEqBody r1 r2) =
        SmtTerm.eq
          (SmtTerm.str_in_re (__eo_to_smt reqVar) (__eo_to_smt r1))
          (SmtTerm.str_in_re (__eo_to_smt reqVar) (__eo_to_smt r2)) := rfl
    rw [h1]
    simp only [__smtx_model_eval]
    rw [hFresh1 (SmtValue.Seq ss), hFresh2 (SmtValue.Seq ss)]
    simp [__smtx_model_eval, native_model_var_lookup, native_model_push,
      __smtx_model_eval_str_in_re, __smtx_model_eval_eq, native_veq,
      SmtValue.Boolean.injEq]
    rw [native_unpack_seq_eq_string_to_values_of_typeof_seq_char hssTy,
      ← native_str_in_re_eq_model, ← native_str_in_re_eq_model]
  -- characterization of regex extensional equality
  have hExtIff : nativeReExtEq R1 R2 = true ↔
      (∀ s : native_String, native_string_valid s = true →
        native_str_in_re s R1 = native_str_in_re s R2) := by
    rw [nativeReExtEq_eq_true_iff]
    constructor
    · intro h s hs
      rw [native_str_in_re_eq_model, native_str_in_re_eq_model]
      exact h s hs
    · intro h s hs
      rw [← native_str_in_re_eq_model, ← native_str_in_re_eq_model]
      exact h s hs
  rw [hLHS]
  rw [smt_value_rel_iff_model_eval_eq_true]
  -- RHS value
  have hRHSeq :
      __smtx_model_eval M (__eo_to_smt (reEqForall r1 r2)) =
        SmtValue.Boolean (nativeReExtEq R1 R2) := by
    rw [re_eq_forall_smt]
    simp only [__smtx_model_eval]
    by_cases hEx :
        ∃ v : SmtValue,
          __smtx_typeof_value v = __eo_to_smt_type seqCharTy ∧
            __smtx_value_canonical v = true ∧
            __smtx_model_eval_not
              (__smtx_model_eval
                (native_model_push M reqName (__eo_to_smt_type seqCharTy) v)
                (__eo_to_smt (reEqBody r1 r2))) =
              SmtValue.Boolean true
    · -- a witness exists: the formula is false, and so is `native_re_ext_eq`
      -- `rw` would have to match the goal's `Decidable` instance syntactically;
      -- routing through `congrArg` lets `refine` unify it up to defeq instead
      refine Eq.trans (congrArg __smtx_model_eval_not (dif_pos hEx)) ?_
      have hNotHp :
          ¬ (∀ s : native_String, native_string_valid s = true →
              native_str_in_re s R1 = native_str_in_re s R2) := by
        rcases hEx with ⟨v, hvTy, _hvCan, hvEval⟩
        rcases seq_value_canonical (T := SmtType.Char) (by rw [← hT]; exact hvTy)
          with ⟨ss, rfl⟩
        have hssTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
          have h := hvTy; rw [hT] at h; simpa [__smtx_typeof_value] using h
        rw [hBodyEval ss hssTy] at hvEval
        simp [__smtx_model_eval_not, native_not] at hvEval
        intro hAll
        exact hvEval (hAll (native_unpack_string ss)
          (native_unpack_string_valid_of_typeof_seq_char hssTy))
      have hFalse : nativeReExtEq R1 R2 = false := by
        cases hVal : nativeReExtEq R1 R2 with
        | false => rfl
        | true => exact absurd (hExtIff.1 hVal) hNotHp
      rw [hFalse]
      rfl
    · -- no witness: the formula is true, and so is `native_re_ext_eq`
      refine Eq.trans (congrArg __smtx_model_eval_not (dif_neg hEx)) ?_
      have hHp : ∀ s : native_String, native_string_valid s = true →
          native_str_in_re s R1 = native_str_in_re s R2 := by
        intro s hs
        by_cases hne : native_str_in_re s R1 = native_str_in_re s R2
        · exact hne
        · exfalso
          apply hEx
          refine ⟨SmtValue.Seq (native_pack_string s), ?_, ?_, ?_⟩
          · rw [hT]
            show __smtx_typeof_seq_value (native_pack_string s) =
              SmtType.Seq SmtType.Char
            exact typeof_pack_string s hs
          · show __smtx_seq_canonical (native_pack_string s) = true
            exact seq_canonical_pack_string s hs
          · rw [hBodyEval (native_pack_string s) (typeof_pack_string s hs),
              native_unpack_string_pack_string s]
            simp [__smtx_model_eval_not, native_not, hne]
      rw [hExtIff.2 hHp]
      rfl
  rw [hRHSeq]
  simp [__smtx_model_eval_eq, native_veq]

end RuleProofs

public theorem cmd_step_re_eq_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_eq_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_eq_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_eq_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.re_eq_elim args premises ≠ Term.Stuck :=
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
              have hArgsTrans :
                  cArgListTranslationOk (CArgList.cons a1 CArgList.nil) := by
                simpa [cmdTranslationOk] using hCmdTrans
              change StepRuleProperties M [] (__eo_prog_re_eq_elim a1)
              have hProgLocal : __eo_prog_re_eq_elim a1 ≠ Term.Stuck := by
                change __eo_prog_re_eq_elim a1 ≠ Term.Stuck at hProg
                exact hProg
              obtain ⟨r1, r2, Q, ha1, hClosed, hQ, hProgEq⟩ :=
                RuleProofs.re_eq_elim_nonstuck_shape a1 hProgLocal
              have hTermTrans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cArgListTranslationOk] using hArgsTrans.1
              -- the produced term equals `a1` (the rule is the identity after guards)
              have hTypeofA1 : __eo_typeof a1 = Term.Bool := by
                have : __eo_typeof (__eo_prog_re_eq_elim a1) = Term.Bool := by
                  change __eo_typeof (__eo_cmd_step_proven s CRule.re_eq_elim
                    (CArgList.cons a1 CArgList.nil) CIndexList.nil) = Term.Bool
                  exact hResultTy
                rwa [hProgEq, ← ha1] at this
              have hBool : RuleProofs.eo_has_bool_type a1 :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hTermTrans hTypeofA1
              -- rewrite everything to the destructured form
              rw [ha1] at hBool hTermTrans
              subst hQ
              -- regex operand types
              obtain ⟨hr1, hr2⟩ :=
                RuleProofs.re_eq_forall_args_reglan r1 r2 hBool
              -- translation of the inner regex equation
              have hEqTrans :
                  RuleProofs.eo_has_smt_translation
                    (RuleProofs.mkEqT r1 r2) := by
                rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                    (RuleProofs.mkEqT r1 r2) (RuleProofs.reEqForall r1 r2)
                    hBool with ⟨_hSame, hLeftNN⟩
                exact hLeftNN
              refine ⟨?_, ?_⟩
              · intro _hPremisesTrue
                rw [hProgEq]
                exact RuleProofs.eo_interprets_eq_of_rel M
                  (RuleProofs.mkEqT r1 r2) (RuleProofs.reEqForall r1 r2)
                  hBool
                  (RuleProofs.re_eq_elim_smt_value_rel M hM r1 r2
                    hClosed hEqTrans hr1 hr2)
              · rw [hProgEq]
                exact hTermTrans
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
