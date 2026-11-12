module

public import Cpc.Proofs.RuleSupport.Cong.HoCong
import all Cpc.Proofs.RuleSupport.Cong.HoCong
public import Cpc.Proofs.Closed.IsClosedRec
import all Cpc.Proofs.Closed.IsClosedRec

/-!
# Arguments of well-typed applications are well typed

If an application spine `(head x₁ … xₙ)`, written `xs.foldl Term.Apply head`,
has an SMT translation, then so does each argument `xᵢ`, for the heads listed
by `SpineArgsHead`. The body of a well-typed quantifier is Boolean.
-/

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false

namespace SpineArgsSupport

open CongSupport

/--
Heads whose application spines have translatable arguments, with the number of
arguments for which `spine_args_have_smt_translation` is proved.

Fixed-arity operators are listed with their full arity: a partial application
such as `(and x)` has no translation of its own. Indices of an indexed operator
(the `i j` of `(_ extract i j)`) belong to the head, not to the arguments.
Applications of a variable or an uninterpreted constant may take any number of
arguments.

Not listed, because their arguments are not all terms with a translation:
`forall` and `exists` (the binder list is an EO list, which has no translation;
see `forall_body_has_smt_translation_of_has_smt_translation` and
`exists_body_has_smt_translation_of_has_smt_translation` for the body).
Other operators are not covered yet.
-/
inductive SpineArgsHead : Term -> Nat -> Prop
  | not : SpineArgsHead (Term.UOp UserOp.not) 1
  | and : SpineArgsHead (Term.UOp UserOp.and) 2
  | or : SpineArgsHead (Term.UOp UserOp.or) 2
  | imp : SpineArgsHead (Term.UOp UserOp.imp) 2
  | xor : SpineArgsHead (Term.UOp UserOp.xor) 2
  | eq : SpineArgsHead (Term.UOp UserOp.eq) 2
  | ite : SpineArgsHead (Term.UOp UserOp.ite) 3
  | extract (i j : Term) : SpineArgsHead (Term.UOp2 UserOp2.extract i j) 1
  | var (s : native_String) (T : Term) (n : Nat) :
      SpineArgsHead (Term.Var (Term.String s) T) n
  | uconst (i : native_Nat) (T : Term) (n : Nat) :
      SpineArgsHead (Term.UConst i T) n

/-- Heads of applications translated by the generic SMT `Apply`. -/
private def GenericSpineHead (t : Term) : Prop :=
  (∃ s T, (appSpineRev t).1 = Term.Var (Term.String s) T) ∨
    (∃ i T, (appSpineRev t).1 = Term.UConst i T)

private theorem genericSpineHead_apply {t : Term} (x : Term)
    (h : GenericSpineHead t) : GenericSpineHead (Term.Apply t x) := by
  simpa [GenericSpineHead, appSpineRev] using h

private theorem eo_to_smt_generic_spine_eq {t : Term} (h : GenericSpineHead t) :
    ∃ F, (∀ s d i j, F ≠ SmtTerm.DtSel s d i j) ∧
      (∀ s d i, F ≠ SmtTerm.DtTester s d i) ∧
      __eo_to_smt t = mkSmtAppSpineRev F ((appSpineRev t).2.map __eo_to_smt) := by
  rcases h with ⟨s, T, hHead⟩ | ⟨i, T, hHead⟩
  · exact ⟨_, (by intro _ _ _ _ h; cases h), (by intro _ _ _ h; cases h),
      eo_to_smt_appSpineRev_var s T t hHead⟩
  · exact ⟨_, (by intro _ _ _ _ h; cases h), (by intro _ _ _ h; cases h),
      eo_to_smt_appSpineRev_uconst i T t hHead⟩

private theorem eo_to_smt_generic_apply_eq {t : Term}
    (h : GenericSpineHead t) (x : Term) :
    __eo_to_smt (Term.Apply t x) =
      SmtTerm.Apply (__eo_to_smt t) (__eo_to_smt x) := by
  rcases h with ⟨s, T, hHead⟩ | ⟨i, T, hHead⟩
  · have hHx : (appSpineRev (Term.Apply t x)).1 =
        Term.Var (Term.String s) T := by simpa [appSpineRev] using hHead
    rw [eo_to_smt_appSpineRev_var s T (Term.Apply t x) hHx,
      eo_to_smt_appSpineRev_var s T t hHead]
    simp [appSpineRev, mkSmtAppSpineRev]
  · have hHx : (appSpineRev (Term.Apply t x)).1 = Term.UConst i T := by
      simpa [appSpineRev] using hHead
    rw [eo_to_smt_appSpineRev_uconst i T (Term.Apply t x) hHx,
      eo_to_smt_appSpineRev_uconst i T t hHead]
    simp [appSpineRev, mkSmtAppSpineRev]

/-- One application step of a generic spine: both parts are translatable. -/
private theorem generic_apply_args_have_smt_translation {t x : Term}
    (h : GenericSpineHead t)
    (hTrans : RuleProofs.eo_has_smt_translation (Term.Apply t x)) :
    RuleProofs.eo_has_smt_translation t ∧
      RuleProofs.eo_has_smt_translation x := by
  rcases eo_to_smt_generic_spine_eq h with ⟨F, hSel, hTester, hT⟩
  have hTranslate := eo_to_smt_generic_apply_eq h x
  have hTy :
      __smtx_typeof (SmtTerm.Apply (__eo_to_smt t) (__eo_to_smt x)) =
        __smtx_typeof_apply (__smtx_typeof (__eo_to_smt t))
          (__smtx_typeof (__eo_to_smt x)) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by rw [hT]; exact mkSmtAppSpineRev_ne_dt_sel hSel _)
      (by rw [hT]; exact mkSmtAppSpineRev_ne_dt_tester hTester _)
  have hNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt t) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans
  simpa using apply_args_have_smt_translation_of_non_none hTy hNN

private theorem generic_spine_args_have_smt_translation :
    ∀ (xs : List Term) {h : Term}, GenericSpineHead h ->
      RuleProofs.eo_has_smt_translation (xs.foldl Term.Apply h) ->
      RuleProofs.eo_has_smt_translation h ∧
        ∀ x ∈ xs, RuleProofs.eo_has_smt_translation x
  | [], _, _, hTrans => ⟨hTrans, by simp⟩
  | x :: xs, h, hHead, hTrans => by
      rcases generic_spine_args_have_smt_translation xs
          (genericSpineHead_apply x hHead) hTrans with ⟨hApp, hRest⟩
      rcases generic_apply_args_have_smt_translation hHead hApp with ⟨hH, hX⟩
      refine ⟨hH, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hX
      · exact hRest y hy

private theorem ite_args_have_smt_translation {c a b : Term}
    (hTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) a) b)) :
    RuleProofs.eo_has_smt_translation c ∧
      RuleProofs.eo_has_smt_translation a ∧
      RuleProofs.eo_has_smt_translation b := by
  have hNN :
      term_has_non_none_type
        (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt a) (__eo_to_smt b)) := hTrans
  rcases ite_args_of_non_none hNN with ⟨T, hc, ha, hb, hT⟩
  unfold RuleProofs.eo_has_smt_translation
  exact ⟨by rw [hc]; simp, by rw [ha]; exact hT, by rw [hb]; exact hT⟩

/--
Every argument of a well-typed application spine `(head x₁ … xₙ)` is well
typed, for the heads and arities listed by `SpineArgsHead`.
-/
theorem spine_args_have_smt_translation (head : Term) (xs : List Term) :
    SpineArgsHead head xs.length ->
    RuleProofs.eo_has_smt_translation (xs.foldl Term.Apply head) ->
    ∀ x ∈ xs, RuleProofs.eo_has_smt_translation x := by
  intro hHead hTrans
  generalize hn : xs.length = n at hHead
  cases hHead with
  | var s T n =>
      exact (generic_spine_args_have_smt_translation xs
        (Or.inl ⟨s, T, by simp [appSpineRev]⟩) hTrans).2
  | uconst i T n =>
      exact (generic_spine_args_have_smt_translation xs
        (Or.inr ⟨i, T, by simp [appSpineRev]⟩) hTrans).2
  | ite =>
      match xs, hn with
      | [c, a, b], _ =>
          rcases ite_args_have_smt_translation hTrans with ⟨hc, ha, hb⟩
          simp [hc, ha, hb]
  | not =>
      match xs, hn with
      | [x], _ =>
          simpa using not_arg_has_smt_translation_of_has_smt_translation
            (by simpa using hTrans)
  | extract i j =>
      match xs, hn with
      | [x], _ =>
          simpa using
            (extract_indices_nat_valid_and_arg_has_smt_translation
              (by simpa using hTrans)).2.2
  | and =>
      match xs, hn with
      | [x, y], _ =>
          simpa using and_args_have_smt_translation_of_has_smt_translation
            (by simpa using hTrans)
  | or =>
      match xs, hn with
      | [x, y], _ =>
          simpa using or_args_have_smt_translation_of_has_smt_translation
            (by simpa using hTrans)
  | imp =>
      match xs, hn with
      | [x, y], _ =>
          simpa using imp_args_have_smt_translation_of_has_smt_translation
            (by simpa using hTrans)
  | xor =>
      match xs, hn with
      | [x, y], _ =>
          simpa using xor_args_have_smt_translation_of_has_smt_translation
            (by simpa using hTrans)
  | eq =>
      match xs, hn with
      | [x, y], _ =>
          simpa using eq_args_have_smt_translation_of_has_smt_translation
            (by simpa using hTrans)

private theorem eo_to_smt_exists_body_bool_of_non_none
    (xs : Term) (body : SmtTerm) (hxs : xs ≠ Term.__eo_List_nil) :
    __smtx_typeof (__eo_to_smt_exists xs body) ≠ SmtType.None ->
    __smtx_typeof body = SmtType.Bool := by
  unfold __eo_to_smt_exists
  split
  · exact absurd rfl hxs
  · intro h
    exact TranslationProofs.eo_to_smt_exists_body_bool_of_bool _ _
      (exists_body_bool_of_non_none h)
  · intro h
    exact absurd TranslationProofs.smtx_typeof_none h

/-- The body of a well-typed existential quantifier is Boolean. -/
theorem exists_body_has_bool_type_of_has_smt_translation
    (xs F : Term)
    (hExists : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) F)) :
    RuleProofs.eo_has_bool_type F := by
  unfold RuleProofs.eo_has_smt_translation at hExists
  unfold RuleProofs.eo_has_bool_type
  by_cases hNil : xs = Term.__eo_List_nil
  · subst hNil
    exact absurd TranslationProofs.smtx_typeof_none hExists
  · apply eo_to_smt_exists_body_bool_of_non_none xs _ hNil
    cases xs <;> first | exact absurd rfl hNil | exact hExists

/-- The body of a well-typed existential quantifier is well typed. -/
theorem exists_body_has_smt_translation_of_has_smt_translation
    (xs F : Term)
    (hExists : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) F)) :
    RuleProofs.eo_has_smt_translation F :=
  RuleProofs.eo_has_smt_translation_of_has_bool_type F
    (exists_body_has_bool_type_of_has_smt_translation xs F hExists)

end SpineArgsSupport
