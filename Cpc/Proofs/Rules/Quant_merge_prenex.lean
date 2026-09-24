module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.Translation.Quantifiers
import all Cpc.Proofs.Translation.Quantifiers

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private def qterm (Q x F : Term) : Term :=
  Term.Apply (Term.Apply Q x) F

private def qeq (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B

private def qexists (x F : Term) : Term :=
  qterm (Term.UOp UserOp.exists) x F

private def qforall (x F : Term) : Term :=
  qterm (Term.UOp UserOp.forall) x F

private theorem eo_to_smt_exists_eq (x F : Term)
    (hx : x ≠ Term.__eo_List_nil) :
    __eo_to_smt (qexists x F) =
      __eo_to_smt_exists x (__eo_to_smt F) := by
  unfold qexists qterm
  cases x <;> first | rfl | exact False.elim (hx rfl)

private theorem eo_to_smt_forall_eq (x F : Term)
    (hx : x ≠ Term.__eo_List_nil) :
    __eo_to_smt (qforall x F) =
      SmtTerm.not (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) := by
  unfold qforall qterm
  cases x <;> first | rfl | exact False.elim (hx rfl)

private theorem smtx_typeof_not_arg_of_bool
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool ->
    __smtx_typeof t = SmtType.Bool := by
  exact TranslationProofs.smtx_typeof_not_arg_bool t

private theorem smtx_typeof_not_bool_of_arg_bool
    (t : SmtTerm) :
    __smtx_typeof t = SmtType.Bool ->
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq]
  simp [hTy, native_ite, native_Teq]

private theorem smtx_typeof_not_arg_of_non_none
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) ≠ SmtType.None ->
    __smtx_typeof t = SmtType.Bool := by
  intro hNN
  cases h : __smtx_typeof t <;>
    simp [typeof_not_eq, h, native_ite, native_Teq] at hNN ⊢

private theorem false_of_smtx_typeof_none_bool :
    __smtx_typeof SmtTerm.None = SmtType.Bool -> False := by
  intro h
  exact TranslationProofs.smtx_typeof_none_ne_bool h

private theorem smtx_typeof_exists_tail_bool_of_cons_bool
    (s : native_String) (T xs : Term) (body : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs)
          body) = SmtType.Bool ->
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool := by
  intro hTy
  have hExists :
      __smtx_typeof
          (SmtTerm.exists s (__eo_to_smt_type T)
            (__eo_to_smt_exists xs body)) = SmtType.Bool := by
    simpa [__eo_to_smt_exists] using hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.exists s (__eo_to_smt_type T)
          (__eo_to_smt_exists xs body)) := by
    unfold term_has_non_none_type
    rw [hExists]
    simp
  exact exists_body_bool_of_non_none hNN

private theorem smtx_type_wf_of_exists_cons_bool
    (s : native_String) (T xs : Term) (body : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs)
          body) = SmtType.Bool ->
    __smtx_type_wf (__eo_to_smt_type T) = true := by
  intro hTy
  have hTail :
      __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool :=
    smtx_typeof_exists_tail_bool_of_cons_bool s T xs body hTy
  have hGuardNN :
      __smtx_typeof_guard_wf (__eo_to_smt_type T) SmtType.Bool ≠ SmtType.None := by
    intro hNone
    have hExists :
        __smtx_typeof
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists xs body)) = SmtType.Bool := by
      simpa [__eo_to_smt_exists] using hTy
    rw [smtx_typeof_exists_term_eq, hTail] at hExists
    simp [native_ite, native_Teq, hNone] at hExists
  exact smtx_typeof_guard_wf_wf_of_non_none
    (__eo_to_smt_type T) SmtType.Bool hGuardNN

private theorem smtx_typeof_eo_to_smt_exists_same_binders
    (xs : Term) (body body' : SmtTerm) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
    __smtx_typeof body' = SmtType.Bool ->
    __smtx_typeof (__eo_to_smt_exists xs body') = SmtType.Bool := by
  intro hTy hBody'
  cases hxs : xs
  case __eo_List_nil =>
      subst hxs
      simpa [__eo_to_smt_exists] using hBody'
  case Apply f a =>
      subst hxs
      cases f with
      | Apply g y =>
          cases g with
          | __eo_List_cons =>
              cases y with
              | Var name T =>
                  cases name with
                  | String s =>
                      have hTail :
                          __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool :=
                        smtx_typeof_exists_tail_bool_of_cons_bool s T a body hTy
                      have hTail' :
                          __smtx_typeof (__eo_to_smt_exists a body') = SmtType.Bool :=
                        smtx_typeof_eo_to_smt_exists_same_binders a body body'
                          hTail hBody'
                      have hWF :
                          __smtx_type_wf (__eo_to_smt_type T) = true :=
                        smtx_type_wf_of_exists_cons_bool s T a body hTy
                      change
                        __smtx_typeof
                          (SmtTerm.exists s (__eo_to_smt_type T)
                            (__eo_to_smt_exists a body')) = SmtType.Bool
                      rw [smtx_typeof_exists_term_eq, hTail']
                      simp [native_ite, native_Teq, __smtx_typeof_guard_wf, hWF]
                  | _ =>
                      simp [__eo_to_smt_exists] at hTy
              | _ =>
                  simp [__eo_to_smt_exists] at hTy
          | _ =>
              simp [__eo_to_smt_exists] at hTy
      | _ =>
          simp [__eo_to_smt_exists] at hTy
  all_goals
      subst hxs
      simp [__eo_to_smt_exists] at hTy

private theorem smtx_model_eval_not_not_true_iff
    (v : SmtValue) :
    __smtx_model_eval_not (__smtx_model_eval_not v) = SmtValue.Boolean true ↔
      v = SmtValue.Boolean true := by
  cases v <;> simp [__smtx_model_eval_not, SmtEval.native_not]

private theorem smtx_model_eval_eo_to_smt_exists_double_not_body_true_iff
    (M : SmtModel) (xs : Term) (body : SmtTerm) :
    __smtx_model_eval M (__eo_to_smt_exists xs (SmtTerm.not (SmtTerm.not body))) =
        SmtValue.Boolean true ↔
      __smtx_model_eval M (__eo_to_smt_exists xs body) = SmtValue.Boolean true := by
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    simpa [__eo_to_smt_exists, __smtx_model_eval] using
      smtx_model_eval_not_not_true_iff (__smtx_model_eval M body)
  case Apply f a =>
    subst hxs
    cases hf : f
    case Apply g y =>
      subst hf
      cases hg : g
      case __eo_List_cons =>
        subst hg
        cases hy : y
        case Var name T =>
          subst hy
          cases hname : name
          case String s =>
            subst hname
            classical
            let P : Prop :=
              ∃ v : SmtValue,
                __smtx_typeof_value v = __eo_to_smt_type T ∧
                  __smtx_value_canonical v = true ∧
                  __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
                    (__eo_to_smt_exists a (SmtTerm.not (SmtTerm.not body))) =
                    SmtValue.Boolean true
            let Q : Prop :=
              ∃ v : SmtValue,
                __smtx_typeof_value v = __eo_to_smt_type T ∧
                  __smtx_value_canonical v = true ∧
                  __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
                    (__eo_to_smt_exists a body) = SmtValue.Boolean true
            have hPQ : P ↔ Q := by
              constructor
              · intro hSat
                rcases hSat with ⟨v, hv, hCan, hEval⟩
                refine ⟨v, hv, hCan, ?_⟩
                exact
                  (smtx_model_eval_eo_to_smt_exists_double_not_body_true_iff
                    (native_model_push M s (__eo_to_smt_type T) v) a body).1 hEval
              · intro hSat
                rcases hSat with ⟨v, hv, hCan, hEval⟩
                refine ⟨v, hv, hCan, ?_⟩
                exact
                  (smtx_model_eval_eo_to_smt_exists_double_not_body_true_iff
                    (native_model_push M s (__eo_to_smt_type T) v) a body).2 hEval
            have hPropEq : P = Q := propext hPQ
            simp [P, Q, __eo_to_smt_exists, __smtx_model_eval, hPropEq]
          all_goals
            subst hname
            simp [__eo_to_smt_exists, __smtx_model_eval]
        all_goals
          subst hy
          simp [__eo_to_smt_exists, __smtx_model_eval]
      all_goals
        subst hg
        simp [__eo_to_smt_exists, __smtx_model_eval]
    all_goals
      subst hf
      simp [__eo_to_smt_exists, __smtx_model_eval]
  all_goals
    subst hxs
    simp [__eo_to_smt_exists, __smtx_model_eval]

private theorem smtx_model_eval_eo_to_smt_exists_double_not_body
    (M : SmtModel) (hM : model_wf M)
    (xs : Term) (body : SmtTerm)
    (hBody : __smtx_typeof body = SmtType.Bool) :
    __smtx_model_eval M (__eo_to_smt_exists xs (SmtTerm.not (SmtTerm.not body))) =
      __smtx_model_eval M (__eo_to_smt_exists xs body) := by
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    rcases smt_model_eval_bool_is_boolean M hM body hBody with ⟨b, hb⟩
    simp [__eo_to_smt_exists, __smtx_model_eval, hb, __smtx_model_eval_not,
      SmtEval.native_not]
  case Apply f a =>
    subst hxs
    cases hf : f
    case Apply g y =>
      subst hf
      cases hg : g
      case __eo_List_cons =>
        subst hg
        cases hy : y
        case Var name T =>
          subst hy
          cases hname : name
          case String s =>
            subst hname
            classical
            let P : Prop :=
              ∃ v : SmtValue,
                __smtx_typeof_value v = __eo_to_smt_type T ∧
                  __smtx_value_canonical v = true ∧
                  __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
                    (__eo_to_smt_exists a (SmtTerm.not (SmtTerm.not body))) =
                    SmtValue.Boolean true
            let Q : Prop :=
              ∃ v : SmtValue,
                __smtx_typeof_value v = __eo_to_smt_type T ∧
                  __smtx_value_canonical v = true ∧
                  __smtx_model_eval (native_model_push M s (__eo_to_smt_type T) v)
                    (__eo_to_smt_exists a body) = SmtValue.Boolean true
            have hPQ : P ↔ Q := by
              constructor
              · intro hSat
                rcases hSat with ⟨v, hv, hCan, hEval⟩
                refine ⟨v, hv, hCan, ?_⟩
                exact
                  (smtx_model_eval_eo_to_smt_exists_double_not_body_true_iff
                    (native_model_push M s (__eo_to_smt_type T) v) a body).1 hEval
              · intro hSat
                rcases hSat with ⟨v, hv, hCan, hEval⟩
                refine ⟨v, hv, hCan, ?_⟩
                exact
                  (smtx_model_eval_eo_to_smt_exists_double_not_body_true_iff
                    (native_model_push M s (__eo_to_smt_type T) v) a body).2 hEval
            have hPropEq : P = Q := propext hPQ
            simp [P, Q, __eo_to_smt_exists, __smtx_model_eval, hPropEq]
          all_goals
            subst hname
            simp [__eo_to_smt_exists, __smtx_model_eval]
        all_goals
          subst hy
          simp [__eo_to_smt_exists, __smtx_model_eval]
      all_goals
        subst hg
        simp [__eo_to_smt_exists, __smtx_model_eval]
    all_goals
      subst hf
      simp [__eo_to_smt_exists, __smtx_model_eval]
  all_goals
    subst hxs
    simp [__eo_to_smt_exists, __smtx_model_eval]

private def eoListOfTerms : List Term -> Term
  | [] => Term.__eo_List_nil
  | x :: xs => Term.Apply (Term.Apply Term.__eo_List_cons x) (eoListOfTerms xs)

private theorem eoListOfTerms_ne_stuck (xs : List Term) :
    eoListOfTerms xs ≠ Term.Stuck := by
  cases xs <;> simp [eoListOfTerms]

private theorem eoListOfTerms_is_list_true (xs : List Term) :
    __eo_is_list Term.__eo_List_cons (eoListOfTerms xs) = Term.Boolean true := by
  induction xs with
  | nil =>
      simp [eoListOfTerms, __eo_is_list, __eo_get_nil_rec, __eo_requires,
        __eo_is_ok, __eo_is_list_nil, native_ite, native_teq, native_not,
        SmtEval.native_not]
  | cons _ xs ih =>
      simp [eoListOfTerms, __eo_is_list, __eo_get_nil_rec, __eo_requires,
        native_ite, native_teq, native_not, SmtEval.native_not]
      simpa [__eo_is_list, eoListOfTerms_ne_stuck xs] using ih

private theorem eo_list_concat_rec_eoListOfTerms (xs ys : List Term) :
    __eo_list_concat_rec (eoListOfTerms xs) (eoListOfTerms ys) =
      eoListOfTerms (xs ++ ys) := by
  induction xs with
  | nil =>
      cases ys <;> rfl
  | cons x xs ih =>
      simp [eoListOfTerms, __eo_list_concat_rec, __eo_mk_apply,
        eoListOfTerms_ne_stuck, ih]

private theorem eo_list_concat_eoListOfTerms (xs ys : List Term) :
    __eo_list_concat Term.__eo_List_cons (eoListOfTerms xs) (eoListOfTerms ys) =
      eoListOfTerms (xs ++ ys) := by
  simp [__eo_list_concat, eoListOfTerms_is_list_true, __eo_requires,
    native_ite, native_teq, native_not, SmtEval.native_not,
    eo_list_concat_rec_eoListOfTerms]

private def IsQuantVarTerm : Term -> Prop
  | Term.Var (Term.String _) _ => True
  | _ => False

private theorem eo_to_smt_exists_bool_as_eoList
    (xs : Term) (body : SmtTerm) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
    ∃ ts, xs = eoListOfTerms ts ∧ ∀ t ∈ ts, IsQuantVarTerm t := by
  intro hTy
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    exact ⟨[], rfl, by simp⟩
  case Apply f a =>
    subst hxs
    cases hf : f
    case Apply g y =>
      subst hf
      cases hg : g
      case __eo_List_cons =>
        subst hg
        cases hy : y
        case Var name T =>
          subst hy
          cases hname : name
          case String s =>
            subst hname
            have hExistsTy :
                __smtx_typeof
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists a body)) =
                  SmtType.Bool := by
              simpa [__eo_to_smt_exists] using hTy
            have hNN :
                term_has_non_none_type
                  (SmtTerm.exists s (__eo_to_smt_type T)
                    (__eo_to_smt_exists a body)) := by
              unfold term_has_non_none_type
              rw [hExistsTy]
              simp
            have hSub : __smtx_typeof (__eo_to_smt_exists a body) =
                SmtType.Bool := by
              simpa using exists_body_bool_of_non_none hNN
            rcases eo_to_smt_exists_bool_as_eoList a body hSub with
              ⟨ts, hTail, hAllTail⟩
            refine ⟨Term.Var (Term.String s) T :: ts, ?_, ?_⟩
            · simp [eoListOfTerms, hTail]
            · intro t ht
              simp at ht
              rcases ht with ht | ht
              · subst t
                simp [IsQuantVarTerm]
              · exact hAllTail t ht
          all_goals
            subst hname
            have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
              simpa [__eo_to_smt_exists] using hTy
            exact False.elim (false_of_smtx_typeof_none_bool hNone)
        all_goals
          subst hy
          have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
            simpa [__eo_to_smt_exists] using hTy
          exact False.elim (false_of_smtx_typeof_none_bool hNone)
      all_goals
        subst hg
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (false_of_smtx_typeof_none_bool hNone)
    all_goals
      subst hf
      have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
        simpa [__eo_to_smt_exists] using hTy
      exact False.elim (false_of_smtx_typeof_none_bool hNone)
  all_goals
    subst hxs
    have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
      simpa [__eo_to_smt_exists] using hTy
    exact False.elim (false_of_smtx_typeof_none_bool hNone)

private theorem eo_to_smt_exists_eoList_append
    (xs ys : List Term) (body : SmtTerm)
    (hxs : ∀ t ∈ xs, IsQuantVarTerm t) :
    __eo_to_smt_exists (eoListOfTerms xs)
        (__eo_to_smt_exists (eoListOfTerms ys) body) =
      __eo_to_smt_exists (eoListOfTerms (xs ++ ys)) body := by
  induction xs with
  | nil =>
      simp [eoListOfTerms]
  | cons x xs ih =>
      have hx : IsQuantVarTerm x := hxs x (by simp)
      have htail : ∀ t ∈ xs, IsQuantVarTerm t := by
        intro t ht
        exact hxs t (by simp [ht])
      cases x <;> simp [IsQuantVarTerm] at hx
      case Var name T =>
        cases name <;> simp at hx
        case String s =>
          simp [eoListOfTerms, ih htail]

private theorem smtx_typeof_exists_bool_or_none_local
    (s : native_String) (T : SmtType) (body : SmtTerm) :
    __smtx_typeof (SmtTerm.exists s T body) = SmtType.Bool ∨
      __smtx_typeof (SmtTerm.exists s T body) = SmtType.None := by
  rw [smtx_typeof_exists_term_eq]
  cases hBody : __smtx_typeof body <;>
    simp [native_ite, native_Teq]
  cases hWf : __smtx_type_wf T <;>
    simp [__smtx_typeof_guard_wf, native_ite, hWf]

private theorem smtx_typeof_qexists_bool_or_none
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool ∨
      __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.None := by
  unfold qexists qterm
  cases x
  case __eo_List_nil =>
    right
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
  case Apply f tail =>
    cases f
    case Apply g head =>
      cases g
      case __eo_List_cons =>
        cases head
        case Var name T =>
          cases name
          case String s =>
            change
              __smtx_typeof
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists tail (__eo_to_smt F))) =
                  SmtType.Bool ∨
                __smtx_typeof
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists tail (__eo_to_smt F))) =
                  SmtType.None
            exact smtx_typeof_exists_bool_or_none_local s (__eo_to_smt_type T)
              (__eo_to_smt_exists tail (__eo_to_smt F))
          all_goals
            right
            change __smtx_typeof SmtTerm.None = SmtType.None
            exact TranslationProofs.smtx_typeof_none
        all_goals
          right
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none
      all_goals
        right
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none
    all_goals
      right
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  all_goals
    right
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none

private theorem eo_to_smt_exists_top_bool_of_non_none
    (x F : Term)
    (hNN : __smtx_typeof (__eo_to_smt (qexists x F)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool := by
  rcases smtx_typeof_qexists_bool_or_none x F with hBool | hNone
  · exact hBool
  · exact False.elim (hNN hNone)

private theorem qexists_non_nil_of_non_none
    (x F : Term)
    (hNN : __smtx_typeof (__eo_to_smt (qexists x F)) ≠ SmtType.None) :
    x ≠ Term.__eo_List_nil := by
  intro hx
  subst x
  apply hNN
  change __smtx_typeof SmtTerm.None = SmtType.None
  exact TranslationProofs.smtx_typeof_none

private theorem qforall_non_nil_of_non_none
    (x F : Term)
    (hNN : __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None) :
    x ≠ Term.__eo_List_nil := by
  intro hx
  subst x
  apply hNN
  change __smtx_typeof SmtTerm.None = SmtType.None
  exact TranslationProofs.smtx_typeof_none

private theorem qforall_inner_exists_bool_of_non_none
    (x F : Term)
    (hNN : __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
      SmtType.Bool := by
  have hx : x ≠ Term.__eo_List_nil := qforall_non_nil_of_non_none x F hNN
  have hNN' := hNN
  rw [eo_to_smt_forall_eq x F hx] at hNN'
  exact smtx_typeof_not_arg_of_non_none
    (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) hNN'

private theorem qforall_top_bool_of_non_none
    (x F : Term)
    (hNN : __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (qforall x F)) = SmtType.Bool := by
  have hx : x ≠ Term.__eo_List_nil := qforall_non_nil_of_non_none x F hNN
  rw [eo_to_smt_forall_eq x F hx]
  exact smtx_typeof_not_bool_of_arg_bool _
    (qforall_inner_exists_bool_of_non_none x F hNN)

private theorem qexists_concat_step
    (M : SmtModel) (acc xs F : Term)
    (hBool : RuleProofs.eo_has_bool_type (qexists acc (qexists xs F))) :
    __smtx_model_eval M (__eo_to_smt (qexists acc (qexists xs F))) =
      __smtx_model_eval M
        (__eo_to_smt (qexists (__eo_list_concat Term.__eo_List_cons acc xs) F)) ∧
    RuleProofs.eo_has_bool_type
      (qexists (__eo_list_concat Term.__eo_List_cons acc xs) F) := by
  unfold RuleProofs.eo_has_bool_type at hBool
  have hAccNN : __smtx_typeof (__eo_to_smt (qexists acc (qexists xs F))) ≠
      SmtType.None := by rw [hBool]; simp
  have hAccNonNil := qexists_non_nil_of_non_none acc (qexists xs F) hAccNN
  have hAccExistsTy :
      __smtx_typeof (__eo_to_smt_exists acc (__eo_to_smt (qexists xs F))) =
        SmtType.Bool := by
    simpa [eo_to_smt_exists_eq acc (qexists xs F) hAccNonNil] using hBool
  have hNestedTy :
      __smtx_typeof (__eo_to_smt (qexists xs F)) = SmtType.Bool :=
    TranslationProofs.eo_to_smt_exists_body_bool_of_bool acc
      (__eo_to_smt (qexists xs F)) hAccExistsTy
  have hXsNN : __smtx_typeof (__eo_to_smt (qexists xs F)) ≠ SmtType.None := by
    rw [hNestedTy]
    simp
  have hXsNonNil := qexists_non_nil_of_non_none xs F hXsNN
  have hXsExistsTy :
      __smtx_typeof (__eo_to_smt_exists xs (__eo_to_smt F)) = SmtType.Bool := by
    simpa [eo_to_smt_exists_eq xs F hXsNonNil] using hNestedTy
  rcases eo_to_smt_exists_bool_as_eoList acc (__eo_to_smt (qexists xs F))
      hAccExistsTy with
    ⟨accs, hAccEq, hAccAll⟩
  rcases eo_to_smt_exists_bool_as_eoList xs (__eo_to_smt F)
      hXsExistsTy with
    ⟨xss, hXsEq, hXsAll⟩
  have hAccsNonempty : accs ≠ [] := by
    intro hNil
    apply hAccNonNil
    rw [hAccEq, hNil]
    rfl
  have hXssNonempty : xss ≠ [] := by
    intro hNil
    apply hXsNonNil
    rw [hXsEq, hNil]
    rfl
  have hConcatNonNil :
      __eo_list_concat Term.__eo_List_cons acc xs ≠ Term.__eo_List_nil := by
    rw [hAccEq, hXsEq, eo_list_concat_eoListOfTerms]
    intro h
    cases accs with
    | nil => exact hAccsNonempty rfl
    | cons _ _ => simp [eoListOfTerms] at h
  have hConcatTranslate :
      __eo_to_smt_exists (__eo_list_concat Term.__eo_List_cons acc xs) (__eo_to_smt F) =
        __eo_to_smt_exists acc (__eo_to_smt (qexists xs F)) := by
    rw [hAccEq, hXsEq, eo_list_concat_eoListOfTerms]
    have hXsTranslate :
        __eo_to_smt (qexists (eoListOfTerms xss) F) =
          __eo_to_smt_exists (eoListOfTerms xss) (__eo_to_smt F) := by
      simpa [hXsEq] using eo_to_smt_exists_eq xs F hXsNonNil
    rw [hXsTranslate]
    exact (eo_to_smt_exists_eoList_append accs xss (__eo_to_smt F)
      hAccAll).symm
  constructor
  · rw [eo_to_smt_exists_eq acc (qexists xs F) hAccNonNil]
    rw [eo_to_smt_exists_eq
      (__eo_list_concat Term.__eo_List_cons acc xs) F hConcatNonNil]
    rw [hConcatTranslate]
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_exists_eq
      (__eo_list_concat Term.__eo_List_cons acc xs) F hConcatNonNil]
    rw [hConcatTranslate]
    exact hAccExistsTy

private theorem qforall_concat_step
    (M : SmtModel) (hM : model_wf M)
    (acc xs F : Term)
    (hBool : RuleProofs.eo_has_bool_type (qforall acc (qforall xs F))) :
    __smtx_model_eval M (__eo_to_smt (qforall acc (qforall xs F))) =
      __smtx_model_eval M
        (__eo_to_smt (qforall (__eo_list_concat Term.__eo_List_cons acc xs) F)) ∧
    RuleProofs.eo_has_bool_type
      (qforall (__eo_list_concat Term.__eo_List_cons acc xs) F) := by
  unfold RuleProofs.eo_has_bool_type at hBool
  have hAccNN : __smtx_typeof (__eo_to_smt (qforall acc (qforall xs F))) ≠
      SmtType.None := by rw [hBool]; simp
  have hAccNonNil := qforall_non_nil_of_non_none acc (qforall xs F) hAccNN
  have hAccExistsTy :
      __smtx_typeof
          (__eo_to_smt_exists acc (SmtTerm.not (__eo_to_smt (qforall xs F)))) =
        SmtType.Bool := by
    have hNot :
        __smtx_typeof
            (SmtTerm.not
              (__eo_to_smt_exists acc
                (SmtTerm.not (__eo_to_smt (qforall xs F))))) =
          SmtType.Bool := by
      simpa [eo_to_smt_forall_eq acc (qforall xs F) hAccNonNil] using hBool
    exact smtx_typeof_not_arg_of_bool _ hNot
  have hNotNestedTy :
      __smtx_typeof (SmtTerm.not (__eo_to_smt (qforall xs F))) =
        SmtType.Bool :=
    TranslationProofs.eo_to_smt_exists_body_bool_of_bool acc
      (SmtTerm.not (__eo_to_smt (qforall xs F))) hAccExistsTy
  have hNestedTy :
      __smtx_typeof (__eo_to_smt (qforall xs F)) = SmtType.Bool :=
    smtx_typeof_not_arg_of_bool _ hNotNestedTy
  have hXsNN : __smtx_typeof (__eo_to_smt (qforall xs F)) ≠ SmtType.None := by
    rw [hNestedTy]
    simp
  have hXsNonNil := qforall_non_nil_of_non_none xs F hXsNN
  have hXsExistsTy :
      __smtx_typeof (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F))) =
        SmtType.Bool := by
    have hNot :
        __smtx_typeof
            (SmtTerm.not
              (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F)))) =
          SmtType.Bool := by
      simpa [eo_to_smt_forall_eq xs F hXsNonNil] using hNestedTy
    exact smtx_typeof_not_arg_of_bool _ hNot
  have hInnerTy :
      __smtx_typeof
        (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F))) =
          SmtType.Bool := hXsExistsTy
  rcases eo_to_smt_exists_bool_as_eoList acc
      (SmtTerm.not (__eo_to_smt (qforall xs F))) hAccExistsTy with
    ⟨accs, hAccEq, hAccAll⟩
  rcases eo_to_smt_exists_bool_as_eoList xs (SmtTerm.not (__eo_to_smt F))
      hXsExistsTy with
    ⟨xss, hXsEq, hXsAll⟩
  have hAccsNonempty : accs ≠ [] := by
    intro hNil
    apply hAccNonNil
    rw [hAccEq, hNil]
    rfl
  have hXssNonempty : xss ≠ [] := by
    intro hNil
    apply hXsNonNil
    rw [hXsEq, hNil]
    rfl
  have hConcatNonNil :
      __eo_list_concat Term.__eo_List_cons acc xs ≠ Term.__eo_List_nil := by
    rw [hAccEq, hXsEq, eo_list_concat_eoListOfTerms]
    intro h
    cases accs with
    | nil => exact hAccsNonempty rfl
    | cons _ _ => simp [eoListOfTerms] at h
  have hAccInnerTy :
      __smtx_typeof
        (__eo_to_smt_exists acc
          (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F)))) =
        SmtType.Bool :=
    smtx_typeof_eo_to_smt_exists_same_binders acc
      (SmtTerm.not (__eo_to_smt (qforall xs F)))
      (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F)))
      hAccExistsTy hInnerTy
  have hConcatExistsTranslate :
      __eo_to_smt_exists (__eo_list_concat Term.__eo_List_cons acc xs)
          (SmtTerm.not (__eo_to_smt F)) =
        __eo_to_smt_exists acc
          (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F))) := by
    rw [hAccEq, hXsEq, eo_list_concat_eoListOfTerms]
    exact (eo_to_smt_exists_eoList_append accs xss
      (SmtTerm.not (__eo_to_smt F)) hAccAll).symm
  have hConcatExistsTy :
      __smtx_typeof
        (__eo_to_smt_exists (__eo_list_concat Term.__eo_List_cons acc xs)
          (SmtTerm.not (__eo_to_smt F))) = SmtType.Bool := by
    rw [hConcatExistsTranslate]
    exact hAccInnerTy
  constructor
  · rw [eo_to_smt_forall_eq acc (qforall xs F) hAccNonNil]
    rw [eo_to_smt_forall_eq
      (__eo_list_concat Term.__eo_List_cons acc xs) F hConcatNonNil]
    rw [eo_to_smt_forall_eq xs F hXsNonNil]
    rw [__smtx_model_eval.eq_7, __smtx_model_eval.eq_7]
    have hDouble :
        __smtx_model_eval M
            (__eo_to_smt_exists acc
              (SmtTerm.not
                (SmtTerm.not
                  (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F)))))) =
          __smtx_model_eval M
            (__eo_to_smt_exists acc
              (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F)))) :=
      smtx_model_eval_eo_to_smt_exists_double_not_body M hM acc
        (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F))) hInnerTy
    rw [hDouble, hConcatExistsTranslate]
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_forall_eq
      (__eo_list_concat Term.__eo_List_cons acc xs) F hConcatNonNil]
    exact smtx_typeof_not_bool_of_arg_bool _ hConcatExistsTy

private theorem merge_exists_eval
    (M : SmtModel) :
    ∀ F acc,
      RuleProofs.eo_has_bool_type (qexists acc F) ->
      acc ≠ Term.__eo_List_nil ->
      __smtx_model_eval M (__eo_to_smt (qexists acc F)) =
        __smtx_model_eval M
          (__eo_to_smt (__mk_quant_merge_prenex (Term.UOp UserOp.exists) F acc))
  | F, acc, hBool, hAccNonNil => by
      have hBoolTy := hBool
      unfold RuleProofs.eo_has_bool_type at hBoolTy
      have hAccExistsTy :
          __smtx_typeof (__eo_to_smt_exists acc (__eo_to_smt F)) =
            SmtType.Bool := by
        simpa [eo_to_smt_exists_eq acc F hAccNonNil] using hBoolTy
      have hBodyBool :
          __smtx_typeof (__eo_to_smt F) = SmtType.Bool :=
        TranslationProofs.eo_to_smt_exists_body_bool_of_bool acc
          (__eo_to_smt F) hAccExistsTy
      rcases eo_to_smt_exists_bool_as_eoList acc (__eo_to_smt F)
          hAccExistsTy with
        ⟨accs, hAccEq, _hAccAll⟩
      subst acc
      cases F with
      | Stuck =>
          have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
            change __smtx_typeof SmtTerm.None = SmtType.Bool at hBodyBool
            exact hBodyBool
          exact False.elim (false_of_smtx_typeof_none_bool hNone)
      | Apply f body =>
          cases f
          case Apply Q xs =>
            cases Q
            case UOp op =>
              cases op
              case «exists» =>
                change
                  __smtx_model_eval M
                      (__eo_to_smt (qexists (eoListOfTerms accs) (qexists xs body))) =
                    __smtx_model_eval M
                      (__eo_to_smt
                        (__mk_quant_merge_prenex (Term.UOp UserOp.exists)
                          (qexists xs body) (eoListOfTerms accs)))
                have hStep := qexists_concat_step M (eoListOfTerms accs) xs body hBool
                have hRec :=
                  merge_exists_eval M body
                    (__eo_list_concat Term.__eo_List_cons (eoListOfTerms accs) xs)
                    hStep.2
                    (by
                      have hStepBool := hStep.2
                      unfold RuleProofs.eo_has_bool_type at hStepBool
                      have hNN : __smtx_typeof
                          (__eo_to_smt
                            (qexists
                              (__eo_list_concat Term.__eo_List_cons
                                (eoListOfTerms accs) xs)
                              body)) ≠ SmtType.None := by
                        rw [hStepBool]
                        simp
                      exact qexists_non_nil_of_non_none
                        (__eo_list_concat Term.__eo_List_cons
                          (eoListOfTerms accs) xs) body hNN)
                rw [hStep.1]
                simpa [qexists, qterm, __mk_quant_merge_prenex, __eo_eq,
                  __eo_ite, native_ite, native_teq,
                  eoListOfTerms_ne_stuck] using hRec
              all_goals
                simp [qexists, qterm, __mk_quant_merge_prenex,
                  __eo_l_1___mk_quant_merge_prenex, __eo_eq, __eo_ite,
                  native_ite, native_teq, eoListOfTerms_ne_stuck]
            case Stuck =>
              have hBad : False := by
                have hNone :
                    __smtx_typeof
                        (__eo_to_smt ((Term.Stuck.Apply xs).Apply body)) =
                      SmtType.None := by
                  change
                    __smtx_typeof
                        (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt xs))
                          (__eo_to_smt body)) = SmtType.None
                  exact TranslationProofs.typeof_apply_apply_none_head_eq
                    (__eo_to_smt xs) (__eo_to_smt body)
                rw [hNone] at hBodyBool
                cases hBodyBool
              exact False.elim hBad
            all_goals
              simp [qexists, qterm, __mk_quant_merge_prenex,
                __eo_l_1___mk_quant_merge_prenex, __eo_eq, __eo_ite,
                native_ite, native_teq, eoListOfTerms_ne_stuck]
          all_goals
            simp [qexists, qterm, __mk_quant_merge_prenex,
              __eo_l_1___mk_quant_merge_prenex, eoListOfTerms_ne_stuck]
      | _ =>
          simp [qexists, qterm, __mk_quant_merge_prenex,
            __eo_l_1___mk_quant_merge_prenex, eoListOfTerms_ne_stuck]

private theorem merge_forall_eval
    (M : SmtModel) (hM : model_wf M) :
    ∀ F acc,
      RuleProofs.eo_has_bool_type (qforall acc F) ->
      acc ≠ Term.__eo_List_nil ->
      __smtx_model_eval M (__eo_to_smt (qforall acc F)) =
        __smtx_model_eval M
          (__eo_to_smt (__mk_quant_merge_prenex (Term.UOp UserOp.forall) F acc))
  | F, acc, hBool, hAccNonNil => by
      have hBoolTy := hBool
      unfold RuleProofs.eo_has_bool_type at hBoolTy
      have hAccNN :
          __smtx_typeof (__eo_to_smt (qforall acc F)) ≠ SmtType.None := by
        rw [hBoolTy]
        simp
      have hAccExistsTy :
          __smtx_typeof
              (__eo_to_smt_exists acc (SmtTerm.not (__eo_to_smt F))) =
            SmtType.Bool :=
        qforall_inner_exists_bool_of_non_none acc F hAccNN
      have hNotBodyBool :
          __smtx_typeof (SmtTerm.not (__eo_to_smt F)) = SmtType.Bool :=
        TranslationProofs.eo_to_smt_exists_body_bool_of_bool acc
          (SmtTerm.not (__eo_to_smt F)) hAccExistsTy
      have hBodyBool :
          __smtx_typeof (__eo_to_smt F) = SmtType.Bool :=
        smtx_typeof_not_arg_of_bool _ hNotBodyBool
      rcases eo_to_smt_exists_bool_as_eoList acc
          (SmtTerm.not (__eo_to_smt F)) hAccExistsTy with
        ⟨accs, hAccEq, _hAccAll⟩
      subst acc
      cases F with
      | Stuck =>
          have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
            change __smtx_typeof SmtTerm.None = SmtType.Bool at hBodyBool
            exact hBodyBool
          exact False.elim (false_of_smtx_typeof_none_bool hNone)
      | Apply f body =>
          cases f
          case Apply Q xs =>
            cases Q
            case UOp op =>
              cases op
              case «forall» =>
                change
                  __smtx_model_eval M
                      (__eo_to_smt (qforall (eoListOfTerms accs) (qforall xs body))) =
                    __smtx_model_eval M
                      (__eo_to_smt
                        (__mk_quant_merge_prenex (Term.UOp UserOp.forall)
                          (qforall xs body) (eoListOfTerms accs)))
                have hStep := qforall_concat_step M hM (eoListOfTerms accs) xs body hBool
                have hRec :=
                  merge_forall_eval M hM body
                    (__eo_list_concat Term.__eo_List_cons (eoListOfTerms accs) xs)
                    hStep.2
                    (by
                      have hStepBool := hStep.2
                      unfold RuleProofs.eo_has_bool_type at hStepBool
                      have hNN : __smtx_typeof
                          (__eo_to_smt
                            (qforall
                              (__eo_list_concat Term.__eo_List_cons
                                (eoListOfTerms accs) xs)
                              body)) ≠ SmtType.None := by
                        rw [hStepBool]
                        simp
                      exact qforall_non_nil_of_non_none
                        (__eo_list_concat Term.__eo_List_cons
                          (eoListOfTerms accs) xs) body hNN)
                rw [hStep.1]
                simpa [qforall, qterm, __mk_quant_merge_prenex, __eo_eq,
                  __eo_ite, native_ite, native_teq,
                  eoListOfTerms_ne_stuck] using hRec
              all_goals
                simp [qforall, qterm, __mk_quant_merge_prenex,
                  __eo_l_1___mk_quant_merge_prenex, __eo_eq, __eo_ite,
                  native_ite, native_teq, eoListOfTerms_ne_stuck]
            case Stuck =>
              have hBad : False := by
                have hNone :
                    __smtx_typeof
                        (__eo_to_smt ((Term.Stuck.Apply xs).Apply body)) =
                      SmtType.None := by
                  change
                    __smtx_typeof
                        (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt xs))
                          (__eo_to_smt body)) = SmtType.None
                  exact TranslationProofs.typeof_apply_apply_none_head_eq
                    (__eo_to_smt xs) (__eo_to_smt body)
                rw [hNone] at hBodyBool
                cases hBodyBool
              exact False.elim hBad
            all_goals
              simp [qforall, qterm, __mk_quant_merge_prenex,
                __eo_l_1___mk_quant_merge_prenex, __eo_eq, __eo_ite,
                native_ite, native_teq, eoListOfTerms_ne_stuck]
          all_goals
            simp [qforall, qterm, __mk_quant_merge_prenex,
              __eo_l_1___mk_quant_merge_prenex, eoListOfTerms_ne_stuck]
      | _ =>
          simp [qforall, qterm, __mk_quant_merge_prenex,
            __eo_l_1___mk_quant_merge_prenex, eoListOfTerms_ne_stuck]

private theorem eq_of_requires_ne_stuck {x y B : Term} :
    __eo_requires x y B ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hEq : native_teq x y = true
  · simpa [native_teq] using hEq
  · have hEqFalse : native_teq x y = false := by
      cases h : native_teq x y <;> simp [h] at hEq ⊢
    unfold __eo_requires at hReq
    simp [hEqFalse, native_ite] at hReq

private theorem body_ne_stuck_of_requires_ne_stuck {x y B : Term} :
    __eo_requires x y B ≠ Term.Stuck ->
    B ≠ Term.Stuck := by
  intro hReq hB
  subst B
  unfold __eo_requires at hReq
  by_cases hEq : native_teq x y = true
  · by_cases hStuck : native_teq x Term.Stuck = true
    · simp [hEq, hStuck, native_ite] at hReq
    · have hStuckFalse : native_teq x Term.Stuck = false := by
        cases h : native_teq x Term.Stuck <;> simp [h] at hStuck ⊢
      simp [hEq, hStuckFalse, native_ite] at hReq
  · have hEqFalse : native_teq x y = false := by
      cases h : native_teq x y <;> simp [h] at hEq ⊢
    simp [hEqFalse, native_ite] at hReq

private theorem lhs_ne_stuck_of_requires_ne_stuck {x y B : Term} :
    __eo_requires x y B ≠ Term.Stuck ->
    x ≠ Term.Stuck := by
  intro hReq hx
  subst x
  unfold __eo_requires at hReq
  simp [native_teq, native_ite, native_not, SmtEval.native_not] at hReq

private theorem eo_or_eq_true_cases_local (x y : Term) :
    __eo_or x y = Term.Boolean true ->
    x = Term.Boolean true ∨ y = Term.Boolean true := by
  intro h
  cases x <;> cases y <;> simp [__eo_or] at h ⊢
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp [native_or] at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hW : w1 = w2
    · subst w2
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at h
    · have hNumNe : Term.Numeral w1 ≠ Term.Numeral w2 := by
        intro hEq
        cases hEq
        exact hW rfl
      simp [__eo_requires, hNumNe, native_ite, native_teq] at h

private theorem quant_merge_shape_of_not_stuck
    (x1 : Term) :
    __eo_prog_quant_merge_prenex x1 ≠ Term.Stuck ->
    ∃ Q x F G,
      x1 = qeq (qterm Q x F) G ∧
      (Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists) ∧
      __eo_prog_quant_merge_prenex x1 = qeq (qterm Q x F) G ∧
      __mk_quant_merge_prenex Q (qterm Q x F) Term.__eo_List_nil = G := by
  intro hProg
  cases x1 with
  | Apply lhs G =>
      cases lhs with
      | Apply eqHead lhsArg =>
          cases eqHead with
          | UOp opEq =>
              cases opEq with
              | eq =>
                  cases lhsArg with
                  | Apply qHead F =>
                      cases qHead with
                      | Apply Q x =>
                          let v0 := qterm Q x F
                          let inner :=
                            __eo_requires
                              (__mk_quant_merge_prenex Q v0 Term.__eo_List_nil) G
                              (qeq v0 G)
                          have hReq :
                              __eo_requires
                                  (__eo_or (__eo_eq Q (Term.UOp UserOp.forall))
                                    (__eo_eq Q (Term.UOp UserOp.exists)))
                                  (Term.Boolean true) inner ≠ Term.Stuck := by
                            simpa [qeq, qterm, v0, inner,
                              __eo_prog_quant_merge_prenex] using hProg
                          have hGuard :
                              __eo_or (__eo_eq Q (Term.UOp UserOp.forall))
                                  (__eo_eq Q (Term.UOp UserOp.exists)) =
                                Term.Boolean true :=
                            eq_of_requires_ne_stuck hReq
                          have hInnerNe : inner ≠ Term.Stuck :=
                            body_ne_stuck_of_requires_ne_stuck hReq
                          have hMk :
                              __mk_quant_merge_prenex Q v0 Term.__eo_List_nil = G :=
                            eq_of_requires_ne_stuck hInnerNe
                          rcases eo_or_eq_true_cases_local
                              (__eo_eq Q (Term.UOp UserOp.forall))
                              (__eo_eq Q (Term.UOp UserOp.exists)) hGuard with
                            hForall | hExists
                          · have hQ : Q = Term.UOp UserOp.forall :=
                              (RuleProofs.eq_of_eo_eq_true Q
                                (Term.UOp UserOp.forall) hForall).symm
                            subst Q
                            refine ⟨Term.UOp UserOp.forall, x, F, G, rfl,
                              Or.inl rfl, ?_, ?_⟩
                            · change __eo_prog_quant_merge_prenex
                                (qeq (qterm (Term.UOp UserOp.forall) x F) G) =
                                  qeq (qterm (Term.UOp UserOp.forall) x F) G
                              have hMk' :
                                  __mk_quant_merge_prenex (Term.UOp UserOp.forall)
                                      (qterm (Term.UOp UserOp.forall) x F)
                                      Term.__eo_List_nil = G := by
                                simpa [v0, qterm] using hMk
                              have hMkNe :
                                  __mk_quant_merge_prenex (Term.UOp UserOp.forall)
                                      (qterm (Term.UOp UserOp.forall) x F)
                                      Term.__eo_List_nil ≠ Term.Stuck := by
                                simpa [v0, qterm] using
                                  lhs_ne_stuck_of_requires_ne_stuck hInnerNe
                              have hMkRaw :
                                  __mk_quant_merge_prenex (Term.UOp UserOp.forall)
                                      (((Term.UOp UserOp.forall).Apply x).Apply F)
                                      Term.__eo_List_nil = G := by
                                simpa [qterm] using hMk'
                              have hMkNeRaw :
                                  __mk_quant_merge_prenex (Term.UOp UserOp.forall)
                                      (((Term.UOp UserOp.forall).Apply x).Apply F)
                                      Term.__eo_List_nil ≠ Term.Stuck := by
                                simpa [qterm] using hMkNe
                              have hGuard' :
                                  __eo_or
                                      (__eo_eq (Term.UOp UserOp.forall)
                                        (Term.UOp UserOp.forall))
                                      (__eo_eq (Term.UOp UserOp.forall)
                                        (Term.UOp UserOp.exists)) =
                                    Term.Boolean true := by
                                simp [__eo_or, __eo_eq, native_or, native_teq]
                              have hGNe : G ≠ Term.Stuck := by
                                intro hG
                                exact hMkNe (hMk'.trans hG)
                              simp [qeq, qterm, __eo_prog_quant_merge_prenex,
                                hGuard', hMkRaw, hGNe,
                                __eo_requires, native_ite,
                                native_teq, native_not, SmtEval.native_not]
                            · simpa [v0, qterm] using hMk
                          · have hQ : Q = Term.UOp UserOp.exists :=
                              (RuleProofs.eq_of_eo_eq_true Q
                                (Term.UOp UserOp.exists) hExists).symm
                            subst Q
                            refine ⟨Term.UOp UserOp.exists, x, F, G, rfl,
                              Or.inr rfl, ?_, ?_⟩
                            · change __eo_prog_quant_merge_prenex
                                (qeq (qterm (Term.UOp UserOp.exists) x F) G) =
                                  qeq (qterm (Term.UOp UserOp.exists) x F) G
                              have hMk' :
                                  __mk_quant_merge_prenex (Term.UOp UserOp.exists)
                                      (qterm (Term.UOp UserOp.exists) x F)
                                      Term.__eo_List_nil = G := by
                                simpa [v0, qterm] using hMk
                              have hMkNe :
                                  __mk_quant_merge_prenex (Term.UOp UserOp.exists)
                                      (qterm (Term.UOp UserOp.exists) x F)
                                      Term.__eo_List_nil ≠ Term.Stuck := by
                                simpa [v0, qterm] using
                                  lhs_ne_stuck_of_requires_ne_stuck hInnerNe
                              have hMkRaw :
                                  __mk_quant_merge_prenex (Term.UOp UserOp.exists)
                                      (((Term.UOp UserOp.exists).Apply x).Apply F)
                                      Term.__eo_List_nil = G := by
                                simpa [qterm] using hMk'
                              have hMkNeRaw :
                                  __mk_quant_merge_prenex (Term.UOp UserOp.exists)
                                      (((Term.UOp UserOp.exists).Apply x).Apply F)
                                      Term.__eo_List_nil ≠ Term.Stuck := by
                                simpa [qterm] using hMkNe
                              have hGuard' :
                                  __eo_or
                                      (__eo_eq (Term.UOp UserOp.exists)
                                        (Term.UOp UserOp.forall))
                                      (__eo_eq (Term.UOp UserOp.exists)
                                        (Term.UOp UserOp.exists)) =
                                    Term.Boolean true := by
                                simp [__eo_or, __eo_eq, native_or, native_teq]
                              have hGNe : G ≠ Term.Stuck := by
                                intro hG
                                exact hMkNe (hMk'.trans hG)
                              simp [qeq, qterm, __eo_prog_quant_merge_prenex,
                                hGuard', hMkRaw, hGNe,
                                __eo_requires, native_ite,
                                native_teq, native_not, SmtEval.native_not]
                            · simpa [v0, qterm] using hMk
                      | _ =>
                          simp [__eo_prog_quant_merge_prenex] at hProg
                  | _ =>
                      simp [__eo_prog_quant_merge_prenex] at hProg
              | _ =>
                  simp [__eo_prog_quant_merge_prenex] at hProg
          | _ =>
              simp [__eo_prog_quant_merge_prenex] at hProg
      | _ =>
          simp [__eo_prog_quant_merge_prenex] at hProg
  | _ =>
      simp [__eo_prog_quant_merge_prenex] at hProg

private theorem quant_merge_eval
    (M : SmtModel) (hM : model_wf M)
    (Q x F : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hBool : RuleProofs.eo_has_bool_type
      (qeq (qterm Q x F)
        (__mk_quant_merge_prenex Q (qterm Q x F) Term.__eo_List_nil))) :
    __smtx_model_eval M (__eo_to_smt (qterm Q x F)) =
      __smtx_model_eval M
        (__eo_to_smt
          (__mk_quant_merge_prenex Q (qterm Q x F) Term.__eo_List_nil)) := by
  rcases hQ with hQ | hQ
  · subst Q
    have hEqBool := hBool
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (qforall x F)
        (__mk_quant_merge_prenex (Term.UOp UserOp.forall) (qforall x F)
          Term.__eo_List_nil) hEqBool with
      ⟨_hSameTy, hLhsNN⟩
    have hxNonNil := qforall_non_nil_of_non_none x F hLhsNN
    have hLhsBool :
        RuleProofs.eo_has_bool_type (qforall x F) :=
      qforall_top_bool_of_non_none x F hLhsNN
    have hInnerTy :
        __smtx_typeof (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
          SmtType.Bool :=
      qforall_inner_exists_bool_of_non_none x F hLhsNN
    rcases eo_to_smt_exists_bool_as_eoList x (SmtTerm.not (__eo_to_smt F))
        hInnerTy with
      ⟨xs, hxEq, hxAll⟩
    have hXsNonempty : xs ≠ [] := by
      intro hNil
      apply hxNonNil
      rw [hxEq, hNil]
      rfl
    have hConcatNil :
        __eo_list_concat Term.__eo_List_cons Term.__eo_List_nil x = x := by
      rw [hxEq]
      exact eo_list_concat_eoListOfTerms [] xs
    have hMkStart :
        __mk_quant_merge_prenex (Term.UOp UserOp.forall) (qforall x F)
            Term.__eo_List_nil =
          __mk_quant_merge_prenex (Term.UOp UserOp.forall) F x := by
      change
        __eo_ite
            (__eo_eq (Term.UOp UserOp.forall) (Term.UOp UserOp.forall))
            (__mk_quant_merge_prenex (Term.UOp UserOp.forall) F
              (__eo_list_concat Term.__eo_List_cons Term.__eo_List_nil x))
            (__eo_l_1___mk_quant_merge_prenex (Term.UOp UserOp.forall)
              (qforall x F) Term.__eo_List_nil) =
          __mk_quant_merge_prenex (Term.UOp UserOp.forall) F x
      simp [__eo_eq, __eo_ite, hConcatNil, native_ite, native_teq]
    change
      __smtx_model_eval M (__eo_to_smt (qforall x F)) =
        __smtx_model_eval M
          (__eo_to_smt
            (__mk_quant_merge_prenex (Term.UOp UserOp.forall)
              (qforall x F) Term.__eo_List_nil))
    rw [hMkStart]
    exact merge_forall_eval M hM F x hLhsBool hxNonNil
  · subst Q
    have hEqBool := hBool
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (qexists x F)
        (__mk_quant_merge_prenex (Term.UOp UserOp.exists) (qexists x F)
          Term.__eo_List_nil) hEqBool with
      ⟨_hSameTy, hLhsNN⟩
    have hxNonNil := qexists_non_nil_of_non_none x F hLhsNN
    have hLhsBool :
        RuleProofs.eo_has_bool_type (qexists x F) :=
      eo_to_smt_exists_top_bool_of_non_none x F hLhsNN
    have hExistsTy :
        __smtx_typeof (__eo_to_smt_exists x (__eo_to_smt F)) =
          SmtType.Bool := by
      have hLhsBoolTy := hLhsBool
      unfold RuleProofs.eo_has_bool_type at hLhsBoolTy
      simpa [eo_to_smt_exists_eq x F hxNonNil] using hLhsBoolTy
    rcases eo_to_smt_exists_bool_as_eoList x (__eo_to_smt F) hExistsTy with
      ⟨xs, hxEq, hxAll⟩
    have hXsNonempty : xs ≠ [] := by
      intro hNil
      apply hxNonNil
      rw [hxEq, hNil]
      rfl
    have hConcatNil :
        __eo_list_concat Term.__eo_List_cons Term.__eo_List_nil x = x := by
      rw [hxEq]
      exact eo_list_concat_eoListOfTerms [] xs
    have hMkStart :
        __mk_quant_merge_prenex (Term.UOp UserOp.exists) (qexists x F)
            Term.__eo_List_nil =
          __mk_quant_merge_prenex (Term.UOp UserOp.exists) F x := by
      change
        __eo_ite
            (__eo_eq (Term.UOp UserOp.exists) (Term.UOp UserOp.exists))
            (__mk_quant_merge_prenex (Term.UOp UserOp.exists) F
              (__eo_list_concat Term.__eo_List_cons Term.__eo_List_nil x))
            (__eo_l_1___mk_quant_merge_prenex (Term.UOp UserOp.exists)
              (qexists x F) Term.__eo_List_nil) =
          __mk_quant_merge_prenex (Term.UOp UserOp.exists) F x
      simp [__eo_eq, __eo_ite, hConcatNil, native_ite, native_teq]
    change
      __smtx_model_eval M (__eo_to_smt (qexists x F)) =
        __smtx_model_eval M
          (__eo_to_smt
            (__mk_quant_merge_prenex (Term.UOp UserOp.exists)
              (qexists x F) Term.__eo_List_nil))
    rw [hMkStart]
    exact merge_exists_eval M F x hLhsBool hxNonNil

public theorem cmd_step_quant_merge_prenex_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_merge_prenex args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.quant_merge_prenex args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_merge_prenex args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.quant_merge_prenex args premises ≠
        Term.Stuck :=
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
              have hTransA1 : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using
                  hCmdTrans
              have hProgQuant :
                  __eo_prog_quant_merge_prenex a1 ≠ Term.Stuck := by
                change __eo_prog_quant_merge_prenex a1 ≠ Term.Stuck at hProg
                simpa using hProg
              rcases quant_merge_shape_of_not_stuck a1 hProgQuant with
                ⟨Q, x, F, G, ha1, hQ, hProgEq, hMkEq⟩
              have hTransFormula :
                  RuleProofs.eo_has_smt_translation (qeq (qterm Q x F) G) := by
                simpa [ha1] using hTransA1
              have hFormulaType :
                  __eo_typeof (qeq (qterm Q x F) G) = Term.Bool := by
                change __eo_typeof (__eo_prog_quant_merge_prenex a1) =
                  Term.Bool at hResultTy
                rw [hProgEq] at hResultTy
                exact hResultTy
              have hFormulaBool :
                  RuleProofs.eo_has_bool_type (qeq (qterm Q x F) G) :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  (qeq (qterm Q x F) G) hTransFormula hFormulaType
              have hMkFormulaBool :
                  RuleProofs.eo_has_bool_type
                    (qeq (qterm Q x F)
                      (__mk_quant_merge_prenex Q (qterm Q x F)
                        Term.__eo_List_nil)) := by
                simpa [hMkEq] using hFormulaBool
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M
                  (__eo_prog_quant_merge_prenex a1) true
                rw [hProgEq]
                apply RuleProofs.eo_interprets_eq_of_rel M
                  (qterm Q x F) G
                · exact hFormulaBool
                · have hEvalEq :=
                    quant_merge_eval M hM Q x F hQ hMkFormulaBool
                  rw [hMkEq] at hEvalEq
                  rw [hEvalEq]
                  exact RuleProofs.smt_value_rel_refl
                    (__smtx_model_eval M (__eo_to_smt G))
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_quant_merge_prenex a1)
                rw [hProgEq]
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  hFormulaBool
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
