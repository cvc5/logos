module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport
public import Cpc.Proofs.RuleSupport.StringSupport
import all Cpc.Proofs.RuleSupport.StringSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private inductive OrClause : Term -> Prop where
  | false : OrClause (Term.Boolean false)
  | cons (x xs : Term) : OrClause xs ->
      OrClause (Term.Apply (Term.Apply Term.or x) xs)

private theorem is_ok_true_of_ne_stuck {x : Term} :
    x ≠ Term.Stuck ->
    __eo_is_ok x = Term.Boolean true := by
  intro hNe
  cases x <;> simp [__eo_is_ok, native_teq, native_not, SmtEval.native_not] at hNe ⊢

private theorem is_list_true_of_get_nil_rec_ne_stuck {f x : Term} :
    __eo_get_nil_rec f x ≠ Term.Stuck ->
    __eo_is_list f x = Term.Boolean true := by
  intro hRec
  have hF : f ≠ Term.Stuck := by
    intro hF
    subst hF
    simp [__eo_get_nil_rec] at hRec
  have hX : x ≠ Term.Stuck := by
    intro hX
    subst hX
    simp [__eo_get_nil_rec] at hRec
  simp [__eo_is_list, is_ok_true_of_ne_stuck hRec]

private theorem orClause_of_is_list_true {c : Term} :
    __eo_is_list Term.or c = Term.Boolean true -> OrClause c := by
  intro hList
  cases c with
  | Stuck =>
      simp [__eo_is_list
        ] at hList
  | Boolean b =>
      cases b with
      | false =>
          exact OrClause.false
      | true =>
          simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
            __eo_is_list_nil, native_ite, native_teq, native_not,
            SmtEval.native_not] at hList
  | Apply f a =>
      cases f with
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | or =>
                  unfold __eo_is_list at hList
                  unfold __eo_is_ok at hList
                  unfold __eo_get_nil_rec at hList
                  unfold __eo_requires at hList
                  simp [native_ite, native_teq, native_not, SmtEval.native_not] at hList
                  exact OrClause.cons x a
                    (orClause_of_is_list_true (is_list_true_of_get_nil_rec_ne_stuck hList))
              | _ =>
                  simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
                    native_ite, native_teq, native_not,
                    SmtEval.native_not] at hList
          | _ =>
              simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
                native_ite, native_teq, native_not,
                SmtEval.native_not] at hList
      | _ =>
          simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
            __eo_is_list_nil, native_ite, native_teq, native_not,
            SmtEval.native_not] at hList
  | _ =>
      simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
        __eo_is_list_nil, native_ite, native_teq, native_not,
        SmtEval.native_not] at hList

private theorem orClause_get_nil_rec_ne_stuck {c : Term} :
    OrClause c -> __eo_get_nil_rec Term.or c ≠ Term.Stuck := by
  intro hClause
  induction hClause with
  | false =>
      simp [__eo_get_nil_rec, __eo_requires, __eo_is_list_nil, native_ite,
        native_teq, native_not, SmtEval.native_not]
  | cons x xs hXs ih =>
      simpa [__eo_get_nil_rec, __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] using ih

private theorem orClause_is_list_true {c : Term} :
    OrClause c -> __eo_is_list Term.or c = Term.Boolean true := by
  intro hClause
  exact is_list_true_of_get_nil_rec_ne_stuck (orClause_get_nil_rec_ne_stuck hClause)

private theorem orClause_ne_stuck {c : Term} :
    OrClause c -> c ≠ Term.Stuck := by
  intro hClause
  cases hClause <;> simp

private theorem eo_eq_eq_true_of_eq {x y : Term} :
    x = y ->
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    __eo_eq x y = Term.Boolean true := by
  intro hEq hX hY
  subst y
  cases x <;> simp [__eo_eq, native_teq] at hX ⊢

private theorem eo_eq_eq_false_of_ne {x y : Term} :
    x ≠ y ->
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    __eo_eq x y = Term.Boolean false := by
  intro hNe hX hY
  by_cases hEq : x = y
  · exact False.elim (hNe hEq)
  · cases x <;> cases y <;>
      simp [__eo_eq, native_teq, eq_comm, hEq] at hNe hX hY ⊢ <;> contradiction

private theorem list_erase_rec_cons_eq
    (x xs e : Term) :
    x = e ->
    x ≠ Term.Stuck ->
    e ≠ Term.Stuck ->
    __eo_list_erase_rec (Term.Apply (Term.Apply Term.or x) xs) e = xs := by
  intro hEq hX hE
  have hEqTerm : __eo_eq x e = Term.Boolean true :=
    eo_eq_eq_true_of_eq hEq hX hE
  simp [__eo_list_erase_rec, hEqTerm, __eo_ite, native_ite, native_teq]

private theorem list_erase_rec_cons_ne
    (x xs e : Term) :
    x ≠ e ->
    x ≠ Term.Stuck ->
    e ≠ Term.Stuck ->
    __eo_list_erase_rec xs e ≠ Term.Stuck ->
    __eo_list_erase_rec (Term.Apply (Term.Apply Term.or x) xs) e =
      Term.Apply (Term.Apply Term.or x) (__eo_list_erase_rec xs e) := by
  intro hNe hX hE hTail
  have hEqTerm : __eo_eq x e = Term.Boolean false :=
    eo_eq_eq_false_of_ne hNe hX hE
  cases hRec : __eo_list_erase_rec xs e <;>
    simp [__eo_list_erase_rec, hEqTerm, __eo_ite, __eo_mk_apply, native_ite, native_teq,
      hRec] at hTail ⊢

private theorem erase_rec_preserves_orClause {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    OrClause (__eo_list_erase_rec c e) := by
  intro hClause hCBool hE
  induction hClause generalizing e with
  | false =>
      simpa [__eo_list_erase_rec] using OrClause.false
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hTail : OrClause (__eo_list_erase_rec xs e) := ih hXsBool hE
      have hTailNe : __eo_list_erase_rec xs e ≠ Term.Stuck :=
        orClause_ne_stuck hTail
      by_cases hEq : x = e
      · rw [list_erase_rec_cons_eq x xs e hEq hX hE]
        exact hXs
      · rw [list_erase_rec_cons_ne x xs e hEq hX hE hTailNe]
        exact OrClause.cons x (__eo_list_erase_rec xs e) hTail

private theorem erase_preserves_orClause {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    OrClause (__eo_list_erase Term.or c e) := by
  intro hClause hCBool hE
  change OrClause
    (__eo_requires (__eo_is_list Term.or c) (Term.Boolean true)
      (__eo_list_erase_rec c e))
  rw [orClause_is_list_true hClause]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact erase_rec_preserves_orClause hClause hCBool hE

private theorem eo_to_smt_false_eq :
    __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false := by
  rfl

private theorem eo_to_smt_not_eq (t : Term) :
    __eo_to_smt (Term.Apply Term.not t) = SmtTerm.not (__eo_to_smt t) := by
  rfl

private theorem eo_interprets_false (M : SmtModel) :
    eo_interprets M (Term.Boolean false) false := by
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  rw [eo_to_smt_false_eq]
  refine smt_interprets.intro_false M (SmtTerm.Boolean false) ?_ ?_
  · rw [__smtx_typeof.eq_1]
  · rw [__smtx_model_eval.eq_1]

private theorem eo_interprets_or_right_of_left_false
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    eo_interprets M A false ->
    eo_interprets M (Term.Apply (Term.Apply Term.or A) B) true ->
    eo_interprets M B true := by
  intro hAFalse hOrTrue
  have hABool : RuleProofs.eo_has_bool_type A :=
    RuleProofs.eo_has_bool_type_of_interprets_false M A hAFalse
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hAFalse hOrTrue ⊢
  rw [RuleProofs.eo_to_smt_or_eq A B] at hOrTrue
  cases hAFalse with
  | intro_false _ hEvalA =>
      cases hOrTrue with
      | intro_true hTyOr hEvalOr =>
          have hBBool : RuleProofs.eo_has_bool_type B :=
            RuleProofs.eo_has_bool_type_or_right A B
              (by simpa [RuleProofs.eo_has_bool_type, RuleProofs.eo_to_smt_or_eq] using hTyOr)
          refine smt_interprets.intro_true M (__eo_to_smt B) hBBool ?_
          rw [__smtx_model_eval.eq_8] at hEvalOr
          rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM B hBBool with ⟨b, hEvalB⟩
          rw [hEvalA, hEvalB, __smtx_model_eval_or, SmtEval.native_or] at hEvalOr
          cases b <;> simp at hEvalOr
          exact hEvalB

private theorem eo_interprets_or_left_of_right_false
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    eo_interprets M B false ->
    eo_interprets M (Term.Apply (Term.Apply Term.or A) B) true ->
    eo_interprets M A true := by
  intro hBFalse hOrTrue
  have hBBool : RuleProofs.eo_has_bool_type B :=
    RuleProofs.eo_has_bool_type_of_interprets_false M B hBFalse
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hBFalse hOrTrue ⊢
  rw [RuleProofs.eo_to_smt_or_eq A B] at hOrTrue
  cases hBFalse with
  | intro_false _ hEvalB =>
      cases hOrTrue with
      | intro_true hTyOr hEvalOr =>
          have hABool : RuleProofs.eo_has_bool_type A :=
            RuleProofs.eo_has_bool_type_or_left A B
              (by simpa [RuleProofs.eo_has_bool_type, RuleProofs.eo_to_smt_or_eq] using hTyOr)
          refine smt_interprets.intro_true M (__eo_to_smt A) hABool ?_
          rw [__smtx_model_eval.eq_8] at hEvalOr
          rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM A hABool with ⟨a, hEvalA⟩
          rw [hEvalA, hEvalB, __smtx_model_eval_or, SmtEval.native_or] at hEvalOr
          cases a <;> simp at hEvalOr
          exact hEvalA

private theorem eo_interprets_not_false_of_true (M : SmtModel) (t : Term) :
    eo_interprets M t true ->
    eo_interprets M (Term.Apply Term.not t) false := by
  intro hTrue
  have hTy : RuleProofs.eo_has_bool_type t :=
    RuleProofs.eo_has_bool_type_of_interprets_true M t hTrue
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hTrue ⊢
  rw [eo_to_smt_not_eq]
  cases hTrue with
  | intro_true _ hEval =>
      refine smt_interprets.intro_false M (SmtTerm.not (__eo_to_smt t)) ?_ ?_
      · simpa [RuleProofs.eo_has_bool_type, eo_to_smt_not_eq]
          using RuleProofs.eo_has_bool_type_not_of_bool_arg t hTy
      · rw [__smtx_model_eval.eq_7]
        rw [hEval]
        simp [__smtx_model_eval_not, SmtEval.native_not]

private theorem to_clause_has_bool_type {c : Term} :
    RuleProofs.eo_has_bool_type c ->
    RuleProofs.eo_has_bool_type (__to_clause c) := by
  intro hCBool
  cases c with
  | Stuck =>
      exact False.elim ((RuleProofs.term_ne_stuck_of_has_bool_type _ hCBool) rfl)
  | Apply f a =>
      cases hf : f with
      | Apply g x =>
          rw [hf] at hCBool
          cases hg : g with
          | UOp op =>
              cases op with
              | or =>
                  simpa [__to_clause, hf, hg] using hCBool
              | _ =>
                  simpa [__to_clause, hf, hg] using
                    RuleProofs.eo_has_bool_type_or_of_bool_args
                      (Term.Apply (Term.Apply g x) a) (Term.Boolean false)
                      hCBool RuleProofs.eo_has_bool_type_false
          | _ =>
              simpa [__to_clause, hf, hg] using
                RuleProofs.eo_has_bool_type_or_of_bool_args
                  (Term.Apply (Term.Apply g x) a) (Term.Boolean false)
                  hCBool RuleProofs.eo_has_bool_type_false
      | _ =>
          simpa [__to_clause, hf] using
            RuleProofs.eo_has_bool_type_or_of_bool_args
              (Term.Apply f a) (Term.Boolean false) hCBool RuleProofs.eo_has_bool_type_false
  | Boolean b =>
      cases b with
      | false =>
          simpa [__to_clause] using RuleProofs.eo_has_bool_type_false
      | true =>
          simpa [__to_clause] using
            RuleProofs.eo_has_bool_type_or_of_bool_args
              (Term.Boolean true) (Term.Boolean false)
              hCBool RuleProofs.eo_has_bool_type_false
  | _ =>
      simpa [__to_clause] using
        RuleProofs.eo_has_bool_type_or_of_bool_args
          _ (Term.Boolean false) hCBool RuleProofs.eo_has_bool_type_false

private theorem to_clause_interprets_true
    (M : SmtModel) (hM : model_wf M) {c : Term} :
    eo_interprets M c true ->
    eo_interprets M (__to_clause c) true := by
  intro hCTrue
  have hCBool : RuleProofs.eo_has_bool_type c :=
    RuleProofs.eo_has_bool_type_of_interprets_true M c hCTrue
  cases c with
  | Stuck =>
      exact False.elim ((RuleProofs.term_ne_stuck_of_interprets_true M _ hCTrue) rfl)
  | Apply f a =>
      cases hf : f with
      | Apply g x =>
          rw [hf] at hCTrue
          cases hg : g with
          | UOp op =>
              cases op with
              | or =>
                  simpa [__to_clause, hf, hg] using hCTrue
              | _ =>
                  simpa [__to_clause, hf, hg] using
                    RuleProofs.eo_interprets_or_left_intro M hM
                      (Term.Apply (Term.Apply g x) a) (Term.Boolean false) hCTrue
                      RuleProofs.eo_has_bool_type_false
          | _ =>
              simpa [__to_clause, hf, hg] using
                RuleProofs.eo_interprets_or_left_intro M hM
                  (Term.Apply (Term.Apply g x) a) (Term.Boolean false) hCTrue
                  RuleProofs.eo_has_bool_type_false
      | _ =>
          simpa [__to_clause, hf] using
            RuleProofs.eo_interprets_or_left_intro M hM
              (Term.Apply f a) (Term.Boolean false) hCTrue
              RuleProofs.eo_has_bool_type_false
  | Boolean b =>
      cases b with
      | false =>
          exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hCTrue)
            (eo_interprets_false M))
      | true =>
          simpa [__to_clause] using
            RuleProofs.eo_interprets_or_left_intro M hM
              (Term.Boolean true) (Term.Boolean false) hCTrue
              RuleProofs.eo_has_bool_type_false
  | _ =>
      simpa [__to_clause] using
        RuleProofs.eo_interprets_or_left_intro M hM
          _ (Term.Boolean false) hCTrue RuleProofs.eo_has_bool_type_false

private theorem list_erase_nonstuck_input_orClause {c e : Term} :
    __eo_list_erase Term.or c e ≠ Term.Stuck ->
    OrClause c := by
  intro hErase
  have hList : __eo_is_list Term.or c = Term.Boolean true := by
    cases hIs : __eo_is_list Term.or c with
    | Boolean b =>
        simp [__eo_list_erase, __eo_requires, hIs, native_ite, native_teq, native_not,
          SmtEval.native_not] at hErase ⊢
        exact hErase.1
    | _ =>
        simp [__eo_list_erase, __eo_requires, hIs, native_ite, native_teq
          ] at hErase
  exact orClause_of_is_list_true hList

private theorem eo_interprets_bool_cases
    (M : SmtModel) (hM : model_wf M) (t : Term) :
    RuleProofs.eo_has_bool_type t ->
    eo_interprets M t true ∨ eo_interprets M t false := by
  intro hTy
  rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM t hTy with ⟨b, hEval⟩
  cases b with
  | true =>
      exact Or.inl (RuleProofs.eo_interprets_of_bool_eval M t true hTy hEval)
  | false =>
      exact Or.inr (RuleProofs.eo_interprets_of_bool_eval M t false hTy hEval)

private theorem erase_rec_preserves_bool_type {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_list_erase_rec c e) := by
  intro hClause hCBool hE
  induction hClause generalizing e with
  | false =>
      simpa [__eo_list_erase_rec] using RuleProofs.eo_has_bool_type_false
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      by_cases hEq : x = e
      · rw [list_erase_rec_cons_eq x xs e hEq hX hE]
        exact hXsBool
      · have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_erase_rec xs e) :=
          ih hXsBool hE
        have hTailNe : __eo_list_erase_rec xs e ≠ Term.Stuck :=
          RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
        rw [list_erase_rec_cons_ne x xs e hEq hX hE hTailNe]
        exact RuleProofs.eo_has_bool_type_or_of_bool_args x (__eo_list_erase_rec xs e)
          hXBool hTailBool

private theorem erase_preserves_bool_type {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_list_erase Term.or c e) := by
  intro hClause hCBool hE
  change RuleProofs.eo_has_bool_type
    (__eo_requires (__eo_is_list Term.or c) (Term.Boolean true) (__eo_list_erase_rec c e))
  rw [orClause_is_list_true hClause]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact erase_rec_preserves_bool_type hClause hCBool hE

private theorem erase_rec_true_of_good_lit
    (M : SmtModel) (hM : model_wf M) {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c true ->
    (¬ RuleProofs.eo_has_bool_type e ∨ eo_interprets M e false) ->
    e ≠ Term.Stuck ->
    eo_interprets M (__eo_list_erase_rec c e) true := by
  intro hClause hCBool hCTrue hGood hE
  induction hClause generalizing e with
  | false =>
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hCTrue)
        (eo_interprets_false M))
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_erase_rec xs e) :=
        erase_rec_preserves_bool_type hXs hXsBool hE
      have hOrTrue : eo_interprets M (Term.Apply (Term.Apply Term.or x) xs) true := by
        simpa using hCTrue
      by_cases hEq : x = e
      · rw [list_erase_rec_cons_eq x xs e hEq hX hE]
        cases hGood with
        | inl hENotBool =>
            exfalso
            apply hENotBool
            simpa [hEq] using hXBool
        | inr hEFalse =>
            have hXFalse : eo_interprets M x false := by
              simpa [hEq] using hEFalse
            exact eo_interprets_or_right_of_left_false M hM x xs hXFalse hOrTrue
      · rcases eo_interprets_bool_cases M hM x hXBool with hXTrue | hXFalse
        · have hTailNe : __eo_list_erase_rec xs e ≠ Term.Stuck :=
            RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
          rw [list_erase_rec_cons_ne x xs e hEq hX hE hTailNe]
          exact RuleProofs.eo_interprets_or_left_intro M hM
            x (__eo_list_erase_rec xs e) hXTrue hTailBool
        · have hXsTrue : eo_interprets M xs true :=
            eo_interprets_or_right_of_left_false M hM x xs hXFalse hOrTrue
          have hTailTrue : eo_interprets M (__eo_list_erase_rec xs e) true :=
            ih hXsBool hXsTrue hGood hE
          have hTailNe : __eo_list_erase_rec xs e ≠ Term.Stuck :=
            RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
          rw [list_erase_rec_cons_ne x xs e hEq hX hE hTailNe]
          exact RuleProofs.eo_interprets_or_right_intro M hM
            x (__eo_list_erase_rec xs e) hXBool hTailTrue

private theorem erase_true_of_good_lit
    (M : SmtModel) (hM : model_wf M) {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c true ->
    (¬ RuleProofs.eo_has_bool_type e ∨ eo_interprets M e false) ->
    e ≠ Term.Stuck ->
    eo_interprets M (__eo_list_erase Term.or c e) true := by
  intro hClause hCBool hCTrue hGood hE
  change eo_interprets M
    (__eo_requires (__eo_is_list Term.or c) (Term.Boolean true) (__eo_list_erase_rec c e)) true
  rw [orClause_is_list_true hClause]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact erase_rec_true_of_good_lit M hM hClause hCBool hCTrue hGood hE

private theorem concat_rec_preserves_orClause {c1 c2 : Term} :
    OrClause c1 ->
    OrClause c2 ->
    OrClause (__eo_list_concat_rec c1 c2) := by
  intro hC1 hC2
  have concat_rec_false (z : Term) :
      __eo_list_concat_rec (Term.Boolean false) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  have concat_rec_cons (x xs z : Term) :
      __eo_list_concat_rec xs z ≠ Term.Stuck ->
      __eo_list_concat_rec (Term.Apply (Term.Apply Term.or x) xs) z =
        Term.Apply (Term.Apply Term.or x) (__eo_list_concat_rec xs z) := by
    intro hTail
    cases z with
    | Stuck =>
        have hStuck : __eo_list_concat_rec xs Term.Stuck = Term.Stuck := by
          cases xs <;> simp [__eo_list_concat_rec]
        exact False.elim (hTail hStuck)
    | _ =>
        simp [__eo_list_concat_rec, __eo_mk_apply]
  induction hC1 generalizing c2 with
  | false =>
      rw [concat_rec_false c2]
      exact hC2
  | cons x xs hXs ih =>
      have hTail : OrClause (__eo_list_concat_rec xs c2) := ih hC2
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck := orClause_ne_stuck hTail
      rw [concat_rec_cons x xs c2 hTailNe]
      exact OrClause.cons x (__eo_list_concat_rec xs c2) hTail

private theorem concat_preserves_orClause {c1 c2 : Term} :
    OrClause c1 ->
    OrClause c2 ->
    OrClause (__eo_list_concat Term.or c1 c2) := by
  intro hC1 hC2
  change OrClause
    (__eo_requires (__eo_is_list Term.or c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list Term.or c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2)))
  rw [orClause_is_list_true hC1, orClause_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact concat_rec_preserves_orClause hC1 hC2

private theorem concat_rec_preserves_bool_type {c1 c2 : Term} :
    OrClause c1 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    RuleProofs.eo_has_bool_type (__eo_list_concat_rec c1 c2) := by
  intro hC1 hC1Bool hC2Bool
  have concat_rec_false (z : Term) :
      __eo_list_concat_rec (Term.Boolean false) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  have concat_rec_cons (x xs z : Term) :
      __eo_list_concat_rec xs z ≠ Term.Stuck ->
      __eo_list_concat_rec (Term.Apply (Term.Apply Term.or x) xs) z =
        Term.Apply (Term.Apply Term.or x) (__eo_list_concat_rec xs z) := by
    intro hTail
    cases z with
    | Stuck =>
        have hStuck : __eo_list_concat_rec xs Term.Stuck = Term.Stuck := by
          cases xs <;> simp [__eo_list_concat_rec]
        exact False.elim (hTail hStuck)
    | _ =>
        simp [__eo_list_concat_rec, __eo_mk_apply]
  induction hC1 generalizing c2 with
  | false =>
      rw [concat_rec_false c2]
      exact hC2Bool
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hC1Bool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hC1Bool
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
        ih hXsBool hC2Bool
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
      rw [concat_rec_cons x xs c2 hTailNe]
      exact RuleProofs.eo_has_bool_type_or_of_bool_args
        x (__eo_list_concat_rec xs c2) hXBool hTailBool

private theorem concat_preserves_bool_type {c1 c2 : Term} :
    OrClause c1 ->
    OrClause c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    RuleProofs.eo_has_bool_type (__eo_list_concat Term.or c1 c2) := by
  intro hC1 hC2 hC1Bool hC2Bool
  change RuleProofs.eo_has_bool_type
    (__eo_requires (__eo_is_list Term.or c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list Term.or c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2)))
  rw [orClause_is_list_true hC1, orClause_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact concat_rec_preserves_bool_type hC1 hC1Bool hC2Bool

private theorem concat_rec_true_of_left_true
    (M : SmtModel) (hM : model_wf M) {c1 c2 : Term} :
    OrClause c1 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M c1 true ->
    eo_interprets M (__eo_list_concat_rec c1 c2) true := by
  intro hC1 hC1Bool hC2Bool hC1True
  have concat_rec_false (z : Term) :
      __eo_list_concat_rec (Term.Boolean false) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  have concat_rec_cons (x xs z : Term) :
      __eo_list_concat_rec xs z ≠ Term.Stuck ->
      __eo_list_concat_rec (Term.Apply (Term.Apply Term.or x) xs) z =
        Term.Apply (Term.Apply Term.or x) (__eo_list_concat_rec xs z) := by
    intro hTail
    cases z with
    | Stuck =>
        have hStuck : __eo_list_concat_rec xs Term.Stuck = Term.Stuck := by
          cases xs <;> simp [__eo_list_concat_rec]
        exact False.elim (hTail hStuck)
    | _ =>
        simp [__eo_list_concat_rec, __eo_mk_apply]
  induction hC1 generalizing c2 with
  | false =>
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hC1True)
        (eo_interprets_false M))
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hC1Bool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hC1Bool
      have hOrTrue : eo_interprets M (Term.Apply (Term.Apply Term.or x) xs) true := by
        simpa using hC1True
      rcases eo_interprets_bool_cases M hM x hXBool with hXTrue | hXFalse
      · have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
            concat_rec_preserves_bool_type hXs hXsBool hC2Bool
        have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
            RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
        rw [concat_rec_cons x xs c2 hTailNe]
        exact RuleProofs.eo_interprets_or_left_intro M hM
          x (__eo_list_concat_rec xs c2) hXTrue hTailBool
      · have hXsTrue : eo_interprets M xs true :=
          eo_interprets_or_right_of_left_false M hM x xs hXFalse hOrTrue
        have hTailTrue : eo_interprets M (__eo_list_concat_rec xs c2) true :=
          ih hXsBool hC2Bool hXsTrue
        have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
          concat_rec_preserves_bool_type hXs hXsBool hC2Bool
        have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
          RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
        rw [concat_rec_cons x xs c2 hTailNe]
        exact RuleProofs.eo_interprets_or_right_intro M hM
          x (__eo_list_concat_rec xs c2) hXBool hTailTrue

private theorem concat_rec_true_of_right_true
    (M : SmtModel) (hM : model_wf M) {c1 c2 : Term} :
    OrClause c1 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M c2 true ->
    eo_interprets M (__eo_list_concat_rec c1 c2) true := by
  intro hC1 hC1Bool hC2Bool hC2True
  have concat_rec_false (z : Term) :
      __eo_list_concat_rec (Term.Boolean false) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  have concat_rec_cons (x xs z : Term) :
      __eo_list_concat_rec xs z ≠ Term.Stuck ->
      __eo_list_concat_rec (Term.Apply (Term.Apply Term.or x) xs) z =
        Term.Apply (Term.Apply Term.or x) (__eo_list_concat_rec xs z) := by
    intro hTail
    cases z with
    | Stuck =>
        have hStuck : __eo_list_concat_rec xs Term.Stuck = Term.Stuck := by
          cases xs <;> simp [__eo_list_concat_rec]
        exact False.elim (hTail hStuck)
    | _ =>
        simp [__eo_list_concat_rec, __eo_mk_apply]
  induction hC1 generalizing c2 with
  | false =>
      rw [concat_rec_false c2]
      exact hC2True
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hC1Bool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hC1Bool
      have hTailTrue : eo_interprets M (__eo_list_concat_rec xs c2) true :=
        ih hXsBool hC2Bool hC2True
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
        concat_rec_preserves_bool_type hXs hXsBool hC2Bool
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
      rw [concat_rec_cons x xs c2 hTailNe]
      exact RuleProofs.eo_interprets_or_right_intro M hM
        x (__eo_list_concat_rec xs c2) hXBool hTailTrue

private theorem concat_true_of_left_true
    (M : SmtModel) (hM : model_wf M) {c1 c2 : Term} :
    OrClause c1 ->
    OrClause c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M c1 true ->
    eo_interprets M (__eo_list_concat Term.or c1 c2) true := by
  intro hC1 hC2 hC1Bool hC2Bool hC1True
  change eo_interprets M
    (__eo_requires (__eo_is_list Term.or c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list Term.or c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2))) true
  rw [orClause_is_list_true hC1, orClause_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact concat_rec_true_of_left_true M hM hC1 hC1Bool hC2Bool hC1True

private theorem concat_true_of_right_true
    (M : SmtModel) (hM : model_wf M) {c1 c2 : Term} :
    OrClause c1 ->
    OrClause c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M c2 true ->
    eo_interprets M (__eo_list_concat Term.or c1 c2) true := by
  intro hC1 hC2 hC1Bool hC2Bool hC2True
  change eo_interprets M
    (__eo_requires (__eo_is_list Term.or c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list Term.or c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2))) true
  rw [orClause_is_list_true hC1, orClause_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact concat_rec_true_of_right_true M hM hC1 hC1Bool hC2Bool hC2True

private inductive SafeOrClause : Term -> Prop where
  | false : SafeOrClause (Term.Boolean false)
  | cons (x xs : Term) : x ≠ Term.Stuck -> SafeOrClause xs ->
      SafeOrClause (Term.Apply (Term.Apply Term.or x) xs)

private inductive GoodOrClause (M : SmtModel) : Term -> Prop where
  | false : GoodOrClause M (Term.Boolean false)
  | cons (x xs : Term) :
      x ≠ Term.Stuck ->
      (¬ RuleProofs.eo_has_bool_type x ∨ eo_interprets M x false) ->
      GoodOrClause M xs ->
      GoodOrClause M (Term.Apply (Term.Apply Term.or x) xs)

private theorem safe_orClause_of_good {M : SmtModel} {c : Term} :
    GoodOrClause M c -> SafeOrClause c := by
  intro hGood
  induction hGood with
  | false =>
      exact SafeOrClause.false
  | cons x xs hX _ hTail ih =>
      exact SafeOrClause.cons x xs hX ih

private theorem orClause_of_safe {c : Term} :
    SafeOrClause c -> OrClause c := by
  intro hSafe
  induction hSafe with
  | false =>
      exact OrClause.false
  | cons x xs _ hTail ih =>
      exact OrClause.cons x xs ih

private theorem safe_orClause_ne_stuck {c : Term} :
    SafeOrClause c -> c ≠ Term.Stuck := by
  intro hSafe
  exact orClause_ne_stuck (orClause_of_safe hSafe)

private theorem safe_orClause_cons {x xs : Term} :
    x ≠ Term.Stuck ->
    SafeOrClause xs ->
    SafeOrClause (Term.Apply (Term.Apply Term.or x) xs) := by
  intro hX hXs
  exact SafeOrClause.cons x xs hX hXs

private theorem eo_list_translation_cons_inv {x xs : Term} :
    EoListAllHaveSmtTranslation (Term.Apply (Term.Apply Term.__eo_List_cons x) xs) ->
    RuleProofs.eo_has_smt_translation x ∧ EoListAllHaveSmtTranslation xs := by
  intro h
  exact h

private theorem eo_list_translation_cases {xs : Term} :
    EoListAllHaveSmtTranslation xs ->
    xs = Term.__eo_List_nil ∨
      ∃ x ts, xs = Term.Apply (Term.Apply Term.__eo_List_cons x) ts := by
  intro hXs
  cases xs with
  | __eo_List_nil =>
      exact Or.inl rfl
  | Apply f a =>
      cases f with
      | Apply g x =>
          cases g with
          | __eo_List_cons =>
              exact Or.inr ⟨x, a, rfl⟩
          | _ =>
              cases hXs
      | _ =>
          cases hXs
  | _ =>
      cases hXs

private theorem erase_rec_preserves_safe {c e : Term} :
    SafeOrClause c ->
    e ≠ Term.Stuck ->
    SafeOrClause (__eo_list_erase_rec c e) := by
  intro hClause hE
  induction hClause generalizing e with
  | false =>
      simpa [__eo_list_erase_rec] using SafeOrClause.false
  | cons x xs hX hXs ih =>
      by_cases hEq : x = e
      · rw [list_erase_rec_cons_eq x xs e hEq hX hE]
        exact hXs
      · have hTail : SafeOrClause (__eo_list_erase_rec xs e) := ih hE
        have hTailNe : __eo_list_erase_rec xs e ≠ Term.Stuck :=
          safe_orClause_ne_stuck hTail
        rw [list_erase_rec_cons_ne x xs e hEq hX hE hTailNe]
        exact SafeOrClause.cons x (__eo_list_erase_rec xs e) hX hTail

private theorem erase_rec_preserves_good
    (M : SmtModel) {c e : Term} :
    GoodOrClause M c ->
    e ≠ Term.Stuck ->
    GoodOrClause M (__eo_list_erase_rec c e) := by
  intro hClause hE
  induction hClause generalizing e with
  | false =>
      simpa [__eo_list_erase_rec] using GoodOrClause.false
  | cons x xs hX hGood hXs ih =>
      by_cases hEq : x = e
      · rw [list_erase_rec_cons_eq x xs e hEq hX hE]
        exact hXs
      · have hTail : GoodOrClause M (__eo_list_erase_rec xs e) := ih hE
        have hTailNe : __eo_list_erase_rec xs e ≠ Term.Stuck :=
          safe_orClause_ne_stuck (safe_orClause_of_good hTail)
        rw [list_erase_rec_cons_ne x xs e hEq hX hE hTailNe]
        exact GoodOrClause.cons x (__eo_list_erase_rec xs e) hX hGood hTail

private theorem erase_rec_changed_implies_good
    (M : SmtModel) {c e : Term} :
    GoodOrClause M c ->
    e ≠ Term.Stuck ->
    __eo_list_erase_rec c e ≠ c ->
    (¬ RuleProofs.eo_has_bool_type e ∨ eo_interprets M e false) := by
  intro hClause hE hChanged
  induction hClause generalizing e with
  | false =>
      exfalso
      apply hChanged
      simp [__eo_list_erase_rec]
  | cons x xs hX hGood hXs ih =>
      by_cases hEq : x = e
      · simpa [hEq] using hGood
      · have hTail : GoodOrClause M (__eo_list_erase_rec xs e) :=
          erase_rec_preserves_good M hXs hE
        have hTailSafe : SafeOrClause (__eo_list_erase_rec xs e) :=
          safe_orClause_of_good hTail
        have hTailNe : __eo_list_erase_rec xs e ≠ Term.Stuck :=
          safe_orClause_ne_stuck hTailSafe
        have hTailChanged : __eo_list_erase_rec xs e ≠ xs := by
          intro hTailEq
          apply hChanged
          rw [list_erase_rec_cons_ne x xs e hEq hX hE hTailNe, hTailEq]
        exact ih hE hTailChanged

private theorem diff_rec_preserves_bool_type {c d : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    SafeOrClause d ->
    RuleProofs.eo_has_bool_type (__eo_list_diff_rec c d) := by
  intro hClause hCBool hD
  induction hClause generalizing d with
  | false =>
      cases hD with
      | false =>
          simpa [__eo_list_diff_rec] using RuleProofs.eo_has_bool_type_false
      | cons _ _ _ _ =>
          simpa [__eo_list_diff_rec] using RuleProofs.eo_has_bool_type_false
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      let d' := __eo_list_erase_rec d x
      have hD' : SafeOrClause d' :=
        erase_rec_preserves_safe hD hX
      have hTail : RuleProofs.eo_has_bool_type (__eo_list_diff_rec xs d') :=
        ih hXsBool hD'
      have hDNe : d ≠ Term.Stuck := safe_orClause_ne_stuck hD
      have hD'Ne : d' ≠ Term.Stuck := safe_orClause_ne_stuck hD'
      by_cases hEq : d' = d
      · have hEqTerm : __eo_eq d' d = Term.Boolean true :=
          eo_eq_eq_true_of_eq hEq hD'Ne hDNe
        have hTailNe : __eo_list_diff_rec xs d' ≠ Term.Stuck :=
          RuleProofs.term_ne_stuck_of_has_bool_type _ hTail
        have hStep :
            __eo_list_diff_rec (Term.Apply (Term.Apply Term.or x) xs) d =
              Term.Apply (Term.Apply Term.or x) (__eo_list_diff_rec xs d') := by
          simp [__eo_list_diff_rec, d', hEqTerm, __eo_prepend_if]
        rw [hStep]
        exact RuleProofs.eo_has_bool_type_or_of_bool_args x (__eo_list_diff_rec xs d')
          hXBool hTail
      · have hEqTerm : __eo_eq d' d = Term.Boolean false :=
          eo_eq_eq_false_of_ne hEq hD'Ne hDNe
        have hTailNe : __eo_list_diff_rec xs d' ≠ Term.Stuck :=
          RuleProofs.term_ne_stuck_of_has_bool_type _ hTail
        have hStep :
            __eo_list_diff_rec (Term.Apply (Term.Apply Term.or x) xs) d =
              __eo_list_diff_rec xs d' := by
          simp [__eo_list_diff_rec, d', hEqTerm, __eo_prepend_if]
        rw [hStep]
        exact hTail

private theorem diff_rec_true_of_good
    (M : SmtModel) (hM : model_wf M) {c d : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c true ->
    GoodOrClause M d ->
    eo_interprets M (__eo_list_diff_rec c d) true := by
  intro hClause hCBool hCTrue hD
  induction hClause generalizing d with
  | false =>
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hCTrue)
        (eo_interprets_false M))
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hOrTrue : eo_interprets M (Term.Apply (Term.Apply Term.or x) xs) true := by
        simpa using hCTrue
      let d' := __eo_list_erase_rec d x
      have hD' : GoodOrClause M d' :=
        erase_rec_preserves_good M hD hX
      have hD'Safe : SafeOrClause d' := safe_orClause_of_good hD'
      have hD'Ne : d' ≠ Term.Stuck := safe_orClause_ne_stuck hD'Safe
      have hDNe : d ≠ Term.Stuck := safe_orClause_ne_stuck (safe_orClause_of_good hD)
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_diff_rec xs d') :=
        diff_rec_preserves_bool_type hXs hXsBool hD'Safe
      by_cases hEq : d' = d
      · have hEqTerm : __eo_eq d' d = Term.Boolean true :=
          eo_eq_eq_true_of_eq hEq hD'Ne hDNe
        have hTailNe : __eo_list_diff_rec xs d' ≠ Term.Stuck :=
          RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
        rcases eo_interprets_bool_cases M hM x hXBool with hXTrue | hXFalse
        · have hStep :
              __eo_list_diff_rec (Term.Apply (Term.Apply Term.or x) xs) d =
                Term.Apply (Term.Apply Term.or x) (__eo_list_diff_rec xs d') := by
            simp [__eo_list_diff_rec, d', hEqTerm, __eo_prepend_if]
          rw [hStep]
          exact RuleProofs.eo_interprets_or_left_intro M hM x (__eo_list_diff_rec xs d')
            hXTrue hTailBool
        · have hXsTrue : eo_interprets M xs true :=
            eo_interprets_or_right_of_left_false M hM x xs hXFalse hOrTrue
          have hTailTrue : eo_interprets M (__eo_list_diff_rec xs d') true :=
            ih hXsBool hXsTrue hD'
          have hStep :
              __eo_list_diff_rec (Term.Apply (Term.Apply Term.or x) xs) d =
                Term.Apply (Term.Apply Term.or x) (__eo_list_diff_rec xs d') := by
            simp [__eo_list_diff_rec, d', hEqTerm, __eo_prepend_if]
          rw [hStep]
          exact RuleProofs.eo_interprets_or_right_intro M hM x (__eo_list_diff_rec xs d')
            hXBool hTailTrue
      · have hEqTerm : __eo_eq d' d = Term.Boolean false :=
          eo_eq_eq_false_of_ne hEq hD'Ne hDNe
        have hTailNe : __eo_list_diff_rec xs d' ≠ Term.Stuck :=
          RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
        have hXGood : (¬ RuleProofs.eo_has_bool_type x ∨ eo_interprets M x false) :=
          erase_rec_changed_implies_good M hD hX hEq
        have hXFalse : eo_interprets M x false := by
          cases hXGood with
          | inl hNotBool =>
              exfalso
              exact hNotBool hXBool
          | inr hFalse =>
              exact hFalse
        have hXsTrue : eo_interprets M xs true :=
          eo_interprets_or_right_of_left_false M hM x xs hXFalse hOrTrue
        have hTailTrue : eo_interprets M (__eo_list_diff_rec xs d') true :=
          ih hXsBool hXsTrue hD'
        have hStep :
            __eo_list_diff_rec (Term.Apply (Term.Apply Term.or x) xs) d =
              __eo_list_diff_rec xs d' := by
          simp [__eo_list_diff_rec, d', hEqTerm, __eo_prepend_if]
        rw [hStep]
        exact hTailTrue

private theorem diff_preserves_bool_type {c d : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    SafeOrClause d ->
    RuleProofs.eo_has_bool_type (__eo_list_diff Term.or c d) := by
  intro hC hCBool hD
  change RuleProofs.eo_has_bool_type
    (__eo_requires (__eo_is_list Term.or c) (Term.Boolean true)
      (__eo_requires (__eo_is_list Term.or d) (Term.Boolean true)
        (__eo_list_diff_rec c d)))
  rw [orClause_is_list_true hC, orClause_is_list_true (orClause_of_safe hD)]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact diff_rec_preserves_bool_type hC hCBool hD

private theorem diff_true_of_good
    (M : SmtModel) (hM : model_wf M) {c d : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c true ->
    GoodOrClause M d ->
    eo_interprets M (__eo_list_diff Term.or c d) true := by
  intro hC hCBool hCTrue hD
  change eo_interprets M
    (__eo_requires (__eo_is_list Term.or c) (Term.Boolean true)
      (__eo_requires (__eo_is_list Term.or d) (Term.Boolean true)
        (__eo_list_diff_rec c d))) true
  rw [orClause_is_list_true hC, orClause_is_list_true (orClause_of_safe (safe_orClause_of_good hD))]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact diff_rec_true_of_good M hM hC hCBool hCTrue hD

private theorem list_diff_nonstuck_input_orClause {a b : Term} :
    __eo_list_diff Term.or a b ≠ Term.Stuck ->
    OrClause a := by
  intro hDiff
  have hList : __eo_is_list Term.or a = Term.Boolean true := by
    cases hIs : __eo_is_list Term.or a with
    | Boolean t =>
        simp [__eo_list_diff, __eo_requires, hIs, native_ite, native_teq, native_not,
          SmtEval.native_not] at hDiff ⊢
        exact hDiff.1
    | _ =>
        simp [__eo_list_diff, __eo_requires, hIs, native_ite, native_teq
          ] at hDiff
  exact orClause_of_is_list_true hList

private theorem concat_false_implies_right_false
    (M : SmtModel) (hM : model_wf M) {c1 c2 : Term} :
    OrClause c1 ->
    OrClause c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M (__eo_list_concat Term.or c1 c2) false ->
    eo_interprets M c2 false := by
  intro hC1 hC2 hC1Bool hC2Bool hConcatFalse
  rcases eo_interprets_bool_cases M hM c2 hC2Bool with hC2True | hC2False
  · have hConcatTrue : eo_interprets M (__eo_list_concat Term.or c1 c2) true :=
      concat_true_of_right_true M hM hC1 hC2 hC1Bool hC2Bool hC2True
    exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hConcatTrue) hConcatFalse)
  · exact hC2False

private theorem not_ne_stuck {t : Term} :
    t ≠ Term.Stuck ->
    Term.Apply Term.not t ≠ Term.Stuck := by
  intro hT
  cases t <;> simp at hT ⊢

private theorem pair_eq_components {a b c d : Term} :
    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) a) b =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) c) d ->
    a = c ∧ b = d := by
  intro hEq
  injection hEq with hPair hB
  have hA : a = c := by
    injection hPair with hA
  exact ⟨hA, hB⟩

private theorem pair_ne_stuck {a b : Term} :
    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) a) b ≠ Term.Stuck := by
  simp

private theorem not_has_bool_type_of_not_bool {t : Term} :
    ¬ RuleProofs.eo_has_bool_type t ->
    ¬ RuleProofs.eo_has_bool_type (Term.Apply Term.not t) := by
  intro hT hNotT
  exact hT (RuleProofs.eo_has_bool_type_not_arg t hNotT)

private theorem list_concat_nonstuck_left_orClause {a b : Term} :
    __eo_list_concat Term.or a b ≠ Term.Stuck ->
    OrClause a := by
  intro hConcat
  have hList : __eo_is_list Term.or a = Term.Boolean true := by
    cases hIs : __eo_is_list Term.or a with
    | Boolean t =>
        simp [__eo_list_concat, __eo_requires, hIs, native_ite, native_teq, native_not,
          SmtEval.native_not] at hConcat ⊢
        exact hConcat.1
    | _ =>
        simp [__eo_list_concat, __eo_requires, hIs, native_ite, native_teq
          ] at hConcat
  exact orClause_of_is_list_true hList

private theorem list_concat_nonstuck_right_orClause {a b : Term} :
    __eo_list_concat Term.or a b ≠ Term.Stuck ->
    OrClause b := by
  intro hConcat
  have hList : __eo_is_list Term.or b = Term.Boolean true := by
    cases hIsA : __eo_is_list Term.or a with
    | Boolean ta =>
        have hTa : ta = true := by
          simp [__eo_list_concat, __eo_requires, hIsA, native_ite, native_teq, native_not,
            SmtEval.native_not] at hConcat
          exact hConcat.1
        cases hIsB : __eo_is_list Term.or b with
        | Boolean tb =>
            simp [__eo_list_concat, __eo_requires, hIsA, hIsB, native_ite, native_teq,
              native_not, SmtEval.native_not] at hConcat ⊢
            exact hConcat.2.1
        | _ =>
            simp [__eo_list_concat, __eo_requires, hIsA, hIsB, native_ite, native_teq,
              native_not, SmtEval.native_not] at hConcat
    | _ =>
        simp [__eo_list_concat, __eo_requires, hIsA, native_ite, native_teq
          ] at hConcat
  exact orClause_of_is_list_true hList

private theorem chain_m_resolve_rec_step_true_false_implies_prev_false_of_safe_bool
    (M : SmtModel) (hM : model_wf M) {Cr rl Cc Cr' L : Term} :
    OrClause Cr ->
    RuleProofs.eo_has_bool_type Cr ->
    SafeOrClause rl ->
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl)
      Cc (Term.Boolean true) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr')
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) ->
    eo_interprets M Cr' false ->
    eo_interprets M Cr false := by
  intro hCr hCrBool hRlSafe hCcBool hLTrans hStep hCr'False
  have hRlNe : rl ≠ Term.Stuck := safe_orClause_ne_stuck hRlSafe
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  have hCcNe : Cc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
  by_cases hEq : Term.Apply Term.not L = Cc
  · have hEqTerm : __eo_eq (Term.Apply Term.not L) Cc = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq (not_ne_stuck hLNe) hCcNe
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm] at hStep'
    rw [hStep']
    exact hCr'False
  · have hEqTerm : __eo_eq (Term.Apply Term.not L) Cc = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq (not_ne_stuck hLNe) hCcNe
    have hDeleteSafe :
        SafeOrClause (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl) :=
      safe_orClause_cons (not_ne_stuck hLNe) hRlSafe
    have hConcatNe :
        __eo_list_concat Term.or
          (__eo_list_diff Term.or Cc
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl))
          Cr ≠ Term.Stuck := by
      intro hConcat
      have hStep' := hStep
      unfold __chain_m_resolve_rec_step at hStep'
      simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hConcat]
        at hStep'
    have hDiffClause :
        OrClause
          (__eo_list_diff Term.or Cc
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl)) :=
      list_concat_nonstuck_left_orClause hConcatNe
    have hCcClause : OrClause Cc :=
      list_diff_nonstuck_input_orClause (orClause_ne_stuck hDiffClause)
    have hDiffBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_diff Term.or Cc
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl)) :=
      diff_preserves_bool_type hCcClause hCcBool hDeleteSafe
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm]
      at hStep'
    have hConcatFalse :
        eo_interprets M
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or Cc
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl))
            Cr) false := by
      rw [hStep']
      exact hCr'False
    exact concat_false_implies_right_false M hM hDiffClause hCr hDiffBool hCrBool hConcatFalse

private theorem chain_m_resolve_rec_step_false_false_implies_prev_false_of_safe_bool
    (M : SmtModel) (hM : model_wf M) {Cr rl Cc Cr' L : Term} :
    OrClause Cr ->
    RuleProofs.eo_has_bool_type Cr ->
    SafeOrClause rl ->
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl)
      Cc (Term.Boolean false) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr')
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl) ->
    eo_interprets M Cr' false ->
    eo_interprets M Cr false := by
  intro hCr hCrBool hRlSafe hCcBool hLTrans hStep hCr'False
  have hRlNe : rl ≠ Term.Stuck := safe_orClause_ne_stuck hRlSafe
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  have hCcNe : Cc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
  by_cases hEq : L = Cc
  · have hEqTerm : __eo_eq L Cc = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq hLNe hCcNe
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm] at hStep'
    rw [hStep']
    exact hCr'False
  · have hEqTerm : __eo_eq L Cc = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq hLNe hCcNe
    have hDeleteSafe :
        SafeOrClause (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) :=
      safe_orClause_cons hLNe hRlSafe
    have hConcatNe :
        __eo_list_concat Term.or
          (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
          Cr ≠ Term.Stuck := by
      intro hConcat
      have hStep' := hStep
      unfold __chain_m_resolve_rec_step at hStep'
      simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hConcat]
        at hStep'
    have hDiffClause :
        OrClause (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
      list_concat_nonstuck_left_orClause hConcatNe
    have hCcClause : OrClause Cc :=
      list_diff_nonstuck_input_orClause (orClause_ne_stuck hDiffClause)
    have hDiffBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
      diff_preserves_bool_type hCcClause hCcBool hDeleteSafe
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm]
      at hStep'
    have hConcatFalse :
        eo_interprets M
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
            Cr) false := by
      rw [hStep']
      exact hCr'False
    exact concat_false_implies_right_false M hM hDiffClause hCr hDiffBool hCrBool hConcatFalse

private theorem chain_m_resolve_rec_step_true_false_implies_good_of_bool
    (M : SmtModel) (hM : model_wf M) {Cr rl Cc Cr' L : Term} :
    OrClause Cr ->
    eo_interprets M Cr false ->
    GoodOrClause M rl ->
    RuleProofs.eo_has_bool_type Cc ->
    eo_interprets M Cc true ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl)
      Cc (Term.Boolean true) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr')
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) ->
    eo_interprets M Cr' false ->
    GoodOrClause M (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) := by
  intro hCr hCrFalse hRlGood hCcBool hCcTrue hLTrans hStep hCr'False
  have hRlNe : rl ≠ Term.Stuck :=
    safe_orClause_ne_stuck (safe_orClause_of_good hRlGood)
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  by_cases hLBool : RuleProofs.eo_has_bool_type L
  · rcases eo_interprets_bool_cases M hM L hLBool with hLTrue | hLFalse
    · have hNotLFalse : eo_interprets M (Term.Apply Term.not L) false :=
        eo_interprets_not_false_of_true M L hLTrue
      have hDeleteGood :
          GoodOrClause M (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl) :=
        GoodOrClause.cons (Term.Apply Term.not L) rl (not_ne_stuck hLNe) (Or.inr hNotLFalse) hRlGood
      have hCcNe : Cc ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
      by_cases hEq : Term.Apply Term.not L = Cc
      · have hCcFalse : eo_interprets M Cc false := by
          simpa [hEq] using hNotLFalse
        exact False.elim ((RuleProofs.eo_interprets_true_not_false M Cc hCcTrue) hCcFalse)
      · have hEqTerm : __eo_eq (Term.Apply Term.not L) Cc = Term.Boolean false :=
          eo_eq_eq_false_of_ne hEq (not_ne_stuck hLNe) hCcNe
        have hConcatNe :
            __eo_list_concat Term.or
              (__eo_list_diff Term.or Cc
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl))
              Cr ≠ Term.Stuck := by
          intro hConcat
          have hStep' := hStep
          unfold __chain_m_resolve_rec_step at hStep'
          simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hConcat]
            at hStep'
        have hDiffClause :
            OrClause
              (__eo_list_diff Term.or Cc
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl)) :=
          list_concat_nonstuck_left_orClause hConcatNe
        have hCcClause : OrClause Cc :=
          list_diff_nonstuck_input_orClause (orClause_ne_stuck hDiffClause)
        have hDeleteSafe : SafeOrClause
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl) :=
          safe_orClause_of_good hDeleteGood
        have hDiffBool :
            RuleProofs.eo_has_bool_type
              (__eo_list_diff Term.or Cc
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl)) :=
          diff_preserves_bool_type hCcClause hCcBool hDeleteSafe
        have hDiffTrue :
            eo_interprets M
              (__eo_list_diff Term.or Cc
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl)) true :=
          diff_true_of_good M hM hCcClause hCcBool hCcTrue hDeleteGood
        have hCrBool : RuleProofs.eo_has_bool_type Cr :=
          RuleProofs.eo_has_bool_type_of_interprets_false M Cr hCrFalse
        have hConcatTrue :
            eo_interprets M
              (__eo_list_concat Term.or
                (__eo_list_diff Term.or Cc
                  (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl))
                Cr) true :=
          concat_true_of_left_true M hM hDiffClause hCr hDiffBool hCrBool hDiffTrue
        have hStep' := hStep
        unfold __chain_m_resolve_rec_step at hStep'
        simp [__eo_mk_apply, __eo_ite, native_ite, native_teq,
          hEqTerm] at hStep'
        have hCr'True : eo_interprets M Cr' true := by
          rw [← hStep']
          exact hConcatTrue
        exact False.elim ((RuleProofs.eo_interprets_true_not_false M Cr' hCr'True) hCr'False)
    · exact GoodOrClause.cons L rl
        (RuleProofs.term_ne_stuck_of_interprets_false M L hLFalse)
        (Or.inr hLFalse) hRlGood
  · exact GoodOrClause.cons L rl hLNe (Or.inl hLBool) hRlGood

private theorem chain_m_resolve_rec_step_false_false_implies_good_of_bool
    (M : SmtModel) (hM : model_wf M) {Cr rl Cc Cr' L : Term} :
    OrClause Cr ->
    eo_interprets M Cr false ->
    GoodOrClause M rl ->
    RuleProofs.eo_has_bool_type Cc ->
    eo_interprets M Cc true ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl)
      Cc (Term.Boolean false) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr')
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl) ->
    eo_interprets M Cr' false ->
    GoodOrClause M (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl) := by
  intro hCr hCrFalse hRlGood hCcBool hCcTrue hLTrans hStep hCr'False
  have hRlNe : rl ≠ Term.Stuck :=
    safe_orClause_ne_stuck (safe_orClause_of_good hRlGood)
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  by_cases hLBool : RuleProofs.eo_has_bool_type L
  · rcases eo_interprets_bool_cases M hM L hLBool with hLTrue | hLFalse
    · have hNotLFalse : eo_interprets M (Term.Apply Term.not L) false :=
        eo_interprets_not_false_of_true M L hLTrue
      exact GoodOrClause.cons (Term.Apply Term.not L) rl
        (not_ne_stuck (RuleProofs.term_ne_stuck_of_interprets_true M L hLTrue))
        (Or.inr hNotLFalse) hRlGood
    · have hDeleteGood :
          GoodOrClause M (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) :=
        GoodOrClause.cons L rl
          (RuleProofs.term_ne_stuck_of_interprets_false M L hLFalse)
          (Or.inr hLFalse) hRlGood
      have hCcNe : Cc ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
      by_cases hEq : L = Cc
      · have hCcFalse : eo_interprets M Cc false := by
          simpa [hEq] using hLFalse
        exact False.elim ((RuleProofs.eo_interprets_true_not_false M Cc hCcTrue) hCcFalse)
      · have hEqTerm : __eo_eq L Cc = Term.Boolean false :=
          eo_eq_eq_false_of_ne hEq hLNe hCcNe
        have hConcatNe :
            __eo_list_concat Term.or
              (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
              Cr ≠ Term.Stuck := by
          intro hConcat
          have hStep' := hStep
          unfold __chain_m_resolve_rec_step at hStep'
          simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hConcat]
            at hStep'
        have hDiffClause :
            OrClause (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
          list_concat_nonstuck_left_orClause hConcatNe
        have hCcClause : OrClause Cc :=
          list_diff_nonstuck_input_orClause (orClause_ne_stuck hDiffClause)
        have hDeleteSafe : SafeOrClause (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) :=
          safe_orClause_of_good hDeleteGood
        have hDiffBool :
            RuleProofs.eo_has_bool_type
              (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
          diff_preserves_bool_type hCcClause hCcBool hDeleteSafe
        have hDiffTrue :
            eo_interprets M
              (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) true :=
          diff_true_of_good M hM hCcClause hCcBool hCcTrue hDeleteGood
        have hCrBool : RuleProofs.eo_has_bool_type Cr :=
          RuleProofs.eo_has_bool_type_of_interprets_false M Cr hCrFalse
        have hConcatTrue :
            eo_interprets M
              (__eo_list_concat Term.or
                (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
                Cr) true :=
          concat_true_of_left_true M hM hDiffClause hCr hDiffBool hCrBool hDiffTrue
        have hStep' := hStep
        unfold __chain_m_resolve_rec_step at hStep'
        simp [__eo_mk_apply, __eo_ite, native_ite, native_teq,
          hEqTerm] at hStep'
        have hCr'True : eo_interprets M Cr' true := by
          rw [← hStep']
          exact hConcatTrue
        exact False.elim ((RuleProofs.eo_interprets_true_not_false M Cr' hCr'True) hCr'False)
  · exact GoodOrClause.cons (Term.Apply Term.not L) rl
      (not_ne_stuck hLNe)
      (Or.inl (not_has_bool_type_of_not_bool hLBool)) hRlGood

private theorem ite_eq_stuck_of_ne_true_false (c t e : Term) :
    c ≠ Term.Boolean true ->
    c ≠ Term.Boolean false ->
    __eo_ite c t e = Term.Stuck := by
  intro hTrue hFalse
  cases c <;> simp [__eo_ite, native_ite, native_teq, hTrue, hFalse]

private theorem chain_m_resolve_rec_step_pair_branch_stuck_of_pol_ne_true_false
    {Cc pol L Cr rl : Term} :
    Cc ≠ Term.Stuck ->
    L ≠ Term.Stuck ->
    pol ≠ Term.Boolean true ->
    pol ≠ Term.Boolean false ->
    (let _v0 := (Term.UOp UserOp.not).Apply L
     let _v1 := __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.or) (__eo_ite pol L _v0)) rl
     let _v2 := __eo_ite pol _v0 L
     __eo_ite (__eo_eq _v2 Cc)
       (__eo_mk_apply ((Term.UOp UserOp._at__at_pair).Apply Cr) _v1)
       (__eo_mk_apply
         (__eo_mk_apply (Term.UOp UserOp._at__at_pair)
           (__eo_list_concat (Term.UOp UserOp.or)
             (__eo_list_diff (Term.UOp UserOp.or) Cc
               (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.or) _v2) rl)) Cr))
         _v1)) = Term.Stuck := by
  intro hCc hL hPolTrue hPolFalse
  simp [hPolTrue, hPolFalse, __eo_eq, __eo_ite, native_ite, native_teq]

private theorem chain_m_resolve_rec_step_stuck_of_pol_ne_true_false
    {r Cc pol L : Term} :
    Cc ≠ Term.Stuck ->
    L ≠ Term.Stuck ->
    pol ≠ Term.Boolean true ->
    pol ≠ Term.Boolean false ->
    __chain_m_resolve_rec_step r Cc pol L = Term.Stuck := by
  intro hCc hL hPolTrue hPolFalse
  unfold __chain_m_resolve_rec_step
  split <;> try contradiction <;> try rfl
  case h_2 =>
    rfl
  case h_4 =>
    exact chain_m_resolve_rec_step_pair_branch_stuck_of_pol_ne_true_false
      hCc hL hPolTrue hPolFalse
  case h_5 =>
    rfl

private theorem chain_m_resolve_rec_step_true_pair_input
    {r Cc Cr' rl' L : Term} :
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step r Cc (Term.Boolean true) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr') rl' ->
    ∃ Cr rl, r = Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
  intro hCcBool hLTrans hStep
  have hCcNe : Cc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  cases r with
  | Stuck =>
      simp [__chain_m_resolve_rec_step] at hStep
  | Boolean b =>
      simp [__chain_m_resolve_rec_step] at hStep
  | Apply f a =>
      cases f with
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_pair =>
                  exact ⟨x, a, rfl⟩
              | _ =>
                  simp [__chain_m_resolve_rec_step] at hStep
          | _ =>
              simp [__chain_m_resolve_rec_step] at hStep
      | _ =>
          simp [__chain_m_resolve_rec_step] at hStep
  | _ =>
      simp [__chain_m_resolve_rec_step] at hStep

private theorem chain_m_resolve_rec_step_false_pair_input
    {r Cc Cr' rl' L : Term} :
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step r Cc (Term.Boolean false) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr') rl' ->
    ∃ Cr rl, r = Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
  intro hCcBool hLTrans hStep
  have hCcNe : Cc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  cases r with
  | Stuck =>
      simp [__chain_m_resolve_rec_step] at hStep
  | Boolean b =>
      simp [__chain_m_resolve_rec_step] at hStep
  | Apply f a =>
      cases f with
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_pair =>
                  exact ⟨x, a, rfl⟩
              | _ =>
                  simp [__chain_m_resolve_rec_step] at hStep
          | _ =>
              simp [__chain_m_resolve_rec_step] at hStep
      | _ =>
          simp [__chain_m_resolve_rec_step] at hStep
  | _ =>
      simp [__chain_m_resolve_rec_step] at hStep

private theorem chain_m_resolve_rec_step_true_pair_pending
    {Cr rl Cc Cr' rl' L : Term} :
    SafeOrClause rl ->
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl)
      Cc (Term.Boolean true) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr') rl' ->
    rl' = Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl := by
  intro hRlSafe hCcBool hLTrans hStep
  have hRlNe : rl ≠ Term.Stuck := safe_orClause_ne_stuck hRlSafe
  have hCcNe : Cc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  by_cases hEq : Term.Apply Term.not L = Cc
  · have hEqTerm : __eo_eq (Term.Apply Term.not L) Cc = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq (not_ne_stuck hLNe) hCcNe
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm] at hStep'
    exact hStep'.2.symm
  · have hEqTerm : __eo_eq (Term.Apply Term.not L) Cc = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq (not_ne_stuck hLNe) hCcNe
    have hConcatNe :
        __eo_list_concat Term.or
          (__eo_list_diff Term.or Cc
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl))
          Cr ≠ Term.Stuck := by
      intro hConcat
      have hStep' := hStep
      unfold __chain_m_resolve_rec_step at hStep'
      simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hConcat]
        at hStep'
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm]
      at hStep'
    exact hStep'.2.symm

private theorem chain_m_resolve_rec_step_false_pair_pending
    {Cr rl Cc Cr' rl' L : Term} :
    SafeOrClause rl ->
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl)
      Cc (Term.Boolean false) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr') rl' ->
    rl' = Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl := by
  intro hRlSafe hCcBool hLTrans hStep
  have hRlNe : rl ≠ Term.Stuck := safe_orClause_ne_stuck hRlSafe
  have hCcNe : Cc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  by_cases hEq : L = Cc
  · have hEqTerm : __eo_eq L Cc = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq hLNe hCcNe
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm] at hStep'
    exact hStep'.2.symm
  · have hEqTerm : __eo_eq L Cc = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq hLNe hCcNe
    have hConcatNe :
        __eo_list_concat Term.or
          (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
          Cr ≠ Term.Stuck := by
      intro hConcat
      have hStep' := hStep
      unfold __chain_m_resolve_rec_step at hStep'
      simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hConcat]
        at hStep'
    have hStep' := hStep
    unfold __chain_m_resolve_rec_step at hStep'
    simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm]
      at hStep'
    exact hStep'.2.symm

private theorem chain_m_resolve_rec_step_true_pair_residual
    {Cr0 rl0 Cc Cr rl L : Term} :
    OrClause Cr0 ->
    RuleProofs.eo_has_bool_type Cr0 ->
    SafeOrClause rl0 ->
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0) rl0)
      Cc (Term.Boolean true) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl ->
    OrClause Cr ∧ RuleProofs.eo_has_bool_type Cr := by
  intro hCr0 hCr0Bool hRl0Safe hCcBool hLTrans hStep
  have hRlNe : rl0 ≠ Term.Stuck := safe_orClause_ne_stuck hRl0Safe
  have hCcNe : Cc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  by_cases hEq : Term.Apply Term.not L = Cc
  · have hEqTerm : __eo_eq (Term.Apply Term.not L) Cc = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq (not_ne_stuck hLNe) hCcNe
    have hStep' :
        Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0)
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0) =
        Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
      simpa [__chain_m_resolve_rec_step, __eo_mk_apply, __eo_ite, native_ite, native_teq,
        hEqTerm, hLNe, hRlNe] using hStep
    have hComps := pair_eq_components hStep'
    exact ⟨by simpa [hComps.1] using hCr0, by simpa [hComps.1] using hCr0Bool⟩
  · have hEqTerm : __eo_eq (Term.Apply Term.not L) Cc = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq (not_ne_stuck hLNe) hCcNe
    have hDeleteSafe :
        SafeOrClause (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0) :=
      safe_orClause_cons (not_ne_stuck hLNe) hRl0Safe
    have hConcatNe :
        __eo_list_concat Term.or
          (__eo_list_diff Term.or Cc
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0))
          Cr0 ≠ Term.Stuck := by
      intro hConcat
      have hStep' := hStep
      unfold __chain_m_resolve_rec_step at hStep'
      simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hConcat]
        at hStep'
    have hDiffClause :
        OrClause
          (__eo_list_diff Term.or Cc
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0)) :=
      list_concat_nonstuck_left_orClause hConcatNe
    have hCcClause : OrClause Cc :=
      list_diff_nonstuck_input_orClause (orClause_ne_stuck hDiffClause)
    have hDiffBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_diff Term.or Cc
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0)) :=
      diff_preserves_bool_type hCcClause hCcBool hDeleteSafe
    have hResidualClause :
        OrClause
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or Cc
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0))
            Cr0) :=
      concat_preserves_orClause hDiffClause hCr0
    have hResidualBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or Cc
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0))
            Cr0) :=
      concat_preserves_bool_type hDiffClause hCr0 hDiffBool hCr0Bool
    have hStep' :
        Term.Apply
          (Term.Apply (Term.UOp UserOp._at__at_pair)
            (__eo_list_concat Term.or
              (__eo_list_diff Term.or Cc
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0))
              Cr0))
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0) =
        Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
      simpa [__chain_m_resolve_rec_step, __eo_mk_apply, __eo_ite, native_ite, native_teq,
        hEqTerm, hLNe, hRlNe, hConcatNe] using hStep
    have hComps := pair_eq_components hStep'
    exact ⟨by simpa [hComps.1] using hResidualClause, by simpa [hComps.1] using hResidualBool⟩

private theorem chain_m_resolve_rec_step_false_pair_residual
    {Cr0 rl0 Cc Cr rl L : Term} :
    OrClause Cr0 ->
    RuleProofs.eo_has_bool_type Cr0 ->
    SafeOrClause rl0 ->
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0) rl0)
      Cc (Term.Boolean false) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl ->
    OrClause Cr ∧ RuleProofs.eo_has_bool_type Cr := by
  intro hCr0 hCr0Bool hRl0Safe hCcBool hLTrans hStep
  have hRlNe : rl0 ≠ Term.Stuck := safe_orClause_ne_stuck hRl0Safe
  have hCcNe : Cc ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  by_cases hEq : L = Cc
  · have hEqTerm : __eo_eq L Cc = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq hLNe hCcNe
    have hStep' :
        Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0)
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0) =
        Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
      simpa [__chain_m_resolve_rec_step, __eo_mk_apply, __eo_ite, native_ite, native_teq,
        hEqTerm, hLNe, hRlNe] using hStep
    have hComps := pair_eq_components hStep'
    exact ⟨by simpa [hComps.1] using hCr0, by simpa [hComps.1] using hCr0Bool⟩
  · have hEqTerm : __eo_eq L Cc = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq hLNe hCcNe
    have hDeleteSafe :
        SafeOrClause (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0) :=
      safe_orClause_cons hLNe hRl0Safe
    have hConcatNe :
        __eo_list_concat Term.or
          (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0))
          Cr0 ≠ Term.Stuck := by
      intro hConcat
      have hStep' := hStep
      unfold __chain_m_resolve_rec_step at hStep'
      simp [__eo_mk_apply, __eo_ite, native_ite, native_teq, hEqTerm, hConcat]
        at hStep'
    have hDiffClause :
        OrClause (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0)) :=
      list_concat_nonstuck_left_orClause hConcatNe
    have hCcClause : OrClause Cc :=
      list_diff_nonstuck_input_orClause (orClause_ne_stuck hDiffClause)
    have hDiffBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0)) :=
      diff_preserves_bool_type hCcClause hCcBool hDeleteSafe
    have hResidualClause :
        OrClause
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0))
            Cr0) :=
      concat_preserves_orClause hDiffClause hCr0
    have hResidualBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0))
            Cr0) :=
      concat_preserves_bool_type hDiffClause hCr0 hDiffBool hCr0Bool
    have hStep' :
        Term.Apply
          (Term.Apply (Term.UOp UserOp._at__at_pair)
            (__eo_list_concat Term.or
              (__eo_list_diff Term.or Cc (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0))
              Cr0))
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0) =
        Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
      simpa [__chain_m_resolve_rec_step, __eo_mk_apply, __eo_ite, native_ite, native_teq,
        hEqTerm, hLNe, hRlNe, hConcatNe] using hStep
    have hComps := pair_eq_components hStep'
    exact ⟨by simpa [hComps.1] using hResidualClause, by simpa [hComps.1] using hResidualBool⟩

private theorem chain_m_resolve_rec_step_true_pair_safe
    {Cr0 rl0 Cc Cr rl L : Term} :
    SafeOrClause rl0 ->
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0) rl0)
      Cc (Term.Boolean true) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl ->
    SafeOrClause rl := by
  intro hRl0Safe hCcBool hLTrans hStep
  have hRlEq :
      rl = Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0 :=
    chain_m_resolve_rec_step_true_pair_pending hRl0Safe hCcBool hLTrans hStep
  rw [hRlEq]
  exact safe_orClause_cons
    (RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans) hRl0Safe

private theorem chain_m_resolve_rec_step_false_pair_safe
    {Cr0 rl0 Cc Cr rl L : Term} :
    SafeOrClause rl0 ->
    RuleProofs.eo_has_bool_type Cc ->
    RuleProofs.eo_has_smt_translation L ->
    __chain_m_resolve_rec_step
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0) rl0)
      Cc (Term.Boolean false) L =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl ->
    SafeOrClause rl := by
  intro hRl0Safe hCcBool hLTrans hStep
  have hLNe : L ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
  have hRlEq :
      rl = Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0 :=
    chain_m_resolve_rec_step_false_pair_pending hRl0Safe hCcBool hLTrans hStep
  rw [hRlEq]
  exact safe_orClause_cons (not_ne_stuck hLNe) hRl0Safe

private theorem chain_m_resolve_rec_true_nil_nil_local :
    __chain_m_resolve_rec (Term.Boolean true) Term.__eo_List_nil Term.__eo_List_nil =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) (Term.Boolean false))
        (Term.Boolean false) := by
  rfl

private theorem chain_m_resolve_rec_true_nil_cons_local (L lits : Term) :
    __chain_m_resolve_rec (Term.Boolean true) Term.__eo_List_nil
      (Term.Apply (Term.Apply Term.__eo_List_cons L) lits) = Term.Stuck := by
  rfl

private theorem chain_m_resolve_rec_true_cons_nil_local (pol pols : Term) :
    __chain_m_resolve_rec (Term.Boolean true)
      (Term.Apply (Term.Apply Term.__eo_List_cons pol) pols) Term.__eo_List_nil = Term.Stuck := by
  rfl

private theorem chain_m_resolve_rec_true_cons_cons_local (pol pols L lits : Term) :
    __chain_m_resolve_rec (Term.Boolean true)
      (Term.Apply (Term.Apply Term.__eo_List_cons pol) pols)
      (Term.Apply (Term.Apply Term.__eo_List_cons L) lits) = Term.Stuck := by
  rfl

private theorem chain_m_resolve_rec_and_nil_local (C Cs lits : Term) :
    __chain_m_resolve_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) C) Cs) Term.__eo_List_nil lits = Term.Stuck := by
  rfl

private theorem chain_m_resolve_rec_and_cons_nil_local (C Cs pol pols : Term) :
    __chain_m_resolve_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) C) Cs)
      (Term.Apply (Term.Apply Term.__eo_List_cons pol) pols) Term.__eo_List_nil = Term.Stuck := by
  rfl

private theorem chain_m_resolve_rec_and_cons_cons_local (C Cs pol pols L lits : Term) :
    __chain_m_resolve_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) C) Cs)
      (Term.Apply (Term.Apply Term.__eo_List_cons pol) pols)
      (Term.Apply (Term.Apply Term.__eo_List_cons L) lits) =
        __chain_m_resolve_rec_step (__chain_m_resolve_rec Cs pols lits) C pol L := by
  rfl

private theorem chain_m_resolve_rec_pair_false_implies_good
    (M : SmtModel) (hM : model_wf M) :
    ∀ premises pols lits Cr rl,
      AllHaveBoolType premises ->
      AllInterpretedTrue M premises ->
      EoListAllHaveSmtTranslation pols ->
      EoListAllHaveSmtTranslation lits ->
      __chain_m_resolve_rec (premiseAndFormulaList premises) pols lits =
        Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl ->
      OrClause Cr ∧
      RuleProofs.eo_has_bool_type Cr ∧
      SafeOrClause rl ∧
      (eo_interprets M Cr false -> GoodOrClause M rl) := by
  intro premises
  induction premises with
  | nil =>
      intro pols lits Cr rl _ _ hPols hLits hRec
      rcases eo_list_translation_cases hPols with hPolsNil | ⟨pol, pols', hPolsCons⟩
      · subst hPolsNil
        rcases eo_list_translation_cases hLits with hLitsNil | ⟨L, lits', hLitsCons⟩
        · subst hLitsNil
          have hBase :
              Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) (Term.Boolean false))
                (Term.Boolean false) =
              Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
            simpa only [premiseAndFormulaList, chain_m_resolve_rec_true_nil_nil_local] using hRec
          have hComps := pair_eq_components hBase
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [hComps.1.symm] using (OrClause.false : OrClause (Term.Boolean false))
          · simpa [hComps.1.symm] using RuleProofs.eo_has_bool_type_false
          · simpa [hComps.2.symm] using (SafeOrClause.false : SafeOrClause (Term.Boolean false))
          · intro _
            simpa [hComps.2.symm] using (GoodOrClause.false : GoodOrClause M (Term.Boolean false))
        · subst hLitsCons
          have hStuck :
              Term.Stuck =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
            simpa only [premiseAndFormulaList, chain_m_resolve_rec_true_nil_cons_local] using hRec
          exact False.elim (pair_ne_stuck hStuck.symm)
      · subst hPolsCons
        rcases eo_list_translation_cases hLits with hLitsNil | ⟨L, lits', hLitsCons⟩
        · subst hLitsNil
          have hStuck :
              Term.Stuck =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
            simpa only [premiseAndFormulaList, chain_m_resolve_rec_true_cons_nil_local] using hRec
          exact False.elim (pair_ne_stuck hStuck.symm)
        · subst hLitsCons
          have hStuck :
              Term.Stuck =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
            simpa only [premiseAndFormulaList, chain_m_resolve_rec_true_cons_cons_local] using hRec
          exact False.elim (pair_ne_stuck hStuck.symm)
  | cons Cc premises ih =>
      intro pols lits Cr rl hPremBool hPremTrue hPols hLits hRec
      have hCcBool : RuleProofs.eo_has_bool_type Cc := hPremBool Cc (by simp)
      have hCcTrue : eo_interprets M Cc true := hPremTrue Cc (by simp)
      have hPremisesBool : AllHaveBoolType premises := by
        intro t ht
        exact hPremBool t (by simp [ht])
      have hPremisesTrue : AllInterpretedTrue M premises := by
        intro t ht
        exact hPremTrue t (by simp [ht])
      rcases eo_list_translation_cases hPols with hPolsNil | ⟨pol, pols', hPolsCons⟩
      · subst hPolsNil
        have hStuck :
            Term.Stuck =
              Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
          simpa only [premiseAndFormulaList, chain_m_resolve_rec_and_nil_local] using hRec
        exact False.elim (pair_ne_stuck hStuck.symm)
      · subst hPolsCons
        rcases eo_list_translation_cons_inv hPols with ⟨hPolTrans, hPols'⟩
        rcases eo_list_translation_cases hLits with hLitsNil | ⟨L, lits', hLitsCons⟩
        · subst hLitsNil
          have hStuck :
              Term.Stuck =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
            simpa only [premiseAndFormulaList, chain_m_resolve_rec_and_cons_nil_local] using hRec
          exact False.elim (pair_ne_stuck hStuck.symm)
        · subst hLitsCons
          rcases eo_list_translation_cons_inv hLits with ⟨hLTrans, hLits'⟩
          have hStep :
              __chain_m_resolve_rec_step
                (__chain_m_resolve_rec (premiseAndFormulaList premises) pols' lits')
                Cc pol L =
              Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
            simpa only [premiseAndFormulaList, chain_m_resolve_rec_and_cons_cons_local] using hRec
          by_cases hPolTrue : pol = Term.Boolean true
          · subst hPolTrue
            rcases chain_m_resolve_rec_step_true_pair_input hCcBool hLTrans hStep with
              ⟨Cr0, rl0, hTailEq⟩
            rcases ih pols' lits' Cr0 rl0 hPremisesBool hPremisesTrue hPols' hLits' hTailEq with
              ⟨hCr0Clause, hCr0Bool, hRl0Safe, hTailGood⟩
            have hStepPair :
                __chain_m_resolve_rec_step
                  (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0) rl0)
                  Cc (Term.Boolean true) L =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
              simpa [hTailEq] using hStep
            have hResidual :=
              chain_m_resolve_rec_step_true_pair_residual
                hCr0Clause hCr0Bool hRl0Safe hCcBool hLTrans hStepPair
            have hRlSafe :=
              chain_m_resolve_rec_step_true_pair_safe hRl0Safe hCcBool hLTrans hStepPair
            have hRlEq :
                rl = Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0 :=
              chain_m_resolve_rec_step_true_pair_pending hRl0Safe hCcBool hLTrans hStepPair
            refine ⟨hResidual.1, hResidual.2, hRlSafe, ?_⟩
            intro hCrFalse
            have hStep' :
                __chain_m_resolve_rec_step
                  (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0) rl0)
                  Cc (Term.Boolean true) L =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0) := by
              simpa [hRlEq] using hStepPair
            have hCr0False :
                eo_interprets M Cr0 false :=
              chain_m_resolve_rec_step_true_false_implies_prev_false_of_safe_bool M hM
                hCr0Clause hCr0Bool hRl0Safe hCcBool hLTrans hStep' hCrFalse
            have hRl0Good : GoodOrClause M rl0 := hTailGood hCr0False
            have hRlGood :
                GoodOrClause M (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl0) :=
              chain_m_resolve_rec_step_true_false_implies_good_of_bool M hM
                hCr0Clause hCr0False hRl0Good hCcBool hCcTrue hLTrans hStep' hCrFalse
            simpa [hRlEq] using hRlGood
          · by_cases hPolFalse : pol = Term.Boolean false
            · subst hPolFalse
              rcases chain_m_resolve_rec_step_false_pair_input hCcBool hLTrans hStep with
                ⟨Cr0, rl0, hTailEq⟩
              rcases ih pols' lits' Cr0 rl0 hPremisesBool hPremisesTrue hPols' hLits' hTailEq with
                ⟨hCr0Clause, hCr0Bool, hRl0Safe, hTailGood⟩
              have hStepPair :
                  __chain_m_resolve_rec_step
                    (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0) rl0)
                    Cc (Term.Boolean false) L =
                  Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
                simpa [hTailEq] using hStep
              have hResidual :=
                chain_m_resolve_rec_step_false_pair_residual
                  hCr0Clause hCr0Bool hRl0Safe hCcBool hLTrans hStepPair
              have hRlSafe :=
                chain_m_resolve_rec_step_false_pair_safe hRl0Safe hCcBool hLTrans hStepPair
              have hRlEq :
                  rl = Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0 :=
                chain_m_resolve_rec_step_false_pair_pending hRl0Safe hCcBool hLTrans hStepPair
              refine ⟨hResidual.1, hResidual.2, hRlSafe, ?_⟩
              intro hCrFalse
              have hStep' :
                  __chain_m_resolve_rec_step
                    (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0) rl0)
                    Cc (Term.Boolean false) L =
                  Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0) := by
                simpa [hRlEq] using hStepPair
              have hCr0False :
                  eo_interprets M Cr0 false :=
                chain_m_resolve_rec_step_false_false_implies_prev_false_of_safe_bool M hM
                  hCr0Clause hCr0Bool hRl0Safe hCcBool hLTrans hStep' hCrFalse
              have hRl0Good : GoodOrClause M rl0 := hTailGood hCr0False
              have hRlGood :
                  GoodOrClause M
                    (Term.Apply (Term.Apply (Term.UOp UserOp.or) (Term.Apply Term.not L)) rl0) :=
                chain_m_resolve_rec_step_false_false_implies_good_of_bool M hM
                  hCr0Clause hCr0False hRl0Good hCcBool hCcTrue hLTrans hStep' hCrFalse
              simpa [hRlEq] using hRlGood
            · have hCcNe : Cc ≠ Term.Stuck :=
                RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
              have hLNe : L ≠ Term.Stuck :=
                RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
              have hStuck :
                  __chain_m_resolve_rec_step
                    (__chain_m_resolve_rec (premiseAndFormulaList premises) pols' lits')
                    Cc pol L = Term.Stuck :=
                chain_m_resolve_rec_step_stuck_of_pol_ne_true_false
                  hCcNe hLNe hPolTrue hPolFalse
              rw [hStuck] at hStep
              exact False.elim (pair_ne_stuck hStep.symm)

private theorem from_clause_preserves_bool_type {c : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    RuleProofs.eo_has_bool_type (__from_clause c) := by
  intro hClause hCBool
  induction hClause with
  | false =>
      simpa [__from_clause] using RuleProofs.eo_has_bool_type_false
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hXsNe : xs ≠ Term.Stuck := orClause_ne_stuck hXs
      by_cases hNil : xs = Term.Boolean false
      · have hEqTerm : __eo_eq xs (Term.Boolean false) = Term.Boolean true :=
          eo_eq_eq_true_of_eq hNil hXsNe (by simp)
        rw [show __from_clause (Term.Apply (Term.Apply Term.or x) xs) =
              __eo_ite (__eo_eq xs (Term.Boolean false)) x
                (Term.Apply (Term.Apply Term.or x) xs) by
              simp [__from_clause]]
        simp [hEqTerm, __eo_ite, native_ite, native_teq]
        exact hXBool
      · have hEqTerm : __eo_eq xs (Term.Boolean false) = Term.Boolean false :=
          eo_eq_eq_false_of_ne hNil hXsNe (by simp)
        rw [show __from_clause (Term.Apply (Term.Apply Term.or x) xs) =
              __eo_ite (__eo_eq xs (Term.Boolean false)) x
                (Term.Apply (Term.Apply Term.or x) xs) by
              simp [__from_clause]]
        simp [hEqTerm, __eo_ite, native_ite, native_teq]
        exact hCBool

private theorem from_clause_true
    (M : SmtModel) (hM : model_wf M) {c : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c true ->
    eo_interprets M (__from_clause c) true := by
  intro hClause hCBool hCTrue
  induction hClause with
  | false =>
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hCTrue)
        (eo_interprets_false M))
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hXsNe : xs ≠ Term.Stuck := orClause_ne_stuck hXs
      have hOrTrue : eo_interprets M (Term.Apply (Term.Apply Term.or x) xs) true := by
        simpa using hCTrue
      by_cases hNil : xs = Term.Boolean false
      · have hEqTerm : __eo_eq xs (Term.Boolean false) = Term.Boolean true :=
          eo_eq_eq_true_of_eq hNil hXsNe (by simp)
        have hXsFalse : eo_interprets M xs false := by
          simpa [hNil] using eo_interprets_false M
        have hXTrue : eo_interprets M x true :=
          eo_interprets_or_left_of_right_false M hM x xs hXsFalse hOrTrue
        rw [show __from_clause (Term.Apply (Term.Apply Term.or x) xs) =
              __eo_ite (__eo_eq xs (Term.Boolean false)) x
                (Term.Apply (Term.Apply Term.or x) xs) by
              simp [__from_clause]]
        simp [hEqTerm, __eo_ite, native_ite, native_teq]
        exact hXTrue
      · have hEqTerm : __eo_eq xs (Term.Boolean false) = Term.Boolean false :=
          eo_eq_eq_false_of_ne hNil hXsNe (by simp)
        rw [show __from_clause (Term.Apply (Term.Apply Term.or x) xs) =
              __eo_ite (__eo_eq xs (Term.Boolean false)) x
                (Term.Apply (Term.Apply Term.or x) xs) by
              simp [__from_clause]]
        simp [hEqTerm, __eo_ite, native_ite, native_teq]
        exact hOrTrue

private theorem from_clause_arg_ne_stuck {c : Term} :
    __from_clause c ≠ Term.Stuck ->
    c ≠ Term.Stuck := by
  intro hFrom hC
  subst hC
  simp [__from_clause] at hFrom

private theorem chain_m_resolve_final_pair_of_nonstuck
    {C1 r : Term} :
    __chain_m_resolve_final C1 r ≠ Term.Stuck ->
    ∃ C2 L rl,
      r = Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) C2)
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) := by
  intro hFinal
  cases hR : r with
  | Apply f a =>
      cases hF : f with
      | Apply g x =>
          cases hG : g with
          | UOp op =>
              cases op with
              | _at__at_pair =>
                  cases hA : a with
                  | Apply f' rl =>
                      cases hF' : f' with
                      | Apply g' L =>
                          cases hG' : g' with
                          | UOp op' =>
                              cases op' with
                              | or =>
                                  refine ⟨x, L, rl, ?_⟩
                                  simp
                              | _ =>
                                  cases C1 <;> simp [__chain_m_resolve_final, hR, hF, hG, hA, hF', hG'] at hFinal
                          | _ =>
                              cases C1 <;> simp [__chain_m_resolve_final, hR, hF, hG, hA, hF', hG'] at hFinal
                      | _ =>
                          cases C1 <;> simp [__chain_m_resolve_final, hR, hF, hG, hA, hF'] at hFinal
                  | _ =>
                      cases C1 <;> simp [__chain_m_resolve_final, hR, hF, hG, hA] at hFinal
              | _ =>
                  cases C1 <;> simp [__chain_m_resolve_final, hR, hF, hG] at hFinal
          | _ =>
              cases C1 <;> simp [__chain_m_resolve_final, hR, hF, hG] at hFinal
      | _ =>
          cases C1 <;> simp [__chain_m_resolve_final, hR, hF] at hFinal
  | _ =>
      cases C1 <;> simp [__chain_m_resolve_final, hR] at hFinal

private theorem chain_m_resolve_final_properties_of_nonstuck
    (M : SmtModel) (hM : model_wf M) {C1 C2 L rl : Term} :
    RuleProofs.eo_has_bool_type C1 ->
    eo_interprets M C1 true ->
    OrClause C2 ->
    RuleProofs.eo_has_bool_type C2 ->
    SafeOrClause (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) ->
    (eo_interprets M C2 false ->
      GoodOrClause M (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) ->
    __chain_m_resolve_final C1
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) C2)
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) ≠ Term.Stuck ->
    OrClause
      (__chain_m_resolve_final C1
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) C2)
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))) ∧
    RuleProofs.eo_has_bool_type
      (__chain_m_resolve_final C1
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) C2)
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))) ∧
    eo_interprets M
      (__chain_m_resolve_final C1
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) C2)
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))) true := by
  intro hC1Bool hC1True hC2 hC2Bool hPendingSafe hPendingGood hFinalNe
  have hC1Ne : C1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type C1 hC1Bool
  by_cases hEq : C1 = L
  · have hLNe : L ≠ Term.Stuck := by
      simpa [hEq] using hC1Ne
    have hEqTerm : __eo_eq C1 L = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq hC1Ne hLNe
    have hFinalEq :
        __chain_m_resolve_final C1
          (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) C2)
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) = C2 := by
      unfold __chain_m_resolve_final
      simp [hEqTerm, __eo_ite, native_ite, native_teq]
    have hC2True : eo_interprets M C2 true := by
      rcases eo_interprets_bool_cases M hM C2 hC2Bool with hTrue | hFalse
      · exact hTrue
      · have hPendingGood' := hPendingGood hFalse
        cases hPendingGood' with
        | cons x xs hX hHead hTail =>
            cases hHead with
            | inl hNotBool =>
                exact False.elim (hNotBool (by simpa [hEq] using hC1Bool))
            | inr hLFalse =>
                have hC1False : eo_interprets M C1 false := by
                  simpa [hEq] using hLFalse
                exact False.elim
                  ((RuleProofs.eo_interprets_true_not_false M C1 hC1True) hC1False)
    refine ⟨?_, ?_, ?_⟩
    · simpa [hFinalEq] using hC2
    · simpa [hFinalEq] using hC2Bool
    · simpa [hFinalEq] using hC2True
  · have hLNe : L ≠ Term.Stuck := by
      cases hPendingSafe with
      | cons x xs hX hXs =>
          simpa using hX
    have hEqTerm : __eo_eq C1 L = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq hC1Ne hLNe
    have hConcatNe :
        __eo_list_concat Term.or
          (__eo_list_diff Term.or C1
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
          C2 ≠ Term.Stuck := by
      intro hConcat
      have hFinalStuck :
          __chain_m_resolve_final C1
            (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) C2)
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) = Term.Stuck := by
        unfold __chain_m_resolve_final
        simp [hEqTerm, __eo_ite, native_ite, native_teq, hConcat]
      exact hFinalNe hFinalStuck
    have hDiffClause :
        OrClause
          (__eo_list_diff Term.or C1
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
      list_concat_nonstuck_left_orClause hConcatNe
    have hC1 :
        OrClause C1 :=
      list_diff_nonstuck_input_orClause (orClause_ne_stuck hDiffClause)
    have hDiffBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_diff Term.or C1
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
      diff_preserves_bool_type hC1 hC1Bool hPendingSafe
    have hFinalEq :
        __chain_m_resolve_final C1
          (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) C2)
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) =
        __eo_list_concat Term.or
          (__eo_list_diff Term.or C1
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
          C2 := by
      unfold __chain_m_resolve_final
      simp [hEqTerm, __eo_ite, native_ite, native_teq]
    have hFinalClause :
        OrClause
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or C1
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
            C2) :=
      concat_preserves_orClause hDiffClause hC2
    have hFinalBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or C1
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
            C2) :=
      concat_preserves_bool_type hDiffClause hC2 hDiffBool hC2Bool
    have hFinalTrue :
        eo_interprets M
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or C1
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
            C2) true := by
      rcases eo_interprets_bool_cases M hM C2 hC2Bool with hC2True | hC2False
      · exact concat_true_of_right_true M hM hDiffClause hC2 hDiffBool hC2Bool hC2True
      · have hPendingGood' := hPendingGood hC2False
        have hDiffTrue :
            eo_interprets M
              (__eo_list_diff Term.or C1
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) true :=
          diff_true_of_good M hM hC1 hC1Bool hC1True hPendingGood'
        exact concat_true_of_left_true M hM hDiffClause hC2 hDiffBool hC2Bool hDiffTrue
    refine ⟨?_, ?_, ?_⟩
    · simpa [hFinalEq] using hFinalClause
    · simpa [hFinalEq] using hFinalBool
    · simpa [hFinalEq] using hFinalTrue

private theorem chain_m_resolve_properties_of_nonstuck
    (M : SmtModel) (hM : model_wf M) :
    ∀ premises pols lits,
      AllHaveBoolType premises ->
      AllInterpretedTrue M premises ->
      EoListAllHaveSmtTranslation pols ->
      EoListAllHaveSmtTranslation lits ->
      __chain_m_resolve (premiseAndFormulaList premises) pols lits ≠ Term.Stuck ->
      OrClause (__chain_m_resolve (premiseAndFormulaList premises) pols lits) ∧
      RuleProofs.eo_has_bool_type (__chain_m_resolve (premiseAndFormulaList premises) pols lits) ∧
      eo_interprets M (__chain_m_resolve (premiseAndFormulaList premises) pols lits) true := by
  intro premises
  cases premises with
  | nil =>
      intro pols lits _ _ _ _ hResNe
      have hStuck :
          __chain_m_resolve (premiseAndFormulaList []) pols lits = Term.Stuck := by
        cases pols <;> cases lits <;> simp [premiseAndFormulaList, __chain_m_resolve]
      exact False.elim (hResNe hStuck)
  | cons C1 premises =>
      intro pols lits hPremBool hPremTrue hPols hLits hResNe
      have hC1Bool : RuleProofs.eo_has_bool_type C1 := hPremBool C1 (by simp)
      have hC1True : eo_interprets M C1 true := hPremTrue C1 (by simp)
      have hPremisesBool : AllHaveBoolType premises := by
        intro t ht
        exact hPremBool t (by simp [ht])
      have hPremisesTrue : AllInterpretedTrue M premises := by
        intro t ht
        exact hPremTrue t (by simp [ht])
      have hChainEq :
          __chain_m_resolve (premiseAndFormulaList (C1 :: premises)) pols lits =
          __chain_m_resolve_final C1
            (__chain_m_resolve_rec (premiseAndFormulaList premises) pols lits) := by
        rcases eo_list_translation_cases hPols with hPolsNil | ⟨pol, pols', hPolsEq⟩
        · rcases eo_list_translation_cases hLits with hLitsNil | ⟨L, lits', hLitsEq⟩
          · simp [premiseAndFormulaList, __chain_m_resolve, hPolsNil, hLitsNil]
          · simp [premiseAndFormulaList, __chain_m_resolve, hPolsNil, hLitsEq]
        · rcases eo_list_translation_cases hLits with hLitsNil | ⟨L, lits', hLitsEq⟩
          · simp [premiseAndFormulaList, __chain_m_resolve, hPolsEq, hLitsNil]
          · simp [premiseAndFormulaList, __chain_m_resolve, hPolsEq, hLitsEq]
      have hFinalNe :
          __chain_m_resolve_final C1
            (__chain_m_resolve_rec (premiseAndFormulaList premises) pols lits) ≠ Term.Stuck := by
        intro hFinalStuck
        apply hResNe
        rw [hChainEq]
        exact hFinalStuck
      rcases chain_m_resolve_final_pair_of_nonstuck hFinalNe with ⟨C2, L, rl, hRecEq⟩
      have hRecProps :=
        chain_m_resolve_rec_pair_false_implies_good M hM premises pols lits C2
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)
          hPremisesBool hPremisesTrue hPols hLits hRecEq
      rcases hRecProps with ⟨hC2, hC2Bool, hPendingSafe, hPendingGood⟩
      have hFinalNe' :
          __chain_m_resolve_final C1
            (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) C2)
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) ≠ Term.Stuck := by
        simpa [hRecEq] using hFinalNe
      have hFinalProps :=
        chain_m_resolve_final_properties_of_nonstuck M hM
          hC1Bool hC1True hC2 hC2Bool hPendingSafe hPendingGood hFinalNe'
      have hResEq :
          __chain_m_resolve (premiseAndFormulaList (C1 :: premises)) pols lits =
          __chain_m_resolve_final C1
            (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) C2)
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) := by
        rw [hChainEq]
        exact congrArg (__chain_m_resolve_final C1) hRecEq
      refine ⟨?_, ?_, ?_⟩
      · rw [hResEq]
        exact hFinalProps.1
      · rw [hResEq]
        exact hFinalProps.2.1
      · rw [hResEq]
        exact hFinalProps.2.2

private theorem chain_m_resolve_rec_pair_structural :
    ∀ premises pols lits Cr rl,
      AllHaveBoolType premises ->
      EoListAllHaveSmtTranslation pols ->
      EoListAllHaveSmtTranslation lits ->
      __chain_m_resolve_rec (premiseAndFormulaList premises) pols lits =
        Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl ->
      OrClause Cr ∧
      RuleProofs.eo_has_bool_type Cr ∧
      SafeOrClause rl := by
  intro premises
  induction premises with
  | nil =>
      intro pols lits Cr rl _ hPols hLits hRec
      rcases eo_list_translation_cases hPols with hPolsNil | ⟨pol, pols', hPolsCons⟩
      · subst hPolsNil
        rcases eo_list_translation_cases hLits with hLitsNil | ⟨L, lits', hLitsCons⟩
        · subst hLitsNil
          have hBase :
              Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) (Term.Boolean false))
                (Term.Boolean false) =
              Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
            have hBase := hRec
            change
              Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) (Term.Boolean false))
                (Term.Boolean false) =
              Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl at hBase
            exact hBase
          have hComps := pair_eq_components hBase
          refine ⟨?_, ?_, ?_⟩
          · simpa [hComps.1.symm] using (OrClause.false : OrClause (Term.Boolean false))
          · simpa [hComps.1.symm] using RuleProofs.eo_has_bool_type_false
          · simpa [hComps.2.symm] using (SafeOrClause.false : SafeOrClause (Term.Boolean false))
        · subst hLitsCons
          have hStuck :
              Term.Stuck =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
            have hStuck := hRec
            change
              Term.Stuck =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl at hStuck
            exact hStuck
          exact False.elim (pair_ne_stuck hStuck.symm)
      · subst hPolsCons
        rcases eo_list_translation_cases hLits with hLitsNil | ⟨L, lits', hLitsCons⟩
        · subst hLitsNil
          have hStuck :
              Term.Stuck =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
            have hStuck := hRec
            change
              Term.Stuck =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl at hStuck
            exact hStuck
          exact False.elim (pair_ne_stuck hStuck.symm)
        · subst hLitsCons
          have hStuck :
              Term.Stuck =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
            have hStuck := hRec
            change
              Term.Stuck =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl at hStuck
            exact hStuck
          exact False.elim (pair_ne_stuck hStuck.symm)
  | cons Cc premises ih =>
      intro pols lits Cr rl hPremBool hPols hLits hRec
      have hCcBool : RuleProofs.eo_has_bool_type Cc := hPremBool Cc (by simp)
      have hPremisesBool : AllHaveBoolType premises := by
        intro t ht
        exact hPremBool t (by simp [ht])
      rcases eo_list_translation_cases hPols with hPolsNil | ⟨pol, pols', hPolsCons⟩
      · subst hPolsNil
        have hStuck :
            Term.Stuck =
              Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
          have hStuck := hRec
          change
            Term.Stuck =
              Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl at hStuck
          exact hStuck
        exact False.elim (pair_ne_stuck hStuck.symm)
      · subst hPolsCons
        rcases eo_list_translation_cons_inv hPols with ⟨_hPolTrans, hPols'⟩
        rcases eo_list_translation_cases hLits with hLitsNil | ⟨L, lits', hLitsCons⟩
        · subst hLitsNil
          have hStuck :
              Term.Stuck =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
            have hStuck := hRec
            change
              Term.Stuck =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl at hStuck
            exact hStuck
          exact False.elim (pair_ne_stuck hStuck.symm)
        · subst hLitsCons
          rcases eo_list_translation_cons_inv hLits with ⟨hLTrans, hLits'⟩
          have hStep :
              __chain_m_resolve_rec_step
                (__chain_m_resolve_rec (premiseAndFormulaList premises) pols' lits')
                Cc pol L =
              Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
            have hStep := hRec
            change
              __chain_m_resolve_rec_step
                (__chain_m_resolve_rec (premiseAndFormulaList premises) pols' lits')
                Cc pol L =
              Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl at hStep
            exact hStep
          by_cases hPolTrue : pol = Term.Boolean true
          · subst hPolTrue
            rcases chain_m_resolve_rec_step_true_pair_input hCcBool hLTrans hStep with
              ⟨Cr0, rl0, hTailEq⟩
            rcases ih pols' lits' Cr0 rl0 hPremisesBool hPols' hLits' hTailEq with
              ⟨hCr0Clause, hCr0Bool, hRl0Safe⟩
            have hStepPair :
                __chain_m_resolve_rec_step
                  (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0) rl0)
                  Cc (Term.Boolean true) L =
                Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
              simpa [hTailEq] using hStep
            have hResidual :=
              chain_m_resolve_rec_step_true_pair_residual
                hCr0Clause hCr0Bool hRl0Safe hCcBool hLTrans hStepPair
            have hRlSafe :=
              chain_m_resolve_rec_step_true_pair_safe hRl0Safe hCcBool hLTrans hStepPair
            exact ⟨hResidual.1, hResidual.2, hRlSafe⟩
          · by_cases hPolFalse : pol = Term.Boolean false
            · subst hPolFalse
              rcases chain_m_resolve_rec_step_false_pair_input hCcBool hLTrans hStep with
                ⟨Cr0, rl0, hTailEq⟩
              rcases ih pols' lits' Cr0 rl0 hPremisesBool hPols' hLits' hTailEq with
                ⟨hCr0Clause, hCr0Bool, hRl0Safe⟩
              have hStepPair :
                  __chain_m_resolve_rec_step
                    (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr0) rl0)
                    Cc (Term.Boolean false) L =
                  Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) Cr) rl := by
                simpa [hTailEq] using hStep
              have hResidual :=
                chain_m_resolve_rec_step_false_pair_residual
                  hCr0Clause hCr0Bool hRl0Safe hCcBool hLTrans hStepPair
              have hRlSafe :=
                chain_m_resolve_rec_step_false_pair_safe hRl0Safe hCcBool hLTrans hStepPair
              exact ⟨hResidual.1, hResidual.2, hRlSafe⟩
            · have hCcNe : Cc ≠ Term.Stuck :=
                RuleProofs.term_ne_stuck_of_has_bool_type Cc hCcBool
              have hLNe : L ≠ Term.Stuck :=
                RuleProofs.term_ne_stuck_of_has_smt_translation L hLTrans
              have hStuck :
                  __chain_m_resolve_rec_step
                    (__chain_m_resolve_rec (premiseAndFormulaList premises) pols' lits')
                    Cc pol L = Term.Stuck :=
                chain_m_resolve_rec_step_stuck_of_pol_ne_true_false
                  hCcNe hLNe hPolTrue hPolFalse
              rw [hStuck] at hStep
              exact False.elim (pair_ne_stuck hStep.symm)

private theorem chain_m_resolve_final_structural_of_nonstuck
    {C1 C2 L rl : Term} :
    RuleProofs.eo_has_bool_type C1 ->
    OrClause C2 ->
    RuleProofs.eo_has_bool_type C2 ->
    SafeOrClause (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl) ->
    __chain_m_resolve_final C1
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) C2)
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) ≠ Term.Stuck ->
    OrClause
      (__chain_m_resolve_final C1
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) C2)
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))) ∧
    RuleProofs.eo_has_bool_type
      (__chain_m_resolve_final C1
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) C2)
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))) := by
  intro hC1Bool hC2 hC2Bool hPendingSafe hFinalNe
  have hC1Ne : C1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type C1 hC1Bool
  by_cases hEq : C1 = L
  · have hLNe : L ≠ Term.Stuck := by
      simpa [hEq] using hC1Ne
    have hEqTerm : __eo_eq C1 L = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq hC1Ne hLNe
    have hFinalEq :
        __chain_m_resolve_final C1
          (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) C2)
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) = C2 := by
      unfold __chain_m_resolve_final
      simp [hEqTerm, __eo_ite, native_ite, native_teq]
    exact ⟨by simpa [hFinalEq] using hC2, by simpa [hFinalEq] using hC2Bool⟩
  · have hLNe : L ≠ Term.Stuck := by
      cases hPendingSafe with
      | cons x xs hX hXs =>
          simpa using hX
    have hEqTerm : __eo_eq C1 L = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq hC1Ne hLNe
    have hConcatNe :
        __eo_list_concat Term.or
          (__eo_list_diff Term.or C1
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
          C2 ≠ Term.Stuck := by
      intro hConcat
      apply hFinalNe
      unfold __chain_m_resolve_final
      simp [hEqTerm, __eo_ite, native_ite, native_teq, hConcat]
    have hDiffClause :
        OrClause
          (__eo_list_diff Term.or C1
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
      list_concat_nonstuck_left_orClause hConcatNe
    have hC1 :
        OrClause C1 :=
      list_diff_nonstuck_input_orClause (orClause_ne_stuck hDiffClause)
    have hDiffBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_diff Term.or C1
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) :=
      diff_preserves_bool_type hC1 hC1Bool hPendingSafe
    have hFinalEq :
        __chain_m_resolve_final C1
          (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) C2)
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) =
        __eo_list_concat Term.or
          (__eo_list_diff Term.or C1
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
          C2 := by
      unfold __chain_m_resolve_final
      simp [hEqTerm, __eo_ite, native_ite, native_teq]
    have hFinalClause :
        OrClause
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or C1
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
            C2) :=
      concat_preserves_orClause hDiffClause hC2
    have hFinalBool :
        RuleProofs.eo_has_bool_type
          (__eo_list_concat Term.or
            (__eo_list_diff Term.or C1
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl))
            C2) :=
      concat_preserves_bool_type hDiffClause hC2 hDiffBool hC2Bool
    exact ⟨by simpa [hFinalEq] using hFinalClause, by simpa [hFinalEq] using hFinalBool⟩

private theorem chain_m_resolve_structural_of_nonstuck
    {M : SmtModel} (hM : model_wf M) :
    ∀ premises pols lits,
      AllHaveBoolType premises ->
      EoListAllHaveSmtTranslation pols ->
      EoListAllHaveSmtTranslation lits ->
      __chain_m_resolve (premiseAndFormulaList premises) pols lits ≠ Term.Stuck ->
      OrClause (__chain_m_resolve (premiseAndFormulaList premises) pols lits) ∧
      RuleProofs.eo_has_bool_type (__chain_m_resolve (premiseAndFormulaList premises) pols lits) := by
  intro premises
  cases premises with
  | nil =>
      intro pols lits _ hPols hLits hResNe
      have hStuck :
          __chain_m_resolve (premiseAndFormulaList []) pols lits = Term.Stuck := by
        cases pols <;> cases lits <;> simp [premiseAndFormulaList, __chain_m_resolve]
      exact False.elim (hResNe hStuck)
  | cons C1 premises =>
      intro pols lits hPremBool hPols hLits hResNe
      have hC1Bool : RuleProofs.eo_has_bool_type C1 := hPremBool C1 (by simp)
      have hPremisesBool : AllHaveBoolType premises := by
        intro t ht
        exact hPremBool t (by simp [ht])
      have hChainEq :
          __chain_m_resolve (premiseAndFormulaList (C1 :: premises)) pols lits =
          __chain_m_resolve_final C1
            (__chain_m_resolve_rec (premiseAndFormulaList premises) pols lits) := by
        rcases eo_list_translation_cases hPols with hPolsNil | ⟨pol, pols', hPolsEq⟩
        · rcases eo_list_translation_cases hLits with hLitsNil | ⟨L, lits', hLitsEq⟩
          · simp [premiseAndFormulaList, __chain_m_resolve, hPolsNil, hLitsNil]
          · simp [premiseAndFormulaList, __chain_m_resolve, hPolsNil, hLitsEq]
        · rcases eo_list_translation_cases hLits with hLitsNil | ⟨L, lits', hLitsEq⟩
          · simp [premiseAndFormulaList, __chain_m_resolve, hPolsEq, hLitsNil]
          · simp [premiseAndFormulaList, __chain_m_resolve, hPolsEq, hLitsEq]
      have hFinalNe :
          __chain_m_resolve_final C1
            (__chain_m_resolve_rec (premiseAndFormulaList premises) pols lits) ≠ Term.Stuck := by
        intro hFinalStuck
        apply hResNe
        rw [hChainEq]
        exact hFinalStuck
      rcases chain_m_resolve_final_pair_of_nonstuck hFinalNe with ⟨C2, L, rl, hRecEq⟩
      have hRecProps :=
        chain_m_resolve_rec_pair_structural premises pols lits C2
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)
          hPremisesBool hPols hLits hRecEq
      rcases hRecProps with ⟨hC2, hC2Bool, hPendingSafe⟩
      have hFinalNe' :
          __chain_m_resolve_final C1
            (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) C2)
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) ≠ Term.Stuck := by
        simpa [hRecEq] using hFinalNe
      have hFinalProps :=
        chain_m_resolve_final_structural_of_nonstuck
          hC1Bool hC2 hC2Bool hPendingSafe hFinalNe'
      have hResEq :
          __chain_m_resolve (premiseAndFormulaList (C1 :: premises)) pols lits =
          __chain_m_resolve_final C1
            (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) C2)
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) L) rl)) := by
        rw [hChainEq]
        exact congrArg (__chain_m_resolve_final C1) hRecEq
      exact ⟨by rw [hResEq]; exact hFinalProps.1, by rw [hResEq]; exact hFinalProps.2⟩

private theorem list_setof_arg_ne_stuck {c : Term} :
    __eo_list_setof Term.or c ≠ Term.Stuck ->
    c ≠ Term.Stuck := by
  intro hSet hC
  subst hC
  simp [__eo_list_setof, __eo_is_list
    ] at hSet
  exact hSet rfl

private theorem eq_true_of_requires_true_not_stuck {x B : Term} :
    __eo_requires x (Term.Boolean true) B ≠ Term.Stuck ->
    x = Term.Boolean true := by
  intro hReq
  cases x <;> cases B <;>
    simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hReq ⊢
  all_goals assumption

private theorem eq_of_eo_eq_true_local (x y : Term) :
    __eo_eq x y = Term.Boolean true ->
    y = x := by
  intro h
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_eq] at h
  · by_cases hy : y = Term.Stuck
    · subst y
      simp [__eo_eq] at h
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using h
      simpa [native_teq] using hDec

private theorem orClause_right_of_minclude_true {c d : Term} :
    __eo_list_minclude Term.or c d = Term.Boolean true ->
    OrClause d := by
  intro hIncl
  have hReqD :
      __eo_requires (__eo_is_list Term.or d) (Term.Boolean true) (__eo_get_elements_rec d) ≠
        Term.Stuck := by
    intro hReqD
    cases hReqC :
        __eo_requires (__eo_is_list Term.or c) (Term.Boolean true) (__eo_get_elements_rec c) <;>
      simp [__eo_list_minclude, __eo_list_minclude_rec, hReqD, hReqC] at hIncl
  have hListD : __eo_is_list Term.or d = Term.Boolean true :=
    eq_true_of_requires_true_not_stuck hReqD
  exact orClause_of_is_list_true hListD

private theorem orClause_left_of_minclude_true {c d : Term} :
    __eo_list_minclude Term.or c d = Term.Boolean true ->
    OrClause c := by
  intro hIncl
  have hReqC :
      __eo_requires (__eo_is_list Term.or c) (Term.Boolean true) (__eo_get_elements_rec c) ≠
        Term.Stuck := by
    intro hReqC
    cases hReqD :
        __eo_requires (__eo_is_list Term.or d) (Term.Boolean true) (__eo_get_elements_rec d) <;>
      simp [__eo_list_minclude, __eo_list_minclude_rec, hReqC, hReqD] at hIncl
  have hListC : __eo_is_list Term.or c = Term.Boolean true :=
    eq_true_of_requires_true_not_stuck hReqC
  exact orClause_of_is_list_true hListC

private theorem get_elements_rec_ne_stuck {c : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    __eo_get_elements_rec c ≠ Term.Stuck := by
  intro hClause hCBool
  induction hClause with
  | false =>
      simp [__eo_get_elements_rec]
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hXsNe : __eo_get_elements_rec xs ≠ Term.Stuck := ih hXsBool
      simp [__eo_get_elements_rec, __eo_mk_apply]

private theorem get_elements_or_eq {x xs : Term} :
    x ≠ Term.Stuck ->
    __eo_get_elements_rec xs ≠ Term.Stuck ->
    __eo_get_elements_rec (Term.Apply (Term.Apply Term.or x) xs) =
      Term.Apply (Term.Apply Term.__eo_List_cons x) (__eo_get_elements_rec xs) := by
  intro hX hXsNe
  simp [__eo_get_elements_rec, __eo_mk_apply]

private theorem erase_rec_true_implies_original_true
    (M : SmtModel) (hM : model_wf M) {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    eo_interprets M (__eo_list_erase_rec c e) true ->
    eo_interprets M c true := by
  intro hClause hCBool hE hEraseTrue
  induction hClause generalizing e with
  | false =>
      have : eo_interprets M (Term.Boolean false) true := by
        simpa [__eo_list_erase_rec] using hEraseTrue
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ this) (eo_interprets_false M))
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      by_cases hEq : x = e
      · rw [list_erase_rec_cons_eq x xs e hEq hX hE] at hEraseTrue
        exact RuleProofs.eo_interprets_or_right_intro M hM x xs hXBool hEraseTrue
      · have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_erase_rec xs e) :=
          erase_rec_preserves_bool_type hXs hXsBool hE
        have hTailNe : __eo_list_erase_rec xs e ≠ Term.Stuck :=
          RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
        rw [list_erase_rec_cons_ne x xs e hEq hX hE hTailNe] at hEraseTrue
        rcases eo_interprets_bool_cases M hM x hXBool with hXTrue | hXFalse
        · exact RuleProofs.eo_interprets_or_left_intro M hM x xs hXTrue hXsBool
        · have hTailTrue : eo_interprets M (__eo_list_erase_rec xs e) true :=
            eo_interprets_or_right_of_left_false M hM x (__eo_list_erase_rec xs e)
              hXFalse hEraseTrue
          have hXsTrue : eo_interprets M xs true :=
            ih hXsBool hE hTailTrue
          exact RuleProofs.eo_interprets_or_right_intro M hM x xs hXBool hXsTrue

private theorem erase_true_implies_original_true
    (M : SmtModel) (hM : model_wf M) {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    eo_interprets M (__eo_list_erase Term.or c e) true ->
    eo_interprets M c true := by
  intro hClause hCBool hE hEraseTrue
  change eo_interprets M
    (__eo_requires (__eo_is_list Term.or c) (Term.Boolean true) (__eo_list_erase_rec c e)) true
    at hEraseTrue
  rw [orClause_is_list_true hClause] at hEraseTrue
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hEraseTrue
  exact erase_rec_true_implies_original_true M hM hClause hCBool hE hEraseTrue

private theorem erase_rec_changed_and_lit_true_implies_clause_true
    (M : SmtModel) (hM : model_wf M) {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type e ->
    eo_interprets M e true ->
    __eo_list_erase_rec c e ≠ c ->
    eo_interprets M c true := by
  intro hClause hCBool hE hEBool hETrue hChanged
  induction hClause generalizing e with
  | false =>
      exfalso
      apply hChanged
      simp [__eo_list_erase_rec]
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      by_cases hEq : x = e
      · have hXTrue : eo_interprets M x true := by
          simpa [hEq] using hETrue
        exact RuleProofs.eo_interprets_or_left_intro M hM x xs hXTrue hXsBool
      · have hTailChanged : __eo_list_erase_rec xs e ≠ xs := by
          intro hTailEq
          have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_erase_rec xs e) :=
            erase_rec_preserves_bool_type hXs hXsBool hE
          have hTailNe : __eo_list_erase_rec xs e ≠ Term.Stuck :=
            RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
          apply hChanged
          rw [list_erase_rec_cons_ne x xs e hEq hX hE hTailNe, hTailEq]
        rcases eo_interprets_bool_cases M hM x hXBool with hXTrue | hXFalse
        · exact RuleProofs.eo_interprets_or_left_intro M hM x xs hXTrue hXsBool
        · have hXsTrue : eo_interprets M xs true :=
            ih hXsBool hE hEBool hETrue hTailChanged
          exact RuleProofs.eo_interprets_or_right_intro M hM x xs hXBool hXsTrue

private theorem erase_changed_and_lit_true_implies_clause_true
    (M : SmtModel) (hM : model_wf M) {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type e ->
    eo_interprets M e true ->
    __eo_list_erase Term.or c e ≠ c ->
    eo_interprets M c true := by
  intro hClause hCBool hE hEBool hETrue hChanged
  have hEraseEq : __eo_list_erase Term.or c e = __eo_list_erase_rec c e := by
    simp [__eo_list_erase, orClause_is_list_true hClause, __eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not]
  apply erase_rec_changed_and_lit_true_implies_clause_true M hM hClause hCBool hE hEBool hETrue
  intro hRecEq
  apply hChanged
  rw [hEraseEq, hRecEq]

private theorem get_elements_erase_rec_eq {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    __eo_get_elements_rec (__eo_list_erase_rec c e) =
      __eo_list_erase_rec (__eo_get_elements_rec c) e := by
  intro hClause hCBool hE
  induction hClause generalizing e with
  | false =>
      simp [__eo_list_erase_rec, __eo_get_elements_rec]
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hElemsXsNe : __eo_get_elements_rec xs ≠ Term.Stuck :=
        get_elements_rec_ne_stuck hXs hXsBool
      by_cases hEq : x = e
      · have hEqTerm : __eo_eq x e = Term.Boolean true :=
          eo_eq_eq_true_of_eq hEq hX hE
        rw [list_erase_rec_cons_eq x xs e hEq hX hE]
        rw [get_elements_or_eq hX hElemsXsNe]
        simp [__eo_list_erase_rec, hEqTerm, __eo_ite, native_ite, native_teq]
      · have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_erase_rec xs e) :=
          erase_rec_preserves_bool_type hXs hXsBool hE
        have hTailNe : __eo_list_erase_rec xs e ≠ Term.Stuck :=
          RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
        have hTailClause : OrClause (__eo_list_erase_rec xs e) :=
          erase_rec_preserves_orClause hXs hXsBool hE
        have hElemsTailNe : __eo_get_elements_rec (__eo_list_erase_rec xs e) ≠ Term.Stuck :=
          get_elements_rec_ne_stuck hTailClause hTailBool
        have hErasedElemsNe : __eo_list_erase_rec (__eo_get_elements_rec xs) e ≠ Term.Stuck := by
          rw [← ih hXsBool hE]
          exact hElemsTailNe
        have hNeTerm : __eo_eq x e = Term.Boolean false :=
          eo_eq_eq_false_of_ne hEq hX hE
        have hConsFnNe : Term.Apply Term.__eo_List_cons x ≠ Term.Stuck := by
          intro h
          cases h
        rw [list_erase_rec_cons_ne x xs e hEq hX hE hTailNe]
        rw [get_elements_or_eq hX hElemsTailNe]
        rw [get_elements_or_eq hX hElemsXsNe]
        simpa [__eo_list_erase_rec, __eo_mk_apply, hNeTerm, __eo_ite, native_ite, native_teq,
          hConsFnNe, hErasedElemsNe] using
          congrArg (Term.Apply (Term.Apply Term.__eo_List_cons x)) (ih hXsBool hE)

private theorem get_elements_erase_eq {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    __eo_get_elements_rec (__eo_list_erase Term.or c e) =
      __eo_list_erase_rec (__eo_get_elements_rec c) e := by
  intro hClause hCBool hE
  have hEraseEq : __eo_list_erase Term.or c e = __eo_list_erase_rec c e := by
    simp [__eo_list_erase, orClause_is_list_true hClause, __eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not]
  rw [hEraseEq]
  exact get_elements_erase_rec_eq hClause hCBool hE

private theorem erase_all_rec_preserves_orClause {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    OrClause (__eo_list_erase_all_rec c e) := by
  intro hClause hCBool hE
  induction hClause generalizing e with
  | false =>
      simpa [__eo_list_erase_all_rec] using OrClause.false
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hTail : OrClause (__eo_list_erase_all_rec xs e) :=
        ih hXsBool hE
      have hTailNe : __eo_list_erase_all_rec xs e ≠ Term.Stuck :=
        orClause_ne_stuck hTail
      by_cases hEq : x = e
      · have hEqTerm : __eo_eq e x = Term.Boolean true :=
          eo_eq_eq_true_of_eq hEq.symm hE hX
        have hStep :
            __eo_list_erase_all_rec (Term.Apply (Term.Apply Term.or x) xs) e =
              __eo_list_erase_all_rec xs e := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm, native_not
            ]
        rw [hStep]
        exact hTail
      · have hEqTerm : __eo_eq e x = Term.Boolean false :=
          eo_eq_eq_false_of_ne (by
            intro hEx
            apply hEq
            exact hEx.symm) hE hX
        have hStep :
            __eo_list_erase_all_rec (Term.Apply (Term.Apply Term.or x) xs) e =
              Term.Apply (Term.Apply Term.or x) (__eo_list_erase_all_rec xs e) := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm, native_not
            ]
        rw [hStep]
        exact OrClause.cons x (__eo_list_erase_all_rec xs e) hTail

private theorem erase_all_rec_preserves_bool_type {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_list_erase_all_rec c e) := by
  intro hClause hCBool hE
  induction hClause generalizing e with
  | false =>
      simpa [__eo_list_erase_all_rec] using RuleProofs.eo_has_bool_type_false
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hTail : RuleProofs.eo_has_bool_type (__eo_list_erase_all_rec xs e) :=
        ih hXsBool hE
      have hTailNe : __eo_list_erase_all_rec xs e ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTail
      by_cases hEq : x = e
      · have hEqTerm : __eo_eq e x = Term.Boolean true :=
          eo_eq_eq_true_of_eq hEq.symm hE hX
        have hStep :
            __eo_list_erase_all_rec (Term.Apply (Term.Apply Term.or x) xs) e =
              __eo_list_erase_all_rec xs e := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm, native_not
            ]
        rw [hStep]
        exact hTail
      · have hEqTerm : __eo_eq e x = Term.Boolean false :=
          eo_eq_eq_false_of_ne (by
            intro hEx
            apply hEq
            exact hEx.symm) hE hX
        have hStep :
            __eo_list_erase_all_rec (Term.Apply (Term.Apply Term.or x) xs) e =
              Term.Apply (Term.Apply Term.or x) (__eo_list_erase_all_rec xs e) := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm, native_not
            ]
        rw [hStep]
        exact RuleProofs.eo_has_bool_type_or_of_bool_args x (__eo_list_erase_all_rec xs e)
          hXBool hTail

private theorem erase_all_rec_true_of_lit_false
    (M : SmtModel) (hM : model_wf M) {c e : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type e ->
    eo_interprets M e false ->
    eo_interprets M c true ->
    eo_interprets M (__eo_list_erase_all_rec c e) true := by
  intro hClause hCBool hE hEBool hEFalse hCTrue
  induction hClause generalizing e with
  | false =>
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hCTrue) (eo_interprets_false M))
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hOrTrue : eo_interprets M (Term.Apply (Term.Apply Term.or x) xs) true := by
        simpa using hCTrue
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_erase_all_rec xs e) :=
        erase_all_rec_preserves_bool_type hXs hXsBool hE
      have hTailNe : __eo_list_erase_all_rec xs e ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
      by_cases hEq : x = e
      · have hXFalse : eo_interprets M x false := by
          simpa [hEq] using hEFalse
        have hXsTrue : eo_interprets M xs true :=
          eo_interprets_or_right_of_left_false M hM x xs hXFalse hOrTrue
        have hTailTrue : eo_interprets M (__eo_list_erase_all_rec xs e) true :=
          ih hXsBool hE hEBool hEFalse hXsTrue
        have hEqTerm : __eo_eq e x = Term.Boolean true :=
          eo_eq_eq_true_of_eq hEq.symm hE hX
        have hStep :
            __eo_list_erase_all_rec (Term.Apply (Term.Apply Term.or x) xs) e =
              __eo_list_erase_all_rec xs e := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm, native_not
            ]
        rw [hStep]
        exact hTailTrue
      · have hEqTerm : __eo_eq e x = Term.Boolean false :=
          eo_eq_eq_false_of_ne (by
            intro hEx
            apply hEq
            exact hEx.symm) hE hX
        rcases eo_interprets_bool_cases M hM x hXBool with hXTrue | hXFalse
        · have hStep :
            __eo_list_erase_all_rec (Term.Apply (Term.Apply Term.or x) xs) e =
              Term.Apply (Term.Apply Term.or x) (__eo_list_erase_all_rec xs e) := by
            simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm, native_not
              ]
          rw [hStep]
          exact RuleProofs.eo_interprets_or_left_intro M hM x (__eo_list_erase_all_rec xs e)
            hXTrue hTailBool
        · have hXsTrue : eo_interprets M xs true :=
            eo_interprets_or_right_of_left_false M hM x xs hXFalse hOrTrue
          have hTailTrue : eo_interprets M (__eo_list_erase_all_rec xs e) true :=
            ih hXsBool hE hEBool hEFalse hXsTrue
          have hStep :
              __eo_list_erase_all_rec (Term.Apply (Term.Apply Term.or x) xs) e =
                Term.Apply (Term.Apply Term.or x) (__eo_list_erase_all_rec xs e) := by
            simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm, native_not
              ]
          rw [hStep]
          exact RuleProofs.eo_interprets_or_right_intro M hM x (__eo_list_erase_all_rec xs e)
            hXBool hTailTrue

private theorem setof_rec_structural {c : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    OrClause (__eo_list_setof_rec c) ∧
      RuleProofs.eo_has_bool_type (__eo_list_setof_rec c) := by
  intro hClause hCBool
  induction hClause with
  | false =>
      exact ⟨by simpa [__eo_list_setof_rec] using OrClause.false,
        by simpa [__eo_list_setof_rec] using RuleProofs.eo_has_bool_type_false⟩
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hTailClause : OrClause (__eo_list_setof_rec xs) := (ih hXsBool).1
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_setof_rec xs) := (ih hXsBool).2
      have hEraseClause : OrClause (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) :=
        erase_all_rec_preserves_orClause hTailClause hTailBool hX
      have hEraseBool : RuleProofs.eo_has_bool_type (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) :=
        erase_all_rec_preserves_bool_type hTailClause hTailBool hX
      have hEraseNe : __eo_list_erase_all_rec (__eo_list_setof_rec xs) x ≠ Term.Stuck :=
        orClause_ne_stuck hEraseClause
      have hStep :
          __eo_list_setof_rec (Term.Apply (Term.Apply Term.or x) xs) =
            Term.Apply (Term.Apply Term.or x)
              (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) := by
        simp [__eo_list_setof_rec, __eo_mk_apply]
      rw [hStep]
      exact ⟨OrClause.cons x (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) hEraseClause,
        RuleProofs.eo_has_bool_type_or_of_bool_args x
          (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) hXBool hEraseBool⟩

private theorem setof_rec_true
    (M : SmtModel) (hM : model_wf M) {c : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c true ->
    eo_interprets M (__eo_list_setof_rec c) true := by
  intro hClause hCBool hCTrue
  induction hClause with
  | false =>
      exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hCTrue) (eo_interprets_false M))
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hOrTrue : eo_interprets M (Term.Apply (Term.Apply Term.or x) xs) true := by
        simpa using hCTrue
      have hTailStruct := setof_rec_structural hXs hXsBool
      have hEraseBool : RuleProofs.eo_has_bool_type (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) :=
        erase_all_rec_preserves_bool_type hTailStruct.1 hTailStruct.2 hX
      have hEraseNe : __eo_list_erase_all_rec (__eo_list_setof_rec xs) x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hEraseBool
      have hStep :
          __eo_list_setof_rec (Term.Apply (Term.Apply Term.or x) xs) =
            Term.Apply (Term.Apply Term.or x)
              (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) := by
        simp [__eo_list_setof_rec, __eo_mk_apply]
      rcases eo_interprets_bool_cases M hM x hXBool with hXTrue | hXFalse
      · rw [hStep]
        exact RuleProofs.eo_interprets_or_left_intro M hM x
          (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) hXTrue hEraseBool
      · have hXsTrue : eo_interprets M xs true :=
          eo_interprets_or_right_of_left_false M hM x xs hXFalse hOrTrue
        have hSetXsTrue : eo_interprets M (__eo_list_setof_rec xs) true :=
          ih hXsBool hXsTrue
        have hEraseTrue : eo_interprets M (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) true :=
          erase_all_rec_true_of_lit_false M hM hTailStruct.1 hTailStruct.2 hX hXBool hXFalse hSetXsTrue
        rw [hStep]
        exact RuleProofs.eo_interprets_or_right_intro M hM x
          (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) hXBool hEraseTrue

private theorem setof_preserves_orClause {c : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    OrClause (__eo_list_setof Term.or c) := by
  intro hClause hCBool
  change OrClause
    (__eo_requires (__eo_is_list Term.or c) (Term.Boolean true) (__eo_list_setof_rec c))
  rw [orClause_is_list_true hClause]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact (setof_rec_structural hClause hCBool).1

private theorem setof_preserves_bool_type {c : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    RuleProofs.eo_has_bool_type (__eo_list_setof Term.or c) := by
  intro hClause hCBool
  change RuleProofs.eo_has_bool_type
    (__eo_requires (__eo_is_list Term.or c) (Term.Boolean true) (__eo_list_setof_rec c))
  rw [orClause_is_list_true hClause]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact (setof_rec_structural hClause hCBool).2

private theorem setof_true
    (M : SmtModel) (hM : model_wf M) {c : Term} :
    OrClause c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c true ->
    eo_interprets M (__eo_list_setof Term.or c) true := by
  intro hClause hCBool hCTrue
  change eo_interprets M
    (__eo_requires (__eo_is_list Term.or c) (Term.Boolean true) (__eo_list_setof_rec c)) true
  rw [orClause_is_list_true hClause]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact setof_rec_true M hM hClause hCBool hCTrue

private theorem orClause_true_of_minclude_true
    (M : SmtModel) (hM : model_wf M) :
    ∀ {c d : Term},
      OrClause c ->
      RuleProofs.eo_has_bool_type c ->
      OrClause d ->
      RuleProofs.eo_has_bool_type d ->
      __eo_list_minclude Term.or c d = Term.Boolean true ->
      eo_interprets M d true ->
      eo_interprets M c true := by
  intro c d hC hCBool hD hDBool hIncl hDTrue
  induction hD generalizing c with
  | false =>
      exfalso
      exact (RuleProofs.eo_interprets_true_not_false M _ hDTrue) (eo_interprets_false M)
  | cons x xs hXs ih =>
      have hDClause : OrClause (Term.Apply (Term.Apply Term.or x) xs) :=
        OrClause.cons x xs hXs
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hDBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hDBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hElemsCNe : __eo_get_elements_rec c ≠ Term.Stuck :=
        get_elements_rec_ne_stuck hC hCBool
      have hElemsXsNe : __eo_get_elements_rec xs ≠ Term.Stuck :=
        get_elements_rec_ne_stuck hXs hXsBool
      let z := __eo_list_erase_rec (__eo_get_elements_rec c) x
      have hInclRec :
          __eo_list_minclude_rec z (__eo_get_elements_rec xs)
            (__eo_not (__eo_eq z (__eo_get_elements_rec c))) = Term.Boolean true := by
        have hIncl' := hIncl
        rw [show __eo_list_minclude Term.or c (Term.Apply (Term.Apply Term.or x) xs) =
            __eo_list_minclude_rec
              (__eo_get_elements_rec c)
              (Term.Apply (Term.Apply Term.__eo_List_cons x) (__eo_get_elements_rec xs))
              (Term.Boolean true) by
              simp [__eo_list_minclude, orClause_is_list_true hC, orClause_is_list_true hDClause,
                __eo_requires, native_ite, native_teq, native_not, SmtEval.native_not,
                get_elements_or_eq hX hElemsXsNe]] at hIncl'
        simpa [__eo_list_minclude_rec, z]
          using hIncl'
      have hZNe : z ≠ Term.Stuck := by
        intro hZ
        have hInclRec' := hInclRec
        rw [hZ] at hInclRec'
        simp [__eo_list_minclude_rec] at hInclRec'
      have hZChanged : z ≠ __eo_get_elements_rec c := by
        intro hEq
        have hEqTerm : __eo_eq z (__eo_get_elements_rec c) = Term.Boolean true :=
          eo_eq_eq_true_of_eq hEq hZNe hElemsCNe
        simp [__eo_list_minclude_rec, hEqTerm, __eo_not, native_not] at hInclRec
      have hNotEqTerm :
          __eo_not (__eo_eq z (__eo_get_elements_rec c)) = Term.Boolean true := by
        have hEqTerm : __eo_eq z (__eo_get_elements_rec c) = Term.Boolean false :=
          eo_eq_eq_false_of_ne hZChanged hZNe hElemsCNe
        simp [__eo_not, hEqTerm, native_not]
      have hTailInclRec :
          __eo_list_minclude_rec z (__eo_get_elements_rec xs) (Term.Boolean true) =
            Term.Boolean true := by
        rw [hNotEqTerm] at hInclRec
        exact hInclRec
      have hEraseChanged : __eo_list_erase Term.or c x ≠ c := by
        intro hEraseEq
        apply hZChanged
        rw [show z = __eo_get_elements_rec (__eo_list_erase Term.or c x) by
            simpa [z] using (get_elements_erase_eq hC hCBool hX).symm]
        exact congrArg __eo_get_elements_rec hEraseEq
      have hEraseClause : OrClause (__eo_list_erase Term.or c x) :=
        erase_preserves_orClause hC hCBool hX
      have hEraseBool : RuleProofs.eo_has_bool_type (__eo_list_erase Term.or c x) :=
        erase_preserves_bool_type hC hCBool hX
      have hTailIncl :
          __eo_list_minclude Term.or (__eo_list_erase Term.or c x) xs = Term.Boolean true := by
        have hGetErase :
            __eo_get_elements_rec (__eo_list_erase Term.or c x) = z := by
          simpa [z] using get_elements_erase_eq hC hCBool hX
        simpa [__eo_list_minclude, orClause_is_list_true hEraseClause, orClause_is_list_true hXs,
          __eo_requires, native_ite, native_teq, native_not, SmtEval.native_not, hGetErase]
          using hTailInclRec
      rcases eo_interprets_bool_cases M hM x hXBool with hXTrue | hXFalse
      · exact erase_changed_and_lit_true_implies_clause_true M hM
          hC hCBool hX hXBool hXTrue hEraseChanged
      · have hXsTrue : eo_interprets M xs true :=
          eo_interprets_or_right_of_left_false M hM x xs hXFalse hDTrue
        have hEraseTrue : eo_interprets M (__eo_list_erase Term.or c x) true :=
          ih hEraseClause hEraseBool hXsBool hTailIncl hXsTrue
        exact erase_true_implies_original_true M hM hC hCBool hX hEraseTrue

theorem cmd_step_chain_m_resolution_properties_aux
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.chain_m_resolution args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.chain_m_resolution args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.chain_m_resolution args premises) := by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.chain_m_resolution args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons Cr args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons pols args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons lits args =>
              cases args with
              | nil =>
                  have hCrTrans : RuleProofs.eo_has_smt_translation Cr := hCmdTrans.1
                  have hPols : EoListAllHaveSmtTranslation pols := hCmdTrans.2.1
                  have hLits : EoListAllHaveSmtTranslation lits := hCmdTrans.2.2.1
                  have hPolsNe : pols ≠ Term.Stuck := by
                    intro hStuck
                    subst hStuck
                    cases hPols
                  have hLitsNe : lits ≠ Term.Stuck := by
                    intro hStuck
                    subst hStuck
                    cases hLits
                  let ps := premiseTermList s premises
                  have hMkPremises :
                      __eo_mk_premise_list (Term.UOp UserOp.and) premises s =
                        premiseAndFormulaList ps := by
                    simpa [ps] using mk_premise_list_and_eq_premiseAndFormulaList s premises
                  have hCmdProgEq :
                      __eo_cmd_step_proven s CRule.chain_m_resolution
                        (CArgList.cons Cr (CArgList.cons pols (CArgList.cons lits CArgList.nil)))
                        premises =
                      __eo_prog_chain_m_resolution Cr pols lits
                        (Proof.pf (premiseAndFormulaList ps)) := by
                    change
                      __eo_prog_chain_m_resolution Cr pols lits
                        (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s)) =
                      __eo_prog_chain_m_resolution Cr pols lits
                        (Proof.pf (premiseAndFormulaList ps))
                    exact congrArg
                      (fun t => __eo_prog_chain_m_resolution Cr pols lits (Proof.pf t))
                      hMkPremises
                  have hProg' :
                      __eo_prog_chain_m_resolution Cr pols lits
                        (Proof.pf (premiseAndFormulaList ps)) ≠ Term.Stuck := by
                    rw [← hCmdProgEq]
                    exact hProg
                  have hCrNe : Cr ≠ Term.Stuck := by
                    intro hStuck
                    subst hStuck
                    simp [__eo_prog_chain_m_resolution] at hProg'
                  have hSetNe :
                      __eo_list_setof Term.or
                        (__chain_m_resolve (premiseAndFormulaList ps) pols lits) ≠ Term.Stuck := by
                    intro hSet
                    apply hProg'
                    simp [__eo_prog_chain_m_resolution, hSet,
                      __eo_requires, __eo_ite, __eo_eq, __from_clause,
                      native_ite, native_teq]
                  have hChainNe :
                      __chain_m_resolve (premiseAndFormulaList ps) pols lits ≠ Term.Stuck :=
                    list_setof_arg_ne_stuck hSetNe
                  have hReqNe :
                      __eo_requires
                        (__eo_ite
                          (__eo_eq
                            (__from_clause
                              (__eo_list_setof Term.or
                                (__chain_m_resolve (premiseAndFormulaList ps) pols lits))) Cr)
                          (Term.Boolean true)
                          (__eo_list_minclude Term.or Cr
                            (__eo_list_setof Term.or
                              (__chain_m_resolve (premiseAndFormulaList ps) pols lits))))
                        (Term.Boolean true) Cr ≠ Term.Stuck := by
                    simpa [__eo_prog_chain_m_resolution, hCrNe, hPolsNe, hLitsNe] using hProg'
                  have hCond :
                      __eo_ite
                        (__eo_eq
                          (__from_clause
                            (__eo_list_setof Term.or
                              (__chain_m_resolve (premiseAndFormulaList ps) pols lits))) Cr)
                        (Term.Boolean true)
                        (__eo_list_minclude Term.or Cr
                          (__eo_list_setof Term.or
                            (__chain_m_resolve (premiseAndFormulaList ps) pols lits))) =
                        Term.Boolean true :=
                    eq_true_of_requires_true_not_stuck hReqNe
                  have hProgEqCr :
                      __eo_prog_chain_m_resolution Cr pols lits
                        (Proof.pf (premiseAndFormulaList ps)) = Cr := by
                    simp [__eo_prog_chain_m_resolution, hCond,
                      __eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
                  have hCrType : __eo_typeof Cr = Term.Bool := by
                    rw [← hProgEqCr, ← hCmdProgEq]
                    exact hResultTy
                  have hCrBool : RuleProofs.eo_has_bool_type Cr :=
                    RuleProofs.eo_typeof_bool_implies_has_bool_type Cr hCrTrans hCrType
                  refine ⟨?_, ?_⟩
                  · intro hTrue
                    have hChainProps :=
                      chain_m_resolve_properties_of_nonstuck M hM ps pols lits
                        hPremisesBool hTrue.true_here hPols hLits hChainNe
                    rw [hCmdProgEq, hProgEqCr]
                    have hSetClause :
                        OrClause (__eo_list_setof Term.or
                          (__chain_m_resolve (premiseAndFormulaList ps) pols lits)) :=
                      setof_preserves_orClause hChainProps.1 hChainProps.2.1
                    have hSetBool :
                        RuleProofs.eo_has_bool_type
                          (__eo_list_setof Term.or
                            (__chain_m_resolve (premiseAndFormulaList ps) pols lits)) :=
                      setof_preserves_bool_type hChainProps.1 hChainProps.2.1
                    have hSetTrue :
                        eo_interprets M
                          (__eo_list_setof Term.or
                            (__chain_m_resolve (premiseAndFormulaList ps) pols lits)) true :=
                      setof_true M hM hChainProps.1 hChainProps.2.1 hChainProps.2.2
                    cases hEq :
                        __eo_eq
                          (__from_clause
                            (__eo_list_setof Term.or
                              (__chain_m_resolve (premiseAndFormulaList ps) pols lits))) Cr with
                    | Boolean b =>
                        cases b with
                        | false =>
                            have hIncl :
                                __eo_list_minclude Term.or Cr
                                  (__eo_list_setof Term.or
                                    (__chain_m_resolve (premiseAndFormulaList ps) pols lits)) =
                                  Term.Boolean true := by
                              simpa [__eo_ite, hEq, native_ite, native_teq] using hCond
                            have hCrClause : OrClause Cr :=
                              orClause_left_of_minclude_true hIncl
                            exact orClause_true_of_minclude_true M hM
                              hCrClause hCrBool hSetClause hSetBool hIncl hSetTrue
                        | true =>
                            have hCrEq : Cr =
                                __from_clause
                                  (__eo_list_setof Term.or
                                    (__chain_m_resolve (premiseAndFormulaList ps) pols lits)) :=
                              eq_of_eo_eq_true_local _ _ hEq
                            rw [hCrEq]
                            exact from_clause_true M hM hSetClause hSetBool hSetTrue
                    | _ =>
                        simp [__eo_ite, hEq, native_ite, native_teq] at hCond
                  · rw [hCmdProgEq, hProgEqCr]
                    exact hCrTrans
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)

theorem cmd_step_chain_resolution_properties_aux
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.chain_resolution args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.chain_resolution args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.chain_resolution args premises) := by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.chain_resolution args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons pols args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons lits args =>
          cases args with
          | nil =>
              have hPols : EoListAllHaveSmtTranslation pols := hCmdTrans.1
              have hLits : EoListAllHaveSmtTranslation lits := hCmdTrans.2.1
              have hPolsNe : pols ≠ Term.Stuck := by
                intro hStuck
                subst hStuck
                cases hPols
              have hLitsNe : lits ≠ Term.Stuck := by
                intro hStuck
                subst hStuck
                cases hLits
              let ps := premiseTermList s premises
              have hMkPremises :
                  __eo_mk_premise_list (Term.UOp UserOp.and) premises s =
                    premiseAndFormulaList ps := by
                simpa [ps] using mk_premise_list_and_eq_premiseAndFormulaList s premises
              have hCmdProgEq :
                  __eo_cmd_step_proven s CRule.chain_resolution
                    (CArgList.cons pols (CArgList.cons lits CArgList.nil)) premises =
                  __eo_prog_chain_resolution pols lits (Proof.pf (premiseAndFormulaList ps)) := by
                change
                  __eo_prog_chain_resolution pols lits
                    (Proof.pf (__eo_mk_premise_list (Term.UOp UserOp.and) premises s)) =
                  __eo_prog_chain_resolution pols lits (Proof.pf (premiseAndFormulaList ps))
                exact congrArg
                  (fun t => __eo_prog_chain_resolution pols lits (Proof.pf t))
                  hMkPremises
              have hProgEq :
                  __eo_prog_chain_resolution pols lits (Proof.pf (premiseAndFormulaList ps)) =
                  __from_clause (__chain_m_resolve (premiseAndFormulaList ps) pols lits) := by
                simp [__eo_prog_chain_resolution]
              have hProg' :
                  __eo_prog_chain_resolution pols lits (Proof.pf (premiseAndFormulaList ps)) ≠
                    Term.Stuck := by
                rw [← hCmdProgEq]
                exact hProg
              have hChainNe :
                  __chain_m_resolve (premiseAndFormulaList ps) pols lits ≠ Term.Stuck := by
                rw [hProgEq] at hProg'
                exact from_clause_arg_ne_stuck hProg'
              refine ⟨?_, ?_⟩
              · intro hTrue
                have hChainProps :=
                  chain_m_resolve_properties_of_nonstuck M hM ps pols lits
                    hPremisesBool hTrue.true_here hPols hLits hChainNe
                rw [hCmdProgEq]
                rw [hProgEq]
                exact from_clause_true M hM hChainProps.1 hChainProps.2.1 hChainProps.2.2
              · have hChainStruct :=
                    chain_m_resolve_structural_of_nonstuck hM ps pols lits
                      hPremisesBool hPols hLits hChainNe
                have hProgBool :
                    RuleProofs.eo_has_bool_type
                      (__eo_prog_chain_resolution pols lits (Proof.pf (premiseAndFormulaList ps))) := by
                  rw [hProgEq]
                  exact from_clause_preserves_bool_type hChainStruct.1 hChainStruct.2
                have hCmdEq :
                    __eo_cmd_step_proven s CRule.chain_resolution
                      (CArgList.cons pols (CArgList.cons lits CArgList.nil)) premises =
                    __eo_prog_chain_resolution pols lits (Proof.pf (premiseAndFormulaList ps)) := hCmdProgEq
                rw [hCmdEq]
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hProgBool
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)

private def resolutionComponent (lit clause : Term) : Term :=
  __eo_ite (__eo_eq lit clause) (Term.Boolean false) (__eo_list_erase Term.or clause lit)

private theorem resolution_component_lit_ne_stuck {lit clause : Term} :
    clause ≠ Term.Stuck ->
    resolutionComponent lit clause ≠ Term.Stuck ->
    lit ≠ Term.Stuck := by
  intro hClause hComp hLit
  subst hLit
  unfold resolutionComponent at hComp
  simp [__eo_eq, __eo_ite, native_ite, native_teq] at hComp

private theorem resolution_component_bool_type {lit clause : Term} :
    RuleProofs.eo_has_bool_type clause ->
    OrClause (resolutionComponent lit clause) ->
    RuleProofs.eo_has_bool_type (resolutionComponent lit clause) := by
  intro hClauseBool hCompClause
  have hCompNe : resolutionComponent lit clause ≠ Term.Stuck :=
    orClause_ne_stuck hCompClause
  have hClauseNe : clause ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type clause hClauseBool
  have hLitNe : lit ≠ Term.Stuck :=
    resolution_component_lit_ne_stuck hClauseNe hCompNe
  by_cases hEq : lit = clause
  · have hEqTerm : __eo_eq lit clause = Term.Boolean true :=
      eo_eq_eq_true_of_eq hEq hLitNe hClauseNe
    unfold resolutionComponent
    simp [hEqTerm, __eo_ite, native_ite, native_teq]
    exact RuleProofs.eo_has_bool_type_false
  · have hEqTerm : __eo_eq lit clause = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq hLitNe hClauseNe
    have hEraseNe : __eo_list_erase Term.or clause lit ≠ Term.Stuck := by
      unfold resolutionComponent at hCompNe
      simp [hEqTerm, __eo_ite, native_ite, native_teq] at hCompNe
      exact hCompNe
    have hClauseOr : OrClause clause :=
      list_erase_nonstuck_input_orClause hEraseNe
    unfold resolutionComponent
    simp [hEqTerm, __eo_ite, native_ite, native_teq]
    exact erase_preserves_bool_type hClauseOr hClauseBool hLitNe

private theorem resolution_component_true
    (M : SmtModel) (hM : model_wf M) {lit clause : Term} :
    RuleProofs.eo_has_bool_type clause ->
    eo_interprets M clause true ->
    (¬ RuleProofs.eo_has_bool_type lit ∨ eo_interprets M lit false) ->
    OrClause (resolutionComponent lit clause) ->
    eo_interprets M (resolutionComponent lit clause) true := by
  intro hClauseBool hClauseTrue hGood hCompClause
  have hCompNe : resolutionComponent lit clause ≠ Term.Stuck :=
    orClause_ne_stuck hCompClause
  have hClauseNe : clause ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type clause hClauseBool
  have hLitNe : lit ≠ Term.Stuck :=
    resolution_component_lit_ne_stuck hClauseNe hCompNe
  by_cases hEq : lit = clause
  · cases hGood with
    | inl hLitNotBool =>
        exfalso
        apply hLitNotBool
        simpa [hEq] using hClauseBool
    | inr hLitFalse =>
        have hClauseFalse : eo_interprets M clause false := by
          simpa [hEq] using hLitFalse
        exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hClauseTrue) hClauseFalse)
  · have hEqTerm : __eo_eq lit clause = Term.Boolean false :=
      eo_eq_eq_false_of_ne hEq hLitNe hClauseNe
    have hEraseNe : __eo_list_erase Term.or clause lit ≠ Term.Stuck := by
      unfold resolutionComponent at hCompNe
      simp [hEqTerm, __eo_ite, native_ite, native_teq] at hCompNe
      exact hCompNe
    have hClauseOr : OrClause clause :=
      list_erase_nonstuck_input_orClause hEraseNe
    unfold resolutionComponent
    simp [hEqTerm, __eo_ite, native_ite, native_teq]
    exact erase_true_of_good_lit M hM hClauseOr hClauseBool hClauseTrue hGood hLitNe

private theorem prog_resolution_true_eq (L C1 C2 : Term) :
    __eo_prog_resolution (Term.Boolean true) L (Proof.pf C1) (Proof.pf C2) =
      __from_clause (__eo_list_concat Term.or
        (resolutionComponent L (__to_clause C1))
        (resolutionComponent (Term.Apply Term.not L) (__to_clause C2))) := by
  by_cases hL : L = Term.Stuck
  · subst hL
    have hComp1 : resolutionComponent Term.Stuck (__to_clause C1) = Term.Stuck := by
      unfold resolutionComponent
      simp [__eo_eq, __eo_ite, native_ite, native_teq]
    simp [__eo_prog_resolution, hComp1, __eo_list_concat, __eo_requires, __eo_is_list,
      __from_clause, native_ite, native_teq
      ]
  · unfold __eo_prog_resolution
    simp [resolutionComponent, __eo_ite, native_ite, native_teq]

private theorem prog_resolution_false_eq (L C1 C2 : Term) :
    __eo_prog_resolution (Term.Boolean false) L (Proof.pf C1) (Proof.pf C2) =
      __from_clause (__eo_list_concat Term.or
        (resolutionComponent (Term.Apply Term.not L) (__to_clause C1))
        (resolutionComponent L (__to_clause C2))) := by
  by_cases hL : L = Term.Stuck
  · subst hL
    have hComp2 : resolutionComponent Term.Stuck (__to_clause C2) = Term.Stuck := by
      unfold resolutionComponent
      simp [__eo_eq, __eo_ite, native_ite, native_teq]
    simp [__eo_prog_resolution, hComp2, __eo_list_concat, __eo_requires, __eo_is_list,
      __eo_is_ok, __from_clause, native_ite, native_teq, native_not,
      SmtEval.native_not]
  · unfold __eo_prog_resolution
    simp [resolutionComponent, __eo_ite, native_ite, native_teq]

private theorem prog_resolution_pol_not_bool_stuck
    (pol L C1 C2 : Term) :
    pol ≠ Term.Boolean true ->
    pol ≠ Term.Boolean false ->
    __eo_prog_resolution pol L (Proof.pf C1) (Proof.pf C2) = Term.Stuck := by
  intro hTrue hFalse
  by_cases hPol : pol = Term.Stuck
  · subst hPol
    unfold __eo_prog_resolution
    simp
  · by_cases hL : L = Term.Stuck
    · subst hL
      unfold __eo_prog_resolution
      simp
    · unfold __eo_prog_resolution
      simp
      have hLit1 : __eo_ite pol L (Term.Apply Term.not L) = Term.Stuck :=
        ite_eq_stuck_of_ne_true_false pol L (Term.Apply Term.not L) hTrue hFalse
      have hLit2 : __eo_ite pol (Term.Apply Term.not L) L = Term.Stuck :=
        ite_eq_stuck_of_ne_true_false pol (Term.Apply Term.not L) L hTrue hFalse
      rw [hLit1, hLit2]
      simp [__eo_list_concat, __eo_is_list, __eo_requires,
        __from_clause, __eo_eq, __eo_ite, native_ite, native_teq
        ]

private theorem prog_resolution_true_properties
    (M : SmtModel) (hM : model_wf M)
    (L C1 C2 : Term) :
    RuleProofs.eo_has_bool_type C1 ->
    RuleProofs.eo_has_bool_type C2 ->
    __eo_prog_resolution (Term.Boolean true) L (Proof.pf C1) (Proof.pf C2) ≠ Term.Stuck ->
    StepRuleProperties M [C1, C2]
      (__eo_prog_resolution (Term.Boolean true) L (Proof.pf C1) (Proof.pf C2)) := by
  intro hC1Bool hC2Bool hProg
  let Cl1 := __to_clause C1
  let Cl2 := __to_clause C2
  let Comp1 := resolutionComponent L Cl1
  let Comp2 := resolutionComponent (Term.Apply Term.not L) Cl2
  have hCl1Bool : RuleProofs.eo_has_bool_type Cl1 := by
    simpa [Cl1] using to_clause_has_bool_type hC1Bool
  have hCl2Bool : RuleProofs.eo_has_bool_type Cl2 := by
    simpa [Cl2] using to_clause_has_bool_type hC2Bool
  have hProgRes :
      __from_clause (__eo_list_concat Term.or Comp1 Comp2) ≠ Term.Stuck := by
    rw [prog_resolution_true_eq L C1 C2] at hProg
    simpa [Cl1, Cl2, Comp1, Comp2] using hProg
  have hConcatNe : __eo_list_concat Term.or Comp1 Comp2 ≠ Term.Stuck :=
    from_clause_arg_ne_stuck hProgRes
  have hComp1Clause : OrClause Comp1 :=
    list_concat_nonstuck_left_orClause hConcatNe
  have hComp2Clause : OrClause Comp2 :=
    list_concat_nonstuck_right_orClause hConcatNe
  have hComp1Bool : RuleProofs.eo_has_bool_type Comp1 :=
    resolution_component_bool_type hCl1Bool hComp1Clause
  have hComp2Bool : RuleProofs.eo_has_bool_type Comp2 :=
    resolution_component_bool_type hCl2Bool hComp2Clause
  have hConcatClause : OrClause (__eo_list_concat Term.or Comp1 Comp2) :=
    concat_preserves_orClause hComp1Clause hComp2Clause
  have hConcatBool : RuleProofs.eo_has_bool_type (__eo_list_concat Term.or Comp1 Comp2) :=
    concat_preserves_bool_type hComp1Clause hComp2Clause hComp1Bool hComp2Bool
  have hFinalBool :
      RuleProofs.eo_has_bool_type
        (__from_clause (__eo_list_concat Term.or Comp1 Comp2)) :=
    from_clause_preserves_bool_type hConcatClause hConcatBool
  refine ⟨?_, ?_⟩
  · intro hTrue
    have hC1True : eo_interprets M C1 true := hTrue C1 (by simp)
    have hC2True : eo_interprets M C2 true := hTrue C2 (by simp)
    have hCl1True : eo_interprets M Cl1 true := by
      simpa [Cl1] using to_clause_interprets_true M hM hC1True
    have hCl2True : eo_interprets M Cl2 true := by
      simpa [Cl2] using to_clause_interprets_true M hM hC2True
    by_cases hLBool : RuleProofs.eo_has_bool_type L
    · rcases eo_interprets_bool_cases M hM L hLBool with hLTrue | hLFalse
      · have hNotLFalse : eo_interprets M (Term.Apply Term.not L) false :=
          eo_interprets_not_false_of_true M L hLTrue
        have hComp2True : eo_interprets M Comp2 true :=
          resolution_component_true M hM hCl2Bool hCl2True (Or.inr hNotLFalse) hComp2Clause
        have hConcatTrue : eo_interprets M (__eo_list_concat Term.or Comp1 Comp2) true :=
          concat_true_of_right_true M hM hComp1Clause hComp2Clause hComp1Bool hComp2Bool
            hComp2True
        have hFinalTrue :
            eo_interprets M (__from_clause (__eo_list_concat Term.or Comp1 Comp2)) true :=
          from_clause_true M hM hConcatClause hConcatBool hConcatTrue
        rw [prog_resolution_true_eq L C1 C2]
        simpa [Cl1, Cl2, Comp1, Comp2] using hFinalTrue
      · have hComp1True : eo_interprets M Comp1 true :=
          resolution_component_true M hM hCl1Bool hCl1True (Or.inr hLFalse) hComp1Clause
        have hConcatTrue : eo_interprets M (__eo_list_concat Term.or Comp1 Comp2) true :=
          concat_true_of_left_true M hM hComp1Clause hComp2Clause hComp1Bool hComp2Bool
            hComp1True
        have hFinalTrue :
            eo_interprets M (__from_clause (__eo_list_concat Term.or Comp1 Comp2)) true :=
          from_clause_true M hM hConcatClause hConcatBool hConcatTrue
        rw [prog_resolution_true_eq L C1 C2]
        simpa [Cl1, Cl2, Comp1, Comp2] using hFinalTrue
    · have hComp1True : eo_interprets M Comp1 true :=
        resolution_component_true M hM hCl1Bool hCl1True (Or.inl hLBool) hComp1Clause
      have hConcatTrue : eo_interprets M (__eo_list_concat Term.or Comp1 Comp2) true :=
        concat_true_of_left_true M hM hComp1Clause hComp2Clause hComp1Bool hComp2Bool
          hComp1True
      have hFinalTrue :
          eo_interprets M (__from_clause (__eo_list_concat Term.or Comp1 Comp2)) true :=
        from_clause_true M hM hConcatClause hConcatBool hConcatTrue
      rw [prog_resolution_true_eq L C1 C2]
      simpa [Cl1, Cl2, Comp1, Comp2] using hFinalTrue
  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
      (by
        rw [prog_resolution_true_eq L C1 C2]
        simpa [Cl1, Cl2, Comp1, Comp2] using hFinalBool)

private theorem prog_resolution_false_properties
    (M : SmtModel) (hM : model_wf M)
    (L C1 C2 : Term) :
    RuleProofs.eo_has_bool_type C1 ->
    RuleProofs.eo_has_bool_type C2 ->
    __eo_prog_resolution (Term.Boolean false) L (Proof.pf C1) (Proof.pf C2) ≠ Term.Stuck ->
    StepRuleProperties M [C1, C2]
      (__eo_prog_resolution (Term.Boolean false) L (Proof.pf C1) (Proof.pf C2)) := by
  intro hC1Bool hC2Bool hProg
  let Cl1 := __to_clause C1
  let Cl2 := __to_clause C2
  let Comp1 := resolutionComponent (Term.Apply Term.not L) Cl1
  let Comp2 := resolutionComponent L Cl2
  have hCl1Bool : RuleProofs.eo_has_bool_type Cl1 := by
    simpa [Cl1] using to_clause_has_bool_type hC1Bool
  have hCl2Bool : RuleProofs.eo_has_bool_type Cl2 := by
    simpa [Cl2] using to_clause_has_bool_type hC2Bool
  have hProgRes :
      __from_clause (__eo_list_concat Term.or Comp1 Comp2) ≠ Term.Stuck := by
    rw [prog_resolution_false_eq L C1 C2] at hProg
    simpa [Cl1, Cl2, Comp1, Comp2] using hProg
  have hConcatNe : __eo_list_concat Term.or Comp1 Comp2 ≠ Term.Stuck :=
    from_clause_arg_ne_stuck hProgRes
  have hComp1Clause : OrClause Comp1 :=
    list_concat_nonstuck_left_orClause hConcatNe
  have hComp2Clause : OrClause Comp2 :=
    list_concat_nonstuck_right_orClause hConcatNe
  have hComp1Bool : RuleProofs.eo_has_bool_type Comp1 :=
    resolution_component_bool_type hCl1Bool hComp1Clause
  have hComp2Bool : RuleProofs.eo_has_bool_type Comp2 :=
    resolution_component_bool_type hCl2Bool hComp2Clause
  have hConcatClause : OrClause (__eo_list_concat Term.or Comp1 Comp2) :=
    concat_preserves_orClause hComp1Clause hComp2Clause
  have hConcatBool : RuleProofs.eo_has_bool_type (__eo_list_concat Term.or Comp1 Comp2) :=
    concat_preserves_bool_type hComp1Clause hComp2Clause hComp1Bool hComp2Bool
  have hFinalBool :
      RuleProofs.eo_has_bool_type
        (__from_clause (__eo_list_concat Term.or Comp1 Comp2)) :=
    from_clause_preserves_bool_type hConcatClause hConcatBool
  refine ⟨?_, ?_⟩
  · intro hTrue
    have hC1True : eo_interprets M C1 true := hTrue C1 (by simp)
    have hC2True : eo_interprets M C2 true := hTrue C2 (by simp)
    have hCl1True : eo_interprets M Cl1 true := by
      simpa [Cl1] using to_clause_interprets_true M hM hC1True
    have hCl2True : eo_interprets M Cl2 true := by
      simpa [Cl2] using to_clause_interprets_true M hM hC2True
    by_cases hLBool : RuleProofs.eo_has_bool_type L
    · rcases eo_interprets_bool_cases M hM L hLBool with hLTrue | hLFalse
      · have hNotLFalse : eo_interprets M (Term.Apply Term.not L) false :=
          eo_interprets_not_false_of_true M L hLTrue
        have hComp1True : eo_interprets M Comp1 true :=
          resolution_component_true M hM hCl1Bool hCl1True (Or.inr hNotLFalse) hComp1Clause
        have hConcatTrue : eo_interprets M (__eo_list_concat Term.or Comp1 Comp2) true :=
          concat_true_of_left_true M hM hComp1Clause hComp2Clause hComp1Bool hComp2Bool
            hComp1True
        have hFinalTrue :
            eo_interprets M (__from_clause (__eo_list_concat Term.or Comp1 Comp2)) true :=
          from_clause_true M hM hConcatClause hConcatBool hConcatTrue
        rw [prog_resolution_false_eq L C1 C2]
        simpa [Cl1, Cl2, Comp1, Comp2] using hFinalTrue
      · have hComp2True : eo_interprets M Comp2 true :=
          resolution_component_true M hM hCl2Bool hCl2True (Or.inr hLFalse) hComp2Clause
        have hConcatTrue : eo_interprets M (__eo_list_concat Term.or Comp1 Comp2) true :=
          concat_true_of_right_true M hM hComp1Clause hComp2Clause hComp1Bool hComp2Bool
            hComp2True
        have hFinalTrue :
            eo_interprets M (__from_clause (__eo_list_concat Term.or Comp1 Comp2)) true :=
          from_clause_true M hM hConcatClause hConcatBool hConcatTrue
        rw [prog_resolution_false_eq L C1 C2]
        simpa [Cl1, Cl2, Comp1, Comp2] using hFinalTrue
    · have hComp2True : eo_interprets M Comp2 true :=
        resolution_component_true M hM hCl2Bool hCl2True (Or.inl hLBool) hComp2Clause
      have hConcatTrue : eo_interprets M (__eo_list_concat Term.or Comp1 Comp2) true :=
        concat_true_of_right_true M hM hComp1Clause hComp2Clause hComp1Bool hComp2Bool
          hComp2True
      have hFinalTrue :
          eo_interprets M (__from_clause (__eo_list_concat Term.or Comp1 Comp2)) true :=
        from_clause_true M hM hConcatClause hConcatBool hConcatTrue
      rw [prog_resolution_false_eq L C1 C2]
      simpa [Cl1, Cl2, Comp1, Comp2] using hFinalTrue
  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
      (by
        rw [prog_resolution_false_eq L C1 C2]
        simpa [Cl1, Cl2, Comp1, Comp2] using hFinalBool)

theorem cmd_step_resolution_properties_aux
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.resolution args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.resolution args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.resolution args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.resolution args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons pol args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons L args =>
          cases args with
          | nil =>
              cases premises with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons n1 premises =>
                  cases premises with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons n2 premises =>
                      cases premises with
                      | nil =>
                          let C1 := __eo_state_proven_nth s n1
                          let C2 := __eo_state_proven_nth s n2
                          have hC1Bool : RuleProofs.eo_has_bool_type C1 :=
                            hPremisesBool C1 (by simp [C1, premiseTermList])
                          have hC2Bool : RuleProofs.eo_has_bool_type C2 :=
                            hPremisesBool C2 (by simp [C2, premiseTermList])
                          change __eo_prog_resolution pol L
                            (Proof.pf (__eo_state_proven_nth s n1))
                            (Proof.pf (__eo_state_proven_nth s n2)) ≠ Term.Stuck at hProg
                          by_cases hPolTrue : pol = Term.Boolean true
                          · subst pol
                            change StepRuleProperties M [__eo_state_proven_nth s n1, __eo_state_proven_nth s n2]
                              (__eo_prog_resolution (Term.Boolean true) L
                                (Proof.pf (__eo_state_proven_nth s n1))
                                (Proof.pf (__eo_state_proven_nth s n2)))
                            simpa [C1, C2, premiseTermList] using
                              prog_resolution_true_properties M hM L C1 C2
                                hC1Bool hC2Bool hProg
                          · by_cases hPolFalse : pol = Term.Boolean false
                            · subst pol
                              change StepRuleProperties M [__eo_state_proven_nth s n1, __eo_state_proven_nth s n2]
                                (__eo_prog_resolution (Term.Boolean false) L
                                  (Proof.pf (__eo_state_proven_nth s n1))
                                  (Proof.pf (__eo_state_proven_nth s n2)))
                              simpa [C1, C2, premiseTermList] using
                                prog_resolution_false_properties M hM L C1 C2
                                  hC1Bool hC2Bool hProg
                            · exact False.elim
                                (hProg (prog_resolution_pol_not_bool_stuck
                                  pol L C1 C2 hPolTrue hPolFalse))
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)

theorem cmd_step_factoring_properties_aux
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.factoring args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.factoring args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.factoring args premises) := by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.factoring args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n premises =>
          cases premises with
          | nil =>
              let C := __eo_state_proven_nth s n
              have hCBool : RuleProofs.eo_has_bool_type C :=
                hPremisesBool C (by simp [C, premiseTermList])
              have hProgFactoring : __eo_prog_factoring (Proof.pf C) ≠ Term.Stuck := by
                change __eo_prog_factoring (Proof.pf (__eo_state_proven_nth s n)) ≠
                  Term.Stuck at hProg
                simpa [C] using hProg
              have hSetNe : __eo_list_setof Term.or C ≠ Term.Stuck :=
                from_clause_arg_ne_stuck hProgFactoring
              have hSetReqNe :
                  __eo_requires (__eo_is_list Term.or C) (Term.Boolean true)
                    (__eo_list_setof_rec C) ≠ Term.Stuck := by
                simpa [__eo_list_setof] using hSetNe
              have hList : __eo_is_list Term.or C = Term.Boolean true :=
                eq_true_of_requires_true_not_stuck hSetReqNe
              have hClause : OrClause C :=
                orClause_of_is_list_true hList
              have hSetClause : OrClause (__eo_list_setof Term.or C) :=
                setof_preserves_orClause hClause hCBool
              have hSetBool : RuleProofs.eo_has_bool_type (__eo_list_setof Term.or C) :=
                setof_preserves_bool_type hClause hCBool
              refine ⟨?_, ?_⟩
              · intro hTrue
                have hSetTrue : eo_interprets M (__eo_list_setof Term.or C) true :=
                  setof_true M hM hClause hCBool
                    (hTrue C (by simp [C, premiseTermList]))
                change eo_interprets M (__eo_prog_factoring (Proof.pf C)) true
                simpa [__eo_prog_factoring] using
                  from_clause_true M hM hSetClause hSetBool hSetTrue
              · change RuleProofs.eo_has_smt_translation (__eo_prog_factoring (Proof.pf C))
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (by
                    change RuleProofs.eo_has_bool_type (__from_clause (__eo_list_setof Term.or C))
                    exact from_clause_preserves_bool_type hSetClause hSetBool)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

theorem cmd_step_reordering_properties_aux
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.reordering args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.reordering args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.reordering args premises) := by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.reordering args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons C2 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n premises =>
              cases premises with
              | nil =>
                  let C1 := __eo_state_proven_nth s n
                  have hC2Trans : RuleProofs.eo_has_smt_translation C2 := hCmdTrans.1
                  have hC1Bool : RuleProofs.eo_has_bool_type C1 :=
                    hPremisesBool C1 (by simp [C1, premiseTermList])
                  have hCmdProgEq :
                      __eo_cmd_step_proven s CRule.reordering
                        (CArgList.cons C2 CArgList.nil) (CIndexList.cons n CIndexList.nil) =
                      __eo_prog_reordering C2 (Proof.pf C1) := by
                    change __eo_prog_reordering C2 (Proof.pf (__eo_state_proven_nth s n)) =
                      __eo_prog_reordering C2 (Proof.pf C1)
                    simp [C1]
                  have hC2Ne : C2 ≠ Term.Stuck :=
                    RuleProofs.term_ne_stuck_of_has_smt_translation C2 hC2Trans
                  have hProgReordering :
                      __eo_prog_reordering C2 (Proof.pf C1) ≠ Term.Stuck := by
                    rw [hCmdProgEq] at hProg
                    exact hProg
                  have hReqNe :
                      __eo_requires (__eo_list_minclude Term.or C2 C1) (Term.Boolean true) C2 ≠
                        Term.Stuck := by
                    simpa [__eo_prog_reordering, hC2Ne] using hProgReordering
                  have hIncl : __eo_list_minclude Term.or C2 C1 = Term.Boolean true :=
                    eq_true_of_requires_true_not_stuck hReqNe
                  have hProgEqC2 : __eo_prog_reordering C2 (Proof.pf C1) = C2 := by
                    simp [__eo_prog_reordering, hIncl, __eo_requires, native_ite,
                      native_teq, native_not, SmtEval.native_not]
                  have hC2Ty : __eo_typeof C2 = Term.Bool := by
                    rw [hCmdProgEq, hProgEqC2] at hResultTy
                    exact hResultTy
                  have hC2Bool : RuleProofs.eo_has_bool_type C2 :=
                    RuleProofs.eo_typeof_bool_implies_has_bool_type C2 hC2Trans hC2Ty
                  have hC2Clause : OrClause C2 :=
                    orClause_left_of_minclude_true hIncl
                  have hC1Clause : OrClause C1 :=
                    orClause_right_of_minclude_true hIncl
                  refine ⟨?_, ?_⟩
                  · intro hTrue
                    rw [hCmdProgEq, hProgEqC2]
                    exact orClause_true_of_minclude_true M hM
                      hC2Clause hC2Bool hC1Clause hC1Bool hIncl
                      (hTrue C1 (by simp [C1, premiseTermList]))
                  · rw [hCmdProgEq, hProgEqC2]
                    exact hC2Trans
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
