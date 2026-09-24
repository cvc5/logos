module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.RegexSupport
public import Cpc.Proofs.Translation.Apply
import all Cpc.Proofs.Translation.Apply
public import Cpc.Proofs.Translation.Inversions
import all Cpc.Proofs.Translation.Inversions

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace CongSupport

attribute [local simp] native_streq native_and native_ite

abbrev mkEq (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

/-- Public equality-term constructor used by rules that reuse congruence support. -/
abbrev eqTerm (x y : Term) : Term :=
  mkEq x y

theorem smtx_model_eval_eq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.eq x y) =
      __smtx_model_eval_eq (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_model_eval_ite_term_eq
    (M : SmtModel) (c t e : SmtTerm) :
    __smtx_model_eval M (SmtTerm.ite c t e) =
      __smtx_model_eval_ite
        (__smtx_model_eval M c) (__smtx_model_eval M t)
        (__smtx_model_eval M e) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_typeof_exists_term_eq
    (s : native_String) (T : SmtType) (body : SmtTerm) :
    __smtx_typeof (SmtTerm.exists s T body) =
      native_ite (native_Teq (__smtx_typeof body) SmtType.Bool)
        (__smtx_typeof_guard_wf T SmtType.Bool) SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only

theorem smtx_model_eval_qdiv_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.qdiv x y) =
      (let yr := __smtx_to_real_coerce (__smtx_model_eval M y)
       let xr := __smtx_to_real_coerce (__smtx_model_eval M x)
       __smtx_model_eval_ite
        (__smtx_model_eval_eq yr
          (SmtValue.Rational (native_mk_rational 0 1)))
        (__smtx_model_eval_apply M
          (native_model_lookup M native_qdiv_by_zero_id
            (SmtType.FunType SmtType.Real SmtType.Real))
          xr)
        (__smtx_model_eval_qdiv_total xr yr)) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_model_eval_qdiv_total_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.qdiv_total x y) =
      __smtx_model_eval_qdiv_total
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_model_eval_int_to_bv_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.int_to_bv x y) =
      __smtx_model_eval_int_to_bv
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_model_eval_map_diff_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.map_diff x y) =
      __smtx_model_eval_map_diff
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_typeof_seq_unit_term_eq (x : SmtTerm) :
    __smtx_typeof (SmtTerm.seq_unit x) =
      __smtx_typeof_guard_wf
        (SmtType.Seq (__smtx_typeof x)) (SmtType.Seq (__smtx_typeof x)) := by
  rw [__smtx_typeof.eq_def] <;> simp only

theorem smtx_typeof_set_singleton_term_eq (x : SmtTerm) :
    __smtx_typeof (SmtTerm.set_singleton x) =
      __smtx_typeof_guard_wf
        (SmtType.Set (__smtx_typeof x)) (SmtType.Set (__smtx_typeof x)) := by
  rw [__smtx_typeof.eq_def] <;> simp only

theorem smtx_model_eval_seq_unit_term_eq (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.seq_unit x) =
      SmtValue.Seq
        (SmtSeq.cons (__smtx_model_eval M x)
          (SmtSeq.empty (__smtx_typeof_value (__smtx_model_eval M x)))) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_model_eval_seq_nth_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.seq_nth x y) =
      __smtx_seq_nth M (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_typeof_set_empty_term_eq (T : SmtType) :
    __smtx_typeof (SmtTerm.set_empty T) =
      __smtx_typeof_guard_wf (SmtType.Set T) (SmtType.Set T) := by
  rw [__smtx_typeof.eq_def] <;> simp only

theorem smtx_model_eval_set_singleton_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.set_singleton x) =
      __smtx_model_eval_set_singleton (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_model_eval_set_union_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.set_union x y) =
      __smtx_model_eval_set_union
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_model_eval_set_inter_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.set_inter x y) =
      __smtx_model_eval_set_inter
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_model_eval_set_minus_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.set_minus x y) =
      __smtx_model_eval_set_minus
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_model_eval_set_subset_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.set_subset x y) =
      __smtx_model_eval_set_subset
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_typeof_ubv_to_int_term_eq (x : SmtTerm) :
    __smtx_typeof (SmtTerm.ubv_to_int x) =
      __smtx_typeof_bv_op_1_ret (__smtx_typeof x) SmtType.Int := by
  rw [__smtx_typeof.eq_def] <;> simp only

theorem smtx_model_eval_ubv_to_int_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.ubv_to_int x) =
      __smtx_model_eval_ubv_to_int (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_typeof_sbv_to_int_term_eq (x : SmtTerm) :
    __smtx_typeof (SmtTerm.sbv_to_int x) =
      __smtx_typeof_bv_op_1_ret (__smtx_typeof x) SmtType.Int := by
  rw [__smtx_typeof.eq_def] <;> simp only

theorem smtx_model_eval_sbv_to_int_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.sbv_to_int x) =
      __smtx_model_eval_sbv_to_int (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_model_eval_str_indexof_re_split_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_indexof_re_split x y z) =
      __smtx_model_eval_str_indexof_re_split
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

def eqPremise? : Term -> Option (Term × Term)
  | Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y => some (x, y)
  | _ => none

theorem eo_mk_apply_eq_of_ne_stuck (f x : Term) :
    f ≠ Term.Stuck ->
    x ≠ Term.Stuck ->
    __eo_mk_apply f x = Term.Apply f x := by
  intro hf hx
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

theorem eo_mk_apply_left_ne_stuck_of_ne_stuck (f x : Term) :
    __eo_mk_apply f x ≠ Term.Stuck ->
    f ≠ Term.Stuck := by
  intro h hF
  subst hF
  exact h (by simp [__eo_mk_apply])

theorem eo_mk_apply_right_ne_stuck_of_ne_stuck (f x : Term) :
    __eo_mk_apply f x ≠ Term.Stuck ->
    x ≠ Term.Stuck := by
  intro h hX
  subst hX
  cases f <;> simp [__eo_mk_apply] at h

theorem eo_requires_arg_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> x = y := by
  intro h
  unfold __eo_requires at h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [hxy, native_ite] at h

theorem eq_of_eo_eq_true (x y : Term) :
    __eo_eq x y = Term.Boolean true ->
    y = x := by
  intro h
  cases x <;> cases y <;> simp [__eo_eq, native_teq] at h ⊢
  all_goals exact h

private theorem eo_get_nil_rec_and_premiseAndFormulaList :
    ∀ ps : List Term,
      __eo_get_nil_rec (Term.UOp UserOp.and) (premiseAndFormulaList ps) =
        Term.Boolean true := by
  intro ps
  induction ps with
  | nil =>
      simp [premiseAndFormulaList, __eo_get_nil_rec, __eo_requires,
        __eo_is_list_nil, native_ite, native_teq, native_not,
        SmtEval.native_not]
  | cons p ps ih =>
      simp [premiseAndFormulaList, __eo_get_nil_rec, __eo_requires, ih,
        native_ite, native_teq, native_not, SmtEval.native_not]

private theorem eo_list_rev_rec_and_premiseAndFormulaList :
    ∀ xs ys : List Term,
      __eo_list_rev_rec (premiseAndFormulaList xs) (premiseAndFormulaList ys) =
        premiseAndFormulaList (xs.reverse ++ ys) := by
  intro xs ys
  induction xs generalizing ys with
  | nil =>
      cases ys <;> rfl
  | cons p xs ih =>
      cases ys with
      | nil =>
          simpa [premiseAndFormulaList, __eo_list_rev_rec, List.reverse_cons,
            List.append_assoc] using ih [p]
      | cons y ys =>
          simpa [premiseAndFormulaList, __eo_list_rev_rec, List.reverse_cons,
            List.append_assoc] using ih (p :: y :: ys)

theorem eo_list_rev_and_premiseAndFormulaList :
    ∀ ps : List Term,
      __eo_list_rev (Term.UOp UserOp.and) (premiseAndFormulaList ps) =
        premiseAndFormulaList ps.reverse := by
  intro ps
  unfold __eo_list_rev
  simp [__eo_requires, premiseAndFormulaList_is_and_list,
    eo_get_nil_rec_and_premiseAndFormulaList, native_ite, native_teq,
    native_not, SmtEval.native_not]
  simpa [premiseAndFormulaList] using
    eo_list_rev_rec_and_premiseAndFormulaList ps []

theorem all_interpreted_true_reverse
    (M : SmtModel) (ps : List Term) :
    AllInterpretedTrue M ps ->
    AllInterpretedTrue M ps.reverse := by
  intro h t ht
  exact h t (by simpa using List.mem_reverse.mp ht)

theorem all_have_bool_type_reverse
    (ps : List Term) :
    AllHaveBoolType ps ->
    AllHaveBoolType ps.reverse := by
  intro h t ht
  exact h t (by simpa using List.mem_reverse.mp ht)

inductive CongTrueSpine (M : SmtModel) : Term -> Term -> Prop where
  | refl (t : Term) : CongTrueSpine M t t
  | app {f g x y : Term} :
      CongTrueSpine M f g ->
      eo_interprets M (mkEq x y) true ->
      StableInAnyVarModel M (mkEq x y) ->
      CongTrueSpine M (Term.Apply f x) (Term.Apply g y)

inductive CongEvidenceSpine
    (M : SmtModel) (premises : List Term) : Term -> Term -> Prop where
  | refl (t : Term) : CongEvidenceSpine M premises t t
  | app {f g x y : Term} :
      CongEvidenceSpine M premises f g ->
      mkEq x y ∈ premises ->
      eo_interprets M (mkEq x y) true ->
      CongEvidenceSpine M premises (Term.Apply f x) (Term.Apply g y)

inductive CongStableSpine (M : SmtModel) : Term -> Term -> Prop where
  | refl (t : Term) : CongStableSpine M t t
  | app {f g x y : Term} :
      CongStableSpine M f g ->
      StableInAnyVarModel M (mkEq x y) ->
      CongStableSpine M (Term.Apply f x) (Term.Apply g y)

inductive CongTypeSpine : Term -> Term -> Prop where
  | refl (t : Term) : CongTypeSpine t t
  | app {f g x y : Term} :
      CongTypeSpine f g ->
      RuleProofs.eo_has_bool_type (mkEq x y) ->
      CongTypeSpine (Term.Apply f x) (Term.Apply g y)

def QuantifierBinderTypesWf : Term -> Prop
  | Term.Apply (Term.Apply Term.__eo_List_cons
      (Term.Var (Term.String _) T)) tail =>
      __smtx_type_wf (__eo_to_smt_type T) = true ∧
        QuantifierBinderTypesWf tail
  | _ => True

theorem congTypeSpine_of_congTrueSpine
    (M : SmtModel) :
    ∀ {t rhs : Term},
      CongTrueSpine M t rhs ->
      CongTypeSpine t rhs
  | _, _, CongTrueSpine.refl t => CongTypeSpine.refl t
  | _, _, CongTrueSpine.app hRec hArg _ =>
      CongTypeSpine.app
        (congTypeSpine_of_congTrueSpine M hRec)
        (RuleProofs.eo_has_bool_type_of_interprets_true M _ hArg)

theorem congTrueSpine_of_congEvidenceSpine
    (M : SmtModel) (premises : List Term)
    (hEvidence : RulePremiseEvidence M premises) :
    ∀ {t rhs : Term},
      CongEvidenceSpine M premises t rhs ->
      CongTrueSpine M t rhs := by
  intro t rhs hSpine
  induction hSpine with
  | refl t =>
      exact CongTrueSpine.refl t
  | app hRec hMem hArg ih =>
      exact
        CongTrueSpine.app ih hArg (by
          intro N hN hAgree
          exact hEvidence.true_in_var_model N hN hAgree _ hMem)

private theorem stableInAnyVarModel_rebase
    {M N : SmtModel} {P : Term} :
    model_agrees_on_globals M N ->
    StableInAnyVarModel M P ->
    StableInAnyVarModel N P := by
  intro hAgreeMN hStable K hK hAgreeNK
  exact hStable K hK (model_agrees_on_globals_trans hAgreeMN hAgreeNK)

theorem congTrueSpine_of_congStableSpine
    (M : SmtModel) (hM : model_wf M) :
    ∀ {t rhs : Term},
      CongStableSpine M t rhs ->
      CongTrueSpine M t rhs
  | _, _, CongStableSpine.refl t => CongTrueSpine.refl t
  | _, _, CongStableSpine.app hRec hArgStable =>
      CongTrueSpine.app
        (congTrueSpine_of_congStableSpine M hM hRec)
        (hArgStable M hM (model_agrees_on_globals_refl M))
        hArgStable

theorem congStableSpine_rebase
    {M N : SmtModel} :
    model_agrees_on_globals M N ->
    ∀ {t rhs : Term},
      CongStableSpine M t rhs ->
      CongStableSpine N t rhs
  | hAgreeMN, _, _, CongStableSpine.refl t => CongStableSpine.refl t
  | hAgreeMN, _, _, CongStableSpine.app hRec hArgStable =>
      CongStableSpine.app
        (congStableSpine_rebase hAgreeMN hRec)
        (stableInAnyVarModel_rebase hAgreeMN hArgStable)

private theorem congEvidenceSpine_mono
    (M : SmtModel) {premises premises' : List Term} :
    (∀ p, p ∈ premises -> p ∈ premises') ->
    ∀ {t rhs : Term},
      CongEvidenceSpine M premises t rhs ->
      CongEvidenceSpine M premises' t rhs
:=
by
  intro hSub t rhs hSpine
  induction hSpine with
  | refl t =>
      exact CongEvidenceSpine.refl t
  | app hRec hMem hArg ih =>
      exact CongEvidenceSpine.app ih (hSub _ hMem) hArg

def appSpineRev : Term -> Term × List Term
  | Term.Apply f x =>
      let spine := appSpineRev f
      (spine.1, x :: spine.2)
  | t => (t, [])

def mkSmtAppSpineRev (head : SmtTerm) : List SmtTerm -> SmtTerm
  | [] => head
  | x :: xs => SmtTerm.Apply (mkSmtAppSpineRev head xs) x

def EqTrueOrSame (M : SmtModel) (x y : Term) : Prop :=
  x = y ∨ eo_interprets M (mkEq x y) true

def EqTrueStableOrSame (M : SmtModel) (x y : Term) : Prop :=
  x = y ∨
    (eo_interprets M (mkEq x y) true ∧
      StableInAnyVarModel M (mkEq x y))

def EqBoolOrSame (x y : Term) : Prop :=
  x = y ∨ RuleProofs.eo_has_bool_type (mkEq x y)

inductive ListRel (R : Term -> Term -> Prop) :
    List Term -> List Term -> Prop where
  | nil : ListRel R [] []
  | cons {x y : Term} {xs ys : List Term} :
      R x y -> ListRel R xs ys -> ListRel R (x :: xs) (y :: ys)

private theorem forall₂_eq_true_or_same_refl
    (M : SmtModel) :
    ∀ xs : List Term, ListRel (EqTrueOrSame M) xs xs
  | [] => ListRel.nil
  | x :: xs =>
      ListRel.cons (by exact Or.inl rfl)
        (forall₂_eq_true_or_same_refl M xs)

private theorem forall₂_eq_bool_or_same_refl :
    ∀ xs : List Term, ListRel EqBoolOrSame xs xs
  | [] => ListRel.nil
  | x :: xs =>
      ListRel.cons (by exact Or.inl rfl)
        (forall₂_eq_bool_or_same_refl xs)

theorem congTrueSpine_appSpineRev
    (M : SmtModel) :
    ∀ {t rhs : Term},
      CongTrueSpine M t rhs ->
      (appSpineRev t).1 = (appSpineRev rhs).1 ∧
        ListRel (EqTrueOrSame M) (appSpineRev t).2 (appSpineRev rhs).2
  | _, _, CongTrueSpine.refl t => by
      exact ⟨rfl, forall₂_eq_true_or_same_refl M (appSpineRev t).2⟩
  | _, _, CongTrueSpine.app hRec hArg _ => by
      rcases congTrueSpine_appSpineRev M hRec with ⟨hHead, hArgs⟩
      exact ⟨hHead, ListRel.cons (by exact Or.inr hArg) hArgs⟩

theorem congTypeSpine_appSpineRev :
    ∀ {t rhs : Term},
      CongTypeSpine t rhs ->
      (appSpineRev t).1 = (appSpineRev rhs).1 ∧
        ListRel EqBoolOrSame (appSpineRev t).2 (appSpineRev rhs).2
  | _, _, CongTypeSpine.refl t => by
      exact ⟨rfl, forall₂_eq_bool_or_same_refl (appSpineRev t).2⟩
  | _, _, CongTypeSpine.app hRec hArg => by
      rcases congTypeSpine_appSpineRev hRec with ⟨hHead, hArgs⟩
      exact ⟨hHead, ListRel.cons (by exact Or.inr hArg) hArgs⟩

private theorem eo_to_smt_apply_generic_of_appSpineRev_var
    (s : native_String) (T t : Term)
    (x : Term)
    (hHead : (appSpineRev t).1 = Term.Var (Term.String s) T) :
    __eo_to_smt (Term.Apply t x) =
      SmtTerm.Apply (__eo_to_smt t) (__eo_to_smt x) := by
  cases t with
  | Apply f y =>
      dsimp [appSpineRev] at hHead
      cases f with
      | Apply f' y' =>
          dsimp [appSpineRev] at hHead
          cases f' with
          | Apply f'' y'' =>
              cases f'' with
              | UOp op => simp [appSpineRev] at hHead
              | _ => rfl
          | Var name U =>
              cases name with
              | String name =>
                  simp [appSpineRev] at hHead
                  rcases hHead with ⟨rfl, rfl⟩
                  rfl
              | _ =>
                  simp [appSpineRev] at hHead
          | _ =>
              simp [appSpineRev] at hHead
      | Var name U =>
          cases name with
          | String name =>
              simp [appSpineRev] at hHead
              rcases hHead with ⟨rfl, rfl⟩
              rfl
          | _ =>
              simp [appSpineRev] at hHead
      | _ =>
          simp [appSpineRev] at hHead
  | Var name U =>
      cases name with
      | String name =>
          simp [appSpineRev] at hHead
          rcases hHead with ⟨rfl, rfl⟩
          rfl
      | _ =>
          simp [appSpineRev] at hHead
  | _ =>
      simp [appSpineRev] at hHead

theorem eo_to_smt_appSpineRev_var
    (s : native_String) (T t : Term)
    (hHead : (appSpineRev t).1 = Term.Var (Term.String s) T) :
    __eo_to_smt t =
      mkSmtAppSpineRev (SmtTerm.Var s (__eo_to_smt_type T))
        ((appSpineRev t).2.map __eo_to_smt) := by
  cases t with
  | Apply f x =>
      dsimp [appSpineRev] at hHead ⊢
      have hF :
          (appSpineRev f).1 = Term.Var (Term.String s) T := hHead
      rw [eo_to_smt_apply_generic_of_appSpineRev_var s T f x hF]
      have ihF := eo_to_smt_appSpineRev_var s T f hF
      rw [ihF]
      rfl
  | Var name U =>
      cases name with
      | String name =>
          simp [appSpineRev] at hHead
          rcases hHead with ⟨rfl, rfl⟩
          rfl
      | _ =>
          simp [appSpineRev] at hHead
  | _ =>
      simp [appSpineRev] at hHead
termination_by t

private theorem eo_to_smt_apply_generic_of_appSpineRev_uconst
    (i : native_Nat) (T t x : Term)
    (hHead : (appSpineRev t).1 = Term.UConst i T) :
    __eo_to_smt (Term.Apply t x) =
      SmtTerm.Apply (__eo_to_smt t) (__eo_to_smt x) := by
  cases t with
  | Apply f y =>
      dsimp [appSpineRev] at hHead
      cases f with
      | Apply f' y' =>
          dsimp [appSpineRev] at hHead
          cases f' with
          | Apply f'' y'' =>
              cases f'' with
              | UOp op => simp [appSpineRev] at hHead
              | _ => rfl
          | UConst i' U =>
              simp [appSpineRev] at hHead
              rcases hHead with ⟨rfl, rfl⟩
              rfl
          | _ =>
              simp [appSpineRev] at hHead
      | UConst i' U =>
          simp [appSpineRev] at hHead
          rcases hHead with ⟨rfl, rfl⟩
          rfl
      | _ =>
          simp [appSpineRev] at hHead
  | UConst i' U =>
      simp [appSpineRev] at hHead
      rcases hHead with ⟨rfl, rfl⟩
      rfl
  | _ =>
      simp [appSpineRev] at hHead

theorem eo_to_smt_appSpineRev_uconst
    (i : native_Nat) (T t : Term)
    (hHead : (appSpineRev t).1 = Term.UConst i T) :
    __eo_to_smt t =
      mkSmtAppSpineRev
        (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
        ((appSpineRev t).2.map __eo_to_smt) := by
  cases t with
  | Apply f x =>
      dsimp [appSpineRev] at hHead ⊢
      have hF :
          (appSpineRev f).1 = Term.UConst i T := hHead
      rw [eo_to_smt_apply_generic_of_appSpineRev_uconst i T f x hF]
      have ihF := eo_to_smt_appSpineRev_uconst i T f hF
      rw [ihF]
      rfl
  | UConst i' U =>
      simp [appSpineRev] at hHead
      rcases hHead with ⟨rfl, rfl⟩
      rfl
  | _ =>
      simp [appSpineRev] at hHead
termination_by t

private theorem eo_to_smt_apply_generic_of_appSpineRev_dtcons
    (s : native_String) (d : DatatypeDecl) (i : native_Nat) (t x : Term)
    (hHead : (appSpineRev t).1 = Term.DtCons s d i) :
    __eo_to_smt (Term.Apply t x) =
      SmtTerm.Apply (__eo_to_smt t) (__eo_to_smt x) := by
  cases t with
  | Apply f y =>
      dsimp [appSpineRev] at hHead
      cases f with
      | Apply f' y' =>
          dsimp [appSpineRev] at hHead
          cases f' with
          | Apply f'' y'' =>
              cases f'' with
              | UOp op => simp [appSpineRev] at hHead
              | _ => rfl
          | DtCons s' d' i' =>
              simp [appSpineRev] at hHead
              rcases hHead with ⟨rfl, rfl, rfl⟩
              rfl
          | _ =>
              simp [appSpineRev] at hHead
      | DtCons s' d' i' =>
          simp [appSpineRev] at hHead
          rcases hHead with ⟨rfl, rfl, rfl⟩
          rfl
      | _ =>
          simp [appSpineRev] at hHead
  | DtCons s' d' i' =>
      simp [appSpineRev] at hHead
      rcases hHead with ⟨rfl, rfl, rfl⟩
      rfl
  | _ =>
      simp [appSpineRev] at hHead

theorem eo_to_smt_appSpineRev_dtcons
    (s : native_String) (d : DatatypeDecl) (i : native_Nat) (t : Term)
    (hHead : (appSpineRev t).1 = Term.DtCons s d i) :
    __eo_to_smt t =
      mkSmtAppSpineRev (__eo_to_smt (Term.DtCons s d i))
        ((appSpineRev t).2.map __eo_to_smt) := by
  cases t with
  | Apply f x =>
      dsimp [appSpineRev] at hHead ⊢
      have hF :
          (appSpineRev f).1 = Term.DtCons s d i := hHead
      rw [eo_to_smt_apply_generic_of_appSpineRev_dtcons s d i f x hF]
      have ihF := eo_to_smt_appSpineRev_dtcons s d i f hF
      rw [ihF]
      rfl
  | DtCons s' d' i' =>
      simp [appSpineRev] at hHead
      rcases hHead with ⟨rfl, rfl, rfl⟩
      rfl
  | _ =>
      simp [appSpineRev] at hHead
termination_by t

private theorem eo_to_smt_apply_generic_of_appSpineRev_dt_sel
    (s : native_String) (d : DatatypeDecl) (i j : native_Nat) (t x : Term)
    (hHead : (appSpineRev t).1 = Term.DtSel s d i j) :
    __eo_to_smt (Term.Apply t x) =
      SmtTerm.Apply (__eo_to_smt t) (__eo_to_smt x) := by
  cases t with
  | Apply f y =>
      dsimp [appSpineRev] at hHead
      cases f with
      | Apply f' y' =>
          dsimp [appSpineRev] at hHead
          cases f' with
          | Apply f'' y'' =>
              cases f'' with
              | UOp op => simp [appSpineRev] at hHead
              | _ => rfl
          | DtSel s' d' i' j' =>
              simp [appSpineRev] at hHead
              rcases hHead with ⟨rfl, rfl, rfl, rfl⟩
              rfl
          | _ =>
              simp [appSpineRev] at hHead
      | DtSel s' d' i' j' =>
          simp [appSpineRev] at hHead
          rcases hHead with ⟨rfl, rfl, rfl, rfl⟩
          rfl
      | _ =>
          simp [appSpineRev] at hHead
  | DtSel s' d' i' j' =>
      simp [appSpineRev] at hHead
      rcases hHead with ⟨rfl, rfl, rfl, rfl⟩
      rfl
  | _ =>
      simp [appSpineRev] at hHead

theorem eo_to_smt_appSpineRev_dt_sel
    (s : native_String) (d : DatatypeDecl) (i j : native_Nat) (t : Term)
    (hHead : (appSpineRev t).1 = Term.DtSel s d i j) :
    __eo_to_smt t =
      mkSmtAppSpineRev (__eo_to_smt (Term.DtSel s d i j))
        ((appSpineRev t).2.map __eo_to_smt) := by
  cases t with
  | Apply f x =>
      dsimp [appSpineRev] at hHead ⊢
      have hF :
          (appSpineRev f).1 = Term.DtSel s d i j := hHead
      rw [eo_to_smt_apply_generic_of_appSpineRev_dt_sel s d i j f x hF]
      have ihF := eo_to_smt_appSpineRev_dt_sel s d i j f hF
      rw [ihF]
      rfl
  | DtSel s' d' i' j' =>
      simp [appSpineRev] at hHead
      rcases hHead with ⟨rfl, rfl, rfl, rfl⟩
      rfl
  | _ =>
      simp [appSpineRev] at hHead
termination_by t

theorem eo_to_smt_dtcons_ne_dt_sel
    (s : native_String) (d : DatatypeDecl) (i : native_Nat) :
    ∀ s' d' i' j',
      __eo_to_smt (Term.DtCons s d i) ≠ SmtTerm.DtSel s' d' i' j' := by
  intro s' d' i' j'
  change
    native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
        (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i) ≠
      SmtTerm.DtSel s' d' i' j'
  cases __eo_to_smt_reserved_datatype_name s <;> simp [native_ite]

theorem eo_to_smt_dtcons_ne_dt_tester
    (s : native_String) (d : DatatypeDecl) (i : native_Nat) :
    ∀ s' d' i',
      __eo_to_smt (Term.DtCons s d i) ≠ SmtTerm.DtTester s' d' i' := by
  intro s' d' i'
  change
    native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
        (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i) ≠
      SmtTerm.DtTester s' d' i'
  cases __eo_to_smt_reserved_datatype_name s <;> simp [native_ite]

private theorem congTrueSpine_uop_eq
    (M : SmtModel) (op : UserOp) (rhs : Term) :
    CongTrueSpine M (Term.UOp op) rhs ->
    rhs = Term.UOp op := by
  intro h
  cases h with
  | refl _ => rfl

private theorem congTypeSpine_uop_eq
    (op : UserOp) (rhs : Term) :
    CongTypeSpine (Term.UOp op) rhs ->
    rhs = Term.UOp op := by
  intro h
  cases h with
  | refl _ => rfl

private theorem congTrueSpine_uop1_eq
    (M : SmtModel) (op : UserOp1) (idx rhs : Term) :
    CongTrueSpine M (Term.UOp1 op idx) rhs ->
    rhs = Term.UOp1 op idx := by
  intro h
  cases h with
  | refl _ => rfl

private theorem congTypeSpine_uop1_eq
    (op : UserOp1) (idx rhs : Term) :
    CongTypeSpine (Term.UOp1 op idx) rhs ->
    rhs = Term.UOp1 op idx := by
  intro h
  cases h with
  | refl _ => rfl

private theorem congTrueSpine_uop2_eq
    (M : SmtModel) (op : UserOp2) (idx₁ idx₂ rhs : Term) :
    CongTrueSpine M (Term.UOp2 op idx₁ idx₂) rhs ->
    rhs = Term.UOp2 op idx₁ idx₂ := by
  intro h
  cases h with
  | refl _ => rfl

private theorem congTypeSpine_uop2_eq
    (op : UserOp2) (idx₁ idx₂ rhs : Term) :
    CongTypeSpine (Term.UOp2 op idx₁ idx₂) rhs ->
    rhs = Term.UOp2 op idx₁ idx₂ := by
  intro h
  cases h with
  | refl _ => rfl

private theorem congTrueSpine_dt_sel_eq
    (M : SmtModel) (s : native_String) (d : DatatypeDecl)
    (i j : native_Nat) (rhs : Term) :
    CongTrueSpine M (Term.DtSel s d i j) rhs ->
    rhs = Term.DtSel s d i j := by
  intro h
  cases h with
  | refl _ => rfl

private theorem congTypeSpine_dt_sel_eq
    (s : native_String) (d : DatatypeDecl) (i j : native_Nat) (rhs : Term) :
    CongTypeSpine (Term.DtSel s d i j) rhs ->
    rhs = Term.DtSel s d i j := by
  intro h
  cases h with
  | refl _ => rfl

theorem congTrueSpine_unary_uop_inv
    (M : SmtModel) (op : UserOp) (x rhs : Term) :
    CongTrueSpine M (Term.Apply (Term.UOp op) x) rhs ->
    ∃ y,
      rhs = Term.Apply (Term.UOp op) y ∧
        EqTrueOrSame M x y := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg _ =>
      have hg : _ := congTrueSpine_uop_eq M op _ hHead
      subst hg
      exact ⟨_, rfl, Or.inr hArg⟩

theorem congTypeSpine_unary_uop_inv
    (op : UserOp) (x rhs : Term) :
    CongTypeSpine (Term.Apply (Term.UOp op) x) rhs ->
    ∃ y,
      rhs = Term.Apply (Term.UOp op) y ∧
        EqBoolOrSame x y := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg =>
      have hg : _ := congTypeSpine_uop_eq op _ hHead
      subst hg
      exact ⟨_, rfl, Or.inr hArg⟩

theorem congTrueSpine_indexed_unary_uop_inv
    (M : SmtModel) (op : UserOp1) (idx x rhs : Term) :
    CongTrueSpine M (Term.Apply (Term.UOp1 op idx) x) rhs ->
    ∃ y,
      rhs = Term.Apply (Term.UOp1 op idx) y ∧
        EqTrueOrSame M x y := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg _ =>
      have hg : _ := congTrueSpine_uop1_eq M op idx _ hHead
      subst hg
      exact ⟨_, rfl, Or.inr hArg⟩

theorem congTypeSpine_indexed_unary_uop_inv
    (op : UserOp1) (idx x rhs : Term) :
    CongTypeSpine (Term.Apply (Term.UOp1 op idx) x) rhs ->
    ∃ y,
      rhs = Term.Apply (Term.UOp1 op idx) y ∧
        EqBoolOrSame x y := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg =>
      have hg : _ := congTypeSpine_uop1_eq op idx _ hHead
      subst hg
      exact ⟨_, rfl, Or.inr hArg⟩

theorem congTrueSpine_indexed2_unary_uop_inv
    (M : SmtModel) (op : UserOp2) (idx₁ idx₂ x rhs : Term) :
    CongTrueSpine M (Term.Apply (Term.UOp2 op idx₁ idx₂) x) rhs ->
    ∃ y,
      rhs = Term.Apply (Term.UOp2 op idx₁ idx₂) y ∧
        EqTrueOrSame M x y := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg _ =>
      have hg : _ := congTrueSpine_uop2_eq M op idx₁ idx₂ _ hHead
      subst hg
      exact ⟨_, rfl, Or.inr hArg⟩

theorem congTypeSpine_indexed2_unary_uop_inv
    (op : UserOp2) (idx₁ idx₂ x rhs : Term) :
    CongTypeSpine (Term.Apply (Term.UOp2 op idx₁ idx₂) x) rhs ->
    ∃ y,
      rhs = Term.Apply (Term.UOp2 op idx₁ idx₂) y ∧
        EqBoolOrSame x y := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg =>
      have hg : _ := congTypeSpine_uop2_eq op idx₁ idx₂ _ hHead
      subst hg
      exact ⟨_, rfl, Or.inr hArg⟩

theorem congTrueSpine_indexed_binary_uop1_inv
    (M : SmtModel) (op : UserOp1) (idx x₁ x₂ rhs : Term) :
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp1 op idx) x₁) x₂) rhs ->
    ∃ y₁ y₂,
      rhs = Term.Apply (Term.Apply (Term.UOp1 op idx) y₁) y₂ ∧
        EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x₁, x₂, rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₂ _ =>
      rcases congTrueSpine_indexed_unary_uop_inv M op idx x₁ _ hHead with
        ⟨y₁, hHeadRhs, hArg₁⟩
      subst hHeadRhs
      exact ⟨y₁, _, rfl, hArg₁, Or.inr hArg₂⟩

theorem congTypeSpine_indexed_binary_uop1_inv
    (op : UserOp1) (idx x₁ x₂ rhs : Term) :
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp1 op idx) x₁) x₂) rhs ->
    ∃ y₁ y₂,
      rhs = Term.Apply (Term.Apply (Term.UOp1 op idx) y₁) y₂ ∧
        EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x₁, x₂, rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₂ =>
      rcases congTypeSpine_indexed_unary_uop_inv op idx x₁ _ hHead with
        ⟨y₁, hHeadRhs, hArg₁⟩
      subst hHeadRhs
      exact ⟨y₁, _, rfl, hArg₁, Or.inr hArg₂⟩

theorem congTrueSpine_dt_sel_inv
    (M : SmtModel) (s : native_String) (d : DatatypeDecl)
    (i j : native_Nat) (x rhs : Term) :
    CongTrueSpine M (Term.Apply (Term.DtSel s d i j) x) rhs ->
    ∃ y,
      rhs = Term.Apply (Term.DtSel s d i j) y ∧
        EqTrueOrSame M x y := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg _ =>
      have hg : _ := congTrueSpine_dt_sel_eq M s d i j _ hHead
      subst hg
      exact ⟨_, rfl, Or.inr hArg⟩

theorem congTypeSpine_dt_sel_inv
    (s : native_String) (d : DatatypeDecl) (i j : native_Nat) (x rhs : Term) :
    CongTypeSpine (Term.Apply (Term.DtSel s d i j) x) rhs ->
    ∃ y,
      rhs = Term.Apply (Term.DtSel s d i j) y ∧
        EqBoolOrSame x y := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg =>
      have hg : _ := congTypeSpine_dt_sel_eq s d i j _ hHead
      subst hg
      exact ⟨_, rfl, Or.inr hArg⟩

theorem congTrueSpine_binary_uop_inv
    (M : SmtModel) (op : UserOp) (x₁ x₂ rhs : Term) :
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp op) x₁) x₂) rhs ->
    ∃ y₁ y₂,
      rhs = Term.Apply (Term.Apply (Term.UOp op) y₁) y₂ ∧
        EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x₁, x₂, rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₂ _ =>
      rcases congTrueSpine_unary_uop_inv M op x₁ _ hHead with
        ⟨y₁, hHeadEq, hArg₁⟩
      subst hHeadEq
      exact ⟨y₁, _, rfl, hArg₁, Or.inr hArg₂⟩

theorem congTypeSpine_binary_uop_inv
    (op : UserOp) (x₁ x₂ rhs : Term) :
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp op) x₁) x₂) rhs ->
    ∃ y₁ y₂,
      rhs = Term.Apply (Term.Apply (Term.UOp op) y₁) y₂ ∧
        EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x₁, x₂, rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₂ =>
      rcases congTypeSpine_unary_uop_inv op x₁ _ hHead with
        ⟨y₁, hHeadEq, hArg₁⟩
      subst hHeadEq
      exact ⟨y₁, _, rfl, hArg₁, Or.inr hArg₂⟩

theorem congTrueSpine_ternary_uop_inv
    (M : SmtModel) (op : UserOp) (x₁ x₂ x₃ rhs : Term) :
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x₁) x₂) x₃)
      rhs ->
    ∃ y₁ y₂ y₃,
      rhs =
        Term.Apply (Term.Apply (Term.Apply (Term.UOp op) y₁) y₂) y₃ ∧
        EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ ∧
          EqTrueOrSame M x₃ y₃ := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₃ _ =>
      rcases congTrueSpine_binary_uop_inv M op x₁ x₂ _ hHead with
        ⟨y₁, y₂, hHeadEq, hArg₁, hArg₂⟩
      subst hHeadEq
      exact ⟨y₁, y₂, _, rfl, hArg₁, hArg₂, Or.inr hArg₃⟩

theorem congTypeSpine_ternary_uop_inv
    (op : UserOp) (x₁ x₂ x₃ rhs : Term) :
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x₁) x₂) x₃)
      rhs ->
    ∃ y₁ y₂ y₃,
      rhs =
        Term.Apply (Term.Apply (Term.Apply (Term.UOp op) y₁) y₂) y₃ ∧
        EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ ∧
          EqBoolOrSame x₃ y₃ := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₃ =>
      rcases congTypeSpine_binary_uop_inv op x₁ x₂ _ hHead with
        ⟨y₁, y₂, hHeadEq, hArg₁, hArg₂⟩
      subst hHeadEq
      exact ⟨y₁, y₂, _, rfl, hArg₁, hArg₂, Or.inr hArg₃⟩

theorem eqTrueOrSame_of_stable {M : SmtModel} {x y : Term}
    (h : EqTrueStableOrSame M x y) : EqTrueOrSame M x y := by
  rcases h with hEq | ⟨hTrue, _⟩
  · exact Or.inl hEq
  · exact Or.inr hTrue

theorem congTrueSpine_uop_eq_stable
    (M : SmtModel) (op : UserOp) (g : Term) :
    CongTrueSpine M (Term.UOp op) g -> g = Term.UOp op := by
  intro h
  cases h with
  | refl _ => rfl

theorem congTrueSpine_unary_uop_inv_stable
    (M : SmtModel) (op : UserOp) (x rhs : Term) :
    CongTrueSpine M (Term.Apply (Term.UOp op) x) rhs ->
    ∃ y,
      rhs = Term.Apply (Term.UOp op) y ∧
        EqTrueStableOrSame M x y := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg hStable =>
      have hg : _ := congTrueSpine_uop_eq_stable M op _ hHead
      subst hg
      exact ⟨_, rfl, Or.inr ⟨hArg, hStable⟩⟩

theorem congTrueSpine_binary_uop_inv_stable
    (M : SmtModel) (op : UserOp) (x₁ x₂ rhs : Term) :
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp op) x₁) x₂) rhs ->
    ∃ y₁ y₂,
      rhs = Term.Apply (Term.Apply (Term.UOp op) y₁) y₂ ∧
        EqTrueStableOrSame M x₁ y₁ ∧ EqTrueStableOrSame M x₂ y₂ := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x₁, x₂, rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg hStable =>
      rcases congTrueSpine_unary_uop_inv_stable M op x₁ _ hHead with
        ⟨y₁, hHeadEq, hArg₁⟩
      subst hHeadEq
      exact ⟨y₁, _, rfl, hArg₁, Or.inr ⟨hArg, hStable⟩⟩

theorem congTrueSpine_ternary_uop_inv_stable
    (M : SmtModel) (op : UserOp) (x₁ x₂ x₃ rhs : Term) :
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x₁) x₂) x₃)
      rhs ->
    ∃ y₁ y₂ y₃,
      rhs =
        Term.Apply (Term.Apply (Term.Apply (Term.UOp op) y₁) y₂) y₃ ∧
        EqTrueStableOrSame M x₁ y₁ ∧ EqTrueStableOrSame M x₂ y₂ ∧
          EqTrueStableOrSame M x₃ y₃ := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg hStable =>
      rcases congTrueSpine_binary_uop_inv_stable M op x₁ x₂ _ hHead with
        ⟨y₁, y₂, hHeadEq, hArg₁, hArg₂⟩
      subst hHeadEq
      exact ⟨y₁, y₂, _, rfl, hArg₁, hArg₂, Or.inr ⟨hArg, hStable⟩⟩

theorem congTrueSpine_quaternary_uop_inv_stable
    (M : SmtModel) (op : UserOp) (x₁ x₂ x₃ x₄ rhs : Term) :
    CongTrueSpine M
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x₁) x₂) x₃) x₄)
      rhs ->
    ∃ y₁ y₂ y₃ y₄,
      rhs =
        Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) y₁) y₂) y₃)
          y₄ ∧
        EqTrueStableOrSame M x₁ y₁ ∧ EqTrueStableOrSame M x₂ y₂ ∧
          EqTrueStableOrSame M x₃ y₃ ∧ EqTrueStableOrSame M x₄ y₄ := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl,
        Or.inl rfl⟩
  | app hHead hArg hStable =>
      rcases congTrueSpine_ternary_uop_inv_stable M op x₁ x₂ x₃ _ hHead with
        ⟨y₁, y₂, y₃, hHeadEq, hArg₁, hArg₂, hArg₃⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, _, rfl, hArg₁, hArg₂, hArg₃,
        Or.inr ⟨hArg, hStable⟩⟩

theorem congTrueSpine_quaternary_uop_inv
    (M : SmtModel) (op : UserOp) (x₁ x₂ x₃ x₄ rhs : Term) :
    CongTrueSpine M
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x₁) x₂) x₃) x₄)
      rhs ->
    ∃ y₁ y₂ y₃ y₄,
      rhs =
        Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) y₁) y₂) y₃)
          y₄ ∧
        EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ ∧
          EqTrueOrSame M x₃ y₃ ∧ EqTrueOrSame M x₄ y₄ := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl,
        Or.inl rfl⟩
  | app hHead hArg₄ _ =>
      rcases congTrueSpine_ternary_uop_inv M op x₁ x₂ x₃ _ hHead with
        ⟨y₁, y₂, y₃, hHeadEq, hArg₁, hArg₂, hArg₃⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, _, rfl, hArg₁, hArg₂, hArg₃, Or.inr hArg₄⟩

theorem congTypeSpine_quaternary_uop_inv
    (op : UserOp) (x₁ x₂ x₃ x₄ rhs : Term) :
    CongTypeSpine
      (Term.Apply
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x₁) x₂) x₃) x₄)
      rhs ->
    ∃ y₁ y₂ y₃ y₄,
      rhs =
        Term.Apply
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) y₁) y₂) y₃)
          y₄ ∧
        EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ ∧
          EqBoolOrSame x₃ y₃ ∧ EqBoolOrSame x₄ y₄ := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, x₄, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl,
        Or.inl rfl⟩
  | app hHead hArg₄ =>
      rcases congTypeSpine_ternary_uop_inv op x₁ x₂ x₃ _ hHead with
        ⟨y₁, y₂, y₃, hHeadEq, hArg₁, hArg₂, hArg₃⟩
      subst hHeadEq
      exact ⟨y₁, y₂, y₃, _, rfl, hArg₁, hArg₂, hArg₃, Or.inr hArg₄⟩

theorem smt_value_rel_of_eq_true_or_same
    (M : SmtModel) (x y : Term) :
    EqTrueOrSame M x y ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) := by
  intro h
  rcases h with hEq | hTrue
  · subst hEq
    exact RuleProofs.smt_value_rel_refl _
  · exact RuleProofs.eo_interprets_eq_rel M x y hTrue

theorem smt_type_eq_of_eq_true_or_same
    (M : SmtModel) (x y : Term) :
    EqTrueOrSame M x y ->
    __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) := by
  intro h
  rcases h with hEq | hTrue
  · subst hEq
    rfl
  · exact (RuleProofs.eo_eq_operands_same_smt_type M x y hTrue).1

theorem smt_type_eq_of_eq_bool_or_same
    (x y : Term) :
    EqBoolOrSame x y ->
    __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) := by
  intro h
  rcases h with hEq | hBool
  · subst hEq
    rfl
  · exact (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type x y hBool).1

private theorem smt_model_eval_eq_of_rel_at_non_reglan_type
    (M : SmtModel) (hM : model_wf M) (x y : SmtTerm)
    (T : SmtType) :
    __smtx_typeof x = T ->
    __smtx_typeof y = T ->
    T ≠ SmtType.None ->
    T ≠ SmtType.RegLan ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M x) (__smtx_model_eval M y) ->
    __smtx_model_eval M x = __smtx_model_eval M y := by
  intro hxTy hyTy hTNN hTReg hRel
  have hxNN : term_has_non_none_type x := by
    unfold term_has_non_none_type
    rw [hxTy]
    exact hTNN
  have hyNN : term_has_non_none_type y := by
    unfold term_has_non_none_type
    rw [hyTy]
    exact hTNN
  have hxValTy :
      __smtx_typeof_value (__smtx_model_eval M x) = T := by
    simpa [hxTy] using smt_model_eval_preserves_type_of_non_none M hM x hxNN
  have hyValTy :
      __smtx_typeof_value (__smtx_model_eval M y) = T := by
    simpa [hyTy] using smt_model_eval_preserves_type_of_non_none M hM y hyNN
  exact RuleProofs.smt_value_rel_eq_of_type_ne_reglan
    hxValTy hyValTy hTReg hRel

theorem eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type
    (M : SmtModel) (hM : model_wf M) (x y : Term)
    (T : SmtType) :
    __smtx_typeof (__eo_to_smt x) = T ->
    __smtx_typeof (__eo_to_smt y) = T ->
    T ≠ SmtType.None ->
    T ≠ SmtType.RegLan ->
    EqTrueOrSame M x y ->
    __smtx_model_eval M (__eo_to_smt x) =
      __smtx_model_eval M (__eo_to_smt y) := by
  intro hxTy hyTy hTNN hTReg hRel
  exact smt_model_eval_eq_of_rel_at_non_reglan_type M hM
    (__eo_to_smt x) (__eo_to_smt y) T hxTy hyTy hTNN hTReg
    (smt_value_rel_of_eq_true_or_same M x y hRel)

theorem smt_typeof_not_arg_bool_of_non_none (x : SmtTerm) :
    __smtx_typeof (SmtTerm.not x) ≠ SmtType.None ->
    __smtx_typeof x = SmtType.Bool := by
  intro hNN
  rw [typeof_not_eq] at hNN
  cases h : __smtx_typeof x <;>
    simp [native_ite, native_Teq, h] at hNN ⊢

theorem smt_typeof_and_args_bool_of_non_none (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.and x y) ≠ SmtType.None ->
    __smtx_typeof x = SmtType.Bool ∧ __smtx_typeof y = SmtType.Bool := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.and x y) := by
    unfold term_has_non_none_type
    exact hNN
  exact bool_binop_args_bool_of_non_none (op := SmtTerm.and)
    (typeof_and_eq x y) hTerm

theorem smt_typeof_or_args_bool_of_non_none (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.or x y) ≠ SmtType.None ->
    __smtx_typeof x = SmtType.Bool ∧ __smtx_typeof y = SmtType.Bool := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.or x y) := by
    unfold term_has_non_none_type
    exact hNN
  exact bool_binop_args_bool_of_non_none (op := SmtTerm.or)
    (typeof_or_eq x y) hTerm

theorem smt_typeof_imp_args_bool_of_non_none (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.imp x y) ≠ SmtType.None ->
    __smtx_typeof x = SmtType.Bool ∧ __smtx_typeof y = SmtType.Bool := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.imp x y) := by
    unfold term_has_non_none_type
    exact hNN
  exact bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
    (typeof_imp_eq x y) hTerm

theorem smt_typeof_xor_args_bool_of_non_none (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.xor x y) ≠ SmtType.None ->
    __smtx_typeof x = SmtType.Bool ∧ __smtx_typeof y = SmtType.Bool := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.xor x y) := by
    unfold term_has_non_none_type
    exact hNN
  exact bool_binop_args_bool_of_non_none (op := SmtTerm.xor)
    (typeof_xor_eq x y) hTerm

private theorem mk_cong_rhs_step_eq_of_eo_eq_true
    (f x y z tail : Term) :
    __eo_eq x y = Term.Boolean true ->
    __mk_cong_rhs (Term.Apply f x)
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (mkEq y z)) tail) =
      __eo_mk_apply (__mk_cong_rhs f tail) z := by
  intro hEq
  simp [__mk_cong_rhs, __eo_ite, hEq,
    native_teq, native_ite]

theorem mk_cong_rhs_congEvidenceSpine_of_list
    (M : SmtModel) :
    ∀ (ps : List Term) (t : Term),
      AllInterpretedTrue M ps ->
      __mk_cong_rhs t (premiseAndFormulaList ps) ≠ Term.Stuck ->
      CongEvidenceSpine M ps t (__mk_cong_rhs t (premiseAndFormulaList ps)) := by
  intro ps
  induction ps with
  | nil =>
      intro t _ hProg
      cases t <;>
        simp [premiseAndFormulaList, __mk_cong_rhs, __eo_l_1___mk_cong_rhs] at hProg ⊢
      all_goals exact CongEvidenceSpine.refl _
  | cons p ps ih =>
      intro t hTrue hProg
      cases p with
      | Apply pf tail =>
          cases pf with
          | Apply pg lhs =>
              cases pg with
              | UOp op =>
                  cases op
                  case eq =>
                    cases t with
                    | Apply f x =>
                        have hHeadTrue :
                            eo_interprets M (mkEq lhs tail) true := by
                          simpa [premiseAndFormulaList, mkEq] using
                            hTrue (mkEq lhs tail) (by simp [mkEq])
                        have hRestTrue : AllInterpretedTrue M ps := by
                          intro q hq
                          exact hTrue q (by simp [hq])
                        have hCond :
                            __eo_eq x lhs = Term.Boolean true := by
                          cases hEq : __eo_eq x lhs <;>
                            simp [premiseAndFormulaList, __mk_cong_rhs,
                              __eo_l_1___mk_cong_rhs, __eo_ite, hEq,
                              native_teq, native_ite] at hProg
                          case Boolean b =>
                            cases b with
                            | false =>
                                simp  at hProg
                            | true =>
                                rfl
                        have hStepEq :=
                          mk_cong_rhs_step_eq_of_eo_eq_true f x lhs tail
                            (premiseAndFormulaList ps) hCond
                        have hMkApplyNN :
                            __eo_mk_apply
                                (__mk_cong_rhs f (premiseAndFormulaList ps)) tail ≠
                              Term.Stuck := by
                          rw [← hStepEq]
                          exact hProg
                        have hRecNN :
                            __mk_cong_rhs f (premiseAndFormulaList ps) ≠
                              Term.Stuck :=
                          eo_mk_apply_left_ne_stuck_of_ne_stuck
                            (__mk_cong_rhs f (premiseAndFormulaList ps)) tail
                            hMkApplyNN
                        have hTailNN : tail ≠ Term.Stuck :=
                          eo_mk_apply_right_ne_stuck_of_ne_stuck
                            (__mk_cong_rhs f (premiseAndFormulaList ps)) tail
                            hMkApplyNN
                        have hRec :=
                          ih f hRestTrue hRecNN
                        have hRecFull :
                            CongEvidenceSpine M
                              ((mkEq lhs tail) :: ps)
                              f (__mk_cong_rhs f (premiseAndFormulaList ps)) :=
                          congEvidenceSpine_mono M
                            (by intro q hq; simp [hq])
                            hRec
                        have hLhs : lhs = x :=
                          eq_of_eo_eq_true x lhs hCond
                        subst lhs
                        change CongEvidenceSpine M
                          ((mkEq x tail) :: ps)
                          (Term.Apply f x)
                          (__mk_cong_rhs (Term.Apply f x)
                            (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                              (mkEq x tail)) (premiseAndFormulaList ps)))
                        rw [hStepEq]
                        rw [eo_mk_apply_eq_of_ne_stuck
                          (__mk_cong_rhs f (premiseAndFormulaList ps)) tail
                          hRecNN hTailNN]
                        exact CongEvidenceSpine.app hRecFull
                          (by simp [mkEq]) hHeadTrue
                    | _ =>
                        exact False.elim (hProg (by
                          simp [premiseAndFormulaList, __mk_cong_rhs,
                            __eo_l_1___mk_cong_rhs]))
                  all_goals
                    exact False.elim (hProg (by
                      cases t <;>
                        simp [premiseAndFormulaList, __mk_cong_rhs,
                          __eo_l_1___mk_cong_rhs]))
              | _ =>
                  exact False.elim (hProg (by
                    cases t <;>
                      simp [premiseAndFormulaList, __mk_cong_rhs,
                        __eo_l_1___mk_cong_rhs]))
          | _ =>
              exact False.elim (hProg (by
                cases t <;>
                  simp [premiseAndFormulaList, __mk_cong_rhs,
                    __eo_l_1___mk_cong_rhs]))
      | _ =>
          exact False.elim (hProg (by
            cases t <;>
              simp [premiseAndFormulaList, __mk_cong_rhs,
                __eo_l_1___mk_cong_rhs]))

theorem mk_cong_rhs_congTypeSpine_of_list :
    ∀ (ps : List Term) (t : Term),
      AllHaveBoolType ps ->
      __mk_cong_rhs t (premiseAndFormulaList ps) ≠ Term.Stuck ->
      CongTypeSpine t (__mk_cong_rhs t (premiseAndFormulaList ps)) := by
  intro ps
  induction ps with
  | nil =>
      intro t _ hProg
      cases t <;>
        simp [premiseAndFormulaList, __mk_cong_rhs, __eo_l_1___mk_cong_rhs] at hProg ⊢
      all_goals exact CongTypeSpine.refl _
  | cons p ps ih =>
      intro t hBool hProg
      cases p with
      | Apply pf tail =>
          cases pf with
          | Apply pg lhs =>
              cases pg with
              | UOp op =>
                  cases op
                  case eq =>
                    cases t with
                    | Apply f x =>
                        have hHeadBool :
                            RuleProofs.eo_has_bool_type (mkEq lhs tail) := by
                          simpa [premiseAndFormulaList, mkEq] using
                            hBool (mkEq lhs tail) (by simp [mkEq])
                        have hRestBool : AllHaveBoolType ps := by
                          intro q hq
                          exact hBool q (by simp [hq])
                        have hCond :
                            __eo_eq x lhs = Term.Boolean true := by
                          cases hEq : __eo_eq x lhs <;>
                            simp [premiseAndFormulaList, __mk_cong_rhs,
                              __eo_l_1___mk_cong_rhs, __eo_ite, hEq,
                              native_teq, native_ite] at hProg
                          case Boolean b =>
                            cases b with
                            | false =>
                                simp  at hProg
                            | true =>
                                rfl
                        have hStepEq :=
                          mk_cong_rhs_step_eq_of_eo_eq_true f x lhs tail
                            (premiseAndFormulaList ps) hCond
                        have hMkApplyNN :
                            __eo_mk_apply
                                (__mk_cong_rhs f (premiseAndFormulaList ps)) tail ≠
                              Term.Stuck := by
                          rw [← hStepEq]
                          exact hProg
                        have hRecNN :
                            __mk_cong_rhs f (premiseAndFormulaList ps) ≠
                              Term.Stuck :=
                          eo_mk_apply_left_ne_stuck_of_ne_stuck
                            (__mk_cong_rhs f (premiseAndFormulaList ps)) tail
                            hMkApplyNN
                        have hTailNN : tail ≠ Term.Stuck :=
                          eo_mk_apply_right_ne_stuck_of_ne_stuck
                            (__mk_cong_rhs f (premiseAndFormulaList ps)) tail
                            hMkApplyNN
                        have hRec :=
                          ih f hRestBool hRecNN
                        have hLhs : lhs = x :=
                          eq_of_eo_eq_true x lhs hCond
                        subst lhs
                        change CongTypeSpine (Term.Apply f x)
                          (__mk_cong_rhs (Term.Apply f x)
                            (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                              (mkEq x tail)) (premiseAndFormulaList ps)))
                        rw [hStepEq]
                        rw [eo_mk_apply_eq_of_ne_stuck
                          (__mk_cong_rhs f (premiseAndFormulaList ps)) tail
                          hRecNN hTailNN]
                        exact CongTypeSpine.app hRec hHeadBool
                    | _ =>
                        exact False.elim (hProg (by
                          simp [premiseAndFormulaList, __mk_cong_rhs,
                            __eo_l_1___mk_cong_rhs]))
                  all_goals
                    exact False.elim (hProg (by
                      cases t <;>
                        simp [premiseAndFormulaList, __mk_cong_rhs,
                          __eo_l_1___mk_cong_rhs]))
              | _ =>
                  exact False.elim (hProg (by
                    cases t <;>
                      simp [premiseAndFormulaList, __mk_cong_rhs,
                        __eo_l_1___mk_cong_rhs]))
          | _ =>
              exact False.elim (hProg (by
                cases t <;>
                  simp [premiseAndFormulaList, __mk_cong_rhs,
                    __eo_l_1___mk_cong_rhs]))
      | _ =>
          exact False.elim (hProg (by
            cases t <;>
              simp [premiseAndFormulaList, __mk_cong_rhs,
                __eo_l_1___mk_cong_rhs]))

theorem eo_prog_cong_pf_eq_of_ne_stuck (t E : Term) :
    t ≠ Term.Stuck ->
    __eo_prog_cong t (Proof.pf E) =
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t)
        (__mk_cong_rhs t (__eo_list_rev (Term.UOp UserOp.and) E)) := by
  intro ht
  cases t <;> simp [__eo_prog_cong] at ht ⊢

theorem mk_nary_cong_rhs_step_eq_of_eo_eq_true
    (f s₁ t lhs s₂ tail : Term) :
    __eo_eq s₁ lhs = Term.Boolean true ->
    __mk_nary_cong_rhs (Term.Apply (Term.Apply f s₁) t)
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (mkEq lhs s₂)) tail) =
      __eo_mk_apply (Term.Apply f s₂) (__mk_nary_cong_rhs t tail) := by
  intro hEq
  simp [__mk_nary_cong_rhs, __eo_ite,
    hEq, native_teq, native_ite]

theorem eo_prog_nary_cong_pf_eq_of_ne_stuck (t E : Term) :
    t ≠ Term.Stuck ->
    __eo_prog_nary_cong t (Proof.pf E) =
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t)
        (__mk_nary_cong_rhs t E) := by
  intro ht
  cases t <;> simp [__eo_prog_nary_cong] at ht ⊢

private theorem eo_typeof_eq_bool_operands_eq (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    A = B := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  · by_cases hB : B = Term.Stuck
    · subst B
      simp [__eo_typeof_eq] at h
    · simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
        native_not] at h
      exact h.symm

private theorem mkEq_typeof_bool_operands_typeof_eq (x y : Term)
    (h : __eo_typeof (mkEq x y) = Term.Bool) :
  __eo_typeof x = __eo_typeof y := by
  change __eo_typeof_eq (__eo_typeof x) (__eo_typeof y) = Term.Bool at h
  exact eo_typeof_eq_bool_operands_eq (__eo_typeof x) (__eo_typeof y) h

private theorem eo_typeof_eq_of_has_bool_type_eq (x y : Term) :
    RuleProofs.eo_has_bool_type (mkEq x y) ->
    __eo_typeof x = __eo_typeof y := by
  intro hBool
  have hTrans :
      RuleProofs.eo_has_smt_translation (mkEq x y) :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type (mkEq x y) hBool
  have hMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation (mkEq x y)
      hTrans
  have hEoBool : __eo_typeof (mkEq x y) = Term.Bool := by
    exact TranslationProofs.eo_to_smt_type_eq_bool (hMatch.symm.trans hBool)
  exact mkEq_typeof_bool_operands_typeof_eq x y hEoBool

theorem eo_type_eq_of_eq_bool_or_same
    (x y : Term) :
    EqBoolOrSame x y ->
    __eo_typeof x = __eo_typeof y := by
  intro h
  rcases h with hEq | hBool
  · subst hEq
    rfl
  · exact eo_typeof_eq_of_has_bool_type_eq x y hBool

theorem eo_type_eq_of_eq_true_or_same
    (M : SmtModel) (x y : Term) :
    EqTrueOrSame M x y ->
    __eo_typeof x = __eo_typeof y := by
  intro h
  rcases h with hEq | hTrue
  · subst hEq
    rfl
  · exact eo_typeof_eq_of_has_bool_type_eq x y
      (RuleProofs.eo_has_bool_type_of_interprets_true M (mkEq x y) hTrue)

theorem congTrueSpine_not_eq_true
    (M : SmtModel) (hM : model_wf M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.not) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.not) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp UserOp.not) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_unary_uop_inv M UserOp.not x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp UserOp.not) x)
        (Term.Apply (Term.UOp UserOp.not) y) hEqBool
    have hxNotNN :
        __smtx_typeof (SmtTerm.not (__eo_to_smt x)) ≠ SmtType.None :=
      hTypes.2
    have hyNotNN :
        __smtx_typeof (SmtTerm.not (__eo_to_smt y)) ≠ SmtType.None := by
      rw [hTypes.1] at hTypes
      exact hTypes.2
    have hxBool :
        __smtx_typeof (__eo_to_smt x) = SmtType.Bool :=
      smt_typeof_not_arg_bool_of_non_none (__eo_to_smt x) hxNotNN
    have hyBool :
        __smtx_typeof (__eo_to_smt y) = SmtType.Bool :=
      smt_typeof_not_arg_bool_of_non_none (__eo_to_smt y) hyNotNN
    have hEvalXY :
        __smtx_model_eval M (__eo_to_smt x) =
          __smtx_model_eval M (__eo_to_smt y) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x y
        SmtType.Bool hxBool hyBool (by simp) (by simp) hArg
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change __smtx_model_eval_eq
      (__smtx_model_eval M (SmtTerm.not (__eo_to_smt x)))
      (__smtx_model_eval M (SmtTerm.not (__eo_to_smt y))) =
        SmtValue.Boolean true
    rw [__smtx_model_eval.eq_7, __smtx_model_eval.eq_7]
    rw [hEvalXY]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl _)

theorem congTypeSpine_not_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp UserOp.not) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.not) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.not) x) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_unary_uop_inv UserOp.not x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  have hxNotTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.not) x)) =
        SmtType.Bool := by
    change __smtx_typeof (SmtTerm.not (__eo_to_smt x)) = SmtType.Bool
    have hxBool :
        __smtx_typeof (__eo_to_smt x) = SmtType.Bool :=
      smt_typeof_not_arg_bool_of_non_none (__eo_to_smt x) (by
        change __smtx_typeof (SmtTerm.not (__eo_to_smt x)) ≠ SmtType.None
        exact hTrans)
    rw [typeof_not_eq, hxBool]
    simp [native_ite, native_Teq]
  have hxyType :
      __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) :=
    smt_type_eq_of_eq_bool_or_same x y hArg
  have hyNotTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.not) y)) =
        SmtType.Bool := by
    change __smtx_typeof (SmtTerm.not (__eo_to_smt y)) = SmtType.Bool
    have hxBool :
        __smtx_typeof (__eo_to_smt x) = SmtType.Bool :=
      smt_typeof_not_arg_bool_of_non_none (__eo_to_smt x) (by
        change __smtx_typeof (SmtTerm.not (__eo_to_smt x)) ≠ SmtType.None
        exact hTrans)
    have hyBool :
        __smtx_typeof (__eo_to_smt y) = SmtType.Bool := by
      rw [← hxyType]
      exact hxBool
    rw [typeof_not_eq, hyBool]
    simp [native_ite, native_Teq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UOp UserOp.not) x)
    (Term.Apply (Term.UOp UserOp.not) y)
    (by rw [hxNotTy, hyNotTy])
    (by rw [hxNotTy]; simp)

theorem smtx_model_eval_eq_false_of_not_smt_value_rel
    (a b : SmtValue) :
    ¬ RuleProofs.smt_value_rel a b ->
    __smtx_model_eval_eq a b = SmtValue.Boolean false := by
  intro h
  cases hEq : __smtx_model_eval_eq a b with
  | Boolean q =>
      cases q with
      | false => rfl
      | true =>
          exact False.elim (h hEq)
  | NotValue =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | Numeral _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | Rational _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | Binary _ _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | Map _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | Fun _ _ _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | Set _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | Seq _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | Char _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | UValue _ _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | RegLan _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | DtCons _ _ _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq
  | Apply _ _ =>
      cases a <;> cases b <;> simp [__smtx_model_eval_eq] at hEq

theorem smtx_model_eval_eq_boolean
    (a b : SmtValue) :
    ∃ q, __smtx_model_eval_eq a b = SmtValue.Boolean q := by
  cases a <;> cases b <;> simp [__smtx_model_eval_eq]

theorem cong_smtx_typeof_eq_non_none
    {T U : SmtType}
    (h : __smtx_typeof_eq T U ≠ SmtType.None) :
    T = U ∧ T ≠ SmtType.None := by
  by_cases hNone : T = SmtType.None
  · subst hNone
    exfalso
    exact h (by
      simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq])
  · by_cases hEq : T = U
    · exact ⟨hEq, hNone⟩
    · exfalso
      exact h (by
        simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq,
          hNone, hEq])

theorem smt_eval_seq_of_smt_type_seq
    (M : SmtModel) (hM : model_wf M) (t : SmtTerm)
    (T : SmtType) :
    __smtx_typeof t = SmtType.Seq T ->
    ∃ s, __smtx_model_eval M t = SmtValue.Seq s := by
  intro hTy
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.Seq T := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t hNN
  exact seq_value_canonical hValTy

theorem smt_eval_reglan_of_smt_type_reglan
    (M : SmtModel) (hM : model_wf M) (t : SmtTerm) :
    __smtx_typeof t = SmtType.RegLan ->
    ∃ r, __smtx_model_eval M t = SmtValue.RegLan r := by
  intro hTy
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.RegLan := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t hNN
  exact reglan_value_canonical hValTy

theorem smt_eval_int_of_smt_type_int
    (M : SmtModel) (hM : model_wf M) (t : SmtTerm) :
    __smtx_typeof t = SmtType.Int ->
    ∃ n, __smtx_model_eval M t = SmtValue.Numeral n := by
  intro hTy
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.Int := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t hNN
  exact int_value_canonical hValTy

private theorem native_re_mk_union_self (r : SmtRegLan) :
    native_re_mk_union r r = r := by
  cases r <;> simp [native_re_mk_union, native_re_union]

private theorem native_re_mk_inter_self (r : SmtRegLan) :
    native_re_mk_inter r r = r := by
  cases r <;> simp [native_re_mk_inter, native_re_inter]

abbrev native_list_in_re := RuleProofs.nativeListInRe
def native_str_in_re (str : native_String) (r : SmtRegLan) : native_Bool :=
  native_string_valid str && native_list_in_re str r

theorem native_string_valid_cons_parts
    {c : native_Char} {cs : List native_Char}
    (h : native_string_valid (c :: cs) = true) :
    native_char_valid c = true ∧ native_string_valid cs = true := by
  simpa [native_string_valid] using h

theorem native_string_valid_cons
    {c : native_Char} {cs : List native_Char}
    (hc : native_char_valid c = true)
    (hcs : native_string_valid cs = true) :
    native_string_valid (c :: cs) = true := by
  simp [native_string_valid, hc]
  simpa [native_string_valid] using hcs

theorem native_string_valid_append_left
    (xs ys : List native_Char) :
    native_string_valid (xs ++ ys) = true ->
      native_string_valid xs = true := by
  intro h
  simp [native_string_valid] at h ⊢
  intro x hx
  exact h.1 x hx

theorem native_string_valid_append_right
    (xs ys : List native_Char) :
    native_string_valid (xs ++ ys) = true ->
      native_string_valid ys = true := by
  intro h
  simp [native_string_valid] at h ⊢
  intro x hx
  exact h.2 x hx

theorem native_string_valid_drop
    (xs : List native_Char) (n : Nat) :
    native_string_valid xs = true ->
      native_string_valid (xs.drop n) = true := by
  intro h
  simp [native_string_valid] at h ⊢
  intro x hx
  exact h x (List.mem_of_mem_drop hx)

private theorem native_list_in_re_empty :
    (xs : List native_Char) -> native_list_in_re xs SmtRegLan.empty = false
  | xs => RuleProofs.nativeListInRe_empty xs

private theorem native_re_mk_union_eq_union_of_ne
    (r s : SmtRegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ s ->
    native_re_mk_union r s = SmtRegLan.union r s := by
  intro hr hs hrs
  cases r <;> cases s <;>
    simp [native_re_mk_union, native_re_union] at hr hs ⊢
  all_goals
    try exact False.elim (hrs rfl)
    try
      intro h
      subst h
      exact False.elim (hrs rfl)
    try
      intro h1 h2
      subst h1
      subst h2
      exact False.elim (hrs rfl)

private theorem native_re_mk_inter_eq_inter_of_ne
    (r s : SmtRegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ s ->
    native_re_mk_inter r s = SmtRegLan.inter r s := by
  intro hr hs hrs
  cases r <;> cases s <;>
    simp [native_re_mk_inter, native_re_inter] at hr hs ⊢
  all_goals
    try exact False.elim (hrs rfl)
    try
      intro h
      subst h
      exact False.elim (hrs rfl)
    try
      intro h1 h2
      subst h1
      subst h2
      exact False.elim (hrs rfl)

private theorem native_re_nullable_mk_union (r s : SmtRegLan) :
    native_re_nullable (native_re_mk_union r s) =
      (native_re_nullable r || native_re_nullable s) :=
  RuleProofs.native_re_nullable_mk_union r s

private theorem native_list_in_re_mk_union :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      native_list_in_re xs (native_re_mk_union r s) =
        (native_list_in_re xs r || native_list_in_re xs s)
  | xs, r, s => RuleProofs.nativeListInRe_mk_union xs r s

private theorem native_re_nullable_mk_concat (r s : SmtRegLan) :
    native_re_nullable (native_re_mk_concat r s) =
      (native_re_nullable r && native_re_nullable s) :=
  RuleProofs.native_re_nullable_mk_concat r s

private theorem native_list_in_re_mk_concat_empty_right
    (xs : List native_Char) (r : SmtRegLan) :
    native_list_in_re xs (native_re_mk_concat r SmtRegLan.empty) = false :=
  RuleProofs.nativeListInRe_mk_concat_empty_right xs r

private theorem native_list_in_re_mk_concat_epsilon_right
    (xs : List native_Char) (r : SmtRegLan) :
    native_list_in_re xs (native_re_mk_concat r SmtRegLan.epsilon) =
      native_list_in_re xs r :=
  RuleProofs.nativeListInRe_mk_concat_epsilon_right xs r

private theorem native_re_mk_concat_eq_concat_of_ne
    (r s : SmtRegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ SmtRegLan.epsilon ->
    s ≠ SmtRegLan.epsilon ->
    native_re_mk_concat r s = SmtRegLan.concat r s := by
  intro hrEmpty hsEmpty hrEps hsEps
  cases r <;> cases s <;>
    simp [native_re_mk_concat, native_re_concat] at hrEmpty hsEmpty hrEps hsEps ⊢

private theorem native_list_in_re_deriv_mk_concat
    (xs : List native_Char) (c : native_Char) (r s : SmtRegLan) :
    native_list_in_re xs (native_re_deriv c (native_re_mk_concat r s)) =
      native_list_in_re xs
        (native_re_mk_union
          (native_re_mk_concat (native_re_deriv c r) s)
          (if native_re_nullable r then native_re_deriv c s else SmtRegLan.empty)) :=
  RuleProofs.nativeListInRe_deriv_mk_concat xs c r s

private def native_list_in_re_concat :
    List native_Char -> SmtRegLan -> SmtRegLan -> native_Bool
  | [], r, s => native_re_nullable r && native_re_nullable s
  | c :: cs, r, s =>
      (native_re_nullable r && native_list_in_re (c :: cs) s) ||
        native_list_in_re_concat cs (native_re_deriv c r) s

private theorem native_list_in_re_concat_eq_shared :
    ∀ xs r s,
      native_list_in_re_concat xs r s =
        RuleProofs.nativeListInReConcat xs r s
  | [], _, _ => rfl
  | _ :: cs, r, s => by
      simp only [native_list_in_re_concat, RuleProofs.nativeListInReConcat]
      rw [native_list_in_re_concat_eq_shared cs (native_re_deriv _ r) s]

private theorem native_list_in_re_mk_concat :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      native_list_in_re xs (native_re_mk_concat r s) =
        native_list_in_re_concat xs r s
  | xs, r, s => by
      rw [native_list_in_re_concat_eq_shared]
      exact RuleProofs.nativeListInRe_mk_concat xs r s

private theorem native_list_in_re_concat_true_iff_exists_append :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      native_list_in_re_concat xs r s = true ↔
        ∃ xs₁ xs₂ : List native_Char,
          xs₁ ++ xs₂ = xs ∧
            native_list_in_re xs₁ r = true ∧
            native_list_in_re xs₂ s = true
  | xs, r, s => by
      rw [native_list_in_re_concat_eq_shared]
      exact RuleProofs.nativeListInReConcat_true_iff_exists_append xs r s

theorem native_list_in_re_mk_concat_true_iff_exists_append
    (xs : List native_Char) (r s : SmtRegLan) :
    native_list_in_re xs (native_re_mk_concat r s) = true ↔
      ∃ xs₁ xs₂ : List native_Char,
        xs₁ ++ xs₂ = xs ∧
          native_list_in_re xs₁ r = true ∧
          native_list_in_re xs₂ s = true := by
  rw [native_list_in_re_mk_concat xs r s]
  exact native_list_in_re_concat_true_iff_exists_append xs r s

private theorem native_list_in_re_mk_concat_congr_valid
    (xs : List native_Char) (r r' s s' : SmtRegLan)
    (hxs : native_string_valid xs = true)
    (hr :
      ∀ ys : List native_Char,
        native_string_valid ys = true ->
          native_list_in_re ys r = native_list_in_re ys r')
    (hs :
      ∀ ys : List native_Char,
        native_string_valid ys = true ->
          native_list_in_re ys s = native_list_in_re ys s') :
    native_list_in_re xs (native_re_mk_concat r s) =
      native_list_in_re xs (native_re_mk_concat r' s') := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rcases
      (native_list_in_re_mk_concat_true_iff_exists_append xs r s).1 h
        with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
    have hAppendValid : native_string_valid (xs₁ ++ xs₂) = true := by
      rw [hAppend]
      exact hxs
    have hValid₁ := native_string_valid_append_left xs₁ xs₂ hAppendValid
    have hValid₂ := native_string_valid_append_right xs₁ xs₂ hAppendValid
    apply (native_list_in_re_mk_concat_true_iff_exists_append xs r' s').2
    refine ⟨xs₁, xs₂, hAppend, ?_, ?_⟩
    · rwa [← hr xs₁ hValid₁]
    · rwa [← hs xs₂ hValid₂]
  · intro h
    rcases
      (native_list_in_re_mk_concat_true_iff_exists_append xs r' s').1 h
        with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
    have hAppendValid : native_string_valid (xs₁ ++ xs₂) = true := by
      rw [hAppend]
      exact hxs
    have hValid₁ := native_string_valid_append_left xs₁ xs₂ hAppendValid
    have hValid₂ := native_string_valid_append_right xs₁ xs₂ hAppendValid
    apply (native_list_in_re_mk_concat_true_iff_exists_append xs r s).2
    refine ⟨xs₁, xs₂, hAppend, ?_, ?_⟩
    · rwa [hr xs₁ hValid₁]
    · rwa [hs xs₂ hValid₂]

private theorem native_re_nullable_mk_inter (r s : SmtRegLan) :
    native_re_nullable (native_re_mk_inter r s) =
      (native_re_nullable r && native_re_nullable s) :=
  RuleProofs.native_re_nullable_mk_inter r s

private theorem native_list_in_re_mk_inter :
    (xs : List native_Char) -> (r s : SmtRegLan) ->
      native_list_in_re xs (native_re_mk_inter r s) =
        (native_list_in_re xs r && native_list_in_re xs s)
  | xs, r, s => RuleProofs.nativeListInRe_mk_inter xs r s

private theorem native_str_in_re_mk_union
    (str : native_String) (r s : SmtRegLan) :
    native_str_in_re str (native_re_mk_union r s) =
      (native_str_in_re str r || native_str_in_re str s) := by
  cases hValid : native_string_valid str
  · simp [native_str_in_re, hValid]
  · simpa [native_str_in_re, native_list_in_re, hValid] using
      native_list_in_re_mk_union str r s

private theorem native_str_in_re_mk_inter
    (str : native_String) (r s : SmtRegLan) :
    native_str_in_re str (native_re_mk_inter r s) =
      (native_str_in_re str r && native_str_in_re str s) := by
  cases hValid : native_string_valid str
  · simp [native_str_in_re, hValid]
  · simpa [native_str_in_re, native_list_in_re, hValid] using
      native_list_in_re_mk_inter str r s

private theorem native_str_in_re_mk_comp_list :
    ∀ (xs : List native_Char) (r : SmtRegLan),
      native_list_in_re xs (native_re_mk_comp r) =
        Bool.not (native_list_in_re xs r)
  | xs, r => RuleProofs.nativeListInRe_mk_comp xs r

theorem native_str_in_re_re_comp
    (s : native_String) (r : SmtRegLan) :
    native_str_in_re s (native_re_comp r) =
      (native_string_valid s && Bool.not (native_str_in_re s r)) :=
  RuleProofs.native_str_in_re_re_comp s r

theorem native_str_in_re_re_union
    (s : native_String) (r₁ r₂ : SmtRegLan) :
    native_str_in_re s (native_re_union r₁ r₂) =
      (native_str_in_re s r₁ || native_str_in_re s r₂) :=
  native_str_in_re_mk_union s r₁ r₂

theorem native_str_in_re_re_concat_congr
    (s : native_String) (r₁ r₁' r₂ r₂' : SmtRegLan)
    (h₁ :
      ∀ str, native_string_valid str = true ->
        native_str_in_re str r₁ = native_str_in_re str r₁')
    (h₂ :
      ∀ str, native_string_valid str = true ->
        native_str_in_re str r₂ = native_str_in_re str r₂') :
    native_str_in_re s (native_re_concat r₁ r₂) =
      native_str_in_re s (native_re_concat r₁' r₂') := by
  by_cases hValid : native_string_valid s = true
  ·
    have h₁List :
        ∀ ys : List native_Char,
          native_string_valid ys = true ->
            native_list_in_re ys r₁ = native_list_in_re ys r₁' := by
      intro ys hys
      simpa [native_str_in_re, native_list_in_re, hys] using h₁ ys hys
    have h₂List :
        ∀ ys : List native_Char,
          native_string_valid ys = true ->
            native_list_in_re ys r₂ = native_list_in_re ys r₂' := by
      intro ys hys
      simpa [native_str_in_re, native_list_in_re, hys] using h₂ ys hys
    simpa [native_str_in_re, native_list_in_re, native_re_concat, hValid, native_list_in_re_mk_concat_congr_valid, native_re_mk_concat] using
      native_list_in_re_mk_concat_congr_valid s r₁ r₁' r₂ r₂'
        hValid h₁List h₂List
  · have hInvalid : native_string_valid s = false := by
      cases h : native_string_valid s <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

theorem native_str_in_re_re_inter
    (s : native_String) (r₁ r₂ : SmtRegLan) :
    native_str_in_re s (native_re_inter r₁ r₂) =
      (native_str_in_re s r₁ && native_str_in_re s r₂) :=
  native_str_in_re_mk_inter s r₁ r₂

theorem native_str_in_re_re_diff
    (s : native_String) (r₁ r₂ : SmtRegLan) :
    native_str_in_re s (native_re_diff r₁ r₂) =
      (native_str_in_re s r₁ && Bool.not (native_str_in_re s r₂)) := by
  cases hValid : native_string_valid s
  · simp [native_str_in_re, hValid]
  · have hInter := native_list_in_re_mk_inter s r₁ (native_re_mk_comp r₂)
    have hComp :
        native_list_in_re s (native_re_mk_comp r₂) =
          Bool.not (native_list_in_re s r₂) := by
      exact native_str_in_re_mk_comp_list s r₂
    rw [hComp] at hInter
    simpa [native_str_in_re, native_re_diff, native_list_in_re, hValid] using
      hInter


end CongSupport
