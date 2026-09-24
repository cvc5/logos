module

public import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ArithModOverModSupport

abbrev plusOp : Term := Term.UOp UserOp.plus
abbrev multOp : Term := Term.UOp UserOp.mult

abbrev modTotalTerm (t c : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) t) c

abbrev eqTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

abbrev plusTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply plusOp x) y

abbrev multTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply multOp x) y

abbrev modPremise (c : Term) : Term :=
  eqTerm (eqTerm c (Term.Numeral 0)) (Term.Boolean false)

abbrev plusConclusion (c ts r ss : Term) : Term :=
  eqTerm
    (modTotalTerm
      (__eo_list_concat plusOp ts
        (plusTerm (modTotalTerm r c) ss)) c)
    (modTotalTerm
      (__eo_list_singleton_elim plusOp
        (__eo_list_concat plusOp ts (plusTerm r ss))) c)

abbrev multConclusion (c ts r ss : Term) : Term :=
  eqTerm
    (modTotalTerm
      (__eo_list_concat multOp ts
        (multTerm (modTotalTerm r c) ss)) c)
    (modTotalTerm
      (__eo_list_singleton_elim multOp
        (__eo_list_concat multOp ts (multTerm r ss))) c)

theorem smtx_typeof_of_eo_int
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Int) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Int := by
  exact TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
    a Term.Int (__eo_to_smt a) rfl hTrans hTy

theorem smtx_eval_mod_total_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.mod_total x y) =
      __smtx_model_eval_mod_total
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_plus_term_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.plus x y) =
      __smtx_model_eval_plus
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_mult_term_eq (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.mult x y) =
      __smtx_model_eval_mult
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem native_to_real_eq_intCast (n : native_Int) :
    native_to_real n = (n : Rat) := by
  rw [native_to_real, native_mk_rational]
  change (n : Rat) / (1 : Rat) = (n : Rat)
  change (n : Rat) * ((1 : Rat)⁻¹) = (n : Rat)
  rw [Rat.inv_def]
  change (n : Rat) * Rat.divInt 1 1 = (n : Rat)
  rw [show Rat.divInt 1 1 = (1 : Rat) by rfl]
  exact Rat.mul_one _

private theorem native_mk_rational_zero :
    native_mk_rational 0 1 = (0 : Rat) := by
  native_decide

private theorem native_mk_rational_one :
    native_mk_rational 1 1 = (1 : Rat) := by
  native_decide

private theorem plus_nil_numeral_zero (n : native_Int)
    (h : __eo_is_list plusOp (Term.Numeral n) = Term.Boolean true) :
    n = 0 := by
  have hRat : (0 : Rat) = (n : Rat) := by
    simpa [plusOp, __eo_is_list, __eo_get_nil_rec, __eo_requires,
      __eo_is_list_nil, __eo_is_list_nil_plus, __eo_to_q, __eo_is_eq,
      __eo_is_ok, native_mk_rational_zero, native_to_real_eq_intCast,
      native_ite, native_teq, native_not, SmtEval.native_not, native_and]
      using h
  exact Rat.intCast_inj.mp hRat.symm

private theorem mult_nil_numeral_one (n : native_Int)
    (h : __eo_is_list multOp (Term.Numeral n) = Term.Boolean true) :
    n = 1 := by
  have hRat : (1 : Rat) = (n : Rat) := by
    simpa [multOp, __eo_is_list, __eo_get_nil_rec, __eo_requires,
      __eo_is_list_nil, __eo_is_list_nil_mult, __eo_to_q, __eo_is_eq,
      __eo_is_ok, native_mk_rational_one, native_to_real_eq_intCast,
      native_ite, native_teq, native_not, SmtEval.native_not, native_and]
      using h
  exact Rat.intCast_inj.mp hRat.symm

private theorem is_list_true_of_get_nil_ne_stuck (f x : Term) :
    __eo_get_nil_rec f x ≠ Term.Stuck ->
    __eo_is_list f x = Term.Boolean true := by
  exact eo_is_list_true_of_get_nil_rec_ne_stuck f x

private theorem get_nil_ne_stuck_of_is_list_true (f x : Term) :
    __eo_is_list f x = Term.Boolean true ->
    __eo_get_nil_rec f x ≠ Term.Stuck := by
  exact eo_get_nil_rec_ne_stuck_of_is_list_true f x

private theorem plus_args_int_of_type_int (x y : Term)
    (hTy : __smtx_typeof (__eo_to_smt (plusTerm x y)) = SmtType.Int) :
    __smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.Int := by
  change __smtx_typeof (SmtTerm.plus (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.Int at hTy
  rw [typeof_plus_eq] at hTy
  cases hx : __smtx_typeof (__eo_to_smt x) <;>
    cases hy : __smtx_typeof (__eo_to_smt y) <;>
    simp [__smtx_typeof_arith_overload_op_2, native_Teq, native_ite,
      hx, hy] at hTy ⊢

private theorem mult_args_int_of_type_int (x y : Term)
    (hTy : __smtx_typeof (__eo_to_smt (multTerm x y)) = SmtType.Int) :
    __smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.Int := by
  change __smtx_typeof (SmtTerm.mult (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.Int at hTy
  rw [typeof_mult_eq] at hTy
  cases hx : __smtx_typeof (__eo_to_smt x) <;>
    cases hy : __smtx_typeof (__eo_to_smt y) <;>
    simp [__smtx_typeof_arith_overload_op_2, native_Teq, native_ite,
      hx, hy] at hTy ⊢

inductive AddListEval (M : SmtModel) : Term -> native_Int -> Prop
  | nil : AddListEval M (Term.Numeral 0) 0
  | cons {x xs : Term} {nx nxs : native_Int} :
      __smtx_typeof (__eo_to_smt x) = SmtType.Int ->
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Numeral nx ->
      AddListEval M xs nxs ->
      AddListEval M (plusTerm x xs) (nx + nxs)

inductive MulListEval (M : SmtModel) : Term -> native_Int -> Prop
  | nil : MulListEval M (Term.Numeral 1) 1
  | cons {x xs : Term} {nx nxs : native_Int} :
      __smtx_typeof (__eo_to_smt x) = SmtType.Int ->
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Numeral nx ->
      MulListEval M xs nxs ->
      MulListEval M (multTerm x xs) (nx * nxs)

theorem AddListEval.ne_stuck
    {M : SmtModel} {xs : Term} {n : native_Int}
    (h : AddListEval M xs n) : xs ≠ Term.Stuck := by
  intro hs
  cases h <;> cases hs

theorem MulListEval.ne_stuck
    {M : SmtModel} {xs : Term} {n : native_Int}
    (h : MulListEval M xs n) : xs ≠ Term.Stuck := by
  intro hs
  cases h <;> cases hs

theorem AddListEval.type_int
    {M : SmtModel} {xs : Term} {n : native_Int}
    (h : AddListEval M xs n) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.Int := by
  induction h with
  | nil =>
      change __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int
      rw [__smtx_typeof.eq_2]
  | cons hxTy _ _ ih =>
      change __smtx_typeof (SmtTerm.plus _ _) = SmtType.Int
      rw [typeof_plus_eq]
      simp [__smtx_typeof_arith_overload_op_2, hxTy, ih]

theorem MulListEval.type_int
    {M : SmtModel} {xs : Term} {n : native_Int}
    (h : MulListEval M xs n) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.Int := by
  induction h with
  | nil =>
      change __smtx_typeof (SmtTerm.Numeral 1) = SmtType.Int
      rw [__smtx_typeof.eq_2]
  | cons hxTy _ _ ih =>
      change __smtx_typeof (SmtTerm.mult _ _) = SmtType.Int
      rw [typeof_mult_eq]
      simp [__smtx_typeof_arith_overload_op_2, hxTy, ih]

theorem AddListEval.eval
    {M : SmtModel} {xs : Term} {n : native_Int}
    (h : AddListEval M xs n) :
    __smtx_model_eval M (__eo_to_smt xs) = SmtValue.Numeral n := by
  induction h with
  | nil =>
      change __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0
      rw [__smtx_model_eval.eq_2]
  | cons _ hxEval _ ih =>
      change __smtx_model_eval M (SmtTerm.plus _ _) = _
      rw [smtx_eval_plus_term_eq, hxEval, ih]
      simp [__smtx_model_eval_plus, native_zplus]

theorem MulListEval.eval
    {M : SmtModel} {xs : Term} {n : native_Int}
    (h : MulListEval M xs n) :
    __smtx_model_eval M (__eo_to_smt xs) = SmtValue.Numeral n := by
  induction h with
  | nil =>
      change __smtx_model_eval M (SmtTerm.Numeral 1) = SmtValue.Numeral 1
      rw [__smtx_model_eval.eq_2]
  | cons _ hxEval _ ih =>
      change __smtx_model_eval M (SmtTerm.mult _ _) = _
      rw [smtx_eval_mult_term_eq, hxEval, ih]
      simp [__smtx_model_eval_mult, native_zmult]

theorem AddListEval.is_list
    {M : SmtModel} {xs : Term} {n : native_Int}
    (h : AddListEval M xs n) :
    __eo_is_list plusOp xs = Term.Boolean true := by
  induction h with
  | nil =>
      native_decide
  | cons _ _ _ ih =>
      unfold __eo_is_list __eo_is_ok
      have hne := get_nil_ne_stuck_of_is_list_true plusOp _ ih
      simp [plusTerm, plusOp, __eo_get_nil_rec, __eo_requires, hne,
        native_ite, native_teq, native_not, SmtEval.native_not]

theorem MulListEval.is_list
    {M : SmtModel} {xs : Term} {n : native_Int}
    (h : MulListEval M xs n) :
    __eo_is_list multOp xs = Term.Boolean true := by
  induction h with
  | nil =>
      native_decide
  | cons _ _ _ ih =>
      unfold __eo_is_list __eo_is_ok
      have hne := get_nil_ne_stuck_of_is_list_true multOp _ ih
      simp [multTerm, multOp, __eo_get_nil_rec, __eo_requires, hne,
        native_ite, native_teq, native_not, SmtEval.native_not]

theorem AddListEval.of_type_and_list
    (M : SmtModel) (hM : model_wf M) {xs : Term} :
    __eo_is_list plusOp xs = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt xs) = SmtType.Int ->
    ∃ n, AddListEval M xs n := by
  intro hList hTy
  cases xs with
  | Stuck =>
      simp [plusOp, __eo_is_list] at hList
  | Numeral n =>
      have hn := plus_nil_numeral_zero n hList
      subst n
      exact ⟨0, AddListEval.nil⟩
  | Apply f xs =>
      cases f with
      | Apply op x =>
          cases op with
          | UOp u =>
              cases u <;>
                try (simp [plusOp, plusTerm, __eo_is_list, __eo_get_nil_rec,
                  __eo_requires, __eo_is_ok, native_ite, native_teq,
                  native_not, SmtEval.native_not] at hList)
              case plus =>
                have hTailList :=
                  is_list_true_of_get_nil_ne_stuck plusOp xs hList
                have hArgsTy := plus_args_int_of_type_int x xs hTy
                rcases smt_eval_int_of_type M hM x hArgsTy.1 with
                  ⟨nx, hxEval⟩
                rcases AddListEval.of_type_and_list M hM
                    hTailList hArgsTy.2 with
                  ⟨nxs, hXs⟩
                exact ⟨nx + nxs, AddListEval.cons hArgsTy.1 hxEval hXs⟩
          | _ =>
              simp [plusOp, plusTerm, __eo_is_list, __eo_get_nil_rec,
                __eo_requires, __eo_is_list_nil, __eo_is_list_nil_plus,
                __eo_to_q, __eo_is_eq, __eo_is_ok, native_ite,
                native_teq, native_not, SmtEval.native_not, native_and] at hList
      | _ =>
          simp [plusOp, plusTerm, __eo_is_list, __eo_get_nil_rec,
            __eo_requires, __eo_is_list_nil, __eo_is_list_nil_plus,
            __eo_to_q, __eo_is_eq, __eo_is_ok, native_ite,
            native_teq, native_not, SmtEval.native_not, native_and] at hList
  | Rational q =>
      change __smtx_typeof (SmtTerm.Rational q) = SmtType.Int at hTy
      rw [__smtx_typeof.eq_3] at hTy
      simp at hTy
  | _ =>
      simp [plusOp, __eo_is_list, __eo_get_nil_rec, __eo_requires,
        __eo_is_list_nil, __eo_is_list_nil_plus, __eo_to_q, __eo_is_eq,
        __eo_is_ok, native_ite, native_teq, native_not, SmtEval.native_not,
        native_and] at hList hTy

theorem MulListEval.of_type_and_list
    (M : SmtModel) (hM : model_wf M) {xs : Term} :
    __eo_is_list multOp xs = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt xs) = SmtType.Int ->
    ∃ n, MulListEval M xs n := by
  intro hList hTy
  cases xs with
  | Stuck =>
      simp [multOp, __eo_is_list] at hList
  | Numeral n =>
      have hn := mult_nil_numeral_one n hList
      subst n
      exact ⟨1, MulListEval.nil⟩
  | Apply f xs =>
      cases f with
      | Apply op x =>
          cases op with
          | UOp u =>
              cases u <;>
                try (simp [multOp, multTerm, __eo_is_list, __eo_get_nil_rec,
                  __eo_requires, __eo_is_ok, native_ite, native_teq,
                  native_not, SmtEval.native_not] at hList)
              case mult =>
                have hTailList :=
                  is_list_true_of_get_nil_ne_stuck multOp xs hList
                have hArgsTy := mult_args_int_of_type_int x xs hTy
                rcases smt_eval_int_of_type M hM x hArgsTy.1 with
                  ⟨nx, hxEval⟩
                rcases MulListEval.of_type_and_list M hM
                    hTailList hArgsTy.2 with
                  ⟨nxs, hXs⟩
                exact ⟨nx * nxs, MulListEval.cons hArgsTy.1 hxEval hXs⟩
          | _ =>
              simp [multOp, multTerm, __eo_is_list, __eo_get_nil_rec,
                __eo_requires, __eo_is_list_nil, __eo_is_list_nil_mult,
                __eo_to_q, __eo_is_eq, __eo_is_ok, native_ite,
                native_teq, native_not, SmtEval.native_not, native_and] at hList
      | _ =>
          simp [multOp, multTerm, __eo_is_list, __eo_get_nil_rec,
            __eo_requires, __eo_is_list_nil, __eo_is_list_nil_mult,
            __eo_to_q, __eo_is_eq, __eo_is_ok, native_ite,
            native_teq, native_not, SmtEval.native_not, native_and] at hList
  | Rational q =>
      change __smtx_typeof (SmtTerm.Rational q) = SmtType.Int at hTy
      rw [__smtx_typeof.eq_3] at hTy
      simp at hTy
  | _ =>
      simp [multOp, __eo_is_list, __eo_get_nil_rec, __eo_requires,
        __eo_is_list_nil, __eo_is_list_nil_mult, __eo_to_q, __eo_is_eq,
        __eo_is_ok, native_ite, native_teq, native_not, SmtEval.native_not,
        native_and] at hList hTy

private theorem list_concat_rec_add_nil_of_ne_stuck {b : Term}
    (hb : b ≠ Term.Stuck) :
    __eo_list_concat_rec (Term.Numeral 0) b = b := by
  cases b <;> simp [__eo_list_concat_rec] at hb ⊢

private theorem list_concat_rec_mul_nil_of_ne_stuck {b : Term}
    (hb : b ≠ Term.Stuck) :
    __eo_list_concat_rec (Term.Numeral 1) b = b := by
  cases b <;> simp [__eo_list_concat_rec] at hb ⊢

private theorem list_concat_rec_cons_of_ne_stuck {f x xs b : Term}
    (hb : b ≠ Term.Stuck) :
    __eo_list_concat_rec (Term.Apply (Term.Apply f x) xs) b =
      __eo_mk_apply (Term.Apply f x) (__eo_list_concat_rec xs b) := by
  cases b <;> simp [__eo_list_concat_rec] at hb ⊢

theorem AddListEval.concat_rec
    {M : SmtModel} {a b : Term} {na nb : native_Int}
    (ha : AddListEval M a na) (hb : AddListEval M b nb) :
    AddListEval M (__eo_list_concat_rec a b) (na + nb) := by
  induction ha generalizing b nb with
  | nil =>
      rw [list_concat_rec_add_nil_of_ne_stuck (AddListEval.ne_stuck hb)]
      simpa using hb
  | cons hxTy hxEval _ ih =>
      have hTail := ih hb
      have hTailNe := AddListEval.ne_stuck hTail
      rw [list_concat_rec_cons_of_ne_stuck (AddListEval.ne_stuck hb)]
      simpa [plusTerm, plusOp, __eo_mk_apply, hTailNe, Int.add_assoc]
        using AddListEval.cons hxTy hxEval hTail

theorem MulListEval.concat_rec
    {M : SmtModel} {a b : Term} {na nb : native_Int}
    (ha : MulListEval M a na) (hb : MulListEval M b nb) :
    MulListEval M (__eo_list_concat_rec a b) (na * nb) := by
  induction ha generalizing b nb with
  | nil =>
      rw [list_concat_rec_mul_nil_of_ne_stuck (MulListEval.ne_stuck hb)]
      simpa using hb
  | cons hxTy hxEval _ ih =>
      have hTail := ih hb
      have hTailNe := MulListEval.ne_stuck hTail
      rw [list_concat_rec_cons_of_ne_stuck (MulListEval.ne_stuck hb)]
      simpa [multTerm, multOp, __eo_mk_apply, hTailNe, Int.mul_assoc]
        using MulListEval.cons hxTy hxEval hTail

theorem AddListEval.concat
    {M : SmtModel} {a b : Term} {na nb : native_Int}
    (ha : AddListEval M a na) (hb : AddListEval M b nb) :
    AddListEval M (__eo_list_concat plusOp a b) (na + nb) := by
  have haList := AddListEval.is_list ha
  have hbList := AddListEval.is_list hb
  simpa [__eo_list_concat, plusOp, haList, hbList, __eo_requires,
    native_ite, native_teq, native_not, SmtEval.native_not] using
    AddListEval.concat_rec ha hb

theorem MulListEval.concat
    {M : SmtModel} {a b : Term} {na nb : native_Int}
    (ha : MulListEval M a na) (hb : MulListEval M b nb) :
    MulListEval M (__eo_list_concat multOp a b) (na * nb) := by
  have haList := MulListEval.is_list ha
  have hbList := MulListEval.is_list hb
  simpa [__eo_list_concat, multOp, haList, hbList, __eo_requires,
    native_ite, native_teq, native_not, SmtEval.native_not] using
    MulListEval.concat_rec ha hb

private theorem plus_singleton_elim_nil :
    __eo_list_singleton_elim plusOp (Term.Numeral 0) = Term.Numeral 0 := by
  simp [plusOp, __eo_list_singleton_elim, __eo_requires,
    __eo_list_singleton_elim_2, __eo_is_list, __eo_get_nil_rec,
    __eo_is_list_nil, __eo_is_list_nil_plus, __eo_to_q, __eo_is_eq,
    native_mk_rational_zero, native_to_real_eq_intCast, __eo_is_ok,
    native_ite, native_teq, native_not, SmtEval.native_not, native_and]

private theorem mult_singleton_elim_nil :
    __eo_list_singleton_elim multOp (Term.Numeral 1) = Term.Numeral 1 := by
  simp [multOp, __eo_list_singleton_elim, __eo_requires,
    __eo_list_singleton_elim_2, __eo_is_list, __eo_get_nil_rec,
    __eo_is_list_nil, __eo_is_list_nil_mult, __eo_to_q, __eo_is_eq,
    native_mk_rational_one, native_to_real_eq_intCast, __eo_is_ok,
    native_ite, native_teq, native_not, SmtEval.native_not, native_and]

private theorem plus_singleton_elim_one (x : Term) :
    __eo_list_singleton_elim plusOp (plusTerm x (Term.Numeral 0)) = x := by
  simp [plusTerm, plusOp, __eo_list_singleton_elim, __eo_requires,
    __eo_list_singleton_elim_2, __eo_is_list, __eo_get_nil_rec,
    __eo_is_list_nil, __eo_is_list_nil_plus, __eo_to_q, __eo_is_eq,
    native_mk_rational_zero, native_to_real_eq_intCast, __eo_is_ok,
    native_ite, native_teq, native_not, SmtEval.native_not, native_and]

private theorem mult_singleton_elim_one (x : Term) :
    __eo_list_singleton_elim multOp (multTerm x (Term.Numeral 1)) = x := by
  simp [multTerm, multOp, __eo_list_singleton_elim, __eo_requires,
    __eo_list_singleton_elim_2, __eo_is_list, __eo_get_nil_rec,
    __eo_is_list_nil, __eo_is_list_nil_mult, __eo_to_q, __eo_is_eq,
    native_mk_rational_one, native_to_real_eq_intCast, __eo_is_ok,
    native_ite, native_teq, native_not, SmtEval.native_not, native_and]

private theorem plus_singleton_elim_many (x y ys : Term)
    (hYs : __eo_is_list plusOp ys = Term.Boolean true) :
    __eo_list_singleton_elim plusOp (plusTerm x (plusTerm y ys)) =
      plusTerm x (plusTerm y ys) := by
  have hYsNe := get_nil_ne_stuck_of_is_list_true plusOp ys hYs
  simp [plusTerm, plusOp, __eo_list_singleton_elim, __eo_requires,
    __eo_list_singleton_elim_2, __eo_is_list, __eo_get_nil_rec,
    __eo_is_list_nil, __eo_is_list_nil_plus, __eo_to_q, __eo_is_eq,
    __eo_is_ok, native_ite, native_teq, native_not, SmtEval.native_not,
    native_and, hYsNe]

private theorem mult_singleton_elim_many (x y ys : Term)
    (hYs : __eo_is_list multOp ys = Term.Boolean true) :
    __eo_list_singleton_elim multOp (multTerm x (multTerm y ys)) =
      multTerm x (multTerm y ys) := by
  have hYsNe := get_nil_ne_stuck_of_is_list_true multOp ys hYs
  simp [multTerm, multOp, __eo_list_singleton_elim, __eo_requires,
    __eo_list_singleton_elim_2, __eo_is_list, __eo_get_nil_rec,
    __eo_is_list_nil, __eo_is_list_nil_mult, __eo_to_q, __eo_is_eq,
    __eo_is_ok, native_ite, native_teq, native_not, SmtEval.native_not,
    native_and, hYsNe]

theorem AddListEval.singleton_elim_eval
    {M : SmtModel} {xs : Term} {n : native_Int}
    (h : AddListEval M xs n) :
    __smtx_typeof (__eo_to_smt (__eo_list_singleton_elim plusOp xs)) =
        SmtType.Int ∧
      __smtx_model_eval M (__eo_to_smt (__eo_list_singleton_elim plusOp xs)) =
        SmtValue.Numeral n := by
  induction h with
  | nil =>
      rw [plus_singleton_elim_nil]
      constructor
      · change __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int
        rw [__smtx_typeof.eq_2]
      · change __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0
        rw [__smtx_model_eval.eq_2]
  | cons hxTy hxEval hTail ih =>
      cases hTail with
      | nil =>
          rw [plus_singleton_elim_one]
          exact ⟨hxTy, by simpa [Int.add_zero] using hxEval⟩
      | cons hyTy hyEval hRest =>
          have hOrigTy := AddListEval.type_int
            (AddListEval.cons hxTy hxEval (AddListEval.cons hyTy hyEval hRest))
          have hOrigEval := AddListEval.eval
            (AddListEval.cons hxTy hxEval (AddListEval.cons hyTy hyEval hRest))
          rw [plus_singleton_elim_many _ _ _ (AddListEval.is_list hRest)]
          exact ⟨hOrigTy, hOrigEval⟩

theorem MulListEval.singleton_elim_eval
    {M : SmtModel} {xs : Term} {n : native_Int}
    (h : MulListEval M xs n) :
    __smtx_typeof (__eo_to_smt (__eo_list_singleton_elim multOp xs)) =
        SmtType.Int ∧
      __smtx_model_eval M (__eo_to_smt (__eo_list_singleton_elim multOp xs)) =
        SmtValue.Numeral n := by
  induction h with
  | nil =>
      rw [mult_singleton_elim_nil]
      constructor
      · change __smtx_typeof (SmtTerm.Numeral 1) = SmtType.Int
        rw [__smtx_typeof.eq_2]
      · change __smtx_model_eval M (SmtTerm.Numeral 1) = SmtValue.Numeral 1
        rw [__smtx_model_eval.eq_2]
  | cons hxTy hxEval hTail ih =>
      cases hTail with
      | nil =>
          rw [mult_singleton_elim_one]
          exact ⟨hxTy, by simpa [Int.mul_one] using hxEval⟩
      | cons hyTy hyEval hRest =>
          have hOrigTy := MulListEval.type_int
            (MulListEval.cons hxTy hxEval (MulListEval.cons hyTy hyEval hRest))
          have hOrigEval := MulListEval.eval
            (MulListEval.cons hxTy hxEval (MulListEval.cons hyTy hyEval hRest))
          rw [mult_singleton_elim_many _ _ _ (MulListEval.is_list hRest)]
          exact ⟨hOrigTy, hOrigEval⟩

theorem mod_add_replace_mod (a r s c : native_Int) :
    native_mod_total (a + (native_mod_total r c + s)) c =
      native_mod_total (a + (r + s)) c := by
  unfold native_mod_total
  change (a + (r % c + s)) % c = (a + (r + s)) % c
  rw [Int.add_emod a (r % c + s) c, Int.add_emod a (r + s) c,
    Int.emod_add_emod r c s]

theorem mod_mul_replace_mod (a r s c : native_Int) :
    native_mod_total (a * (native_mod_total r c * s)) c =
      native_mod_total (a * (r * s)) c := by
  have hLeft : a * (r % c * s) = r % c * (a * s) := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hRight : a * (r * s) = r * (a * s) := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  unfold native_mod_total
  change (a * (r % c * s)) % c = (a * (r * s)) % c
  rw [hLeft, hRight]
  calc
    (r % c * (a * s)) % c =
        ((r % c) % c * ((a * s) % c)) % c := Int.mul_emod (r % c) (a * s) c
    _ = (r % c * ((a * s) % c)) % c := by rw [Int.emod_emod]
    _ = (r * (a * s)) % c := (Int.mul_emod r (a * s) c).symm

end ArithModOverModSupport
