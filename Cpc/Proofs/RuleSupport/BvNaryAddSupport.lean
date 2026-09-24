module

public import Cpc.Proofs.RuleSupport.BvAllOnesCmpSupport
import all Cpc.Proofs.RuleSupport.BvAllOnesCmpSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport
public import Cpc.Proofs.RuleSupport.BvXorOnesSupport
import all Cpc.Proofs.RuleSupport.BvXorOnesSupport

public section

/-! Shared typing and evaluation support for n-ary bit-vector addition lists. -/

open Eo
open SmtEval
open Smtm

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvNaryAddSupport

abbrev op : Term := Term.UOp UserOp.bvadd

@[expose] def add (x y : Term) : Term :=
  Term.Apply (Term.Apply op x) y

@[simp] theorem add_eq (x y : Term) :
    add x y = Term.Apply (Term.Apply op x) y := rfl

private theorem term_ne_stuck_of_smt_bitvec_type
    {t : Term} {w : Nat} :
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    t ≠ Term.Stuck := by
  intro hTy h
  subst t
  change __smtx_typeof SmtTerm.None = SmtType.BitVec w at hTy
  rw [TranslationProofs.smtx_typeof_none] at hTy
  cases hTy

theorem addArgsOfBitvecType (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt (add x y)) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.bvadd (__eo_to_smt x) (__eo_to_smt y)) =
        SmtType.BitVec w := by
    have hsimpa := hTy
    try simp [add, op] at hsimpa ⊢
    exact hsimpa
  have hNN : term_has_non_none_type
      (SmtTerm.bvadd (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [hTy']
    intro h
    cases h
  rcases bv_binop_args_of_non_none (op := SmtTerm.bvadd)
      (show
        __smtx_typeof (SmtTerm.bvadd (__eo_to_smt x) (__eo_to_smt y)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt x))
            (__smtx_typeof (__eo_to_smt y)) by
        rw [__smtx_typeof.eq_def] <;> simp only) hNN with
    ⟨w', hXTy, hYTy⟩
  have hWidth : w' = w := by
    have hResult : SmtType.BitVec w' = SmtType.BitVec w := by
      rw [show
          __smtx_typeof (SmtTerm.bvadd (__eo_to_smt x) (__eo_to_smt y)) =
            __smtx_typeof_bv_op_2
              (__smtx_typeof (__eo_to_smt x))
              (__smtx_typeof (__eo_to_smt y)) by
          rw [__smtx_typeof.eq_def] <;> simp only] at hTy'
      simpa [__smtx_typeof_bv_op_2, hXTy, hYTy, native_ite,
        native_nateq, Smtm.native_nateq] using hTy'
    cases hResult
    rfl
  subst w'
  exact ⟨hXTy, hYTy⟩

theorem addSmtType (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt (add x y)) = SmtType.BitVec w := by
  intro hXTy hYTy
  change __smtx_typeof
      (SmtTerm.bvadd (__eo_to_smt x) (__eo_to_smt y)) = _
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2, hXTy, hYTy, native_ite,
    native_nateq, Smtm.native_nateq]

private theorem emod_add_left_congr
    (a b m : Int) : ((a % m) + b) % m = (a + b) % m := by
  rw [Int.add_emod, Int.emod_emod]
  exact (Int.add_emod a b m).symm

private theorem emod_add_right_congr
    (a b m : Int) : (a + (b % m)) % m = (a + b) % m := by
  rw [Int.add_comm a, Int.add_comm a]
  exact emod_add_left_congr b a m

theorem addAssocEval
    (M : SmtModel) (hM : model_wf M)
    (x y z : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __smtx_model_eval M (__eo_to_smt (add (add x y) z)) =
      __smtx_model_eval M (__eo_to_smt (add x (add y z))) := by
  intro hXTy hYTy hZTy
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) w
      hXTy with ⟨nx, hXEval, _hXCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt y) w
      hYTy with ⟨ny, hYEval, _hYCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt z) w
      hZTy with ⟨nz, hZEval, _hZCan⟩
  change __smtx_model_eval_bvadd
      (__smtx_model_eval_bvadd
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)))
      (__smtx_model_eval M (__eo_to_smt z)) =
    __smtx_model_eval_bvadd
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval_bvadd
        (__smtx_model_eval M (__eo_to_smt y))
        (__smtx_model_eval M (__eo_to_smt z)))
  rw [hXEval, hYEval, hZEval]
  simp only [__smtx_model_eval_bvadd]
  have hPayload :
      native_mod_total
          (native_zplus
            (native_mod_total (native_zplus nx ny)
              (native_int_pow2 (native_nat_to_int w))) nz)
          (native_int_pow2 (native_nat_to_int w)) =
        native_mod_total
          (native_zplus nx
            (native_mod_total (native_zplus ny nz)
              (native_int_pow2 (native_nat_to_int w))))
          (native_int_pow2 (native_nat_to_int w)) := by
    unfold native_mod_total native_zplus
    calc
      (((nx + ny) % native_int_pow2 (native_nat_to_int w)) + nz) %
          native_int_pow2 (native_nat_to_int w) =
        ((nx + ny) + nz) % native_int_pow2 (native_nat_to_int w) :=
          emod_add_left_congr _ _ _
      _ = (nx + (ny + nz)) % native_int_pow2 (native_nat_to_int w) := by
        rw [Int.add_assoc]
      _ = (nx + ((ny + nz) % native_int_pow2 (native_nat_to_int w))) %
          native_int_pow2 (native_nat_to_int w) :=
        (emod_add_right_congr _ _ _).symm
  rw [hPayload]

theorem addCommEval
    (M : SmtModel) (hM : model_wf M)
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_model_eval M (__eo_to_smt (add x y)) =
      __smtx_model_eval M (__eo_to_smt (add y x)) := by
  intro hXTy hYTy
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) w
      hXTy with ⟨nx, hXEval, _hXCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt y) w
      hYTy with ⟨ny, hYEval, _hYCan⟩
  change __smtx_model_eval_bvadd
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) =
    __smtx_model_eval_bvadd
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt x))
  rw [hXEval, hYEval]
  simp [__smtx_model_eval_bvadd, native_zplus, Int.add_comm]

private theorem nilPayloadEqZero
    (M : SmtModel) (nil : Term) (w : Nat) (n : Int) :
    __eo_is_list_nil op nil = Term.Boolean true ->
    __smtx_model_eval M (__eo_to_smt nil) =
      SmtValue.Binary (native_nat_to_int w) n ->
    n = 0 := by
  intro hNilTrue hNilEval
  cases nil <;>
    simp [op, __eo_is_list_nil, __eo_is_list_nil_bvadd, __eo_to_z,
      __eo_is_eq, native_and, native_not, SmtEval.native_not, native_teq,
      native_zeq] at hNilTrue
  case Numeral z =>
    rw [show __eo_to_smt (Term.Numeral z) = SmtTerm.Numeral z by rfl] at hNilEval
    rw [__smtx_model_eval] at hNilEval
    cases hNilEval
  case Rational q =>
    rw [show __eo_to_smt (Term.Rational q) = SmtTerm.Rational q by rfl] at hNilEval
    rw [__smtx_model_eval] at hNilEval
    cases hNilEval
  case String s =>
    rw [show __eo_to_smt (Term.String s) = SmtTerm.String s by rfl] at hNilEval
    rw [__smtx_model_eval] at hNilEval
    cases hNilEval
  case Binary wb nb =>
    have hEvalEq : SmtValue.Binary wb nb =
        SmtValue.Binary (native_nat_to_int w) n := by
      rw [show __eo_to_smt (Term.Binary wb nb) = SmtTerm.Binary wb nb by rfl]
        at hNilEval
      rw [__smtx_model_eval] at hNilEval
      exact hNilEval
    injection hEvalEq with _ hPayloadEq
    subst n
    exact hNilTrue.symm

private theorem addLeftZeroEval
    (M : SmtModel) (hM : model_wf M)
    (nil x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt nil) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_is_list_nil op nil = Term.Boolean true ->
    __smtx_model_eval M (__eo_to_smt (add nil x)) =
      __smtx_model_eval M (__eo_to_smt x) := by
  intro hNilTy hXTy hNil
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt nil) w
      hNilTy with ⟨nn, hNilEval, _hNilCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) w
      hXTy with ⟨nx, hXEval, hXCan⟩
  have hNilZero := nilPayloadEqZero M nil w nn hNil hNilEval
  subst nn
  have hMod : native_mod_total nx
      (native_int_pow2 (native_nat_to_int w)) = nx := by
    have hEq : nx = native_mod_total nx
        (native_int_pow2 (native_nat_to_int w)) := by
      simpa [native_zeq] using hXCan
    exact hEq.symm
  change __smtx_model_eval_bvadd
      (__smtx_model_eval M (__eo_to_smt nil))
      (__smtx_model_eval M (__eo_to_smt x)) = _
  rw [hNilEval, hXEval]
  simp [__smtx_model_eval_bvadd, native_zplus, hMod]

private theorem addRightZeroEval
    (M : SmtModel) (hM : model_wf M)
    (x nil : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt nil) = SmtType.BitVec w ->
    __eo_is_list_nil op nil = Term.Boolean true ->
    __smtx_model_eval M (__eo_to_smt (add x nil)) =
      __smtx_model_eval M (__eo_to_smt x) := by
  intro hXTy hNilTy hNil
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) w
      hXTy with ⟨nx, hXEval, hXCan⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt nil) w
      hNilTy with ⟨nn, hNilEval, _hNilCan⟩
  have hNilZero := nilPayloadEqZero M nil w nn hNil hNilEval
  subst nn
  have hMod : native_mod_total nx
      (native_int_pow2 (native_nat_to_int w)) = nx := by
    have hEq : nx = native_mod_total nx
        (native_int_pow2 (native_nat_to_int w)) := by
      simpa [native_zeq] using hXCan
    exact hEq.symm
  change __smtx_model_eval_bvadd
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt nil)) = _
  rw [hXEval, hNilEval]
  simp [__smtx_model_eval_bvadd, native_zplus, hMod]

theorem evalRightZero
    (M : SmtModel) (hM : model_wf M)
    (x nil : Term) (w : Nat)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.BitVec w)
    (hNil : __eo_is_list_nil op nil = Term.Boolean true) :
    __smtx_model_eval M (__eo_to_smt (add x nil)) =
      __smtx_model_eval M (__eo_to_smt x) :=
  addRightZeroEval M hM x nil w hXTy hNilTy hNil

private theorem isListTrueNeStuck {t : Term} :
    __eo_is_list op t = Term.Boolean true -> t ≠ Term.Stuck := by
  intro hList h
  subst t
  simp [op, __eo_is_list] at hList

private theorem isListNilBooleanOfNeStuck (t : Term) :
    t ≠ Term.Stuck ->
    ∃ b, __eo_is_list_nil op t = Term.Boolean b := by
  intro hNe
  cases t <;>
    simp [op, __eo_is_list_nil, __eo_is_list_nil_bvadd, __eo_to_z,
      __eo_is_eq, native_and, native_not, native_teq, native_zeq] at hNe ⊢

theorem listConcatRecSmtType
    (a z : Term) (w : Nat) :
    __eo_is_list op a = Term.Boolean true ->
    __eo_is_list op z = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) =
      SmtType.BitVec w := by
  intro hAList hZList hATy hZTy
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z => simp [op, __eo_is_list] at hAList
  | case2 a hA => simp [op, __eo_is_list] at hZList
  | case3 f x xs z hZNe ih =>
      have hf : f = op := eo_is_list_cons_head_eq_of_true op f x xs hAList
      subst f
      have hXsList := eo_is_list_tail_true_of_cons_self op x xs hAList
      have hArgs := addArgsOfBitvecType x xs w (by
        simpa [add, op] using hATy)
      have hTailTy := ih hXsList hZList hArgs.2 hZTy
      have hTailNe := term_ne_stuck_of_smt_bitvec_type hTailTy
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck op x xs z hTailNe]
      exact addSmtType x (__eo_list_concat_rec xs z) w hArgs.1 hTailTy
  | case4 nil z hNil hZNe hNot =>
      have hNilTrue : __eo_is_list_nil op nil = Term.Boolean true := by
        have hGet := eo_get_nil_rec_ne_stuck_of_is_list_true op nil hAList
        have hReq : __eo_requires (__eo_is_list_nil op nil)
            (Term.Boolean true) nil ≠ Term.Stuck := by
          simpa [__eo_get_nil_rec] using hGet
        exact eo_requires_eq_of_ne_stuck _ _ _ hReq
      rw [show __eo_list_concat_rec nil z = z by
        cases nil <;> cases z <;>
          simp [op, __eo_is_list_nil, __eo_list_concat_rec] at hNilTrue ⊢]
      exact hZTy

theorem listConcatSmtType
    (a z : Term) (w : Nat) :
    __eo_is_list op a = Term.Boolean true ->
    __eo_is_list op z = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt (__eo_list_concat op a z)) =
      SmtType.BitVec w := by
  intro hAList hZList hATy hZTy
  simpa [__eo_list_concat, hAList, hZList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using
    listConcatRecSmtType a z w hAList hZList hATy hZTy

theorem listSingletonElimSmtType
    (c : Term) (w : Nat) :
    __eo_is_list op c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt (__eo_list_singleton_elim op c)) =
      SmtType.BitVec w := by
  intro hList hTy
  change __smtx_typeof
      (__eo_to_smt
        (__eo_requires (__eo_is_list op c) (Term.Boolean true)
          (__eo_list_singleton_elim_2 c))) = _
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg : g = op := eo_is_list_cons_head_eq_of_true
            op g head tail hList
          subst g
          have hArgs := addArgsOfBitvecType head tail w (by
            simpa [add, op] using hTy)
          have hTailList := eo_is_list_tail_true_of_cons_self
            op head tail hList
          have hTailNe := isListTrueNeStuck hTailList
          rcases isListNilBooleanOfNeStuck tail hTailNe with ⟨b, hNil⟩
          cases b <;> simp [__eo_list_singleton_elim_2, hNil, __eo_ite,
            native_ite, native_teq, hArgs.1, hTy]
      | _ => simpa [__eo_list_singleton_elim_2] using hTy
  | _ => simpa [__eo_list_singleton_elim_2] using hTy

theorem listConcatRecEvalEq
    (M : SmtModel) (hM : model_wf M)
    (a z : Term) (w : Nat) :
    __eo_is_list op a = Term.Boolean true ->
    __eo_is_list op z = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec a z)) =
      __smtx_model_eval M (__eo_to_smt (add a z)) := by
  intro hAList hZList hATy hZTy
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z => simp [op, __eo_is_list] at hAList
  | case2 a hA => simp [op, __eo_is_list] at hZList
  | case3 f x xs z hZNe ih =>
      have hf : f = op := eo_is_list_cons_head_eq_of_true op f x xs hAList
      subst f
      have hXsList := eo_is_list_tail_true_of_cons_self op x xs hAList
      have hArgs := addArgsOfBitvecType x xs w (by
        simpa [add, op] using hATy)
      have hTailTy := listConcatRecSmtType xs z w
        hXsList hZList hArgs.2 hZTy
      have hTailNe := term_ne_stuck_of_smt_bitvec_type hTailTy
      have hIH := ih hXsList hZList hArgs.2 hZTy
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck op x xs z hTailNe]
      calc
        __smtx_model_eval M
            (__eo_to_smt (add x (__eo_list_concat_rec xs z))) =
          __smtx_model_eval M (__eo_to_smt (add x (add xs z))) := by
            change __smtx_model_eval_bvadd
                (__smtx_model_eval M (__eo_to_smt x))
                (__smtx_model_eval M
                  (__eo_to_smt (__eo_list_concat_rec xs z))) =
              __smtx_model_eval_bvadd
                (__smtx_model_eval M (__eo_to_smt x))
                (__smtx_model_eval M (__eo_to_smt (add xs z)))
            rw [hIH]
        _ = __smtx_model_eval M (__eo_to_smt (add (add x xs) z)) :=
          (addAssocEval M hM x xs z w hArgs.1 hArgs.2 hZTy).symm
  | case4 nil z hNil hZNe hNot =>
      have hNilTrue : __eo_is_list_nil op nil = Term.Boolean true := by
        have hGet := eo_get_nil_rec_ne_stuck_of_is_list_true op nil hAList
        have hReq : __eo_requires (__eo_is_list_nil op nil)
            (Term.Boolean true) nil ≠ Term.Stuck := by
          simpa [__eo_get_nil_rec] using hGet
        exact eo_requires_eq_of_ne_stuck _ _ _ hReq
      rw [show __eo_list_concat_rec nil z = z by
        cases nil <;> cases z <;>
          simp [op, __eo_is_list_nil, __eo_list_concat_rec] at hNilTrue ⊢]
      exact (addLeftZeroEval M hM nil z w hATy hZTy hNilTrue).symm

theorem listConcatEvalEq
    (M : SmtModel) (hM : model_wf M)
    (a z : Term) (w : Nat) :
    __eo_is_list op a = Term.Boolean true ->
    __eo_is_list op z = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __smtx_model_eval M (__eo_to_smt (__eo_list_concat op a z)) =
      __smtx_model_eval M (__eo_to_smt (add a z)) := by
  intro hAList hZList hATy hZTy
  simpa [__eo_list_concat, hAList, hZList, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not] using
    listConcatRecEvalEq M hM a z w hAList hZList hATy hZTy

theorem listSingletonElimEvalEq
    (M : SmtModel) (hM : model_wf M)
    (c : Term) (w : Nat) :
    __eo_is_list op c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w ->
    __smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim op c)) =
      __smtx_model_eval M (__eo_to_smt c) := by
  intro hList hTy
  change __smtx_model_eval M
      (__eo_to_smt
        (__eo_requires (__eo_is_list op c) (Term.Boolean true)
          (__eo_list_singleton_elim_2 c))) = _
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg : g = op := eo_is_list_cons_head_eq_of_true
            op g head tail hList
          subst g
          have hArgs := addArgsOfBitvecType head tail w (by
            simpa [add, op] using hTy)
          have hTailList := eo_is_list_tail_true_of_cons_self
            op head tail hList
          have hTailNe := isListTrueNeStuck hTailList
          rcases isListNilBooleanOfNeStuck tail hTailNe with ⟨b, hNil⟩
          cases b with
          | false =>
              simp [__eo_list_singleton_elim_2, hNil, __eo_ite,
                native_ite, native_teq]
          | true =>
              simp [__eo_list_singleton_elim_2, hNil, __eo_ite,
                native_ite, native_teq]
              exact (addRightZeroEval M hM head tail w
                hArgs.1 hArgs.2 hNil).symm
      | _ => simpa [__eo_list_singleton_elim_2]
  | _ => simpa [__eo_list_singleton_elim_2]

/-! EO-level inversion support.  A syntactic n-ary list may be its nil
identity, so its SMT type is represented by `ListTypeOrNil` until a
non-empty tail fixes the common width. -/

def ListTypeOrNil (t : Term) (w : Nat) : Prop :=
  __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ∨
    ∀ tail, __eo_list_concat_rec t tail = tail

theorem addArgsOfEoBitvecType (x y width : Term) :
    __eo_typeof (add x y) =
        Term.Apply (Term.UOp UserOp.BitVec) width ->
    __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
      __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) width := by
  intro h
  exact BvXorOnesSupport.typeof_bvxor_args_of_result_bitvec x y width
    (by have hsimpa := h; (try simp [add, op] at hsimpa ⊢); exact hsimpa)

private theorem listConcatRecConsOfRightNeStuck
    (f x xs z : Term) :
    z ≠ Term.Stuck ->
    __eo_list_concat_rec (Term.Apply (Term.Apply f x) xs) z =
      __eo_mk_apply (Term.Apply f x) (__eo_list_concat_rec xs z) := by
  intro hZ
  cases z <;> first | exact absurd rfl hZ | rfl

private theorem mkApplyRightStuck (f : Term) :
    __eo_mk_apply f Term.Stuck = Term.Stuck := by
  cases f <;> rfl

private theorem mkApplyEqApplyOfArgsNeStuck
    (f x : Term) :
    f ≠ Term.Stuck -> x ≠ Term.Stuck ->
    __eo_mk_apply f x = Term.Apply f x := by
  intro hF hX
  cases f <;> cases x <;> simp_all [__eo_mk_apply]

theorem listConcatRecRightTypeNeStuck
    (a z : Term) :
    __eo_is_list op a = Term.Boolean true ->
    __eo_typeof (__eo_list_concat_rec a z) ≠ Term.Stuck ->
    __eo_typeof z ≠ Term.Stuck := by
  intro hList hTyNe
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z => simp [op, __eo_is_list] at hList
  | case2 a hA =>
      apply False.elim
      apply hTyNe
      cases a <;> rfl
  | case3 f x xs z hz ih =>
      have hf := eo_is_list_cons_head_eq_of_true op f x xs hList
      subst f
      have hTailList := eo_is_list_tail_true_of_cons_self op x xs hList
      have hTailNe : __eo_list_concat_rec xs z ≠ Term.Stuck := by
        intro h
        apply hTyNe
        rw [listConcatRecConsOfRightNeStuck op x xs z hz,
          h, mkApplyRightStuck]
        rfl
      have hTailTyNe :
          __eo_typeof (__eo_list_concat_rec xs z) ≠ Term.Stuck := by
        intro h
        apply hTyNe
        rw [listConcatRecConsOfRightNeStuck op x xs z hz,
          mkApplyEqApplyOfArgsNeStuck _ _ (by simp [op]) hTailNe]
        change __eo_typeof_bvand (__eo_typeof x)
          (__eo_typeof (__eo_list_concat_rec xs z)) = Term.Stuck
        rw [h]
        simp [__eo_typeof_bvand]
      exact ih hTailList hTailTyNe
  | case4 nil z hNil hZ hNot =>
      have hEq : __eo_list_concat_rec nil z = z := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      simpa [hEq] using hTyNe

theorem listConcatRecResultType
    (a z width : Term) :
    __eo_is_list op a = Term.Boolean true ->
    __eo_typeof z = Term.Apply (Term.UOp UserOp.BitVec) width ->
    __eo_typeof (__eo_list_concat_rec a z) ≠ Term.Stuck ->
    __eo_typeof (__eo_list_concat_rec a z) =
      Term.Apply (Term.UOp UserOp.BitVec) width := by
  intro hList hZTy hResultNe
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z => simp [op, __eo_is_list] at hList
  | case2 a hA => cases hZTy
  | case3 f x xs z hz ih =>
      have hf := eo_is_list_cons_head_eq_of_true op f x xs hList
      subst f
      have hTailList := eo_is_list_tail_true_of_cons_self op x xs hList
      have hTailNe : __eo_list_concat_rec xs z ≠ Term.Stuck := by
        intro h
        apply hResultNe
        rw [listConcatRecConsOfRightNeStuck op x xs z hz,
          h, mkApplyRightStuck]
        rfl
      have hTailTyNe :
          __eo_typeof (__eo_list_concat_rec xs z) ≠ Term.Stuck := by
        intro h
        apply hResultNe
        rw [listConcatRecConsOfRightNeStuck op x xs z hz,
          mkApplyEqApplyOfArgsNeStuck _ _ (by simp [op]) hTailNe]
        change __eo_typeof_bvand (__eo_typeof x)
          (__eo_typeof (__eo_list_concat_rec xs z)) = Term.Stuck
        rw [h]
        simp [__eo_typeof_bvand]
      have hTailTy := ih hTailList hZTy hTailTyNe
      have hOuterNe :
          __eo_typeof_bvand (__eo_typeof x)
              (__eo_typeof (__eo_list_concat_rec xs z)) ≠ Term.Stuck := by
        rw [listConcatRecConsOfRightNeStuck op x xs z hz,
          mkApplyEqApplyOfArgsNeStuck _ _ (by simp [op]) hTailNe]
          at hResultNe
        exact hResultNe
      rcases BvXorOnesSupport.typeof_bvand_arg_types_of_ne_stuck hOuterNe with
        ⟨actualWidth, hXTy, hTailShape⟩
      have hWidth : actualWidth = width := by
        rw [hTailTy] at hTailShape
        cases hTailShape
        rfl
      subst actualWidth
      have hWidthNe : width ≠ Term.Stuck := by
        intro h
        apply hOuterNe
        rw [hXTy, hTailTy, h]
        simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
          native_teq, native_not]
      rw [listConcatRecConsOfRightNeStuck op x xs z hz,
        mkApplyEqApplyOfArgsNeStuck _ _ (by simp [op]) hTailNe]
      change __eo_typeof_bvand (__eo_typeof x)
        (__eo_typeof (__eo_list_concat_rec xs z)) = _
      rw [hXTy, hTailTy]
      simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
        native_teq, native_not, hWidthNe]
  | case4 nil z hNil hZ hNot =>
      have hEq : __eo_list_concat_rec nil z = z := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      simpa [hEq] using hZTy

theorem listConcatRecReplaceTailType
    (a z₁ z₂ width : Term) :
    __eo_is_list op a = Term.Boolean true ->
    __eo_typeof (__eo_list_concat_rec a z₁) =
      Term.Apply (Term.UOp UserOp.BitVec) width ->
    __eo_typeof z₂ = Term.Apply (Term.UOp UserOp.BitVec) width ->
    __eo_typeof (__eo_list_concat_rec a z₂) =
      Term.Apply (Term.UOp UserOp.BitVec) width := by
  intro hList hFirstTy hZ₂Ty
  induction a, z₁ using __eo_list_concat_rec.induct generalizing z₂ with
  | case1 z => simp [op, __eo_is_list] at hList
  | case2 a hA =>
      have hBad : __eo_typeof (__eo_list_concat_rec a Term.Stuck) =
          Term.Stuck := by
        cases a <;> rfl
      rw [hBad] at hFirstTy
      cases hFirstTy
  | case3 f x xs z hz ih =>
      have hf := eo_is_list_cons_head_eq_of_true op f x xs hList
      subst f
      have hTailList := eo_is_list_tail_true_of_cons_self op x xs hList
      have hTail₁Ne : __eo_list_concat_rec xs z ≠ Term.Stuck := by
        intro h
        rw [listConcatRecConsOfRightNeStuck op x xs z hz,
          h, mkApplyRightStuck] at hFirstTy
        cases hFirstTy
      rw [listConcatRecConsOfRightNeStuck op x xs z hz,
        mkApplyEqApplyOfArgsNeStuck _ _ (by simp [op]) hTail₁Ne]
        at hFirstTy
      have hParts := addArgsOfEoBitvecType x
        (__eo_list_concat_rec xs z) width (by
          simpa [add, op] using hFirstTy)
      have hTail₂Ty := ih z₂ hTailList hParts.2 hZ₂Ty
      have hZ₂Ne : z₂ ≠ Term.Stuck := by
        intro h
        subst z₂
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) width at hZ₂Ty
        cases hZ₂Ty
      have hTail₂Ne : __eo_list_concat_rec xs z₂ ≠ Term.Stuck := by
        intro h
        rw [h] at hTail₂Ty
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) width at hTail₂Ty
        cases hTail₂Ty
      rw [listConcatRecConsOfRightNeStuck op x xs z₂ hZ₂Ne,
        mkApplyEqApplyOfArgsNeStuck _ _ (by simp [op]) hTail₂Ne]
      change __eo_typeof_bvand (__eo_typeof x)
        (__eo_typeof (__eo_list_concat_rec xs z₂)) = _
      rw [hParts.1, hTail₂Ty]
      have hWidthNe : width ≠ Term.Stuck := by
        intro h
        subst width
        change __eo_typeof_bvand (__eo_typeof x)
          (__eo_typeof (__eo_list_concat_rec xs z)) =
            Term.Apply (Term.UOp UserOp.BitVec) Term.Stuck at hFirstTy
        rw [hParts.1, hParts.2] at hFirstTy
        simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
          native_teq, native_not] at hFirstTy
      simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
        native_teq, native_not, hWidthNe]
  | case4 nil z hNil hZ hNot =>
      have hEq : __eo_list_concat_rec nil z₂ = z₂ := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      simpa [hEq] using hZ₂Ty

theorem listSingletonElimEoType
    (c width : Term) :
    __eo_is_list op c = Term.Boolean true ->
    __eo_typeof c = Term.Apply (Term.UOp UserOp.BitVec) width ->
    __eo_typeof (__eo_list_singleton_elim op c) =
      Term.Apply (Term.UOp UserOp.BitVec) width := by
  intro hList hTy
  change __eo_typeof
      (__eo_requires (__eo_is_list op c) (Term.Boolean true)
        (__eo_list_singleton_elim_2 c)) = _
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg := eo_is_list_cons_head_eq_of_true op g head tail hList
          subst g
          have hParts := addArgsOfEoBitvecType head tail width
            (by simpa [add, op] using hTy)
          have hTailList := eo_is_list_tail_true_of_cons_self op head tail hList
          have hTailNe := isListTrueNeStuck hTailList
          rcases isListNilBooleanOfNeStuck tail hTailNe with ⟨b, hNil⟩
          cases b <;>
            simp [__eo_list_singleton_elim_2, hNil, __eo_ite,
              native_ite, native_teq, hParts.1, hTy]
      | _ => simpa [__eo_list_singleton_elim_2] using hTy
  | _ => simpa [__eo_list_singleton_elim_2] using hTy

theorem listSmtTypeOrNilOfConcatType
    (a z : Term) (W : native_Int) :
    RuleProofs.eo_has_smt_translation a ->
    __eo_is_list op a = Term.Boolean true ->
    z ≠ Term.Stuck ->
    __eo_typeof (__eo_list_concat_rec a z) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ->
    native_zleq 0 W = true ->
    ListTypeOrNil a (native_int_to_nat W) := by
  intro hATrans hAList hZNe hConcatTy hW0
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z => simp [op, __eo_is_list] at hAList
  | case2 a hA => exact False.elim (hZNe rfl)
  | case3 f x xs z hz ih =>
      have hf := eo_is_list_cons_head_eq_of_true op f x xs hAList
      subst f
      have hTailNe : __eo_list_concat_rec xs z ≠ Term.Stuck := by
        intro hTail
        rw [listConcatRecConsOfRightNeStuck op x xs z hz,
          hTail, mkApplyRightStuck] at hConcatTy
        cases hConcatTy
      rw [listConcatRecConsOfRightNeStuck op x xs z hz,
        mkApplyEqApplyOfArgsNeStuck _ _ (by simp [op]) hTailNe]
        at hConcatTy
      have hXTypeof :=
        (addArgsOfEoBitvecType x
          (__eo_list_concat_rec xs z) (Term.Numeral W)
          (by simpa [add, op] using hConcatTy)).1
      have hNonNone :
          __smtx_typeof (__eo_to_smt x) =
            SmtType.BitVec (native_int_to_nat W) := by
        have hExpected :=
          RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
            x (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W))
              (__eo_to_smt x) rfl
              (by
                intro hNone
                apply hATrans
                change __smtx_typeof
                    (SmtTerm.bvadd (__eo_to_smt x) (__eo_to_smt xs)) =
                  SmtType.None
                rw [__smtx_typeof.eq_def] <;> simp only
                simp [__smtx_typeof_bv_op_2, hNone, native_ite])
              hXTypeof
        simpa [__eo_to_smt_type, hW0, native_ite] using hExpected
      apply Or.inl
      change __smtx_typeof
          (SmtTerm.bvadd (__eo_to_smt x) (__eo_to_smt xs)) = _
      rw [__smtx_typeof.eq_def] <;> simp only
      have hXsExpected :
          __smtx_typeof (__eo_to_smt xs) =
            SmtType.BitVec (native_int_to_nat W) := by
        have hWhole :
            __smtx_typeof
                (SmtTerm.bvadd (__eo_to_smt x) (__eo_to_smt xs)) ≠
              SmtType.None := by
          intro hNone
          exact hATrans hNone
        rcases bv_binop_args_of_non_none (op := SmtTerm.bvadd)
            (show
              __smtx_typeof
                  (SmtTerm.bvadd (__eo_to_smt x) (__eo_to_smt xs)) =
                __smtx_typeof_bv_op_2
                  (__smtx_typeof (__eo_to_smt x))
                  (__smtx_typeof (__eo_to_smt xs)) by
              rw [__smtx_typeof.eq_def] <;> simp only) hWhole with
          ⟨w, hXTy, hXsTy⟩
        rw [hNonNone] at hXTy
        cases hXTy
        exact hXsTy
      simp [__smtx_typeof_bv_op_2, hNonNone, hXsExpected,
        native_nateq, native_ite]
  | case4 nil z hNil hZ hNot =>
      apply Or.inr
      intro tail
      unfold __eo_list_concat_rec
      split <;> simp_all

end BvNaryAddSupport
