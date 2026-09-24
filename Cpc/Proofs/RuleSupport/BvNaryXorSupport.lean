module

public import Cpc.Proofs.RuleSupport.BvCommutativeXorSupport
import all Cpc.Proofs.RuleSupport.BvCommutativeXorSupport
public import Cpc.Proofs.RuleSupport.BvExtractRewriteSupport
import all Cpc.Proofs.RuleSupport.BvExtractRewriteSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport

public section

/-! Shared typing and evaluation support for n-ary bit-vector XOR lists. -/

open Eo
open SmtEval
open Smtm

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvNaryXorSupport

private abbrev xor (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x) y

private theorem term_ne_stuck_of_smt_bitvec_type
    {t : Term} {w : native_Nat} :
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    t ≠ Term.Stuck := by
  intro hTy hStuck
  subst t
  change __smtx_typeof SmtTerm.None = SmtType.BitVec w at hTy
  rw [TranslationProofs.smtx_typeof_none] at hTy
  cases hTy

private theorem bvxor_args_of_bitvec_type (y x : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt (xor y x)) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.bvxor (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.BitVec w := by
    simpa [xor] using hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.bvxor (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hTy']
    intro h
    cases h
  rcases bv_binop_args_of_non_none (op := SmtTerm.bvxor)
      (show
        __smtx_typeof (SmtTerm.bvxor (__eo_to_smt y) (__eo_to_smt x)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt y))
            (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_44]) hNN with
    ⟨w', hyTy, hxTy⟩
  have hWidth : w' = w := by
    have hResult : SmtType.BitVec w' = SmtType.BitVec w := by
      rw [show
          __smtx_typeof (SmtTerm.bvxor (__eo_to_smt y) (__eo_to_smt x)) =
            __smtx_typeof_bv_op_2
              (__smtx_typeof (__eo_to_smt y))
              (__smtx_typeof (__eo_to_smt x)) by
          rw [__smtx_typeof.eq_44]] at hTy'
      simpa [__smtx_typeof_bv_op_2, hyTy, hxTy, native_ite, native_nateq,
        Smtm.native_nateq] using hTy'
    cases hResult
    rfl
  subst w'
  exact ⟨hyTy, hxTy⟩

private theorem native_int_pow2_nat (w : Nat) :
    native_int_pow2 (native_nat_to_int w) = (2 ^ w : Int) := by
  have h : ¬ (↑w : Int) < 0 := by simp
  simp [native_int_pow2, native_zexp_total, native_nat_to_int, h]

private theorem bitvec_toInt_emod_pow (w : Nat) (x : BitVec w) :
    x.toInt % (2 ^ w : Int) = x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond]
  by_cases h : 2 * x.toNat < 2 ^ w
  · simp [h]
    exact Int.emod_eq_of_lt (by exact Int.natCast_nonneg _)
      (by exact_mod_cast x.isLt)
  · simp [h]
    exact Int.emod_eq_of_lt (by exact Int.natCast_nonneg _)
      (by exact_mod_cast x.isLt)

private theorem native_mod_pow2_eq_bitvec_toNat (w : Nat) (n : Int) :
    native_mod_total n (native_int_pow2 (native_nat_to_int w)) =
      ((BitVec.ofInt w n).toNat : Int) := by
  rw [native_int_pow2_nat]
  change n % (2 ^ w : Int) = ((BitVec.ofInt w n).toNat : Int)
  rw [BitVec.toNat_ofInt]
  have hpow : 0 < (2 ^ w : Int) := by
    exact_mod_cast Nat.two_pow_pos w
  exact (Int.toNat_of_nonneg (Int.emod_nonneg n (Int.ne_of_gt hpow))).symm

private theorem native_binary_xor_mod_eq_toNat
    (w : Nat) (n1 n2 : Int) :
    native_mod_total (native_binary_xor (native_nat_to_int w) n1 n2)
        (native_int_pow2 (native_nat_to_int w)) =
      ((BitVec.ofInt w n1 ^^^ BitVec.ofInt w n2).toNat : Int) := by
  cases w with
  | zero =>
      simp [native_binary_xor, impl_native_pixor, native_mod_total,
        native_int_pow2_nat]
  | succ w =>
      simp [native_binary_xor, impl_native_pixor, native_mod_total,
        native_nat_to_int, native_ite, native_zeq]
      exact bitvec_toInt_emod_pow (Nat.succ w)
        (BitVec.ofInt (Nat.succ w) n1 ^^^ BitVec.ofInt (Nat.succ w) n2)

private theorem native_binary_xor_right_zero_mod_nat
    (w : Nat) (n : Int) :
    native_mod_total (native_binary_xor (native_nat_to_int w) n 0)
        (native_int_pow2 (native_nat_to_int w)) =
      native_mod_total n (native_int_pow2 (native_nat_to_int w)) := by
  rw [native_binary_xor_mod_eq_toNat, native_mod_pow2_eq_bitvec_toNat]
  simp

private theorem native_binary_xor_left_zero_mod_nat
    (w : Nat) (n : Int) :
    native_mod_total (native_binary_xor (native_nat_to_int w) 0 n)
        (native_int_pow2 (native_nat_to_int w)) =
      native_mod_total n (native_int_pow2 (native_nat_to_int w)) := by
  rw [native_binary_xor_mod_eq_toNat, native_mod_pow2_eq_bitvec_toNat]
  simp

private theorem native_binary_xor_assoc_mod_nat
    (w : Nat) (n1 n2 n3 : Int) :
    native_mod_total
        (native_binary_xor (native_nat_to_int w)
          (native_mod_total (native_binary_xor (native_nat_to_int w) n1 n2)
            (native_int_pow2 (native_nat_to_int w))) n3)
        (native_int_pow2 (native_nat_to_int w)) =
      native_mod_total
        (native_binary_xor (native_nat_to_int w) n1
          (native_mod_total (native_binary_xor (native_nat_to_int w) n2 n3)
            (native_int_pow2 (native_nat_to_int w))))
        (native_int_pow2 (native_nat_to_int w)) := by
  have h12 :
      BitVec.ofInt w
          (native_mod_total (native_binary_xor (native_nat_to_int w) n1 n2)
            (native_int_pow2 (native_nat_to_int w))) =
        BitVec.ofInt w n1 ^^^ BitVec.ofInt w n2 := by
    rw [native_binary_xor_mod_eq_toNat]
    exact _root_.bitvec_ofInt_natCast_toNat _
  have h23 :
      BitVec.ofInt w
          (native_mod_total (native_binary_xor (native_nat_to_int w) n2 n3)
            (native_int_pow2 (native_nat_to_int w))) =
        BitVec.ofInt w n2 ^^^ BitVec.ofInt w n3 := by
    rw [native_binary_xor_mod_eq_toNat]
    exact _root_.bitvec_ofInt_natCast_toNat _
  calc
    native_mod_total
        (native_binary_xor (native_nat_to_int w)
          (native_mod_total (native_binary_xor (native_nat_to_int w) n1 n2)
            (native_int_pow2 (native_nat_to_int w))) n3)
        (native_int_pow2 (native_nat_to_int w)) =
      ((BitVec.ofInt w
          (native_mod_total (native_binary_xor (native_nat_to_int w) n1 n2)
            (native_int_pow2 (native_nat_to_int w))) ^^^
        BitVec.ofInt w n3).toNat : Int) := by
          rw [native_binary_xor_mod_eq_toNat]
    _ = (((BitVec.ofInt w n1 ^^^ BitVec.ofInt w n2) ^^^
          BitVec.ofInt w n3).toNat : Int) := by
          rw [h12]
    _ = ((BitVec.ofInt w n1 ^^^ (BitVec.ofInt w n2 ^^^
          BitVec.ofInt w n3)).toNat : Int) := by
          rw [BitVec.xor_assoc]
    _ =
      ((BitVec.ofInt w n1 ^^^
        BitVec.ofInt w
          (native_mod_total (native_binary_xor (native_nat_to_int w) n2 n3)
            (native_int_pow2 (native_nat_to_int w)))).toNat : Int) := by
          rw [h23]
    _ =
      native_mod_total
        (native_binary_xor (native_nat_to_int w) n1
          (native_mod_total (native_binary_xor (native_nat_to_int w) n2 n3)
            (native_int_pow2 (native_nat_to_int w))))
        (native_int_pow2 (native_nat_to_int w)) := by
          symm
          rw [native_binary_xor_mod_eq_toNat]

private def EvalCanonical (M : SmtModel) (w : Nat) (t : Term) : Prop :=
  ∃ n,
    __smtx_model_eval M (__eo_to_smt t) =
        SmtValue.Binary (native_nat_to_int w) n ∧
      native_zeq n
          (native_mod_total n (native_int_pow2 (native_nat_to_int w))) =
        true

private theorem evalCanonical_of_smt_type
    (M : SmtModel) (hM : model_wf M) (t : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    EvalCanonical M w t := by
  intro hTy
  exact _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt t) w hTy

private theorem xor_eval_canonical
    (M : SmtModel) (x y : Term) (w : Nat) :
    EvalCanonical M w x ->
    EvalCanonical M w y ->
    EvalCanonical M w (xor x y) := by
  intro hx hy
  rcases hx with ⟨nx, hxEval, _hxMod⟩
  rcases hy with ⟨ny, hyEval, _hyMod⟩
  refine ⟨
    native_mod_total
      (native_binary_xor (native_nat_to_int w) nx ny)
      (native_int_pow2 (native_nat_to_int w)), ?_, ?_⟩
  · change __smtx_model_eval M
        (SmtTerm.bvxor (__eo_to_smt x) (__eo_to_smt y)) =
      SmtValue.Binary (native_nat_to_int w)
        (native_mod_total
          (native_binary_xor (native_nat_to_int w) nx ny)
          (native_int_pow2 (native_nat_to_int w)))
    simp [__smtx_model_eval, __smtx_model_eval_bvxor, hxEval, hyEval]
  · exact native_mod_total_canonical (native_nat_to_int w)
      (native_binary_xor (native_nat_to_int w) nx ny)

private def ListCanonical (M : SmtModel) (w : Nat) : Term -> Prop
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x) xs =>
      EvalCanonical M w x ∧ ListCanonical M w xs
  | t => EvalCanonical M w t

private theorem listCanonical_eval
    (M : SmtModel) (w : Nat) :
    (t : Term) -> ListCanonical M w t -> EvalCanonical M w t
  | t, h => by
      cases t with
      | Apply f xs =>
          cases f with
          | Apply g x =>
              cases g with
              | UOp op =>
                  cases op
                  case bvxor =>
                    exact xor_eval_canonical M x xs w h.1
                      (listCanonical_eval M w xs h.2)
                  all_goals
                    simpa [ListCanonical] using h
              | _ =>
                  simpa [ListCanonical] using h
          | _ =>
              simpa [ListCanonical] using h
      | _ =>
          simpa [ListCanonical] using h

private theorem listCanonical_of_smt_type
    (M : SmtModel) (hM : model_wf M) (w : Nat) :
    (t : Term) ->
    __eo_is_list (Term.UOp UserOp.bvxor) t = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    ListCanonical M w t
  | t, hList, hTy => by
      induction t using __eo_get_elements_rec.induct with
      | case1 =>
          simp [__eo_is_list] at hList
      | case2 f x xs ih =>
          have hf : f = Term.UOp UserOp.bvxor :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.bvxor) f x xs hList
          subst f
          have hXsList :
              __eo_is_list (Term.UOp UserOp.bvxor) xs =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.bvxor) x xs hList
          have hArgs := bvxor_args_of_bitvec_type x xs w (by
            simpa [xor] using hTy)
          exact ⟨
            evalCanonical_of_smt_type M hM x w hArgs.1,
            ih hXsList hArgs.2⟩
      | case3 t _hNil hNot =>
          cases t with
          | Apply f xs =>
              cases f with
              | Apply g x =>
                  exact False.elim (hNot g x xs rfl)
              | _ =>
                  simpa [ListCanonical] using
                    evalCanonical_of_smt_type M hM _ w hTy
          | _ =>
              simpa [ListCanonical] using
                evalCanonical_of_smt_type M hM _ w hTy

private theorem is_list_true_ne_stuck {t : Term} :
    __eo_is_list (Term.UOp UserOp.bvxor) t = Term.Boolean true ->
    t ≠ Term.Stuck := by
  intro hList hStuck
  subst t
  simp [__eo_is_list] at hList

private theorem is_list_nil_boolean_of_ne_stuck (t : Term) :
    t ≠ Term.Stuck ->
    ∃ b, __eo_is_list_nil (Term.UOp UserOp.bvxor) t = Term.Boolean b := by
  intro hNe
  cases t <;>
    simp [__eo_is_list_nil, __eo_is_list_nil_bvxor, __eo_to_z,
      __eo_is_eq, native_and, native_not, native_teq, native_zeq] at hNe ⊢

private theorem nil_payload_eq_zero
    (M : SmtModel) (nil : Term) (w : Nat) (n : Int) :
    __eo_is_list_nil (Term.UOp UserOp.bvxor) nil = Term.Boolean true ->
    __smtx_model_eval M (__eo_to_smt nil) =
      SmtValue.Binary (native_nat_to_int w) n ->
    n = 0 := by
  intro hNilTrue hNilEval
  cases nil <;>
    simp [__eo_is_list_nil, __eo_is_list_nil_bvxor, __eo_to_z,
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
    have hEvalEq :
        SmtValue.Binary wb nb =
          SmtValue.Binary (native_nat_to_int w) n := by
      rw [show __eo_to_smt (Term.Binary wb nb) =
          SmtTerm.Binary wb nb by rfl] at hNilEval
      rw [__smtx_model_eval] at hNilEval
      exact hNilEval
    injection hEvalEq with hWidthEq hPayloadEq
    subst wb
    subst n
    exact hNilTrue.symm

private theorem eval_xor_right_zero
    (M : SmtModel) (x nil : Term) (w : Nat) (nx : Int) :
    __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (native_nat_to_int w) nx ->
    __smtx_model_eval M (__eo_to_smt nil) =
        SmtValue.Binary (native_nat_to_int w) 0 ->
    native_zeq nx
        (native_mod_total nx (native_int_pow2 (native_nat_to_int w))) =
      true ->
    __smtx_model_eval M (__eo_to_smt (xor x nil)) =
      __smtx_model_eval M (__eo_to_smt x) := by
  intro hxEval hNilEval hxMod
  have hModEq :
      native_mod_total nx (native_int_pow2 (native_nat_to_int w)) = nx := by
    have hEq :
        nx = native_mod_total nx
          (native_int_pow2 (native_nat_to_int w)) := by
      simpa [native_zeq] using hxMod
    exact hEq.symm
  change __smtx_model_eval M
      (SmtTerm.bvxor (__eo_to_smt x) (__eo_to_smt nil)) =
    __smtx_model_eval M (__eo_to_smt x)
  simp only [__smtx_model_eval, __smtx_model_eval_bvxor, hxEval, hNilEval]
  rw [native_binary_xor_right_zero_mod_nat w nx, hModEq]

private theorem eval_xor_left_zero
    (M : SmtModel) (nil x : Term) (w : Nat) (nx : Int) :
    __smtx_model_eval M (__eo_to_smt nil) =
        SmtValue.Binary (native_nat_to_int w) 0 ->
    __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (native_nat_to_int w) nx ->
    native_zeq nx
        (native_mod_total nx (native_int_pow2 (native_nat_to_int w))) =
      true ->
    __smtx_model_eval M (__eo_to_smt (xor nil x)) =
      __smtx_model_eval M (__eo_to_smt x) := by
  intro hNilEval hxEval hxMod
  have hModEq :
      native_mod_total nx (native_int_pow2 (native_nat_to_int w)) = nx := by
    have hEq :
        nx = native_mod_total nx
          (native_int_pow2 (native_nat_to_int w)) := by
      simpa [native_zeq] using hxMod
    exact hEq.symm
  change __smtx_model_eval M
      (SmtTerm.bvxor (__eo_to_smt nil) (__eo_to_smt x)) =
    __smtx_model_eval M (__eo_to_smt x)
  simp only [__smtx_model_eval, __smtx_model_eval_bvxor, hNilEval, hxEval]
  rw [native_binary_xor_left_zero_mod_nat w nx, hModEq]

private theorem eval_xor_assoc
    (M : SmtModel) (x y z : Term) (w : Nat) (nx ny nz : Int) :
    __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (native_nat_to_int w) nx ->
    __smtx_model_eval M (__eo_to_smt y) =
        SmtValue.Binary (native_nat_to_int w) ny ->
    __smtx_model_eval M (__eo_to_smt z) =
        SmtValue.Binary (native_nat_to_int w) nz ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x) y)) z)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y) z))) := by
  intro hxEval hyEval hzEval
  change __smtx_model_eval M
      (SmtTerm.bvxor
        (SmtTerm.bvxor (__eo_to_smt x) (__eo_to_smt y))
        (__eo_to_smt z)) =
    __smtx_model_eval M
      (SmtTerm.bvxor (__eo_to_smt x)
        (SmtTerm.bvxor (__eo_to_smt y) (__eo_to_smt z)))
  simp only [__smtx_model_eval, __smtx_model_eval_bvxor, hxEval, hyEval,
    hzEval]
  rw [native_binary_xor_assoc_mod_nat]

/-- Concatenating two well-typed n-ary XOR lists preserves their common
    bit-vector type. -/
theorem listConcatRecSmtType
    (a z : Term) (w : Nat) :
    __eo_is_list (Term.UOp UserOp.bvxor) a = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) z = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) =
      SmtType.BitVec w := by
  intro hAList hZList hATy hZTy
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      simp [__eo_is_list] at hAList
  | case2 a hA =>
      simp [__eo_is_list] at hZList
  | case3 f x xs z hZNe ih =>
      have hf : f = Term.UOp UserOp.bvxor :=
        eo_is_list_cons_head_eq_of_true
          (Term.UOp UserOp.bvxor) f x xs hAList
      subst f
      have hXsList :
          __eo_is_list (Term.UOp UserOp.bvxor) xs = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self
          (Term.UOp UserOp.bvxor) x xs hAList
      have hArgs := bvxor_args_of_bitvec_type x xs w (by
        simpa [xor] using hATy)
      have hTailTy := ih hXsList hZList hArgs.2 hZTy
      have hTailNe : __eo_list_concat_rec xs z ≠ Term.Stuck :=
        term_ne_stuck_of_smt_bitvec_type hTailTy
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck
        (Term.UOp UserOp.bvxor) x xs z hTailNe]
      change __smtx_typeof
          (SmtTerm.bvxor (__eo_to_smt x)
            (__eo_to_smt (__eo_list_concat_rec xs z))) =
        SmtType.BitVec w
      rw [__smtx_typeof.eq_44]
      simp [__smtx_typeof_bv_op_2, hArgs.1, hTailTy,
        native_nateq, native_ite]
  | case4 nil z hNil hZNe hNot =>
      have hNilTrue :
          __eo_is_list_nil (Term.UOp UserOp.bvxor) nil =
            Term.Boolean true := by
        have hGet :=
          eo_get_nil_rec_ne_stuck_of_is_list_true
            (Term.UOp UserOp.bvxor) nil hAList
        have hReq :
            __eo_requires
                (__eo_is_list_nil (Term.UOp UserOp.bvxor) nil)
                (Term.Boolean true) nil ≠ Term.Stuck := by
          simpa [__eo_get_nil_rec] using hGet
        exact eo_requires_eq_of_ne_stuck
          (__eo_is_list_nil (Term.UOp UserOp.bvxor) nil)
          (Term.Boolean true) nil hReq
      rw [show __eo_list_concat_rec nil z = z by
        cases nil <;> cases z <;>
          simp [__eo_is_list_nil, __eo_list_concat_rec] at hNilTrue ⊢]
      exact hZTy

/-- Removing the singleton-list wrapper from a well-typed n-ary XOR list
    preserves its bit-vector type. -/
theorem listSingletonElimSmtType
    (c : Term) (w : Nat) :
    __eo_is_list (Term.UOp UserOp.bvxor) c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w ->
    __smtx_typeof
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.bvxor) c)) =
      SmtType.BitVec w := by
  intro hList hTy
  change __smtx_typeof
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.bvxor) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))) =
    SmtType.BitVec w
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg : g = Term.UOp UserOp.bvxor :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.bvxor) g head tail hList
          subst g
          have hArgs := bvxor_args_of_bitvec_type head tail w (by
            simpa [xor] using hTy)
          have hTailList :
              __eo_is_list (Term.UOp UserOp.bvxor) tail =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.bvxor) head tail hList
          have hTailNe : tail ≠ Term.Stuck :=
            is_list_true_ne_stuck hTailList
          rcases is_list_nil_boolean_of_ne_stuck tail hTailNe with
            ⟨b, hNil⟩
          cases b <;>
            simp [__eo_list_singleton_elim_2, hNil, __eo_ite,
              native_ite, native_teq, hArgs.1, hTy]
          -- v4.33 leaves the folded `__eo_to_smt` application; `exact` still
          -- closes it by iota reduction.
          exact hTy
      | _ =>
          simpa [__eo_list_singleton_elim_2] using hTy
  | _ =>
      simpa [__eo_list_singleton_elim_2] using hTy

private theorem list_concat_rec_eval_eq_of_canonical
    (M : SmtModel) (w : Nat) :
    (a z : Term) ->
    __eo_is_list (Term.UOp UserOp.bvxor) a = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) z = Term.Boolean true ->
    ListCanonical M w a ->
    ListCanonical M w z ->
    __smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec a z)) =
      __smtx_model_eval M (__eo_to_smt (xor a z))
  | a, z, hAList, hZList, hACan, hZCan => by
      induction a, z using __eo_list_concat_rec.induct with
      | case1 z =>
          simp [__eo_is_list] at hAList
      | case2 a hA =>
          simp [__eo_is_list] at hZList
      | case3 g x y z hZNe ih =>
          have hg : g = Term.UOp UserOp.bvxor :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.bvxor) g x y hAList
          subst g
          have hYList :
              __eo_is_list (Term.UOp UserOp.bvxor) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.bvxor) x y hAList
          have hTailNe : __eo_list_concat_rec y z ≠ Term.Stuck :=
            eo_list_concat_rec_ne_stuck_of_list
              (Term.UOp UserOp.bvxor) y z hYList hZNe
          have hIH := ih hYList hZList hACan.2 hZCan
          rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck
            (Term.UOp UserOp.bvxor) x y z hTailNe]
          rcases hACan.1 with ⟨nx, hxEval, _hxMod⟩
          rcases listCanonical_eval M w y hACan.2 with
            ⟨ny, hyEval, _hyMod⟩
          rcases listCanonical_eval M w z hZCan with
            ⟨nz, hzEval, _hzMod⟩
          calc
            __smtx_model_eval M
                (__eo_to_smt (xor x (__eo_list_concat_rec y z))) =
              __smtx_model_eval M (__eo_to_smt (xor x (xor y z))) := by
                change __smtx_model_eval_bvxor
                    (__smtx_model_eval M (__eo_to_smt x))
                    (__smtx_model_eval M
                      (__eo_to_smt (__eo_list_concat_rec y z))) =
                  __smtx_model_eval_bvxor
                    (__smtx_model_eval M (__eo_to_smt x))
                    (__smtx_model_eval M (__eo_to_smt (xor y z)))
                rw [hIH]
            _ = __smtx_model_eval M
                (__eo_to_smt (xor (xor x y) z)) :=
              (eval_xor_assoc M x y z w nx ny nz hxEval hyEval hzEval).symm
      | case4 nil z hNil hZNe hNot =>
          have hNilTrue :
              __eo_is_list_nil (Term.UOp UserOp.bvxor) nil =
                Term.Boolean true := by
            have hGet :=
              eo_get_nil_rec_ne_stuck_of_is_list_true
                (Term.UOp UserOp.bvxor) nil hAList
            have hReq :
                __eo_requires
                    (__eo_is_list_nil (Term.UOp UserOp.bvxor) nil)
                    (Term.Boolean true) nil ≠ Term.Stuck := by
              simpa [__eo_get_nil_rec] using hGet
            exact eo_requires_eq_of_ne_stuck
              (__eo_is_list_nil (Term.UOp UserOp.bvxor) nil)
              (Term.Boolean true) nil hReq
          rcases listCanonical_eval M w nil hACan with
            ⟨nnil, hNilEval, _hNilMod⟩
          have hNilZero := nil_payload_eq_zero M nil w nnil
            hNilTrue hNilEval
          subst nnil
          rcases listCanonical_eval M w z hZCan with
            ⟨nz, hzEval, hzMod⟩
          rw [show __eo_list_concat_rec nil z = z by
            cases nil <;> cases z <;>
              simp [__eo_is_list_nil, __eo_list_concat_rec] at hNilTrue ⊢]
          exact (eval_xor_left_zero M nil z w nz
            hNilEval hzEval hzMod).symm

/-- Concatenating two well-typed n-ary XOR lists has the same model value as
    applying binary XOR to their aggregate values. -/
theorem listConcatRecEvalEq
    (M : SmtModel) (hM : model_wf M)
    (a z : Term) (w : Nat) :
    __eo_is_list (Term.UOp UserOp.bvxor) a = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) z = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec a z)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) z)) := by
  intro hAList hZList hATy hZTy
  exact list_concat_rec_eval_eq_of_canonical M w a z hAList hZList
    (listCanonical_of_smt_type M hM w a hAList hATy)
    (listCanonical_of_smt_type M hM w z hZList hZTy)

/-- Eliminating the singleton wrapper of a well-typed n-ary XOR list preserves
    its model value. -/
theorem listSingletonElimEvalEq
    (M : SmtModel) (hM : model_wf M)
    (c : Term) (w : Nat) :
    __eo_is_list (Term.UOp UserOp.bvxor) c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w ->
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.bvxor) c)) =
      __smtx_model_eval M (__eo_to_smt c) := by
  intro hList hTy
  have hCan := listCanonical_of_smt_type M hM w c hList hTy
  change __smtx_model_eval M
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.bvxor) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))) =
    __smtx_model_eval M (__eo_to_smt c)
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg : g = Term.UOp UserOp.bvxor :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.bvxor) g head tail hList
          subst g
          have hTailList :
              __eo_is_list (Term.UOp UserOp.bvxor) tail =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.bvxor) head tail hList
          have hTailNe : tail ≠ Term.Stuck :=
            is_list_true_ne_stuck hTailList
          rcases is_list_nil_boolean_of_ne_stuck tail hTailNe with
            ⟨b, hNil⟩
          simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite,
            native_teq]
          cases b
          · rfl
          · rcases hCan.1 with ⟨nhead, hHeadEval, hHeadMod⟩
            rcases listCanonical_eval M w tail hCan.2 with
              ⟨ntail, hTailEval, _hTailMod⟩
            have hTailZero := nil_payload_eq_zero M tail w ntail
              hNil hTailEval
            subst ntail
            exact (eval_xor_right_zero M head tail w nhead
              hHeadEval hTailEval hHeadMod).symm
      | _ =>
          simpa [__eo_list_singleton_elim_2]
  | _ =>
      simpa [__eo_list_singleton_elim_2]

theorem binaryArgsSmtType
    (x y : Term) (w : Nat) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x) y)) =
      SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w :=
  bvxor_args_of_bitvec_type x y w

theorem binarySmtType
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x) y)) =
      SmtType.BitVec w := by
  intro hX hY
  change __smtx_typeof
      (SmtTerm.bvxor (__eo_to_smt x) (__eo_to_smt y)) = _
  rw [__smtx_typeof.eq_44]
  simp [__smtx_typeof_bv_op_2, hX, hY, native_nateq, native_ite]

theorem evalAssoc
    (M : SmtModel) (hM : model_wf M)
    (x y z : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec w ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x) y)) z)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y) z))) := by
  intro hX hY hZ
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) w hX with
    ⟨nx, hXE, _⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt y) w hY with
    ⟨ny, hYE, _⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt z) w hZ with
    ⟨nz, hZE, _⟩
  exact eval_xor_assoc M x y z w nx ny nz hXE hYE hZE

theorem evalComm
    (M : SmtModel) (hM : model_wf M)
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x) y)) =
      __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y) x)) := by
  intro hX hY
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) w hX with
    ⟨nx, hXE, _⟩
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt y) w hY with
    ⟨ny, hYE, _⟩
  change __smtx_model_eval_bvxor
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) =
    __smtx_model_eval_bvxor
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt x))
  rw [hXE, hYE]
  simp [__smtx_model_eval_bvxor, native_binary_xor, impl_native_pixor,
    BitVec.xor_comm]

theorem evalRightNil
    (M : SmtModel) (hM : model_wf M)
    (x nil : Term) (w : Nat) :
    __eo_is_list_nil (Term.UOp UserOp.bvxor) nil = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt nil) = SmtType.BitVec w ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x) nil)) =
      __smtx_model_eval M (__eo_to_smt x) := by
  intro hNil hXTy hNilTy
  rcases evalCanonical_of_smt_type M hM x w hXTy with
    ⟨nx, hXEval, hXMod⟩
  rcases evalCanonical_of_smt_type M hM nil w hNilTy with
    ⟨nnil, hNilEval, _hNilMod⟩
  have hZero := nil_payload_eq_zero M nil w nnil hNil hNilEval
  subst nnil
  exact eval_xor_right_zero M x nil w nx hXEval hNilEval hXMod

end BvNaryXorSupport
