module

public import Cpc.Proofs.RuleSupport.BvAbstractionFullSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionFullSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionDslSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionEvalSupport
public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8000

open Eo SmtEval Smtm

namespace BvAbstraction
namespace Matcher

theorem bv_bitwidth_ne_stuck_shape {T : Term} :
    __bv_bitwidth T ≠ Term.Stuck ->
    ∃ n, T = Term.Apply (Term.UOp UserOp.BitVec) n := by
  intro h
  cases T <;> try (exfalso; apply h; rfl)
  case Apply f n =>
    cases f <;> try (exfalso; apply h; rfl)
    case UOp op =>
      cases op <;> try (exfalso; apply h; rfl)
      exact ⟨n, rfl⟩

theorem eo_to_bin_width_ne_stuck {w n : Term} :
    __eo_to_bin w n ≠ Term.Stuck -> w ≠ Term.Stuck := by
  intro h hw
  rw [hw] at h
  cases n <;> simp [__eo_to_bin] at h

theorem validated_to_bin_literal {c : Term} {w : Nat} {k : Int}
    (hTy : __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w)
    (h : __eo_eq c
      (__eo_to_bin (__bv_bitwidth (__eo_typeof c)) (Term.Numeral k)) =
        Term.Boolean true) :
    c = Term.Binary (native_nat_to_int w)
      (native_mod_total k (native_int_pow2 (native_nat_to_int w))) := by
  let gen := __eo_to_bin (__bv_bitwidth (__eo_typeof c)) (Term.Numeral k)
  have hGenEq : gen = c := support_eq_of_eo_eq_true c gen h
  have hcNe : c ≠ Term.Stuck := by
    intro hc
    rw [hc] at h
    simp [__eo_eq] at h
  have hGenNe : gen ≠ Term.Stuck := by rw [hGenEq]; exact hcNe
  have hBwNe : __bv_bitwidth (__eo_typeof c) ≠ Term.Stuck :=
    eo_to_bin_width_ne_stuck hGenNe
  rcases bv_bitwidth_ne_stuck_shape hBwNe with ⟨n, hEoTy⟩
  have hTransTy :
      __eo_to_smt_type (__eo_typeof c) = __smtx_typeof (__eo_to_smt c) :=
    TranslationProofs.eo_to_smt_type_typeof_of_smt_type c rfl (by
      rw [hTy]
      simp)
  rw [hEoTy, hTy] at hTransTy
  have hn : n = Term.Numeral (native_nat_to_int w) := by
    cases n <;> simp [__eo_to_smt_type, native_ite, native_zleq] at hTransTy
    case Numeral i =>
      have hi : 0 ≤ i := by
        by_cases hi : 0 ≤ i
        · exact hi
        · simp [hi] at hTransTy
      simp [hi] at hTransTy
      cases hTransTy
      congr 1
      exact (Int.toNat_of_nonneg hi).symm
  dsimp [gen] at hGenEq hGenNe
  rw [hEoTy, hn] at hGenEq
  have hGenNe' : __eo_to_bin (Term.Numeral (native_nat_to_int w))
      (Term.Numeral k) ≠ Term.Stuck := by
    simpa [hEoTy, hn, gen, __bv_bitwidth] using hGenNe
  have hwLe : native_nat_to_int w ≤ 4294967296 := by
    by_cases hwLe : native_nat_to_int w ≤ 4294967296
    · exact hwLe
    · simp [__eo_to_bin, native_ite, native_zleq, hwLe] at hGenNe'
  simp [__bv_bitwidth, __eo_to_bin, __eo_mk_binary, native_ite, native_zleq,
    hwLe, native_mod_total] at hGenEq
  exact hGenEq.symm

theorem validated_zero {c : Term} {w : Nat}
    (hTy : __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w)
    (h : __eo_eq c
      (__eo_to_bin (__bv_bitwidth (__eo_typeof c)) (Term.Numeral 0)) =
        Term.Boolean true) :
    c = Dsl.constTerm w 0 := by
  simpa [Dsl.constTerm, native_mod_total] using validated_to_bin_literal hTy h

theorem validated_one {c : Term} {w : Nat} (hw : 0 < w)
    (hTy : __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w)
    (h : __eo_eq c
      (__eo_to_bin (__bv_bitwidth (__eo_typeof c)) (Term.Numeral 1)) =
        Term.Boolean true) :
    c = Dsl.constTerm w 1 := by
  have hp : (1 : Int) < (2 : Int) ^ w := by
    exact_mod_cast Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  simpa [Dsl.constTerm, native_mod_total, native_int_pow2_nat,
    Int.emod_eq_of_lt (by omega) hp] using validated_to_bin_literal hTy h

def allOnesGenerator (c : Term) : Term :=
  let width := __bv_bitwidth (__eo_typeof c)
  __eo_to_bin width
    (__eo_add
      (__eo_ite (__eo_is_z width)
        (__eo_ite (__eo_is_neg width) (Term.Numeral 0)
          (__eo_pow (Term.Numeral 2) width))
        (__eo_mk_apply (Term.UOp UserOp.int_pow2) width))
      (Term.Numeral (-1)))

theorem validated_width_type {c n : Term} {w : Nat}
    (hTy : __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w)
    (h : __eo_eq c (__eo_to_bin (__bv_bitwidth (__eo_typeof c)) n) =
      Term.Boolean true) :
    __eo_typeof c = Term.Apply (Term.UOp UserOp.BitVec)
      (Term.Numeral (native_nat_to_int w)) := by
  let gen := __eo_to_bin (__bv_bitwidth (__eo_typeof c)) n
  have hGenEq : gen = c := support_eq_of_eo_eq_true c gen h
  have hcNe : c ≠ Term.Stuck := by
    intro hc
    rw [hc] at h
    simp [__eo_eq] at h
  have hGenNe : gen ≠ Term.Stuck := by rw [hGenEq]; exact hcNe
  have hBwNe : __bv_bitwidth (__eo_typeof c) ≠ Term.Stuck :=
    eo_to_bin_width_ne_stuck hGenNe
  rcases bv_bitwidth_ne_stuck_shape hBwNe with ⟨width, hEoTy⟩
  have hTransTy :
      __eo_to_smt_type (__eo_typeof c) = __smtx_typeof (__eo_to_smt c) :=
    TranslationProofs.eo_to_smt_type_typeof_of_smt_type c rfl (by
      rw [hTy]
      simp)
  rw [hEoTy, hTy] at hTransTy
  have hn : width = Term.Numeral (native_nat_to_int w) := by
    cases width <;>
      simp [__eo_to_smt_type, native_ite, native_zleq] at hTransTy
    case Numeral i =>
      have hi : 0 ≤ i := by
        by_cases hi : 0 ≤ i
        · exact hi
        · simp [hi] at hTransTy
      simp [hi] at hTransTy
      cases hTransTy
      congr 1
      exact (Int.toNat_of_nonneg hi).symm
  rw [hEoTy, hn]

theorem validated_ones {c : Term} {w : Nat}
    (hTy : __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w)
    (h : __eo_eq c (allOnesGenerator c) = Term.Boolean true) :
    c = Dsl.constTerm w ((2 : Int) ^ w - 1) := by
  have hRaw : __eo_eq c
      (__eo_to_bin (__bv_bitwidth (__eo_typeof c))
        (__eo_add
          (__eo_ite (__eo_is_z (__bv_bitwidth (__eo_typeof c)))
            (__eo_ite (__eo_is_neg (__bv_bitwidth (__eo_typeof c)))
              (Term.Numeral 0)
              (__eo_pow (Term.Numeral 2) (__bv_bitwidth (__eo_typeof c))))
            (__eo_mk_apply (Term.UOp UserOp.int_pow2)
              (__bv_bitwidth (__eo_typeof c))))
          (Term.Numeral (-1)))) = Term.Boolean true := by
    simpa [allOnesGenerator] using h
  have hType := validated_width_type hTy hRaw
  have hwNonneg : ¬((w : Int) < 0) :=
    Int.not_lt_of_ge (Int.natCast_nonneg w)
  have hLit : __eo_eq c
      (__eo_to_bin (__bv_bitwidth (__eo_typeof c))
        (Term.Numeral ((2 : Int) ^ w - 1))) = Term.Boolean true := by
    simpa [hType, __bv_bitwidth, __eo_is_z, __eo_is_z_internal,
      __eo_is_neg, __eo_pow, __eo_add, native_ite, native_teq, native_zlt,
      native_and, native_not, native_zexp_total, native_zplus,
      SmtEval.native_nat_to_int, hwNonneg, Int.sub_eq_add_neg] using hRaw
  have hResult := validated_to_bin_literal hTy hLit
  have hp : (0 : Int) < (2 : Int) ^ w := by
    exact_mod_cast Nat.two_pow_pos w
  have hk0 : 0 ≤ (2 : Int) ^ w - 1 := by omega
  have hklt : (2 : Int) ^ w - 1 < (2 : Int) ^ w := by omega
  simpa [Dsl.constTerm, native_mod_total, native_int_pow2_nat,
    Int.emod_eq_of_lt hk0 hklt] using hResult

theorem eo_and_eq_true_args (a b : Term) :
    __eo_and a b = Term.Boolean true ->
      a = Term.Boolean true ∧ b = Term.Boolean true := by
  intro h
  cases a <;> cases b <;>
    simp [__eo_and, __eo_requires, native_ite, native_teq,
      native_not, SmtEval.native_not, native_and, SmtEval.native_and]
      at h ⊢
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hW : w1 = w2
    · subst w2
      simp at h
    · have hNumNe : Term.Numeral w1 ≠ Term.Numeral w2 := by
        intro hEq
        cases hEq
        exact hW rfl
      simp [hW] at h

theorem eo_ite_eq_true_cases (c a b : Term) :
    __eo_ite c a b = Term.Boolean true ->
      (c = Term.Boolean true ∧ a = Term.Boolean true) ∨
      (c = Term.Boolean false ∧ b = Term.Boolean true) := by
  intro h
  cases c <;> simp [__eo_ite, native_teq, native_ite] at h ⊢
  case Boolean q => cases q <;> simp_all

theorem and_true3 (a b c : Term) :
    __eo_and (__eo_and a b) c = Term.Boolean true ->
      a = Term.Boolean true ∧ b = Term.Boolean true ∧ c = Term.Boolean true := by
  intro h
  rcases eo_and_eq_true_args _ _ h with ⟨hab, hc⟩
  rcases eo_and_eq_true_args _ _ hab with ⟨ha, hb⟩
  exact ⟨ha, hb, hc⟩

theorem and_true4 (a b c d : Term) :
    __eo_and (__eo_and (__eo_and a b) c) d = Term.Boolean true ->
      a = Term.Boolean true ∧ b = Term.Boolean true ∧
      c = Term.Boolean true ∧ d = Term.Boolean true := by
  intro h
  rcases eo_and_eq_true_args _ _ h with ⟨habc, hd⟩
  rcases and_true3 a b c habc with ⟨ha, hb, hc⟩
  exact ⟨ha, hb, hc, hd⟩

theorem and_true3r (a b c : Term) :
    __eo_and a (__eo_and b c) = Term.Boolean true ->
      a = Term.Boolean true ∧ b = Term.Boolean true ∧ c = Term.Boolean true := by
  intro h
  rcases eo_and_eq_true_args _ _ h with ⟨ha, hbc⟩
  rcases eo_and_eq_true_args _ _ hbc with ⟨hb, hc⟩
  exact ⟨ha, hb, hc⟩

theorem and_true4r (a b c d : Term) :
    __eo_and a (__eo_and b (__eo_and c d)) = Term.Boolean true ->
      a = Term.Boolean true ∧ b = Term.Boolean true ∧
      c = Term.Boolean true ∧ d = Term.Boolean true := by
  intro h
  rcases eo_and_eq_true_args _ _ h with ⟨ha, hbcd⟩
  rcases and_true3r b c d hbcd with ⟨hb, hc, hd⟩
  exact ⟨ha, hb, hc, hd⟩

theorem and_true5 (a b c d e : Term) :
    __eo_and (__eo_and (__eo_and (__eo_and a b) c) d) e =
      Term.Boolean true ->
      a = Term.Boolean true ∧ b = Term.Boolean true ∧
      c = Term.Boolean true ∧ d = Term.Boolean true ∧
      e = Term.Boolean true := by
  intro h
  rcases eo_and_eq_true_args _ _ h with ⟨habcd, he⟩
  rcases and_true4 a b c d habcd with ⟨ha, hb, hc, hd⟩
  exact ⟨ha, hb, hc, hd, he⟩

theorem and_true6 (a b c d e f : Term) :
    __eo_and (__eo_and (__eo_and (__eo_and (__eo_and a b) c) d) e) f =
      Term.Boolean true ->
      a = Term.Boolean true ∧ b = Term.Boolean true ∧
      c = Term.Boolean true ∧ d = Term.Boolean true ∧
      e = Term.Boolean true ∧ f = Term.Boolean true := by
  intro h
  rcases eo_and_eq_true_args _ _ h with ⟨habcde, hf⟩
  rcases and_true5 a b c d e habcde with ⟨ha, hb, hc, hd, he⟩
  exact ⟨ha, hb, hc, hd, he, hf⟩

theorem aliases2 {a b a' b' : Term}
    (h : __eo_and (__eo_eq a a') (__eo_eq b b') = Term.Boolean true) :
    a' = a ∧ b' = b := by
  rcases eo_and_eq_true_args _ _ h with ⟨ha, hb⟩
  exact ⟨support_eq_of_eo_eq_true a a' ha,
    support_eq_of_eo_eq_true b b' hb⟩

theorem aliases3 {a b c a' b' c' : Term}
    (h : __eo_and (__eo_and (__eo_eq a a') (__eo_eq b b'))
      (__eo_eq c c') = Term.Boolean true) :
    a' = a ∧ b' = b ∧ c' = c := by
  rcases and_true3 _ _ _ h with ⟨ha, hb, hc⟩
  exact ⟨support_eq_of_eo_eq_true a a' ha,
    support_eq_of_eo_eq_true b b' hb,
    support_eq_of_eo_eq_true c c' hc⟩

theorem aliases4 {a b c d a' b' c' d' : Term}
    (h : __eo_and (__eo_and (__eo_and (__eo_eq a a') (__eo_eq b b'))
      (__eo_eq c c')) (__eo_eq d d') = Term.Boolean true) :
    a' = a ∧ b' = b ∧ c' = c ∧ d' = d := by
  rcases and_true4 _ _ _ _ h with ⟨ha, hb, hc, hd⟩
  exact ⟨support_eq_of_eo_eq_true a a' ha,
    support_eq_of_eo_eq_true b b' hb,
    support_eq_of_eo_eq_true c c' hc,
    support_eq_of_eo_eq_true d d' hd⟩

theorem aliases5 {a b c d e a' b' c' d' e' : Term}
    (h : __eo_and (__eo_and (__eo_and (__eo_and (__eo_eq a a')
      (__eo_eq b b')) (__eo_eq c c')) (__eo_eq d d')) (__eo_eq e e') =
      Term.Boolean true) :
    a' = a ∧ b' = b ∧ c' = c ∧ d' = d ∧ e' = e := by
  rcases and_true5 _ _ _ _ _ h with ⟨ha, hb, hc, hd, he⟩
  exact ⟨support_eq_of_eo_eq_true a a' ha,
    support_eq_of_eo_eq_true b b' hb,
    support_eq_of_eo_eq_true c c' hc,
    support_eq_of_eo_eq_true d d' hd,
    support_eq_of_eo_eq_true e e' he⟩

theorem aliases6 {a b c d e f a' b' c' d' e' f' : Term}
    (h : __eo_and (__eo_and (__eo_and (__eo_and (__eo_and (__eo_eq a a')
      (__eo_eq b b')) (__eo_eq c c')) (__eo_eq d d')) (__eo_eq e e'))
      (__eo_eq f f') = Term.Boolean true) :
    a' = a ∧ b' = b ∧ c' = c ∧ d' = d ∧ e' = e ∧ f' = f := by
  rcases and_true6 _ _ _ _ _ _ h with ⟨ha, hb, hc, hd, he, hf⟩
  exact ⟨support_eq_of_eo_eq_true a a' ha,
    support_eq_of_eo_eq_true b b' hb,
    support_eq_of_eo_eq_true c c' hc,
    support_eq_of_eo_eq_true d d' hd,
    support_eq_of_eo_eq_true e e' he,
    support_eq_of_eo_eq_true f f' hf⟩

theorem bool_not_decide_true_of {p : Prop} [Decidable p] (h : ¬p) :
    (!decide p) = true := by
  simp [h]

theorem bool_imp_not_decide_true_of {p : Prop} [Decidable p] {b : Bool}
    (h : ¬p -> b = true) : (!(!decide p) || b) = true := by
  by_cases hp : p <;> simp [hp, h]

theorem raw_urem_result_bool (x s t l : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l) ->
      RuleProofs.eo_has_bool_type l := by
  intro hBool
  change __smtx_typeof
      (SmtTerm.imp
        (SmtTerm.eq (SmtTerm.bvurem (__eo_to_smt x) (__eo_to_smt s))
          (__eo_to_smt t)) (__eo_to_smt l)) = SmtType.Bool at hBool
  have hNN : term_has_non_none_type
      (SmtTerm.imp
        (SmtTerm.eq (SmtTerm.bvurem (__eo_to_smt x) (__eo_to_smt s))
          (__eo_to_smt t)) (__eo_to_smt l)) := by
    unfold term_has_non_none_type
    rw [hBool]
    simp
  exact (bool_binop_args_bool_of_non_none
    (typeof_imp_eq
      (SmtTerm.eq (SmtTerm.bvurem (__eo_to_smt x) (__eo_to_smt s))
        (__eo_to_smt t)) (__eo_to_smt l)) hNN).2

theorem raw_udiv_result_bool (x s t l : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l) ->
      RuleProofs.eo_has_bool_type l := by
  intro hBool
  change __smtx_typeof
      (SmtTerm.imp
        (SmtTerm.eq (SmtTerm.bvudiv (__eo_to_smt x) (__eo_to_smt s))
          (__eo_to_smt t)) (__eo_to_smt l)) = SmtType.Bool at hBool
  have hNN : term_has_non_none_type
      (SmtTerm.imp
        (SmtTerm.eq (SmtTerm.bvudiv (__eo_to_smt x) (__eo_to_smt s))
          (__eo_to_smt t)) (__eo_to_smt l)) := by
    unfold term_has_non_none_type
    rw [hBool]
    simp
  exact (bool_binop_args_bool_of_non_none
    (typeof_imp_eq
      (SmtTerm.eq (SmtTerm.bvudiv (__eo_to_smt x) (__eo_to_smt s))
        (__eo_to_smt t)) (__eo_to_smt l)) hNN).2

theorem raw_mul_result_bool (x s t l : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) s)) t)) l) ->
      RuleProofs.eo_has_bool_type l := by
  intro hBool
  change __smtx_typeof
      (SmtTerm.imp
        (SmtTerm.eq (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt s))
          (__eo_to_smt t)) (__eo_to_smt l)) = SmtType.Bool at hBool
  have hNN : term_has_non_none_type
      (SmtTerm.imp
        (SmtTerm.eq (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt s))
          (__eo_to_smt t)) (__eo_to_smt l)) := by
    unfold term_has_non_none_type
    rw [hBool]
    simp
  exact (bool_binop_args_bool_of_non_none
    (typeof_imp_eq
      (SmtTerm.eq (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt s))
        (__eo_to_smt t)) (__eo_to_smt l)) hNN).2

theorem imp_eq_eq_operand_types (a b c d : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b))
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) c) d)) ->
      (__smtx_typeof (__eo_to_smt a) = __smtx_typeof (__eo_to_smt b)) ∧
      (__smtx_typeof (__eo_to_smt c) = __smtx_typeof (__eo_to_smt d)) := by
  intro hBool
  change __smtx_typeof
      (SmtTerm.imp (SmtTerm.eq (__eo_to_smt a) (__eo_to_smt b))
        (SmtTerm.eq (__eo_to_smt c) (__eo_to_smt d))) = SmtType.Bool at hBool
  have hNN : term_has_non_none_type
      (SmtTerm.imp (SmtTerm.eq (__eo_to_smt a) (__eo_to_smt b))
        (SmtTerm.eq (__eo_to_smt c) (__eo_to_smt d))) := by
    unfold term_has_non_none_type
    rw [hBool]
    simp
  have hArgs := bool_binop_args_bool_of_non_none
    (typeof_imp_eq (SmtTerm.eq (__eo_to_smt a) (__eo_to_smt b))
      (SmtTerm.eq (__eo_to_smt c) (__eo_to_smt d))) hNN
  exact ⟨(RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type a b hArgs.1).1,
    (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type c d hArgs.2).1⟩

theorem bv_op2_args_of_result
    {op : SmtTerm -> SmtTerm -> SmtTerm} {a b : SmtTerm} {w : Nat}
    (hOp : __smtx_typeof (op a b) =
      __smtx_typeof_bv_op_2 (__smtx_typeof a) (__smtx_typeof b))
    (hResult : __smtx_typeof (op a b) = SmtType.BitVec w) :
    __smtx_typeof a = SmtType.BitVec w ∧
      __smtx_typeof b = SmtType.BitVec w := by
  have hNN : term_has_non_none_type (op a b) := by
    unfold term_has_non_none_type
    rw [hResult]
    simp
  rcases bv_binop_args_of_non_none hOp hNN with ⟨w', ha, hb⟩
  rw [hOp, ha, hb] at hResult
  simp [__smtx_typeof_bv_op_2, native_ite, native_nateq] at hResult
  subst w'
  exact ⟨ha, hb⟩

theorem bv_cmp_args_of_bool
    {op : SmtTerm -> SmtTerm -> SmtTerm} {a b : SmtTerm}
    (hOp : __smtx_typeof (op a b) =
      __smtx_typeof_bv_op_2_ret (__smtx_typeof a) (__smtx_typeof b)
        SmtType.Bool)
    (hResult : __smtx_typeof (op a b) = SmtType.Bool) :
    ∃ w : Nat, __smtx_typeof a = SmtType.BitVec w ∧
      __smtx_typeof b = SmtType.BitVec w := by
  have hNN : term_has_non_none_type (op a b) := by
    unfold term_has_non_none_type
    rw [hResult]
    simp
  exact bv_binop_ret_args_of_non_none hOp hNN

theorem bv_cmp_left_type_of_right
    {op : SmtTerm -> SmtTerm -> SmtTerm} {a b : SmtTerm} {w : Nat}
    (hOp : __smtx_typeof (op a b) =
      __smtx_typeof_bv_op_2_ret (__smtx_typeof a) (__smtx_typeof b)
        SmtType.Bool)
    (hResult : __smtx_typeof (op a b) = SmtType.Bool)
    (hb : __smtx_typeof b = SmtType.BitVec w) :
    __smtx_typeof a = SmtType.BitVec w := by
  obtain ⟨w', ha, hb'⟩ := bv_cmp_args_of_bool hOp hResult
  have hww : w' = w := by
    rw [hb] at hb'
    injection hb' with h
    exact h.symm
  subst w'
  exact ha

theorem bv_op1_arg_of_result
    {op : SmtTerm -> SmtTerm} {a : SmtTerm} {w : Nat}
    (hOp : __smtx_typeof (op a) = __smtx_typeof_bv_op_1 (__smtx_typeof a))
    (hResult : __smtx_typeof (op a) = SmtType.BitVec w) :
    __smtx_typeof a = SmtType.BitVec w := by
  have hNN : term_has_non_none_type (op a) := by
    unfold term_has_non_none_type
    rw [hResult]
    simp
  obtain ⟨w', ha⟩ := bv_unop_arg_of_non_none hOp hNN
  rw [hOp, ha] at hResult
  simp [__smtx_typeof_bv_op_1] at hResult
  subst w'
  exact ha

namespace Raw

inductive Expr where
  | x | s | t | lit (c : Term)
  | neg (a : Expr) | not (a : Expr)
  | mul (a b : Expr) | add (a b : Expr) | sub (a b : Expr)
  | and (a b : Expr) | or (a b : Expr) | xor (a b : Expr)
  | shl (a b : Expr) | lshr (a b : Expr)
deriving DecidableEq

def Expr.term (x s t : Term) : Expr -> Term
  | .x => x
  | .s => s
  | .t => t
  | .lit c => c
  | .neg a => Term.Apply (Term.UOp UserOp.bvneg) (a.term x s t)
  | .not a => Term.Apply (Term.UOp UserOp.bvnot) (a.term x s t)
  | .mul a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
      (a.term x s t)) (b.term x s t)
  | .add a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvadd)
      (a.term x s t)) (b.term x s t)
  | .sub a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvsub)
      (a.term x s t)) (b.term x s t)
  | .and a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvand)
      (a.term x s t)) (b.term x s t)
  | .or a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvor)
      (a.term x s t)) (b.term x s t)
  | .xor a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvxor)
      (a.term x s t)) (b.term x s t)
  | .shl a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvshl)
      (a.term x s t)) (b.term x s t)
  | .lshr a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvlshr)
      (a.term x s t)) (b.term x s t)

def Expr.hasVar : Expr -> Bool
  | .x | .s | .t => true
  | .lit _ => false
  | .neg a | .not a => a.hasVar
  | .mul a b | .add a b | .sub a b | .and a b | .or a b |
      .xor a b | .shl a b | .lshr a b => a.hasVar || b.hasVar

def Expr.literals : Expr -> List Term
  | .x | .s | .t => []
  | .lit c => [c]
  | .neg a | .not a => a.literals
  | .mul a b | .add a b | .sub a b | .and a b | .or a b |
      .xor a b | .shl a b | .lshr a b => a.literals ++ b.literals

theorem Expr.literals_typed_of_type (e : Expr) (x s t : Term) (w : Nat)
    (hTy : __smtx_typeof (__eo_to_smt (e.term x s t)) = SmtType.BitVec w) :
    ∀ c ∈ e.literals,
      __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w := by
  induction e generalizing w with
  | x | s | t => simp [literals]
  | lit c => simpa [literals, term] using hTy
  | neg a ih =>
      have ha := bv_op1_arg_of_result (op := SmtTerm.bvneg) (a := __eo_to_smt (a.term x s t))
        (by rfl) hTy
      simpa [literals] using ih w ha
  | not a ih =>
      have ha := bv_op1_arg_of_result (op := SmtTerm.bvnot) (a := __eo_to_smt (a.term x s t))
        (by rfl) hTy
      simpa [literals] using ih w ha
  | mul a b iha ihb =>
      have hab := bv_op2_args_of_result (a := __eo_to_smt (a.term x s t))
        (b := __eo_to_smt (b.term x s t)) (by rfl) hTy
      intro c hc
      simp only [literals, List.mem_append] at hc
      rcases hc with hc | hc
      · exact iha w hab.1 c hc
      · exact ihb w hab.2 c hc
  | add a b iha ihb =>
      have hab := bv_op2_args_of_result (a := __eo_to_smt (a.term x s t))
        (b := __eo_to_smt (b.term x s t)) (by rfl) hTy
      intro c hc
      simp only [literals, List.mem_append] at hc
      rcases hc with hc | hc
      · exact iha w hab.1 c hc
      · exact ihb w hab.2 c hc
  | sub a b iha ihb =>
      have hab := bv_op2_args_of_result (a := __eo_to_smt (a.term x s t))
        (b := __eo_to_smt (b.term x s t)) (by rfl) hTy
      intro c hc
      simp only [literals, List.mem_append] at hc
      rcases hc with hc | hc
      · exact iha w hab.1 c hc
      · exact ihb w hab.2 c hc
  | and a b iha ihb =>
      have hab := bv_op2_args_of_result (a := __eo_to_smt (a.term x s t))
        (b := __eo_to_smt (b.term x s t)) (by rfl) hTy
      intro c hc
      simp only [literals, List.mem_append] at hc
      rcases hc with hc | hc
      · exact iha w hab.1 c hc
      · exact ihb w hab.2 c hc
  | or a b iha ihb =>
      have hab := bv_op2_args_of_result (a := __eo_to_smt (a.term x s t))
        (b := __eo_to_smt (b.term x s t)) (by rfl) hTy
      intro c hc
      simp only [literals, List.mem_append] at hc
      rcases hc with hc | hc
      · exact iha w hab.1 c hc
      · exact ihb w hab.2 c hc
  | xor a b iha ihb =>
      have hab := bv_op2_args_of_result (a := __eo_to_smt (a.term x s t))
        (b := __eo_to_smt (b.term x s t)) (by rfl) hTy
      intro c hc
      simp only [literals, List.mem_append] at hc
      rcases hc with hc | hc
      · exact iha w hab.1 c hc
      · exact ihb w hab.2 c hc
  | shl a b iha ihb =>
      have hab := bv_op2_args_of_result (a := __eo_to_smt (a.term x s t))
        (b := __eo_to_smt (b.term x s t)) (by rfl) hTy
      intro c hc
      simp only [literals, List.mem_append] at hc
      rcases hc with hc | hc
      · exact iha w hab.1 c hc
      · exact ihb w hab.2 c hc
  | lshr a b iha ihb =>
      have hab := bv_op2_args_of_result (a := __eo_to_smt (a.term x s t))
        (b := __eo_to_smt (b.term x s t)) (by rfl) hTy
      intro c hc
      simp only [literals, List.mem_append] at hc
      rcases hc with hc | hc
      · exact iha w hab.1 c hc
      · exact ihb w hab.2 c hc

theorem Expr.type_of_hasVar (e : Expr) (x s t : Term) (w : Nat)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hVar : e.hasVar = true)
    (hNN : term_has_non_none_type (__eo_to_smt (e.term x s t))) :
    __smtx_typeof (__eo_to_smt (e.term x s t)) = SmtType.BitVec w := by
  induction e with
  | x => exact hxTy
  | s => exact hsTy
  | t => exact htTy
  | lit c => simp [hasVar] at hVar
  | neg a ih =>
      obtain ⟨u, ha⟩ := bv_unop_arg_of_non_none (op := SmtTerm.bvneg)
        (t := __eo_to_smt (a.term x s t)) (by rfl) hNN
      have haW := ih (by simpa [hasVar] using hVar) (by
        unfold term_has_non_none_type
        rw [ha]
        simp)
      rw [show __smtx_typeof (__eo_to_smt ((Expr.neg a).term x s t)) =
        __smtx_typeof_bv_op_1 (__smtx_typeof (__eo_to_smt (a.term x s t))) by rfl,
        haW]
      simp [__smtx_typeof_bv_op_1]
  | not a ih =>
      obtain ⟨u, ha⟩ := bv_unop_arg_of_non_none (op := SmtTerm.bvnot)
        (t := __eo_to_smt (a.term x s t)) (by rfl) hNN
      have haW := ih (by simpa [hasVar] using hVar) (by
        unfold term_has_non_none_type
        rw [ha]
        simp)
      rw [show __smtx_typeof (__eo_to_smt ((Expr.not a).term x s t)) =
        __smtx_typeof_bv_op_1 (__smtx_typeof (__eo_to_smt (a.term x s t))) by rfl,
        haW]
      simp [__smtx_typeof_bv_op_1]
  | mul a b iha ihb =>
      obtain ⟨u, ha, hb⟩ := bv_binop_args_of_non_none
        (t1 := __eo_to_smt (a.term x s t)) (t2 := __eo_to_smt (b.term x s t))
        (by rfl) hNN
      simp only [hasVar, Bool.or_eq_true] at hVar
      have hu : u = w := by
        rcases hVar with hVar | hVar
        · have haW := iha hVar (by unfold term_has_non_none_type; rw [ha]; simp)
          rw [ha] at haW
          injection haW
        · have hbW := ihb hVar (by unfold term_has_non_none_type; rw [hb]; simp)
          rw [hb] at hbW
          injection hbW
      subst u
      rw [show __smtx_typeof (__eo_to_smt (Expr.term x s t (.mul a b))) =
        __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt (a.term x s t)))
          (__smtx_typeof (__eo_to_smt (b.term x s t))) by rfl, ha, hb]
      simp [__smtx_typeof_bv_op_2, native_nateq, native_ite]
  | add a b iha ihb =>
      obtain ⟨u, ha, hb⟩ := bv_binop_args_of_non_none
        (t1 := __eo_to_smt (a.term x s t)) (t2 := __eo_to_smt (b.term x s t))
        (by rfl) hNN
      simp only [hasVar, Bool.or_eq_true] at hVar
      have hu : u = w := by
        rcases hVar with hVar | hVar
        · have haW := iha hVar (by unfold term_has_non_none_type; rw [ha]; simp)
          rw [ha] at haW
          injection haW
        · have hbW := ihb hVar (by unfold term_has_non_none_type; rw [hb]; simp)
          rw [hb] at hbW
          injection hbW
      subst u
      rw [show __smtx_typeof (__eo_to_smt (Expr.term x s t (.add a b))) =
        __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt (a.term x s t)))
          (__smtx_typeof (__eo_to_smt (b.term x s t))) by rfl, ha, hb]
      simp [__smtx_typeof_bv_op_2, native_nateq, native_ite]
  | sub a b iha ihb =>
      obtain ⟨u, ha, hb⟩ := bv_binop_args_of_non_none
        (t1 := __eo_to_smt (a.term x s t)) (t2 := __eo_to_smt (b.term x s t))
        (by rfl) hNN
      simp only [hasVar, Bool.or_eq_true] at hVar
      have hu : u = w := by
        rcases hVar with hVar | hVar
        · have haW := iha hVar (by unfold term_has_non_none_type; rw [ha]; simp)
          rw [ha] at haW
          injection haW
        · have hbW := ihb hVar (by unfold term_has_non_none_type; rw [hb]; simp)
          rw [hb] at hbW
          injection hbW
      subst u
      rw [show __smtx_typeof (__eo_to_smt (Expr.term x s t (.sub a b))) =
        __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt (a.term x s t)))
          (__smtx_typeof (__eo_to_smt (b.term x s t))) by rfl, ha, hb]
      simp [__smtx_typeof_bv_op_2, native_nateq, native_ite]
  | and a b iha ihb =>
      obtain ⟨u, ha, hb⟩ := bv_binop_args_of_non_none
        (t1 := __eo_to_smt (a.term x s t)) (t2 := __eo_to_smt (b.term x s t))
        (by rfl) hNN
      simp only [hasVar, Bool.or_eq_true] at hVar
      have hu : u = w := by
        rcases hVar with hVar | hVar
        · have haW := iha hVar (by unfold term_has_non_none_type; rw [ha]; simp)
          rw [ha] at haW
          injection haW
        · have hbW := ihb hVar (by unfold term_has_non_none_type; rw [hb]; simp)
          rw [hb] at hbW
          injection hbW
      subst u
      rw [show __smtx_typeof (__eo_to_smt (Expr.term x s t (.and a b))) =
        __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt (a.term x s t)))
          (__smtx_typeof (__eo_to_smt (b.term x s t))) by rfl, ha, hb]
      simp [__smtx_typeof_bv_op_2, native_nateq, native_ite]
  | or a b iha ihb =>
      obtain ⟨u, ha, hb⟩ := bv_binop_args_of_non_none
        (t1 := __eo_to_smt (a.term x s t)) (t2 := __eo_to_smt (b.term x s t))
        (by rfl) hNN
      simp only [hasVar, Bool.or_eq_true] at hVar
      have hu : u = w := by
        rcases hVar with hVar | hVar
        · have haW := iha hVar (by unfold term_has_non_none_type; rw [ha]; simp)
          rw [ha] at haW
          injection haW
        · have hbW := ihb hVar (by unfold term_has_non_none_type; rw [hb]; simp)
          rw [hb] at hbW
          injection hbW
      subst u
      rw [show __smtx_typeof (__eo_to_smt (Expr.term x s t (.or a b))) =
        __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt (a.term x s t)))
          (__smtx_typeof (__eo_to_smt (b.term x s t))) by rfl, ha, hb]
      simp [__smtx_typeof_bv_op_2, native_nateq, native_ite]
  | xor a b iha ihb =>
      obtain ⟨u, ha, hb⟩ := bv_binop_args_of_non_none
        (t1 := __eo_to_smt (a.term x s t)) (t2 := __eo_to_smt (b.term x s t))
        (by rfl) hNN
      simp only [hasVar, Bool.or_eq_true] at hVar
      have hu : u = w := by
        rcases hVar with hVar | hVar
        · have haW := iha hVar (by unfold term_has_non_none_type; rw [ha]; simp)
          rw [ha] at haW
          injection haW
        · have hbW := ihb hVar (by unfold term_has_non_none_type; rw [hb]; simp)
          rw [hb] at hbW
          injection hbW
      subst u
      rw [show __smtx_typeof (__eo_to_smt (Expr.term x s t (.xor a b))) =
        __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt (a.term x s t)))
          (__smtx_typeof (__eo_to_smt (b.term x s t))) by rfl, ha, hb]
      simp [__smtx_typeof_bv_op_2, native_nateq, native_ite]
  | shl a b iha ihb =>
      obtain ⟨u, ha, hb⟩ := bv_binop_args_of_non_none
        (t1 := __eo_to_smt (a.term x s t)) (t2 := __eo_to_smt (b.term x s t))
        (by rfl) hNN
      simp only [hasVar, Bool.or_eq_true] at hVar
      have hu : u = w := by
        rcases hVar with hVar | hVar
        · have haW := iha hVar (by unfold term_has_non_none_type; rw [ha]; simp)
          rw [ha] at haW
          injection haW
        · have hbW := ihb hVar (by unfold term_has_non_none_type; rw [hb]; simp)
          rw [hb] at hbW
          injection hbW
      subst u
      rw [show __smtx_typeof (__eo_to_smt (Expr.term x s t (.shl a b))) =
        __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt (a.term x s t)))
          (__smtx_typeof (__eo_to_smt (b.term x s t))) by rfl, ha, hb]
      simp [__smtx_typeof_bv_op_2, native_nateq, native_ite]
  | lshr a b iha ihb =>
      obtain ⟨u, ha, hb⟩ := bv_binop_args_of_non_none
        (t1 := __eo_to_smt (a.term x s t)) (t2 := __eo_to_smt (b.term x s t))
        (by rfl) hNN
      simp only [hasVar, Bool.or_eq_true] at hVar
      have hu : u = w := by
        rcases hVar with hVar | hVar
        · have haW := iha hVar (by
            unfold term_has_non_none_type
            rw [ha]
            simp)
          rw [ha] at haW
          injection haW
        · have hbW := ihb hVar (by
            unfold term_has_non_none_type
            rw [hb]
            simp)
          rw [hb] at hbW
          injection hbW
      subst u
      rw [show __smtx_typeof (__eo_to_smt (Expr.term x s t (.lshr a b))) =
        __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt (a.term x s t)))
          (__smtx_typeof (__eo_to_smt (b.term x s t))) by rfl,
        ha, hb]
      simp [__smtx_typeof_bv_op_2, native_nateq, native_ite]

inductive Pred where
  | eq (a b : Expr) | ult (a b : Expr) | ule (a b : Expr) | uge (a b : Expr)
  | true | not (p : Pred) | and (p q : Pred) | imp (p q : Pred)
deriving DecidableEq

def Pred.term (x s t : Term) : Pred -> Term
  | .eq a b => Term.Apply (Term.Apply (Term.UOp UserOp.eq)
      (a.term x s t)) (b.term x s t)
  | .ult a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvult)
      (a.term x s t)) (b.term x s t)
  | .ule a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvule)
      (a.term x s t)) (b.term x s t)
  | .uge a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvuge)
      (a.term x s t)) (b.term x s t)
  | .true => Term.Boolean Bool.true
  | .not p => Term.Apply (Term.UOp UserOp.not) (p.term x s t)
  | .and p q => Term.Apply (Term.Apply (Term.UOp UserOp.and)
      (p.term x s t)) (q.term x s t)
  | .imp p q => Term.Apply (Term.Apply (Term.UOp UserOp.imp)
      (p.term x s t)) (q.term x s t)

def Pred.anchored : Pred -> Bool
  | .eq a b | .ult a b | .ule a b | .uge a b => a.hasVar || b.hasVar
  | .true => Bool.true
  | .not p => p.anchored
  | .and p q | .imp p q => p.anchored && q.anchored

def Pred.literals : Pred -> List Term
  | .eq a b | .ult a b | .ule a b | .uge a b => a.literals ++ b.literals
  | .true => []
  | .not p => p.literals
  | .and p q | .imp p q => p.literals ++ q.literals

theorem Pred.literals_typed_of_bool (p : Pred) (x s t : Term) (w : Nat)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hAnchor : p.anchored = Bool.true)
    (hBool : RuleProofs.eo_has_bool_type (p.term x s t)) :
    ∀ c ∈ p.literals,
      __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w := by
  induction p with
  | eq a b =>
      have hSame := RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (a.term x s t) (b.term x s t) hBool
      simp only [anchored, Bool.or_eq_true] at hAnchor
      have hATy : __smtx_typeof (__eo_to_smt (a.term x s t)) = SmtType.BitVec w := by
        rcases hAnchor with haVar | hbVar
        · exact a.type_of_hasVar x s t w hxTy hsTy htTy haVar hSame.2
        · exact hSame.1.trans
            (b.type_of_hasVar x s t w hxTy hsTy htTy hbVar (by
              unfold term_has_non_none_type
              rw [← hSame.1]
              exact hSame.2))
      have hBTy := hSame.1.symm.trans hATy
      intro c hc
      simp only [literals, List.mem_append] at hc
      rcases hc with hc | hc
      · exact a.literals_typed_of_type x s t w hATy c hc
      · exact b.literals_typed_of_type x s t w hBTy c hc
  | ult a b | ule a b | uge a b =>
      obtain ⟨u, ha, hb⟩ := bv_cmp_args_of_bool
        (a := __eo_to_smt (a.term x s t)) (b := __eo_to_smt (b.term x s t))
        (by rfl) hBool
      simp only [anchored, Bool.or_eq_true] at hAnchor
      have hu : u = w := by
        rcases hAnchor with haVar | hbVar
        · have haW := a.type_of_hasVar x s t w hxTy hsTy htTy haVar (by
            unfold term_has_non_none_type
            rw [ha]
            simp)
          rw [ha] at haW
          injection haW
        · have hbW := b.type_of_hasVar x s t w hxTy hsTy htTy hbVar (by
            unfold term_has_non_none_type
            rw [hb]
            simp)
          rw [hb] at hbW
          injection hbW
      subst u
      intro c hc
      simp only [literals, List.mem_append] at hc
      rcases hc with hc | hc
      · exact a.literals_typed_of_type x s t w ha c hc
      · exact b.literals_typed_of_type x s t w hb c hc
  | true => simp [literals]
  | not p ih =>
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        exact RuleProofs.eo_has_bool_type_not_arg (p.term x s t) hBool
      exact ih hAnchor hpBool
  | and p q ihp ihq =>
      change __smtx_typeof (SmtTerm.and (__eo_to_smt (p.term x s t))
        (__eo_to_smt (q.term x s t))) = SmtType.Bool at hBool
      have hNN : term_has_non_none_type
          (SmtTerm.and (__eo_to_smt (p.term x s t)) (__eo_to_smt (q.term x s t))) := by
        unfold term_has_non_none_type
        rw [hBool]
        simp
      have hArgs := bool_binop_args_bool_of_non_none
        (typeof_and_eq (__eo_to_smt (p.term x s t)) (__eo_to_smt (q.term x s t))) hNN
      simp only [anchored, Bool.and_eq_true] at hAnchor
      intro c hc
      simp only [literals, List.mem_append] at hc
      rcases hc with hc | hc
      · exact ihp hAnchor.1 hArgs.1 c hc
      · exact ihq hAnchor.2 hArgs.2 c hc
  | imp p q ihp ihq =>
      change __smtx_typeof (SmtTerm.imp (__eo_to_smt (p.term x s t))
        (__eo_to_smt (q.term x s t))) = SmtType.Bool at hBool
      have hNN : term_has_non_none_type
          (SmtTerm.imp (__eo_to_smt (p.term x s t)) (__eo_to_smt (q.term x s t))) := by
        unfold term_has_non_none_type
        rw [hBool]
        simp
      have hArgs := bool_binop_args_bool_of_non_none
        (typeof_imp_eq (__eo_to_smt (p.term x s t)) (__eo_to_smt (q.term x s t))) hNN
      simp only [anchored, Bool.and_eq_true] at hAnchor
      intro c hc
      simp only [literals, List.mem_append] at hc
      rcases hc with hc | hc
      · exact ihp hAnchor.1 hArgs.1 c hc
      · exact ihq hAnchor.2 hArgs.2 c hc

end Raw

theorem matcher_urem15_sound
    (M : SmtModel) (hM : model_total_typed M)
    (x s t l : Term) (w : Nat) (xb sb tb : BitVec w)
    (hw : 3 ≤ w)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l))
    (hmatch : __eo_l_14___bv_abstraction_lemma_urem x s t l =
      Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l)
      true := by
  fun_cases __eo_l_14___bv_abstraction_lemma_urem x s t l
  all_goals simp only [__eo_l_14___bv_abstraction_lemma_urem] at hmatch
  all_goals try { simp [__eo_l_15___bv_abstraction_lemma_urem] at hmatch }
  case case5 ps cone pt zero hxne hsne htne =>
    simp only [__eo_l_15___bv_abstraction_lemma_urem] at hmatch
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases eo_and_eq_true_args _ _ hAliases with ⟨hsAlias, htAlias⟩
      have eps : ps = s := support_eq_of_eo_eq_true s ps hsAlias
      have ept : pt = t := support_eq_of_eo_eq_true t pt htAlias
      subst ps; subst pt
      rcases eo_and_eq_true_args _ _ hVals with ⟨hOne, hZero⟩
      have htypes := imp_eq_eq_operand_types s cone t zero
        (raw_urem_result_bool x s t _ hBool)
      have hcTy : __smtx_typeof (__eo_to_smt cone) = SmtType.BitVec w :=
        htypes.1.symm.trans hsTy
      have hzTy : __smtx_typeof (__eo_to_smt zero) = SmtType.BitVec w :=
        htypes.2.symm.trans htTy
      have hc := validated_one (by omega) hcTy hOne
      have hz := validated_zero hzTy hZero
      subst cone; subst zero
      change eo_interprets M
        ((Dsl.uremPred (.imp (.eq .s .one) (.eq .t .zero))).term w x s t)
        true
      apply Dsl.sound_urem_pred (q := .imp (.eq .s .one) (.eq .t .zero))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      by_cases hsOne : sb = 1#w
      · rw [hsOne] at hAnte
        have htZero : tb = 0#w := by simpa using hAnte.symm
        simp [hsOne, htZero]
      · simp [hsOne]
    · exact False.elim (by simp [__eo_l_15___bv_abstraction_lemma_urem]
        at hFallback)

theorem matcher_urem14_sound
    (M : SmtModel) (hM : model_total_typed M)
    (x s t l : Term) (w : Nat) (xb sb tb : BitVec w)
    (hw : 3 ≤ w)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l))
    (hmatch : __eo_l_13___bv_abstraction_lemma_urem x s t l =
      Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l)
      true := by
  fun_cases __eo_l_13___bv_abstraction_lemma_urem x s t l
  all_goals simp only [__eo_l_13___bv_abstraction_lemma_urem] at hmatch
  all_goals try { simp at hmatch }
  case case5 ps px ps2 z1 z2 pt hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hc, hVals⟩
      rcases eo_and_eq_true_args _ _ hc with ⟨hc1, htAlias⟩
      rcases eo_and_eq_true_args _ _ hc1 with ⟨hc2, hsAlias2⟩
      rcases eo_and_eq_true_args _ _ hc2 with ⟨hsAlias, hxAlias⟩
      have eps : ps = s := support_eq_of_eo_eq_true s ps hsAlias
      have epx : px = x := support_eq_of_eo_eq_true x px hxAlias
      have eps2 : ps2 = s := support_eq_of_eo_eq_true s ps2 hsAlias2
      have ept : pt = t := support_eq_of_eo_eq_true t pt htAlias
      subst ps; subst px; subst ps2; subst pt
      rcases eo_and_eq_true_args _ _ hVals with ⟨hz1, hz2⟩
      have hResultBool := raw_urem_result_bool x s t _ hBool
      change __smtx_typeof (SmtTerm.bvuge
        (SmtTerm.bvxor (SmtTerm.bvneg (__eo_to_smt s))
          (SmtTerm.bvxor
            (SmtTerm.bvor (__eo_to_smt x)
              (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt z1)))
            (__eo_to_smt z2))) (__eo_to_smt t)) = SmtType.Bool at hResultBool
      obtain ⟨w', hExprTy, hTargetTy⟩ := bv_cmp_args_of_bool
        (show __smtx_typeof (SmtTerm.bvuge
            (SmtTerm.bvxor (SmtTerm.bvneg (__eo_to_smt s))
              (SmtTerm.bvxor
                (SmtTerm.bvor (__eo_to_smt x)
                  (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt z1)))
                (__eo_to_smt z2))) (__eo_to_smt t)) =
            __smtx_typeof_bv_op_2_ret
              (__smtx_typeof (SmtTerm.bvxor (SmtTerm.bvneg (__eo_to_smt s))
                (SmtTerm.bvxor
                  (SmtTerm.bvor (__eo_to_smt x)
                    (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt z1)))
                  (__eo_to_smt z2))))
              (__smtx_typeof (__eo_to_smt t)) SmtType.Bool by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hResultBool
      have hww : w' = w := by
        rw [htTy] at hTargetTy
        injection hTargetTy with h
        exact h.symm
      subst w'
      have hInner := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvxor
            (SmtTerm.bvor (__eo_to_smt x)
              (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt z1)))
            (__eo_to_smt z2)) =
            __smtx_typeof_bv_op_2
              (__smtx_typeof (SmtTerm.bvor (__eo_to_smt x)
                (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt z1))))
              (__smtx_typeof (__eo_to_smt z2)) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        (bv_op2_args_of_result
          (show __smtx_typeof (SmtTerm.bvxor
              (SmtTerm.bvneg (__eo_to_smt s))
              (SmtTerm.bvxor
                (SmtTerm.bvor (__eo_to_smt x)
                  (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt z1)))
                (__eo_to_smt z2))) =
              __smtx_typeof_bv_op_2
                (__smtx_typeof (SmtTerm.bvneg (__eo_to_smt s)))
                (__smtx_typeof (SmtTerm.bvxor
                  (SmtTerm.bvor (__eo_to_smt x)
                    (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt z1)))
                  (__eo_to_smt z2))) by
            rw [__smtx_typeof.eq_def] <;> simp only)
          hExprTy).2
      have hOrOuter := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvor (__eo_to_smt x)
            (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt z1))) =
            __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt x))
              (__smtx_typeof (SmtTerm.bvor (__eo_to_smt s)
                (__eo_to_smt z1))) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hInner.1
      have hOrInner := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt z1)) =
            __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt s))
              (__smtx_typeof (__eo_to_smt z1)) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hOrOuter.2
      have ez1 := validated_zero hOrInner.2 hz1
      have ez2 := validated_zero hInner.2 hz2
      subst z1; subst z2
      change eo_interprets M
        ((Dsl.uremPred
          (.uge (.xor (.neg .s) (.xor (.or .x (.or .s .zero)) .zero)) .t)).term
          w x s t) true
      apply Dsl.sound_urem_pred
        (q := .uge (.xor (.neg .s) (.xor (.or .x (.or .s .zero)) .zero)) .t)
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      have hsem := Urem15Case.urem15 xb sb
      rw [hAnte] at hsem
      exact decide_eq_true (by simpa using hsem)
    · exact matcher_urem15_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_urem15_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_urem13_sound
    (M : SmtModel) (hM : model_total_typed M)
    (x s t l : Term) (w : Nat) (xb sb tb : BitVec w)
    (hw : 3 ≤ w)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l))
    (hmatch : __eo_l_12___bv_abstraction_lemma_urem x s t l =
      Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l)
      true := by
  fun_cases __eo_l_12___bv_abstraction_lemma_urem x s t l
  all_goals simp only [__eo_l_12___bv_abstraction_lemma_urem] at hmatch
  all_goals try { simp at hmatch }
  case case5 px ps zero pt hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hc, hZero⟩
      rcases eo_and_eq_true_args _ _ hc with ⟨hc1, htAlias⟩
      rcases eo_and_eq_true_args _ _ hc1 with ⟨hxAlias, hsAlias⟩
      have epx : px = x := support_eq_of_eo_eq_true x px hxAlias
      have eps : ps = s := support_eq_of_eo_eq_true s ps hsAlias
      have ept : pt = t := support_eq_of_eo_eq_true t pt htAlias
      subst px; subst ps; subst pt
      have hResultBool := raw_urem_result_bool x s t _ hBool
      change __smtx_typeof (SmtTerm.bvuge
        (SmtTerm.bvadd (__eo_to_smt x)
          (SmtTerm.bvadd (SmtTerm.bvneg (__eo_to_smt s)) (__eo_to_smt zero)))
        (__eo_to_smt t)) = SmtType.Bool at hResultBool
      have hExprTy := bv_cmp_left_type_of_right
        (show __smtx_typeof (SmtTerm.bvuge
            (SmtTerm.bvadd (__eo_to_smt x)
              (SmtTerm.bvadd (SmtTerm.bvneg (__eo_to_smt s))
                (__eo_to_smt zero))) (__eo_to_smt t)) =
            __smtx_typeof_bv_op_2_ret
              (__smtx_typeof (SmtTerm.bvadd (__eo_to_smt x)
                (SmtTerm.bvadd (SmtTerm.bvneg (__eo_to_smt s))
                  (__eo_to_smt zero))))
              (__smtx_typeof (__eo_to_smt t)) SmtType.Bool by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hResultBool htTy
      have hOuter := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvadd (__eo_to_smt x)
            (SmtTerm.bvadd (SmtTerm.bvneg (__eo_to_smt s))
              (__eo_to_smt zero))) =
            __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt x))
              (__smtx_typeof (SmtTerm.bvadd (SmtTerm.bvneg (__eo_to_smt s))
                (__eo_to_smt zero))) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hExprTy
      have hInner := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvadd (SmtTerm.bvneg (__eo_to_smt s))
            (__eo_to_smt zero)) =
            __smtx_typeof_bv_op_2
              (__smtx_typeof (SmtTerm.bvneg (__eo_to_smt s)))
              (__smtx_typeof (__eo_to_smt zero)) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hOuter.2
      have ez := validated_zero hInner.2 hZero
      subst zero
      change eo_interprets M
        ((Dsl.uremPred (.uge (.add .x (.add (.neg .s) .zero)) .t)).term
          w x s t) true
      apply Dsl.sound_urem_pred
        (q := .uge (.add .x (.add (.neg .s) .zero)) .t)
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      have hsem := urem14 xb sb
      rw [hAnte] at hsem
      exact decide_eq_true (by simpa using hsem)
    · exact matcher_urem14_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_urem14_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_urem12_sound
    (M : SmtModel) (hM : model_total_typed M)
    (x s t l : Term) (w : Nat) (xb sb tb : BitVec w)
    (hw : 3 ≤ w)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l))
    (hmatch : __eo_l_11___bv_abstraction_lemma_urem x s t l =
      Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l)
      true := by
  fun_cases __eo_l_11___bv_abstraction_lemma_urem x s t l
  all_goals simp only [__eo_l_11___bv_abstraction_lemma_urem] at hmatch
  all_goals try { simp at hmatch }
  case case5 px px2 pt zero hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hc, hZero⟩
      rcases eo_and_eq_true_args _ _ hc with ⟨hc1, htAlias⟩
      rcases eo_and_eq_true_args _ _ hc1 with ⟨hxAlias, hxAlias2⟩
      have epx : px = x := support_eq_of_eo_eq_true x px hxAlias
      have epx2 : px2 = x := support_eq_of_eo_eq_true x px2 hxAlias2
      have ept : pt = t := support_eq_of_eo_eq_true t pt htAlias
      subst px; subst px2; subst pt
      have hResultBool := raw_urem_result_bool x s t _ hBool
      have hEqBool := RuleProofs.eo_has_bool_type_not_arg _ hResultBool
      rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type _ _ hEqBool
        with ⟨hSides, hRightNN⟩
      have hRightTy : __smtx_typeof (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvor)
            (Term.Apply (Term.UOp UserOp.bvneg) x))
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvor)
              (Term.Apply (Term.UOp UserOp.bvneg)
                (Term.Apply (Term.UOp UserOp.bvnot) t))) zero))) =
          SmtType.BitVec w := hSides.symm.trans hxTy
      change __smtx_typeof (SmtTerm.bvor (SmtTerm.bvneg (__eo_to_smt x))
        (SmtTerm.bvor (SmtTerm.bvneg (SmtTerm.bvnot (__eo_to_smt t)))
          (__eo_to_smt zero))) = SmtType.BitVec w at hRightTy
      have hOuter := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvor (SmtTerm.bvneg (__eo_to_smt x))
            (SmtTerm.bvor (SmtTerm.bvneg (SmtTerm.bvnot (__eo_to_smt t)))
              (__eo_to_smt zero))) =
            __smtx_typeof_bv_op_2
              (__smtx_typeof (SmtTerm.bvneg (__eo_to_smt x)))
              (__smtx_typeof (SmtTerm.bvor
                (SmtTerm.bvneg (SmtTerm.bvnot (__eo_to_smt t)))
                (__eo_to_smt zero))) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hRightTy
      have hInner := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvor
            (SmtTerm.bvneg (SmtTerm.bvnot (__eo_to_smt t)))
            (__eo_to_smt zero)) =
            __smtx_typeof_bv_op_2
              (__smtx_typeof (SmtTerm.bvneg (SmtTerm.bvnot (__eo_to_smt t))))
              (__smtx_typeof (__eo_to_smt zero)) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hOuter.2
      have ez := validated_zero hInner.2 hZero
      subst zero
      change eo_interprets M
        ((Dsl.uremPred
          (.not (.eq .x (.or (.neg .x) (.or (.neg (.not .t)) .zero))))).term
          w x s t) true
      apply Dsl.sound_urem_pred
        (q := .not (.eq .x (.or (.neg .x) (.or (.neg (.not .t)) .zero))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      have hsem := Urem13Case.urem13 hw xb sb
      rw [hAnte] at hsem
      have hneq : ¬xb = -xb ||| (-~~~tb ||| 0#w) := by simpa using hsem
      exact bool_not_decide_true_of hneq
    · exact matcher_urem13_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_urem13_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_urem11_sound
    (M : SmtModel) (hM : model_total_typed M)
    (x s t l : Term) (w : Nat) (xb sb tb : BitVec w)
    (hw : 3 ≤ w)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l))
    (hmatch : __eo_l_10___bv_abstraction_lemma_urem x s t l =
      Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l)
      true := by
  fun_cases __eo_l_10___bv_abstraction_lemma_urem x s t l
  all_goals simp only [__eo_l_10___bv_abstraction_lemma_urem] at hmatch
  all_goals try { simp at hmatch }
  case case5 pt px ps z1 z2 pt2 cone z3 width3 width2 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hc, hVals⟩
      rcases eo_and_eq_true_args _ _ hc with ⟨hc1, htAlias2⟩
      rcases eo_and_eq_true_args _ _ hc1 with ⟨hc2, hsAlias⟩
      rcases eo_and_eq_true_args _ _ hc2 with ⟨htAlias, hxAlias⟩
      have ept : pt = t := support_eq_of_eo_eq_true t pt htAlias
      have epx : px = x := support_eq_of_eo_eq_true x px hxAlias
      have eps : ps = s := support_eq_of_eo_eq_true s ps hsAlias
      have ept2 : pt2 = t := support_eq_of_eo_eq_true t pt2 htAlias2
      subst pt; subst px; subst ps; subst pt2
      rcases eo_and_eq_true_args _ _ hVals with ⟨hz1, hVals2⟩
      rcases eo_and_eq_true_args _ _ hVals2 with ⟨hz2, hVals3⟩
      rcases eo_and_eq_true_args _ _ hVals3 with ⟨hOne, hz3⟩
      change __eo_eq z2 (allOnesGenerator z2) = Term.Boolean true at hz2
      change __eo_eq z3 (allOnesGenerator z3) = Term.Boolean true at hz3
      have hResultBool := raw_urem_result_bool x s t _ hBool
      change __smtx_typeof (SmtTerm.bvuge
        (SmtTerm.bvand (__eo_to_smt t)
          (SmtTerm.bvand
            (SmtTerm.bvor (__eo_to_smt x)
              (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt z1)))
            (__eo_to_smt z2)))
        (SmtTerm.bvand (__eo_to_smt t)
          (SmtTerm.bvand (__eo_to_smt cone) (__eo_to_smt z3)))) =
        SmtType.Bool at hResultBool
      obtain ⟨w', hLeftTy, hRightTy⟩ := bv_cmp_args_of_bool
        (show __smtx_typeof (SmtTerm.bvuge
            (SmtTerm.bvand (__eo_to_smt t)
              (SmtTerm.bvand
                (SmtTerm.bvor (__eo_to_smt x)
                  (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt z1)))
                (__eo_to_smt z2)))
            (SmtTerm.bvand (__eo_to_smt t)
              (SmtTerm.bvand (__eo_to_smt cone) (__eo_to_smt z3)))) =
            __smtx_typeof_bv_op_2_ret
              (__smtx_typeof (SmtTerm.bvand (__eo_to_smt t)
                (SmtTerm.bvand
                  (SmtTerm.bvor (__eo_to_smt x)
                    (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt z1)))
                  (__eo_to_smt z2))))
              (__smtx_typeof (SmtTerm.bvand (__eo_to_smt t)
                (SmtTerm.bvand (__eo_to_smt cone) (__eo_to_smt z3))))
              SmtType.Bool by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hResultBool
      have hLeft := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvand (__eo_to_smt t)
            (SmtTerm.bvand
              (SmtTerm.bvor (__eo_to_smt x)
                (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt z1)))
              (__eo_to_smt z2))) =
            __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt t))
              (__smtx_typeof (SmtTerm.bvand
                (SmtTerm.bvor (__eo_to_smt x)
                  (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt z1)))
                (__eo_to_smt z2))) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hLeftTy
      have hww : w' = w := by
        rw [htTy] at hLeft
        injection hLeft.1 with h
        exact h.symm
      subst w'
      have hLeftRest := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvand
            (SmtTerm.bvor (__eo_to_smt x)
              (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt z1)))
            (__eo_to_smt z2)) =
            __smtx_typeof_bv_op_2
              (__smtx_typeof (SmtTerm.bvor (__eo_to_smt x)
                (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt z1))))
              (__smtx_typeof (__eo_to_smt z2)) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hLeft.2
      have hOrOuter := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvor (__eo_to_smt x)
            (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt z1))) =
            __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt x))
              (__smtx_typeof (SmtTerm.bvor (__eo_to_smt s)
                (__eo_to_smt z1))) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hLeftRest.1
      have hOrInner := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt z1)) =
            __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt s))
              (__smtx_typeof (__eo_to_smt z1)) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hOrOuter.2
      have hRight := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvand (__eo_to_smt t)
            (SmtTerm.bvand (__eo_to_smt cone) (__eo_to_smt z3))) =
            __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt t))
              (__smtx_typeof (SmtTerm.bvand (__eo_to_smt cone)
                (__eo_to_smt z3))) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hRightTy
      have hRightRest := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvand (__eo_to_smt cone)
            (__eo_to_smt z3)) =
            __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt cone))
              (__smtx_typeof (__eo_to_smt z3)) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hRight.2
      have ez1 := validated_zero hOrInner.2 hz1
      have ez2 := validated_ones hLeftRest.2 hz2
      have ec := validated_one (by omega) hRightRest.1 hOne
      have ez3 := validated_ones hRightRest.2 hz3
      subst z1; subst z2; subst cone; subst z3
      change eo_interprets M
        ((Dsl.uremPred
          (.uge (.and .t (.and (.or .x (.or .s .zero)) .ones))
            (.and .t (.and .one .ones)))).term w x s t) true
      apply Dsl.sound_urem_pred
        (q := .uge (.and .t (.and (.or .x (.or .s .zero)) .ones))
          (.and .t (.and .one .ones)))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      have hsem := urem12 hw xb sb
      rw [hAnte] at hsem
      apply decide_eq_true
      rw [BitVec.neg_one_eq_allOnes, BitVec.and_allOnes,
        BitVec.and_allOnes, BitVec.and_comm tb]
      simp only [BitVec.or_zero]
      exact hsem
    · exact matcher_urem12_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_urem12_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_urem10_sound
    (M : SmtModel) (hM : model_total_typed M)
    (x s t l : Term) (w : Nat) (xb sb tb : BitVec w)
    (hw : 3 ≤ w)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l))
    (hmatch : __eo_l_9___bv_abstraction_lemma_urem x s t l =
      Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l)
      true := by
  fun_cases __eo_l_9___bv_abstraction_lemma_urem x s t l
  all_goals simp only [__eo_l_9___bv_abstraction_lemma_urem] at hmatch
  all_goals try { simp at hmatch }
  case case5 pt px ps zero hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hc, hZero⟩
      rcases eo_and_eq_true_args _ _ hc with ⟨hc1, hsAlias⟩
      rcases eo_and_eq_true_args _ _ hc1 with ⟨htAlias, hxAlias⟩
      have ept : pt = t := support_eq_of_eo_eq_true t pt htAlias
      have epx : px = x := support_eq_of_eo_eq_true x px hxAlias
      have eps : ps = s := support_eq_of_eo_eq_true s ps hsAlias
      subst pt; subst px; subst ps
      have hResultBool := raw_urem_result_bool x s t _ hBool
      have hEqBool := RuleProofs.eo_has_bool_type_not_arg _ hResultBool
      rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type _ _ hEqBool
        with ⟨hSides, hRightNN⟩
      have hRightTy : __smtx_typeof (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvor)
            (Term.Apply (Term.UOp UserOp.bvnot) x))
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvor)
              (Term.Apply (Term.UOp UserOp.bvneg) s)) zero))) =
          SmtType.BitVec w := hSides.symm.trans htTy
      change __smtx_typeof (SmtTerm.bvor (SmtTerm.bvnot (__eo_to_smt x))
        (SmtTerm.bvor (SmtTerm.bvneg (__eo_to_smt s)) (__eo_to_smt zero))) =
        SmtType.BitVec w at hRightTy
      have hOuter := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvor (SmtTerm.bvnot (__eo_to_smt x))
            (SmtTerm.bvor (SmtTerm.bvneg (__eo_to_smt s))
              (__eo_to_smt zero))) =
            __smtx_typeof_bv_op_2
              (__smtx_typeof (SmtTerm.bvnot (__eo_to_smt x)))
              (__smtx_typeof (SmtTerm.bvor (SmtTerm.bvneg (__eo_to_smt s))
                (__eo_to_smt zero))) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hRightTy
      have hInner := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvor (SmtTerm.bvneg (__eo_to_smt s))
            (__eo_to_smt zero)) =
            __smtx_typeof_bv_op_2
              (__smtx_typeof (SmtTerm.bvneg (__eo_to_smt s)))
              (__smtx_typeof (__eo_to_smt zero)) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hOuter.2
      have ez := validated_zero hInner.2 hZero
      subst zero
      change eo_interprets M
        ((Dsl.uremPred
          (.not (.eq .t (.or (.not .x) (.or (.neg .s) .zero))))).term
          w x s t) true
      apply Dsl.sound_urem_pred
        (q := .not (.eq .t (.or (.not .x) (.or (.neg .s) .zero))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      have hsem := urem11 hw xb sb
      rw [hAnte] at hsem
      have hneq : ¬tb = ~~~xb ||| (-sb ||| 0#w) := by simpa using hsem
      exact bool_not_decide_true_of hneq
    · exact matcher_urem11_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_urem11_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_urem9_sound
    (M : SmtModel) (hM : model_total_typed M)
    (x s t l : Term) (w : Nat) (xb sb tb : BitVec w)
    (hw : 3 ≤ w)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l))
    (hmatch : __eo_l_8___bv_abstraction_lemma_urem x s t l =
      Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l)
      true := by
  fun_cases __eo_l_8___bv_abstraction_lemma_urem x s t l
  all_goals simp only [__eo_l_8___bv_abstraction_lemma_urem] at hmatch
  all_goals try { simp at hmatch }
  case case5 cone pt px ps zero ones widthTerm hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hc, hVals⟩
      rcases eo_and_eq_true_args _ _ hc with ⟨hc1, hsAlias⟩
      rcases eo_and_eq_true_args _ _ hc1 with ⟨htAlias, hxAlias⟩
      have ept : pt = t := support_eq_of_eo_eq_true t pt htAlias
      have epx : px = x := support_eq_of_eo_eq_true x px hxAlias
      have eps : ps = s := support_eq_of_eo_eq_true s ps hsAlias
      subst pt; subst px; subst ps
      rcases eo_and_eq_true_args _ _ hVals with ⟨hOne, hVals2⟩
      rcases eo_and_eq_true_args _ _ hVals2 with ⟨hZero, hOnes⟩
      change __eo_eq ones (allOnesGenerator ones) = Term.Boolean true at hOnes
      have hResultBool := raw_urem_result_bool x s t _ hBool
      have hEqBool := RuleProofs.eo_has_bool_type_not_arg _ hResultBool
      rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type _ _ hEqBool
        with ⟨hSides, hExprNN⟩
      have hRhsNN : term_has_non_none_type
          (SmtTerm.bvand (__eo_to_smt t)
            (SmtTerm.bvand
              (SmtTerm.bvnot (SmtTerm.bvor (__eo_to_smt x)
                (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt zero))))
              (__eo_to_smt ones))) := by
        unfold term_has_non_none_type
        exact fun hNone => hExprNN (hSides.trans hNone)
      obtain ⟨w', htArg, hRestTy⟩ := bv_binop_args_of_non_none
        (show __smtx_typeof (SmtTerm.bvand (__eo_to_smt t)
            (SmtTerm.bvand
              (SmtTerm.bvnot (SmtTerm.bvor (__eo_to_smt x)
                (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt zero))))
              (__eo_to_smt ones))) =
            __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt t))
              (__smtx_typeof (SmtTerm.bvand
                (SmtTerm.bvnot (SmtTerm.bvor (__eo_to_smt x)
                  (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt zero))))
                (__eo_to_smt ones))) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hRhsNN
      have hww : w' = w := by
        rw [htTy] at htArg
        injection htArg with h
        exact h.symm
      subst w'
      have hRest := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvand
            (SmtTerm.bvnot (SmtTerm.bvor (__eo_to_smt x)
              (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt zero))))
            (__eo_to_smt ones)) =
            __smtx_typeof_bv_op_2
              (__smtx_typeof (SmtTerm.bvnot (SmtTerm.bvor (__eo_to_smt x)
                (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt zero)))))
              (__smtx_typeof (__eo_to_smt ones)) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hRestTy
      have hOrTy := bv_op1_arg_of_result
        (show __smtx_typeof (SmtTerm.bvnot (SmtTerm.bvor (__eo_to_smt x)
            (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt zero)))) =
            __smtx_typeof_bv_op_1 (__smtx_typeof
              (SmtTerm.bvor (__eo_to_smt x)
                (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt zero)))) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hRest.1
      have hOrOuter := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvor (__eo_to_smt x)
            (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt zero))) =
            __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt x))
              (__smtx_typeof (SmtTerm.bvor (__eo_to_smt s)
                (__eo_to_smt zero))) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hOrTy
      have hOrInner := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt zero)) =
            __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt s))
              (__smtx_typeof (__eo_to_smt zero)) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hOrOuter.2
      have hExprTy : __smtx_typeof
          (SmtTerm.bvand (__eo_to_smt t)
            (SmtTerm.bvand
              (SmtTerm.bvnot (SmtTerm.bvor (__eo_to_smt x)
                (SmtTerm.bvor (__eo_to_smt s) (__eo_to_smt zero))))
              (__eo_to_smt ones))) = SmtType.BitVec w := by
        rw [__smtx_typeof.eq_def]
        simp [__smtx_typeof_bv_op_2, htTy, hRestTy, native_ite, native_nateq]
      have hConeTy : __smtx_typeof (__eo_to_smt cone) = SmtType.BitVec w :=
        hSides.trans hExprTy
      have ec := validated_one (by omega) hConeTy hOne
      have ez := validated_zero hOrInner.2 hZero
      have eo := validated_ones hRest.2 hOnes
      subst cone; subst zero; subst ones
      change eo_interprets M
        ((Dsl.uremPred
          (.not (.eq .one
            (.and .t (.and (.not (.or .x (.or .s .zero))) .ones))))).term
          w x s t) true
      apply Dsl.sound_urem_pred
        (q := .not (.eq .one
          (.and .t (.and (.not (.or .x (.or .s .zero))) .ones))))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      have hsem := urem10 hw xb sb
      rw [hAnte] at hsem
      have hneq : ¬1#w =
          tb &&& (~~~(xb ||| (sb ||| 0#w)) &&& -1#w) := by
        simpa only [BitVec.or_zero, BitVec.neg_one_eq_allOnes,
          BitVec.and_allOnes] using hsem
      exact bool_not_decide_true_of hneq
    · exact matcher_urem10_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_urem10_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_urem8_sound
    (M : SmtModel) (hM : model_total_typed M)
    (x s t l : Term) (w : Nat) (xb sb tb : BitVec w)
    (hw : 3 ≤ w)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l))
    (hmatch : __eo_l_7___bv_abstraction_lemma_urem x s t l =
      Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l)
      true := by
  fun_cases __eo_l_7___bv_abstraction_lemma_urem x s t l
  all_goals simp only [__eo_l_7___bv_abstraction_lemma_urem] at hmatch
  all_goals try { simp at hmatch }
  case case5 px pt px2 ps ones zero widthTerm hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hc, hVals⟩
      rcases eo_and_eq_true_args _ _ hc with ⟨hc1, hsAlias⟩
      rcases eo_and_eq_true_args _ _ hc1 with ⟨hc2, hxAlias2⟩
      rcases eo_and_eq_true_args _ _ hc2 with ⟨hxAlias, htAlias⟩
      have epx : px = x := support_eq_of_eo_eq_true x px hxAlias
      have ept : pt = t := support_eq_of_eo_eq_true t pt htAlias
      have epx2 : px2 = x := support_eq_of_eo_eq_true x px2 hxAlias2
      have eps : ps = s := support_eq_of_eo_eq_true s ps hsAlias
      subst px; subst pt; subst px2; subst ps
      rcases eo_and_eq_true_args _ _ hVals with ⟨hOnes, hZero⟩
      change __eo_eq ones (allOnesGenerator ones) = Term.Boolean true at hOnes
      have hResultBool := raw_urem_result_bool x s t _ hBool
      change __smtx_typeof (SmtTerm.bvuge (__eo_to_smt x)
        (SmtTerm.bvor (__eo_to_smt t)
          (SmtTerm.bvor
            (SmtTerm.bvand (__eo_to_smt x)
              (SmtTerm.bvand (__eo_to_smt s) (__eo_to_smt ones)))
            (__eo_to_smt zero)))) = SmtType.Bool at hResultBool
      obtain ⟨w', hLeftTy, hRightTy⟩ := bv_cmp_args_of_bool
        (show __smtx_typeof (SmtTerm.bvuge (__eo_to_smt x)
            (SmtTerm.bvor (__eo_to_smt t)
              (SmtTerm.bvor
                (SmtTerm.bvand (__eo_to_smt x)
                  (SmtTerm.bvand (__eo_to_smt s) (__eo_to_smt ones)))
                (__eo_to_smt zero)))) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof (__eo_to_smt x))
              (__smtx_typeof (SmtTerm.bvor (__eo_to_smt t)
                (SmtTerm.bvor
                  (SmtTerm.bvand (__eo_to_smt x)
                    (SmtTerm.bvand (__eo_to_smt s) (__eo_to_smt ones)))
                  (__eo_to_smt zero)))) SmtType.Bool by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hResultBool
      have hww : w' = w := by
        rw [hxTy] at hLeftTy
        injection hLeftTy with h
        exact h.symm
      subst w'
      have hOuter := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvor (__eo_to_smt t)
            (SmtTerm.bvor
              (SmtTerm.bvand (__eo_to_smt x)
                (SmtTerm.bvand (__eo_to_smt s) (__eo_to_smt ones)))
              (__eo_to_smt zero))) =
            __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt t))
              (__smtx_typeof (SmtTerm.bvor
                (SmtTerm.bvand (__eo_to_smt x)
                  (SmtTerm.bvand (__eo_to_smt s) (__eo_to_smt ones)))
                (__eo_to_smt zero))) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hRightTy
      have hRest := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvor
            (SmtTerm.bvand (__eo_to_smt x)
              (SmtTerm.bvand (__eo_to_smt s) (__eo_to_smt ones)))
            (__eo_to_smt zero)) =
            __smtx_typeof_bv_op_2
              (__smtx_typeof (SmtTerm.bvand (__eo_to_smt x)
                (SmtTerm.bvand (__eo_to_smt s) (__eo_to_smt ones))))
              (__smtx_typeof (__eo_to_smt zero)) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hOuter.2
      have hAndOuter := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvand (__eo_to_smt x)
            (SmtTerm.bvand (__eo_to_smt s) (__eo_to_smt ones))) =
            __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt x))
              (__smtx_typeof (SmtTerm.bvand (__eo_to_smt s)
                (__eo_to_smt ones))) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hRest.1
      have hAndInner := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvand (__eo_to_smt s)
            (__eo_to_smt ones)) =
            __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt s))
              (__smtx_typeof (__eo_to_smt ones)) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hAndOuter.2
      have eo := validated_ones hAndInner.2 hOnes
      have ez := validated_zero hRest.2 hZero
      subst ones; subst zero
      change eo_interprets M
        ((Dsl.uremPred
          (.uge .x (.or .t (.or (.and .x (.and .s .ones)) .zero)))).term
          w x s t) true
      apply Dsl.sound_urem_pred
        (q := .uge .x (.or .t (.or (.and .x (.and .s .ones)) .zero)))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      have hsem := urem9 xb sb
      rw [hAnte] at hsem
      have hsAnd : sb &&& (-1#w) = sb := by
        rw [BitVec.neg_one_eq_allOnes, BitVec.and_allOnes]
      exact decide_eq_true (by simpa [hsAnd] using hsem)
    · exact matcher_urem9_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_urem9_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_urem7_sound
    (M : SmtModel) (hM : model_total_typed M)
    (x s t l : Term) (w : Nat) (xb sb tb : BitVec w)
    (hw : 3 ≤ w)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l))
    (hmatch : __eo_l_6___bv_abstraction_lemma_urem x s t l =
      Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l)
      true := by
  fun_cases __eo_l_6___bv_abstraction_lemma_urem x s t l
  all_goals simp only [__eo_l_6___bv_abstraction_lemma_urem] at hmatch
  all_goals try { simp at hmatch }
  case case5 px px2 ps pt ps2 z1 z2 ones widthTerm hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hc, hVals⟩
      rcases eo_and_eq_true_args _ _ hc with ⟨hc1, hsAlias2⟩
      rcases eo_and_eq_true_args _ _ hc1 with ⟨hc2, htAlias⟩
      rcases eo_and_eq_true_args _ _ hc2 with ⟨hc3, hsAlias⟩
      rcases eo_and_eq_true_args _ _ hc3 with ⟨hxAlias, hxAlias2⟩
      have epx : px = x := support_eq_of_eo_eq_true x px hxAlias
      have epx2 : px2 = x := support_eq_of_eo_eq_true x px2 hxAlias2
      have eps : ps = s := support_eq_of_eo_eq_true s ps hsAlias
      have ept : pt = t := support_eq_of_eo_eq_true t pt htAlias
      have eps2 : ps2 = s := support_eq_of_eo_eq_true s ps2 hsAlias2
      subst px; subst px2; subst ps; subst pt; subst ps2
      rcases eo_and_eq_true_args _ _ hVals with ⟨hz1, hVals2⟩
      rcases eo_and_eq_true_args _ _ hVals2 with ⟨hz2, hOnes⟩
      change __eo_eq ones (allOnesGenerator ones) = Term.Boolean true at hOnes
      have hResultBool := raw_urem_result_bool x s t _ hBool
      rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type _ _
        hResultBool with ⟨hSides, hRightNN⟩
      change __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof (SmtTerm.bvand
          (__eo_to_smt x)
          (SmtTerm.bvand
            (SmtTerm.bvor (__eo_to_smt s)
              (SmtTerm.bvor
                (SmtTerm.bvor (__eo_to_smt t)
                  (SmtTerm.bvor (SmtTerm.bvneg (__eo_to_smt s))
                    (__eo_to_smt z1)))
                (__eo_to_smt z2)))
            (__eo_to_smt ones))) at hSides
      have hRightTy : __smtx_typeof (SmtTerm.bvand
          (__eo_to_smt x)
          (SmtTerm.bvand
            (SmtTerm.bvor (__eo_to_smt s)
              (SmtTerm.bvor
                (SmtTerm.bvor (__eo_to_smt t)
                  (SmtTerm.bvor (SmtTerm.bvneg (__eo_to_smt s))
                    (__eo_to_smt z1)))
                (__eo_to_smt z2)))
            (__eo_to_smt ones))) = SmtType.BitVec w := hSides.symm.trans hxTy
      have hOuter := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvand
            (__eo_to_smt x)
            (SmtTerm.bvand
              (SmtTerm.bvor (__eo_to_smt s)
                (SmtTerm.bvor
                  (SmtTerm.bvor (__eo_to_smt t)
                    (SmtTerm.bvor (SmtTerm.bvneg (__eo_to_smt s))
                      (__eo_to_smt z1)))
                  (__eo_to_smt z2)))
              (__eo_to_smt ones))) =
            __smtx_typeof_bv_op_2
              (__smtx_typeof (__eo_to_smt x))
              (__smtx_typeof (SmtTerm.bvand
                (SmtTerm.bvor (__eo_to_smt s)
                  (SmtTerm.bvor
                    (SmtTerm.bvor (__eo_to_smt t)
                      (SmtTerm.bvor (SmtTerm.bvneg (__eo_to_smt s))
                        (__eo_to_smt z1)))
                    (__eo_to_smt z2)))
                (__eo_to_smt ones))) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hRightTy
      have hAndRest := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvand
            (SmtTerm.bvor (__eo_to_smt s)
              (SmtTerm.bvor
                (SmtTerm.bvor (__eo_to_smt t)
                  (SmtTerm.bvor (SmtTerm.bvneg (__eo_to_smt s))
                    (__eo_to_smt z1)))
                (__eo_to_smt z2)))
            (__eo_to_smt ones)) =
            __smtx_typeof_bv_op_2
              (__smtx_typeof (SmtTerm.bvor (__eo_to_smt s)
                (SmtTerm.bvor
                  (SmtTerm.bvor (__eo_to_smt t)
                    (SmtTerm.bvor (SmtTerm.bvneg (__eo_to_smt s))
                      (__eo_to_smt z1)))
                  (__eo_to_smt z2))))
              (__smtx_typeof (__eo_to_smt ones)) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hOuter.2
      have hOrS := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvor (__eo_to_smt s)
            (SmtTerm.bvor
              (SmtTerm.bvor (__eo_to_smt t)
                (SmtTerm.bvor (SmtTerm.bvneg (__eo_to_smt s))
                  (__eo_to_smt z1)))
              (__eo_to_smt z2))) =
            __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt s))
              (__smtx_typeof (SmtTerm.bvor
                (SmtTerm.bvor (__eo_to_smt t)
                  (SmtTerm.bvor (SmtTerm.bvneg (__eo_to_smt s))
                    (__eo_to_smt z1)))
                (__eo_to_smt z2))) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hAndRest.1
      have hOrZ2 := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvor
            (SmtTerm.bvor (__eo_to_smt t)
              (SmtTerm.bvor (SmtTerm.bvneg (__eo_to_smt s))
                (__eo_to_smt z1)))
            (__eo_to_smt z2)) =
            __smtx_typeof_bv_op_2
              (__smtx_typeof (SmtTerm.bvor (__eo_to_smt t)
                (SmtTerm.bvor (SmtTerm.bvneg (__eo_to_smt s))
                  (__eo_to_smt z1))))
              (__smtx_typeof (__eo_to_smt z2)) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hOrS.2
      have hOrT := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvor (__eo_to_smt t)
            (SmtTerm.bvor (SmtTerm.bvneg (__eo_to_smt s))
              (__eo_to_smt z1))) =
            __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt t))
              (__smtx_typeof (SmtTerm.bvor (SmtTerm.bvneg (__eo_to_smt s))
                (__eo_to_smt z1))) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hOrZ2.1
      have hOrNeg := bv_op2_args_of_result
        (show __smtx_typeof (SmtTerm.bvor (SmtTerm.bvneg (__eo_to_smt s))
            (__eo_to_smt z1)) =
            __smtx_typeof_bv_op_2
              (__smtx_typeof (SmtTerm.bvneg (__eo_to_smt s)))
              (__smtx_typeof (__eo_to_smt z1)) by
          rw [__smtx_typeof.eq_def] <;> simp only)
        hOrT.2
      have ez1 := validated_zero hOrNeg.2 hz1
      have ez2 := validated_zero hOrZ2.2 hz2
      have eo := validated_ones hAndRest.2 hOnes
      subst z1; subst z2; subst ones
      change eo_interprets M
        ((Dsl.uremPred
          (.eq .x (.and .x
            (.and (.or .s (.or (.or .t (.or (.neg .s) .zero)) .zero))
              .ones)))).term
          w x s t) true
      apply Dsl.sound_urem_pred
        (q := .eq .x (.and .x
          (.and (.or .s (.or (.or .t (.or (.neg .s) .zero)) .zero)) .ones)))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      have hsem := urem8 hw xb sb
      rw [hAnte] at hsem
      apply decide_eq_true
      rw [BitVec.neg_one_eq_allOnes, BitVec.and_allOnes]
      rw [BitVec.or_zero, BitVec.or_zero]
      simpa only [BitVec.or_assoc] using hsem
    · exact matcher_urem8_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_urem8_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_urem6_sound
    (M : SmtModel) (hM : model_total_typed M)
    (x s t l : Term) (w : Nat) (xb sb tb : BitVec w)
    (hw : 3 ≤ w)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l))
    (hmatch : __eo_l_5___bv_abstraction_lemma_urem x s t l =
      Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l)
      true := by
  fun_cases __eo_l_5___bv_abstraction_lemma_urem x s t l
  all_goals simp only [__eo_l_5___bv_abstraction_lemma_urem] at hmatch
  all_goals try { simp at hmatch }
  case case5 px ps pt px2 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hc, hTrue⟩
      rcases eo_and_eq_true_args _ _ hc with ⟨hc1, hxAlias2⟩
      rcases eo_and_eq_true_args _ _ hc1 with ⟨hc2, htAlias⟩
      rcases eo_and_eq_true_args _ _ hc2 with ⟨hxAlias, hsAlias⟩
      have epx : px = x := support_eq_of_eo_eq_true x px hxAlias
      have eps : ps = s := support_eq_of_eo_eq_true s ps hsAlias
      have ept : pt = t := support_eq_of_eo_eq_true t pt htAlias
      have epx2 : px2 = x := support_eq_of_eo_eq_true x px2 hxAlias2
      subst px; subst ps; subst pt; subst px2
      change eo_interprets M
        ((Dsl.uremPred (.imp (.ult .x .s) (.eq .t .x))).term w x s t) true
      apply Dsl.sound_urem_pred (q := .imp (.ult .x .s) (.eq .t .x))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply Dsl.bool_imp_true_of (p := xb < sb)
      intro hlt
      have hrem := urem6 xb sb hlt
      exact decide_eq_true (hAnte.symm.trans hrem)
    · exact matcher_urem7_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_urem7_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_urem5_sound
    (M : SmtModel) (hM : model_total_typed M)
    (x s t l : Term) (w : Nat) (xb sb tb : BitVec w)
    (hw : 3 ≤ w)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l))
    (hmatch : __eo_l_4___bv_abstraction_lemma_urem x s t l =
      Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l)
      true := by
  fun_cases __eo_l_4___bv_abstraction_lemma_urem x s t l
  all_goals simp only [__eo_l_4___bv_abstraction_lemma_urem] at hmatch
  all_goals try { simp at hmatch }
  case case5 ps px pt zero hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hc, hZero⟩
      rcases eo_and_eq_true_args _ _ hc with ⟨hc1, htAlias⟩
      rcases eo_and_eq_true_args _ _ hc1 with ⟨hsAlias, hxAlias⟩
      have eps : ps = s := support_eq_of_eo_eq_true s ps hsAlias
      have epx : px = x := support_eq_of_eo_eq_true x px hxAlias
      have ept : pt = t := support_eq_of_eo_eq_true t pt htAlias
      subst ps; subst px; subst pt
      have htypes := imp_eq_eq_operand_types s x t zero
        (raw_urem_result_bool x s t _ hBool)
      have hzTy : __smtx_typeof (__eo_to_smt zero) = SmtType.BitVec w :=
        htypes.2.symm.trans htTy
      have ez := validated_zero hzTy hZero
      subst zero
      change eo_interprets M
        ((Dsl.uremPred (.imp (.eq .s .x) (.eq .t .zero))).term w x s t) true
      apply Dsl.sound_urem_pred (q := .imp (.eq .s .x) (.eq .t .zero))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply Dsl.bool_imp_true_of (p := sb = xb)
      intro hsx
      have hrem := urem5 xb sb hsx
      exact decide_eq_true (hAnte.symm.trans hrem)
    · exact matcher_urem6_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_urem6_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_urem4_sound
    (M : SmtModel) (hM : model_total_typed M)
    (x s t l : Term) (w : Nat) (xb sb tb : BitVec w)
    (hw : 3 ≤ w)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l))
    (hmatch : __eo_l_3___bv_abstraction_lemma_urem x s t l =
      Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l)
      true := by
  fun_cases __eo_l_3___bv_abstraction_lemma_urem x s t l
  all_goals simp only [__eo_l_3___bv_abstraction_lemma_urem] at hmatch
  all_goals try { simp at hmatch }
  case case5 ps zero pt px hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hc, hZero⟩
      rcases eo_and_eq_true_args _ _ hc with ⟨hc1, hxAlias⟩
      rcases eo_and_eq_true_args _ _ hc1 with ⟨hsAlias, htAlias⟩
      have eps : ps = s := support_eq_of_eo_eq_true s ps hsAlias
      have ept : pt = t := support_eq_of_eo_eq_true t pt htAlias
      have epx : px = x := support_eq_of_eo_eq_true x px hxAlias
      subst ps; subst pt; subst px
      have htypes := imp_eq_eq_operand_types s zero t x
        (raw_urem_result_bool x s t _ hBool)
      have hzTy : __smtx_typeof (__eo_to_smt zero) = SmtType.BitVec w :=
        htypes.1.symm.trans hsTy
      have ez := validated_zero hzTy hZero
      subst zero
      change eo_interprets M
        ((Dsl.uremPred (.imp (.eq .s .zero) (.eq .t .x))).term w x s t) true
      apply Dsl.sound_urem_pred (q := .imp (.eq .s .zero) (.eq .t .x))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply Dsl.bool_imp_true_of (p := sb = 0#w)
      intro hs0
      have hrem := urem4 xb sb hs0
      exact decide_eq_true (hAnte.symm.trans hrem)
    · exact matcher_urem5_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_urem5_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_urem3_sound
    (M : SmtModel) (hM : model_total_typed M)
    (x s t l : Term) (w : Nat) (xb sb tb : BitVec w)
    (hw : 3 ≤ w)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l))
    (hmatch : __eo_l_2___bv_abstraction_lemma_urem x s t l =
      Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l)
      true := by
  fun_cases __eo_l_2___bv_abstraction_lemma_urem x s t l
  all_goals simp only [__eo_l_2___bv_abstraction_lemma_urem] at hmatch
  all_goals try { simp at hmatch }
  case case5 px zero pt zero2 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hc, hZero⟩
      rcases eo_and_eq_true_args _ _ hc with ⟨hc1, hzAlias⟩
      rcases eo_and_eq_true_args _ _ hc1 with ⟨hxAlias, htAlias⟩
      have epx : px = x := support_eq_of_eo_eq_true x px hxAlias
      have ept : pt = t := support_eq_of_eo_eq_true t pt htAlias
      have ez2 : zero2 = zero := support_eq_of_eo_eq_true zero zero2 hzAlias
      subst px; subst pt; subst zero2
      have htypes := imp_eq_eq_operand_types x zero t zero
        (raw_urem_result_bool x s t _ hBool)
      have hzTy : __smtx_typeof (__eo_to_smt zero) = SmtType.BitVec w :=
        htypes.1.symm.trans hxTy
      have ez := validated_zero hzTy hZero
      subst zero
      change eo_interprets M
        ((Dsl.uremPred (.imp (.eq .x .zero) (.eq .t .zero))).term w x s t) true
      apply Dsl.sound_urem_pred (q := .imp (.eq .x .zero) (.eq .t .zero))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply Dsl.bool_imp_true_of (p := xb = 0#w)
      intro hx0
      have hrem := urem3 xb sb hx0
      exact decide_eq_true (hAnte.symm.trans hrem)
    · exact matcher_urem4_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_urem4_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_urem2_sound
    (M : SmtModel) (hM : model_total_typed M)
    (x s t l : Term) (w : Nat) (xb sb tb : BitVec w)
    (hw : 3 ≤ w)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l))
    (hmatch : __eo_l_1___bv_abstraction_lemma_urem x s t l =
      Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l)
      true := by
  fun_cases __eo_l_1___bv_abstraction_lemma_urem x s t l
  all_goals simp only [__eo_l_1___bv_abstraction_lemma_urem] at hmatch
  all_goals try { simp at hmatch }
  case case5 ps zero pt ps2 hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hc, hZero⟩
      rcases eo_and_eq_true_args _ _ hc with ⟨hc1, hsAlias2⟩
      rcases eo_and_eq_true_args _ _ hc1 with ⟨hsAlias, htAlias⟩
      have eps : ps = s := support_eq_of_eo_eq_true s ps hsAlias
      have ept : pt = t := support_eq_of_eo_eq_true t pt htAlias
      have eps2 : ps2 = s := support_eq_of_eo_eq_true s ps2 hsAlias2
      subst ps; subst pt; subst ps2
      have hResultBool := raw_urem_result_bool x s t _ hBool
      change __smtx_typeof (SmtTerm.imp
        (SmtTerm.not (SmtTerm.eq (__eo_to_smt s) (__eo_to_smt zero)))
        (SmtTerm.bvult (__eo_to_smt t) (__eo_to_smt s))) = SmtType.Bool
        at hResultBool
      have hNN : term_has_non_none_type (SmtTerm.imp
          (SmtTerm.not (SmtTerm.eq (__eo_to_smt s) (__eo_to_smt zero)))
          (SmtTerm.bvult (__eo_to_smt t) (__eo_to_smt s))) := by
        unfold term_has_non_none_type
        rw [hResultBool]
        simp
      have hArgs := bool_binop_args_bool_of_non_none
        (typeof_imp_eq
          (SmtTerm.not (SmtTerm.eq (__eo_to_smt s) (__eo_to_smt zero)))
          (SmtTerm.bvult (__eo_to_smt t) (__eo_to_smt s))) hNN
      have hNotBool : RuleProofs.eo_has_bool_type
          (Term.Apply (Term.UOp UserOp.not)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) s) zero)) := hArgs.1
      have hEqBool := RuleProofs.eo_has_bool_type_not_arg _ hNotBool
      have hSides :=
        (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type s zero hEqBool).1
      have hzTy : __smtx_typeof (__eo_to_smt zero) = SmtType.BitVec w :=
        hSides.symm.trans hsTy
      have ez := validated_zero hzTy hZero
      subst zero
      change eo_interprets M
        ((Dsl.uremPred (.imp (.not (.eq .s .zero)) (.ult .t .s))).term
          w x s t) true
      apply Dsl.sound_urem_pred
        (q := .imp (.not (.eq .s .zero)) (.ult .t .s))
        M (by omega) x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_imp_not_decide_true_of (p := sb = 0#w)
      intro hs0
      exact decide_eq_true (urem2 xb sb tb hs0 hAnte)
    · exact matcher_urem3_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_urem3_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem to_z_numeral_eval (M : SmtModel) (y : Term) (w : Nat)
    (yb : BitVec w) (n : Int)
    (hz : __eo_to_z y = Term.Numeral n)
    (hev : __smtx_model_eval M (__eo_to_smt y) = bvValue yb) :
    yb.toNat = n := by
  cases y <;>
    first
    | (rename_i width payload
       change __smtx_model_eval M (SmtTerm.Binary width payload) = _ at hev
       simp only [__smtx_model_eval] at hev
       injection hev with _ hpayload
       change Term.Numeral payload = Term.Numeral n at hz
       injection hz with hn
       exact hpayload.symm.trans hn)
    | (change __smtx_model_eval M (SmtTerm.Numeral _) = _ at hev
       simp only [__smtx_model_eval, bvValue, reduceCtorEq] at hev)
    | (change __smtx_model_eval M (SmtTerm.Rational _) = _ at hev
       simp only [__smtx_model_eval, bvValue, reduceCtorEq] at hev)
    | (change __smtx_model_eval M (SmtTerm.String _) = _ at hev
       simp only [__smtx_model_eval, bvValue, reduceCtorEq] at hev)
    | (simp only [__eo_to_z, reduceCtorEq] at hz)

theorem matcher_urem1_sound
    (M : SmtModel) (hM : model_total_typed M)
    (x s t l : Term) (w : Nat) (xb sb tb : BitVec w)
    (hw : 3 ≤ w)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l))
    (hmatch : __bv_abstraction_lemma_urem x s t l = Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) s)) t)) l)
      true := by
  fun_cases __bv_abstraction_lemma_urem x s t l
  all_goals simp only [__bv_abstraction_lemma_urem] at hmatch
  all_goals try { simp at hmatch }
  case case5 ps c pt z h px powerTerm hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hVals⟩
      rcases eo_and_eq_true_args _ _ hAliases with ⟨hAliases', hxAlias⟩
      rcases eo_and_eq_true_args _ _ hAliases' with ⟨hsAlias, htAlias⟩
      have eps : ps = s := support_eq_of_eo_eq_true s ps hsAlias
      have ept : pt = t := support_eq_of_eo_eq_true t pt htAlias
      have epx : px = x := support_eq_of_eo_eq_true x px hxAlias
      subst ps; subst pt; subst px
      rcases eo_and_eq_true_args _ _ hVals with ⟨hZero, hPower⟩
      have hLBool := raw_urem_result_bool x s t _ hBool
      change RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) s) c))
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t)
            (Term.Apply (Term.Apply (Term.UOp UserOp.concat) z)
              (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
                (Term.Apply (Term.UOp2 UserOp2.extract h (Term.Numeral 0)) x))
                (Term.Binary 0 0))))) at hLBool
      change __smtx_typeof
        (SmtTerm.imp (SmtTerm.eq (__eo_to_smt s) (__eo_to_smt c))
          (SmtTerm.eq (__eo_to_smt t)
            (SmtTerm.concat (__eo_to_smt z)
              (SmtTerm.concat
                (SmtTerm.extract (__eo_to_smt h) (SmtTerm.Numeral 0)
                  (__eo_to_smt x))
                (SmtTerm.Binary 0 0))))) = SmtType.Bool at hLBool
      have hLNN : term_has_non_none_type
          (SmtTerm.imp (SmtTerm.eq (__eo_to_smt s) (__eo_to_smt c))
            (SmtTerm.eq (__eo_to_smt t)
              (SmtTerm.concat (__eo_to_smt z)
                (SmtTerm.concat
                  (SmtTerm.extract (__eo_to_smt h) (SmtTerm.Numeral 0)
                    (__eo_to_smt x))
                  (SmtTerm.Binary 0 0))))) := by
        unfold term_has_non_none_type
        rw [hLBool]
        simp
      have hLArgs := bool_binop_args_bool_of_non_none
        (typeof_imp_eq (SmtTerm.eq (__eo_to_smt s) (__eo_to_smt c))
          (SmtTerm.eq (__eo_to_smt t)
            (SmtTerm.concat (__eo_to_smt z)
              (SmtTerm.concat
                (SmtTerm.extract (__eo_to_smt h) (SmtTerm.Numeral 0)
                  (__eo_to_smt x))
                (SmtTerm.Binary 0 0))))) hLNN
      have hAnteTypes :=
        RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type s c hLArgs.1
      have hcTy : __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w :=
        hAnteTypes.1.symm.trans hsTy
      have hConsTypes :=
        RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type t
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat) z)
            (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
              (Term.Apply (Term.UOp2 UserOp2.extract h (Term.Numeral 0)) x))
              (Term.Binary 0 0))) hLArgs.2
      have hRhsTy : __smtx_typeof
          (SmtTerm.concat (__eo_to_smt z)
            (SmtTerm.concat
              (SmtTerm.extract (__eo_to_smt h) (SmtTerm.Numeral 0)
                (__eo_to_smt x))
              (SmtTerm.Binary 0 0))) = SmtType.BitVec w :=
        hConsTypes.1.symm.trans htTy
      have hRhsNN : term_has_non_none_type
          (SmtTerm.concat (__eo_to_smt z)
            (SmtTerm.concat
              (SmtTerm.extract (__eo_to_smt h) (SmtTerm.Numeral 0)
                (__eo_to_smt x))
              (SmtTerm.Binary 0 0))) := by
        unfold term_has_non_none_type
        rw [hRhsTy]
        simp
      rcases bv_concat_args_of_non_none hRhsNN with
        ⟨p, q, hzTy, hInnerTy⟩
      have hInnerNN : term_has_non_none_type
          (SmtTerm.concat
            (SmtTerm.extract (__eo_to_smt h) (SmtTerm.Numeral 0)
              (__eo_to_smt x))
            (SmtTerm.Binary 0 0)) := by
        unfold term_has_non_none_type
        rw [hInnerTy]
        simp
      rcases bv_concat_args_of_non_none hInnerNN with
        ⟨r, emptyWidth, hExtractTy, hEmptyTy⟩
      have hExtractNN : term_has_non_none_type
          (SmtTerm.extract (__eo_to_smt h) (SmtTerm.Numeral 0)
            (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [hExtractTy]
        simp
      rcases extract_args_of_non_none hExtractNN with
        ⟨i, j, wx, hh, hj, hxTy', hj0, hExtractPos, hiw⟩
      injection hj with hjEq
      subst j
      rw [hxTy] at hxTy'
      injection hxTy' with hwx
      subst wx
      have hi0 : 0 ≤ i := by
        have hiPos : 0 < i + 1 := by
          simpa [SmtEval.native_zlt, native_zplus, native_zneg] using hExtractPos
        exact Int.le_of_lt_add_one hiPos
      let k : Nat := i.toNat
      have hik : (k : Int) = i := Int.toNat_of_nonneg hi0
      rw [← hik] at hh hiw hExtractPos
      have eh : h = Term.Numeral (k : Int) :=
        TranslationProofs.eo_to_smt_eq_numeral h (k : Int) hh
      subst h
      have hkw : k < w := by
        simpa [native_zlt, SmtEval.native_nat_to_int] using hiw
      have hr : r = k + 1 := by
        rw [typeof_extract_eq, hxTy] at hExtractTy
        change __smtx_typeof_extract (SmtTerm.Numeral (k : Int))
          (SmtTerm.Numeral 0) (SmtType.BitVec w) = SmtType.BitVec r
          at hExtractTy
        simp [__smtx_typeof_extract, native_ite, SmtEval.native_zleq,
          SmtEval.native_zlt, native_zplus, native_zneg,
          SmtEval.native_int_to_nat, SmtEval.native_nat_to_int, hkw]
          at hExtractTy
        exact hExtractTy.symm
      subst r
      have hew : emptyWidth = 0 := by
        change SmtType.BitVec 0 = SmtType.BitVec emptyWidth at hEmptyTy
        injection hEmptyTy with h
        exact h.symm
      subst emptyWidth
      have hq : q = k + 1 := by
        rw [typeof_concat_eq, hExtractTy, hEmptyTy] at hInnerTy
        simp [__smtx_typeof_concat, native_nat_plus] at hInnerTy
        simpa [SmtEval.native_int_to_nat, SmtEval.native_nat_to_int,
          native_zplus] using hInnerTy.symm
      subst q
      have hpw : p + (k + 1) = w := by
        rw [typeof_concat_eq, hzTy, hInnerTy] at hRhsTy
        simp [__smtx_typeof_concat, native_nat_plus] at hRhsTy
        simp only [SmtEval.native_int_to_nat, SmtEval.native_nat_to_int,
          native_zplus] at hRhsTy
        have hToNat :
            Int.toNat (Int.ofNat p + Int.ofNat (k + 1)) = p + (k + 1) := rfl
        rw [hToNat] at hRhsTy
        exact hRhsTy
      have ez := validated_zero hzTy hZero
      subst z
      obtain ⟨cb, hc⟩ := eval_as_bvValue M hM c w hcTy
      have hPower' : __eo_to_z c =
          Term.Numeral ((2 : Int) ^ (k + 1)) := by
        have hkNonneg : ¬((k : Int) + 1 < 0) := by omega
        have hEq := support_eq_of_eo_eq_true (__eo_to_z c)
          (Term.Numeral ((2 : Int) ^ (k + 1)))
        apply (hEq ?_).symm
        simpa [__eo_add, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
          __eo_pow, native_ite, native_teq, native_zlt, native_zexp_total,
          native_zplus, native_and, native_not, hkNonneg] using hPower
      have hcbInt : (cb.toNat : Int) = (2 : Int) ^ (k + 1) :=
        to_z_numeral_eval M c w cb ((2 : Int) ^ (k + 1)) hPower' hc
      have hcb : cb.toNat = 2 ^ (k + 1) := by exact_mod_cast hcbInt
      have hRhsEval : __smtx_model_eval M
          (SmtTerm.concat (__eo_to_smt (Dsl.constTerm p 0))
            (SmtTerm.concat
              (SmtTerm.extract (SmtTerm.Numeral (k : Int))
                (SmtTerm.Numeral 0) (__eo_to_smt x))
              (SmtTerm.Binary 0 0))) =
          bvValue (BitVec.ofNat w (xb.toNat % 2 ^ (k + 1))) := by
        change __smtx_model_eval_concat
          (__smtx_model_eval M (__eo_to_smt (Dsl.constTerm p 0)))
          (__smtx_model_eval_concat
            (__smtx_model_eval_extract (SmtValue.Numeral (k : Int))
              (SmtValue.Numeral 0)
              (__smtx_model_eval M (__eo_to_smt x)))
            (SmtValue.Binary 0 0)) = _
        rw [Dsl.eval_constTerm_zero, hx]
        exact eval_zero_concat_extract_zero xb hkw hpw
      have hRem : xb % cb =
          BitVec.ofNat w (xb.toNat % 2 ^ (k + 1)) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_umod, hcb, BitVec.toNat_ofNat]
        have hlt : xb.toNat % 2 ^ (k + 1) < 2 ^ w := by
          exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
            (Nat.le_of_lt (by simpa [hcb] using cb.isLt))
        rw [Nat.mod_eq_of_lt hlt]
      rw [RuleProofs.eo_interprets_iff_smt_interprets]
      refine smt_interprets.intro_true M _ hBool ?_
      change __smtx_model_eval_imp
        (__smtx_model_eval_eq
          (__smtx_model_eval_bvurem
            (__smtx_model_eval M (__eo_to_smt x))
            (__smtx_model_eval M (__eo_to_smt s)))
          (__smtx_model_eval M (__eo_to_smt t)))
        (__smtx_model_eval_imp
          (__smtx_model_eval_eq
            (__smtx_model_eval M (__eo_to_smt s))
            (__smtx_model_eval M (__eo_to_smt c)))
          (__smtx_model_eval_eq
            (__smtx_model_eval M (__eo_to_smt t))
            (__smtx_model_eval M
              (SmtTerm.concat (__eo_to_smt (Dsl.constTerm p 0))
                (SmtTerm.concat
                  (SmtTerm.extract (SmtTerm.Numeral (k : Int))
                    (SmtTerm.Numeral 0) (__eo_to_smt x))
                  (SmtTerm.Binary 0 0)))))) = SmtValue.Boolean true
      rw [hx, hs, ht, hc, hRhsEval, eval_bvurem_bvValue (by omega),
        eval_eq_bvValue, eval_eq_bvValue, eval_eq_bvValue]
      simp only [__smtx_model_eval_imp, __smtx_model_eval_not,
        __smtx_model_eval_or, native_not, native_or]
      congr 1
      change (!decide (xb % sb = tb) ||
        (!decide (sb = cb) ||
          decide (tb = BitVec.ofNat w (xb.toNat % 2 ^ (k + 1))))) = true
      apply Dsl.bool_imp_true_of
      intro hAnte
      apply Dsl.bool_imp_true_of
      intro hSc
      have hRemS : xb % sb =
          BitVec.ofNat w (xb.toNat % 2 ^ (k + 1)) := by
        rw [hSc]
        exact hRem
      exact decide_eq_true (hAnte.symm.trans hRemS)
    · exact matcher_urem2_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2
  case case6 =>
    exact matcher_urem2_sound M hM x s t l w xb sb tb hw hxTy hsTy htTy
      hx hs ht hBool hmatch

theorem matcher_udiv37_sound
    (M : SmtModel) (hM : model_total_typed M)
    (x s t l : Term) (w : Nat) (xb sb tb : BitVec w)
    (hw : 3 ≤ w)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l))
    (hmatch : __eo_l_37___bv_abstraction_lemma_udiv x s t l =
      Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l)
      true := by
  fun_cases __eo_l_37___bv_abstraction_lemma_udiv x s t l <;>
    simp [__eo_l_37___bv_abstraction_lemma_udiv] at hmatch

theorem matcher_udiv36_sound
    (M : SmtModel) (hM : model_total_typed M)
    (x s t l : Term) (w : Nat) (xb sb tb : BitVec w)
    (hw : 3 ≤ w)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.BitVec w)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l))
    (hmatch : __eo_l_36___bv_abstraction_lemma_udiv x s t l =
      Term.Boolean true) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) s)) t)) l)
      true := by
  fun_cases __eo_l_36___bv_abstraction_lemma_udiv x s t l
  all_goals simp only [__eo_l_36___bv_abstraction_lemma_udiv] at hmatch
  all_goals try { simp [__eo_l_37___bv_abstraction_lemma_udiv] at hmatch }
  case case5 px1 cone px2 px3 pt hxne hsne htne =>
    rcases eo_ite_eq_true_cases _ _ _ hmatch with hCurrent | hFallback
    · rcases hCurrent with ⟨hAliases, hOne⟩
      rcases eo_and_eq_true_args _ _ hAliases with ⟨hxxx, htAlias⟩
      rcases eo_and_eq_true_args _ _ hxxx with ⟨hxx, hx3Alias⟩
      rcases eo_and_eq_true_args _ _ hxx with ⟨hx1Alias, hx2Alias⟩
      have epx1 : px1 = x := support_eq_of_eo_eq_true x px1 hx1Alias
      have epx2 : px2 = x := support_eq_of_eo_eq_true x px2 hx2Alias
      have epx3 : px3 = x := support_eq_of_eo_eq_true x px3 hx3Alias
      have ept : pt = t := support_eq_of_eo_eq_true t pt htAlias
      subst px1; subst px2; subst px3; subst pt
      let p : Raw.Pred := .not (.eq .x
        (.sub (.lit cone) (.shl .x (.sub .x .t))))
      have hpBool : RuleProofs.eo_has_bool_type (p.term x s t) := by
        simpa [p, Raw.Pred.term, Raw.Expr.term] using
          raw_udiv_result_bool x s t _ hBool
      have hLits := p.literals_typed_of_bool x s t w hxTy hsTy htTy
        rfl hpBool
      have hcTy : __smtx_typeof (__eo_to_smt cone) = SmtType.BitVec w :=
        hLits cone (by simp [p, Raw.Pred.literals, Raw.Expr.literals])
      have hc := validated_one (by omega) hcTy hOne
      subst cone
      change eo_interprets M
        ((Dsl.udivPred (.not (.eq .x
          (.sub .one (.shl .x (.sub .x .t)))))).term w x s t) true
      apply Dsl.sound_udiv_pred (q := .not (.eq .x
        (.sub .one (.shl .x (.sub .x .t))))) M (by omega)
        x s t xb sb tb hx hs ht hBool
      intro hAnte
      simp only [Dsl.Pred.value, Dsl.Expr.value]
      apply bool_not_decide_true_of
      intro hEq
      apply Udiv36Case.udiv36 hw xb sb
      rw [hAnte]
      exact hEq
    · exact matcher_udiv37_sound M hM x s t _ w xb sb tb hw hxTy hsTy htTy
        hx hs ht hBool hFallback.2

end Matcher
end BvAbstraction
