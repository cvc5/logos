module

public import Cpc.Proofs.RuleSupport.BvAbstractionEvalSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionEvalSupport

public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

open Eo SmtEval Smtm

namespace BvAbstraction
namespace Dsl

inductive Expr where
  | x | s | t | zero | one | ones
  | neg (a : Expr) | not (a : Expr)
  | mul (a b : Expr) | add (a b : Expr) | sub (a b : Expr)
  | and (a b : Expr) | or (a b : Expr) | xor (a b : Expr)
  | shl (a b : Expr) | lshr (a b : Expr)
  | udiv (a b : Expr) | urem (a b : Expr)
deriving DecidableEq

def constTerm (w : Nat) (n : Int) : Term :=
  Term.Binary (native_nat_to_int w) n

def Expr.term (w : Nat) (x s t : Term) : Expr -> Term
  | .x => x
  | .s => s
  | .t => t
  | .zero => constTerm w 0
  | .one => constTerm w 1
  | .ones => constTerm w ((2 : Int) ^ w - 1)
  | .neg a => Term.Apply (Term.UOp UserOp.bvneg) (a.term w x s t)
  | .not a => Term.Apply (Term.UOp UserOp.bvnot) (a.term w x s t)
  | .mul a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
      (a.term w x s t)) (b.term w x s t)
  | .add a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvadd)
      (a.term w x s t)) (b.term w x s t)
  | .sub a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvsub)
      (a.term w x s t)) (b.term w x s t)
  | .and a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvand)
      (a.term w x s t)) (b.term w x s t)
  | .or a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvor)
      (a.term w x s t)) (b.term w x s t)
  | .xor a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvxor)
      (a.term w x s t)) (b.term w x s t)
  | .shl a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvshl)
      (a.term w x s t)) (b.term w x s t)
  | .lshr a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvlshr)
      (a.term w x s t)) (b.term w x s t)
  | .udiv a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv)
      (a.term w x s t)) (b.term w x s t)
  | .urem a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvurem)
      (a.term w x s t)) (b.term w x s t)

def Expr.value {w : Nat} (x s t : BitVec w) : Expr -> BitVec w
  | .x => x
  | .s => s
  | .t => t
  | .zero => 0#w
  | .one => 1#w
  | .ones => -1#w
  | .neg a => -(a.value x s t)
  | .not a => ~~~(a.value x s t)
  | .mul a b => a.value x s t * b.value x s t
  | .add a b => a.value x s t + b.value x s t
  | .sub a b => a.value x s t - b.value x s t
  | .and a b => a.value x s t &&& b.value x s t
  | .or a b => a.value x s t ||| b.value x s t
  | .xor a b => a.value x s t ^^^ b.value x s t
  | .shl a b => a.value x s t <<< (b.value x s t).toNat
  | .lshr a b => a.value x s t >>> (b.value x s t).toNat
  | .udiv a b => (a.value x s t).smtUDiv (b.value x s t)
  | .urem a b => a.value x s t % b.value x s t

theorem eval_constTerm_zero (M : SmtModel) (w : Nat) :
    __smtx_model_eval M (__eo_to_smt (constTerm w 0)) = bvValue (0#w) := by
  change SmtValue.Binary (native_nat_to_int w) 0 = bvValue (0#w)
  simp [bvValue]

theorem eval_constTerm_one (M : SmtModel) (w : Nat) (hw : 0 < w) :
    __smtx_model_eval M (__eo_to_smt (constTerm w 1)) = bvValue (1#w) := by
  change SmtValue.Binary (native_nat_to_int w) 1 = bvValue (1#w)
  simp only [bvValue]
  congr 1
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
    (Nat.one_lt_two_pow (Nat.ne_of_gt hw))]
  norm_cast

theorem eval_constTerm_ones (M : SmtModel) (w : Nat) (hw : 0 < w) :
    __smtx_model_eval M (__eo_to_smt (constTerm w ((2 : Int) ^ w - 1))) =
      bvValue (-1#w) := by
  change SmtValue.Binary (native_nat_to_int w) ((2 : Int) ^ w - 1) =
    bvValue (-1#w)
  simp only [bvValue]
  congr 1
  have hone : (1#w).toNat = 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
      (Nat.one_lt_two_pow (Nat.ne_of_gt hw))]
  have honePos : 0#w < 1#w := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.zero_mod, hone]
    exact Nat.zero_lt_one
  rw [BitVec.toNat_neg_of_pos honePos, hone]
  norm_cast
  have hle : 1 ≤ 2 ^ w :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.two_pow_pos w))
  exact (Int.ofNat_sub hle).symm

theorem Expr.eval_term (M : SmtModel) {w : Nat} (hw : 0 < w)
    (x s t : Term) (xb sb tb : BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb) (e : Expr) :
    __smtx_model_eval M (__eo_to_smt (e.term w x s t)) =
      bvValue (e.value xb sb tb) := by
  induction e with
  | x => exact hx
  | s => exact hs
  | t => exact ht
  | zero => exact eval_constTerm_zero M w
  | one => exact eval_constTerm_one M w hw
  | ones => exact eval_constTerm_ones M w hw
  | neg a ih =>
      change __smtx_model_eval_bvneg
          (__smtx_model_eval M (__eo_to_smt (a.term w x s t))) = _
      rw [ih, eval_bvneg_bvValue]
      rfl
  | not a ih =>
      change __smtx_model_eval_bvnot
          (__smtx_model_eval M (__eo_to_smt (a.term w x s t))) = _
      rw [ih, eval_bvnot_bvValue]
      rfl
  | mul a b iha ihb =>
      change __smtx_model_eval_bvmul
          (__smtx_model_eval M (__eo_to_smt (a.term w x s t)))
          (__smtx_model_eval M (__eo_to_smt (b.term w x s t))) = _
      rw [iha, ihb, eval_bvmul_bvValue]
      rfl
  | add a b iha ihb =>
      change __smtx_model_eval_bvadd
          (__smtx_model_eval M (__eo_to_smt (a.term w x s t)))
          (__smtx_model_eval M (__eo_to_smt (b.term w x s t))) = _
      rw [iha, ihb, eval_bvadd_bvValue]
      rfl
  | sub a b iha ihb =>
      change __smtx_model_eval_bvsub
          (__smtx_model_eval M (__eo_to_smt (a.term w x s t)))
          (__smtx_model_eval M (__eo_to_smt (b.term w x s t))) = _
      rw [iha, ihb, eval_bvsub_bvValue]
      rfl
  | and a b iha ihb =>
      change __smtx_model_eval_bvand
          (__smtx_model_eval M (__eo_to_smt (a.term w x s t)))
          (__smtx_model_eval M (__eo_to_smt (b.term w x s t))) = _
      rw [iha, ihb, eval_bvand_bvValue hw]
      rfl
  | or a b iha ihb =>
      change __smtx_model_eval_bvor
          (__smtx_model_eval M (__eo_to_smt (a.term w x s t)))
          (__smtx_model_eval M (__eo_to_smt (b.term w x s t))) = _
      rw [iha, ihb, eval_bvor_bvValue hw]
      rfl
  | xor a b iha ihb =>
      change __smtx_model_eval_bvxor
          (__smtx_model_eval M (__eo_to_smt (a.term w x s t)))
          (__smtx_model_eval M (__eo_to_smt (b.term w x s t))) = _
      rw [iha, ihb, eval_bvxor_bvValue hw]
      rfl
  | shl a b iha ihb =>
      change __smtx_model_eval_bvshl
          (__smtx_model_eval M (__eo_to_smt (a.term w x s t)))
          (__smtx_model_eval M (__eo_to_smt (b.term w x s t))) = _
      rw [iha, ihb, eval_bvshl_bvValue]
      rfl
  | lshr a b iha ihb =>
      change __smtx_model_eval_bvlshr
          (__smtx_model_eval M (__eo_to_smt (a.term w x s t)))
          (__smtx_model_eval M (__eo_to_smt (b.term w x s t))) = _
      rw [iha, ihb, eval_bvlshr_bvValue]
      rfl
  | udiv a b iha ihb =>
      change __smtx_model_eval_bvudiv
          (__smtx_model_eval M (__eo_to_smt (a.term w x s t)))
          (__smtx_model_eval M (__eo_to_smt (b.term w x s t))) = _
      rw [iha, ihb, eval_bvudiv_bvValue hw]
      rfl
  | urem a b iha ihb =>
      change __smtx_model_eval_bvurem
          (__smtx_model_eval M (__eo_to_smt (a.term w x s t)))
          (__smtx_model_eval M (__eo_to_smt (b.term w x s t))) = _
      rw [iha, ihb, eval_bvurem_bvValue hw]
      rfl

inductive Pred where
  | eq (a b : Expr) | ult (a b : Expr) | ule (a b : Expr) | uge (a b : Expr)
  | true | not (p : Pred) | and (p q : Pred) | imp (p q : Pred)
deriving DecidableEq

def Pred.term (w : Nat) (x s t : Term) : Pred -> Term
  | .eq a b => Term.Apply (Term.Apply (Term.UOp UserOp.eq)
      (a.term w x s t)) (b.term w x s t)
  | .ult a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvult)
      (a.term w x s t)) (b.term w x s t)
  | .ule a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvule)
      (a.term w x s t)) (b.term w x s t)
  | .uge a b => Term.Apply (Term.Apply (Term.UOp UserOp.bvuge)
      (a.term w x s t)) (b.term w x s t)
  | .true => Term.Boolean Bool.true
  | .not p => Term.Apply (Term.UOp UserOp.not) (p.term w x s t)
  | .and p q => Term.Apply (Term.Apply (Term.UOp UserOp.and)
      (p.term w x s t)) (q.term w x s t)
  | .imp p q => Term.Apply (Term.Apply (Term.UOp UserOp.imp)
      (p.term w x s t)) (q.term w x s t)

def Pred.value {w : Nat} (x s t : BitVec w) : Pred -> Bool
  | .eq a b => decide (a.value x s t = b.value x s t)
  | .ult a b => decide (a.value x s t < b.value x s t)
  | .ule a b => decide (a.value x s t ≤ b.value x s t)
  | .uge a b => decide (b.value x s t ≤ a.value x s t)
  | .true => Bool.true
  | .not p => !(p.value x s t)
  | .and p q => p.value x s t && q.value x s t
  | .imp p q => !(p.value x s t) || q.value x s t

theorem Pred.eval_term (M : SmtModel) {w : Nat} (hw : 0 < w)
    (x s t : Term) (xb sb tb : BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb) (p : Pred) :
    __smtx_model_eval M (__eo_to_smt (p.term w x s t)) =
      SmtValue.Boolean (p.value xb sb tb) := by
  induction p with
  | eq a b =>
      change __smtx_model_eval_eq
          (__smtx_model_eval M (__eo_to_smt (a.term w x s t)))
          (__smtx_model_eval M (__eo_to_smt (b.term w x s t))) = _
      rw [a.eval_term M hw x s t xb sb tb hx hs ht,
        b.eval_term M hw x s t xb sb tb hx hs ht, eval_eq_bvValue]
      rfl
  | ult a b =>
      change __smtx_model_eval_bvult
          (__smtx_model_eval M (__eo_to_smt (a.term w x s t)))
          (__smtx_model_eval M (__eo_to_smt (b.term w x s t))) = _
      rw [a.eval_term M hw x s t xb sb tb hx hs ht,
        b.eval_term M hw x s t xb sb tb hx hs ht, eval_bvult_bvValue]
      rfl
  | ule a b =>
      change __smtx_model_eval_bvule
          (__smtx_model_eval M (__eo_to_smt (a.term w x s t)))
          (__smtx_model_eval M (__eo_to_smt (b.term w x s t))) = _
      rw [a.eval_term M hw x s t xb sb tb hx hs ht,
        b.eval_term M hw x s t xb sb tb hx hs ht, eval_bvule_bvValue]
      rfl
  | uge a b =>
      change __smtx_model_eval_bvuge
          (__smtx_model_eval M (__eo_to_smt (a.term w x s t)))
          (__smtx_model_eval M (__eo_to_smt (b.term w x s t))) = _
      rw [a.eval_term M hw x s t xb sb tb hx hs ht,
        b.eval_term M hw x s t xb sb tb hx hs ht, eval_bvuge_bvValue]
      rfl
  | true => rfl
  | not p ih =>
      change __smtx_model_eval_not
          (__smtx_model_eval M (__eo_to_smt (p.term w x s t))) = _
      rw [ih]
      change SmtValue.Boolean (!(p.value xb sb tb)) =
        SmtValue.Boolean (!(p.value xb sb tb))
      rfl
  | and p q ihp ihq =>
      change __smtx_model_eval_and
          (__smtx_model_eval M (__eo_to_smt (p.term w x s t)))
          (__smtx_model_eval M (__eo_to_smt (q.term w x s t))) = _
      rw [ihp, ihq]
      change SmtValue.Boolean (p.value xb sb tb && q.value xb sb tb) =
        SmtValue.Boolean (p.value xb sb tb && q.value xb sb tb)
      rfl
  | imp p q ihp ihq =>
      change __smtx_model_eval_imp
          (__smtx_model_eval M (__eo_to_smt (p.term w x s t)))
          (__smtx_model_eval M (__eo_to_smt (q.term w x s t))) = _
      rw [ihp, ihq]
      simp [__smtx_model_eval_imp, __smtx_model_eval_or,
        __smtx_model_eval_not, native_not, native_or]
      rfl

theorem sound_pred (M : SmtModel) {w : Nat} (hw : 0 < w)
    (x s t : Term) (xb sb tb : BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (p : Pred) (hBool : RuleProofs.eo_has_bool_type (p.term w x s t))
    (hp : p.value xb sb tb = true) :
    eo_interprets M (p.term w x s t) true := by
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  refine smt_interprets.intro_true M _ hBool ?_
  rw [p.eval_term M hw x s t xb sb tb hx hs ht, hp]

def uremPred (q : Pred) : Pred :=
  .imp (.eq (.urem .x .s) .t) q

def udivPred (q : Pred) : Pred :=
  .imp (.eq (.udiv .x .s) .t) q

def mulPred (q : Pred) : Pred :=
  .imp (.eq (.mul .x .s) .t) q

theorem bool_imp_true_of {p : Prop} [Decidable p] {b : Bool}
    (h : p -> b = true) : (!decide p || b) = true := by
  cases hd : decide p with
  | false => rfl
  | true =>
      have hp : p := of_decide_eq_true hd
      simpa [hd] using h hp

theorem sound_urem_pred (M : SmtModel) {w : Nat} (hw : 0 < w)
    (x s t : Term) (xb sb tb : BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (q : Pred)
    (hBool : RuleProofs.eo_has_bool_type ((uremPred q).term w x s t))
    (hq : xb % sb = tb -> q.value xb sb tb = true) :
    eo_interprets M ((uremPred q).term w x s t) true := by
  apply sound_pred M hw x s t xb sb tb hx hs ht _ hBool
  simp only [uremPred, Pred.value, Expr.value]
  exact bool_imp_true_of hq

theorem sound_udiv_pred (M : SmtModel) {w : Nat} (hw : 0 < w)
    (x s t : Term) (xb sb tb : BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (q : Pred)
    (hBool : RuleProofs.eo_has_bool_type ((udivPred q).term w x s t))
    (hq : xb.smtUDiv sb = tb -> q.value xb sb tb = true) :
    eo_interprets M ((udivPred q).term w x s t) true := by
  apply sound_pred M hw x s t xb sb tb hx hs ht _ hBool
  simp only [udivPred, Pred.value, Expr.value]
  exact bool_imp_true_of hq

theorem sound_mul_pred (M : SmtModel) {w : Nat} (hw : 0 < w)
    (x s t : Term) (xb sb tb : BitVec w)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bvValue xb)
    (hs : __smtx_model_eval M (__eo_to_smt s) = bvValue sb)
    (ht : __smtx_model_eval M (__eo_to_smt t) = bvValue tb)
    (q : Pred)
    (hBool : RuleProofs.eo_has_bool_type ((mulPred q).term w x s t))
    (hq : xb * sb = tb -> q.value xb sb tb = true) :
    eo_interprets M ((mulPred q).term w x s t) true := by
  apply sound_pred M hw x s t xb sb tb hx hs ht _ hBool
  simp only [mulPred, Pred.value, Expr.value]
  exact bool_imp_true_of hq

end Dsl
end BvAbstraction
