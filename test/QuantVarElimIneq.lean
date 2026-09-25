import Cpc.Proofs.Rules.Quant_var_elim_ineq
import Lean

open Eo SmtEval

/-! Checker regressions for arithmetic quantifier elimination. -/
namespace QuantVarElimIneqTests
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def var (name : String) (T : UserOp) : Term :=
  Term.Var (Term.String (native_string_lit name)) (Term.UOp T)
private def binders : List Term → Term
  | [] => Term.__eo_List_nil
  | x :: xs => (Term.__eo_List_cons.Apply x).Apply (binders xs)
private def bin (op : UserOp) (a b : Term) := ((Term.UOp op).Apply a).Apply b
private def disj (a b : Term) := bin UserOp.or a (bin UserOp.or b (Term.Boolean false))
private def all (xs : List Term) (f : Term) := bin UserOp.forall (binders xs) f
private def conclusion (xs : List Term) (f g : Term) := bin UserOp.eq (all xs f) g
private def x := var "x" UserOp.Int
private def y := var "y" UserOp.Int
private def r := var "r" UserOp.Real
private def p := Term.Var (Term.String (native_string_lit "p")) Term.Bool

-- Strict integer and non-strict real bounds both admit elimination.
example : __eo_prog_quant_var_elim_ineq
    (conclusion [x] (bin UserOp.lt x (Term.Numeral 0)) (Term.Boolean false)) =
    conclusion [x] (bin UserOp.lt x (Term.Numeral 0)) (Term.Boolean false) := by native_decide

example : __eo_prog_quant_var_elim_ineq
    (conclusion [r] (bin UserOp.leq r (Term.Rational 0)) (Term.Boolean false)) =
    conclusion [r] (bin UserOp.leq r (Term.Rational 0)) (Term.Boolean false) := by native_decide

-- Lower bounds use the opposite escape direction.
example : __eo_prog_quant_var_elim_ineq
    (conclusion [x] (bin UserOp.geq x (Term.Numeral 0)) (Term.Boolean false)) =
    conclusion [x] (bin UserOp.geq x (Term.Numeral 0)) (Term.Boolean false) := by native_decide

-- An equality excludes only a bounded set of assignments.
example : __eo_prog_quant_var_elim_ineq
    (conclusion [x] (bin UserOp.eq x (Term.Numeral 0)) (Term.Boolean false)) =
    conclusion [x] (bin UserOp.eq x (Term.Numeral 0)) (Term.Boolean false) := by native_decide

-- Retain the disjunct independent of the eliminated variable.
example : __eo_prog_quant_var_elim_ineq
    (conclusion [x] (disj (bin UserOp.leq x (Term.Numeral 0)) p) p) =
    conclusion [x] (disj (bin UserOp.leq x (Term.Numeral 0)) p) p := by native_decide

-- Eliminate a binder while preserving the other quantifiers.
example : __eo_prog_quant_var_elim_ineq
    (conclusion [x,y] (disj (bin UserOp.leq x y) p) (all [y] p)) =
    conclusion [x,y] (disj (bin UserOp.leq x y) p) (all [y] p) := by native_decide

-- Repeated binders exercise multiset difference and erase-first semantics.
example : __eo_prog_quant_var_elim_ineq
    (conclusion [x,x,y] (disj (bin UserOp.leq x y) p) (all [x,y] p)) =
    conclusion [x,x,y] (disj (bin UserOp.leq x y) p) (all [x,y] p) := by native_decide

-- Opposite directions cannot be made false together.
example : __eo_prog_quant_var_elim_ineq
    (conclusion [x] (disj (bin UserOp.leq x (Term.Numeral 0))
      (bin UserOp.geq x (Term.Numeral 0))) (Term.Boolean false)) = Term.Stuck := by native_decide

-- Cancellation must not produce a spurious nonzero direction.
example : __eo_prog_quant_var_elim_ineq
    (conclusion [x] (bin UserOp.lt (bin UserOp.neg x x) (Term.Numeral 0))
      (Term.Boolean false)) = Term.Stuck := by native_decide

-- Nonlinear monomials containing the eliminated variable are rejected.
example : __eo_prog_quant_var_elim_ineq
    (conclusion [x] (bin UserOp.leq (bin UserOp.mult x x) (Term.Numeral 0))
      (Term.Boolean false)) = Term.Stuck := by native_decide

end QuantVarElimIneqTests

-- Check the transitive proof dependencies, not just the rule file's source.
open Lean Elab Command in
run_cmd do
  let axioms ← liftCoreM <| Lean.collectAxioms ``cmd_step_quant_var_elim_ineq_properties
  if axioms.contains ``sorryAx then
    throwError "quant_var_elim_ineq depends on sorryAx"
