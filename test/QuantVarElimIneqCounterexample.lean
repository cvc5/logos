import Cpc.Logos
import Cpc.Proofs.Assumptions
import Cpc.Proofs.TypePreservation.Helpers

open Eo SmtEval Smtm
/-!
Regression test for the polynomial occurrence check in `quant_var_elim_ineq`.

The original rule accepted `(= (forall ((x Int)) (<= x (abs x))) false)`.
The generic occurrence check mistakes the monomial `(@mon [abs x] -1)` for
a binder and skips its variable list. The dedicated polynomial occurrence
check must find `x` and reject this invalid equivalence.

Run:
  lake build Cpc.Proofs.Assumptions Cpc.Proofs.TypePreservation.Helpers
  lake env lean test/QuantVarElimIneqCounterexample.lean
-/
namespace QuantVarElimIneqCounterexample
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def x : Term := Term.Var (Term.String (native_string_lit "x")) (Term.UOp UserOp.Int)
def xs : Term := (Term.__eo_List_cons.Apply x).Apply Term.__eo_List_nil
def body : Term := ((Term.UOp UserOp.leq).Apply x).Apply ((Term.UOp UserOp.abs).Apply x)
def formula : Term := ((Term.UOp UserOp.eq).Apply
  (((Term.UOp UserOp.forall).Apply xs).Apply body)).Apply (Term.Boolean false)

/-- The source term has a free occurrence of `x`. -/
theorem abs_contains_x :
    __contains_atomic_term_list_free_rec ((Term.UOp UserOp.abs).Apply x)
      xs Term.__eo_List_nil = Term.Boolean true := by
  native_decide

/-- The generic occurrence check loses that occurrence in the polynomial encoding. -/
theorem polynomial_hides_x :
    __contains_atomic_term_list_free_rec
      (__poly_neg (__get_arith_poly_norm ((Term.UOp UserOp.abs).Apply x)))
      xs Term.__eo_List_nil = Term.Boolean false := by
  native_decide

/-- The dedicated polynomial occurrence check finds the hidden occurrence. -/
theorem polynomial_contains_x :
    __poly_contains_atomic_term_free
      (__poly_neg (__get_arith_poly_norm ((Term.UOp UserOp.abs).Apply x))) x =
      Term.Boolean true := by
  native_decide

/-- The corrected checker rejects the invalid equivalence. -/
theorem rejected : __eo_prog_quant_var_elim_ineq formula = Term.Stuck := by
  native_decide

theorem result_type : __eo_typeof formula = Term.Bool := by
  native_decide

theorem translation_type : __smtx_typeof (__eo_to_smt formula) = SmtType.Bool := by
  native_decide

def args : CArgList := CArgList.cons formula CArgList.nil

theorem command_translation_ok :
    cmdTranslationOk (CCmd.step CRule.quant_var_elim_ineq args CIndexList.nil) := by
  change (__smtx_typeof (__eo_to_smt formula) ≠ SmtType.None) ∧ True
  simp [translation_type]

theorem command_rejected (s : CState) :
    __eo_cmd_step_proven s CRule.quant_var_elim_ineq args CIndexList.nil = Term.Stuck := by
  exact rejected

def sx : SmtTerm := SmtTerm.Var (native_string_lit "x") SmtType.Int
def sbody : SmtTerm := SmtTerm.leq sx (SmtTerm.abs sx)
def slhs : SmtTerm := SmtTerm.not
  (SmtTerm.exists (native_string_lit "x") SmtType.Int (SmtTerm.not sbody))

theorem body_true (M : SmtModel) (n : Int) :
    __smtx_model_eval
      (native_model_push M (native_string_lit "x") SmtType.Int (SmtValue.Numeral n))
      sbody = SmtValue.Boolean true := by
  have hn : native_zleq n (native_zabs n) = true := by
    change decide (n ≤ native_zabs n) = true
    apply decide_eq_true
    dsimp only [native_zabs]
    split
    · rename_i h
      exact Int.le_trans (Int.le_of_lt h) (Int.neg_nonneg_of_nonpos (Int.le_of_lt h))
    · exact Int.le_refl n
  simp [sbody, sx, __smtx_model_eval, native_model_var_lookup, native_model_push,
    __smtx_model_eval_abs, __smtx_model_eval_leq, hn]

theorem lhs_true (M : SmtModel) :
    __smtx_model_eval M slhs = SmtValue.Boolean true := by
  have hNo : ¬ ∃ v : SmtValue,
      __smtx_typeof_value v = SmtType.Int ∧
      __smtx_value_canonical v = true ∧
      __smtx_model_eval (native_model_push M (native_string_lit "x") SmtType.Int v)
        (SmtTerm.not sbody) = SmtValue.Boolean true := by
    rintro ⟨v, hv, _, he⟩
    obtain ⟨n, rfl⟩ := int_value_canonical hv
    rw [__smtx_model_eval.eq_def] at he
    simp only [body_true, __smtx_model_eval_not, SmtEval.native_not] at he
    contradiction
  have hExists : __smtx_model_eval M
      (SmtTerm.exists (native_string_lit "x") SmtType.Int (SmtTerm.not sbody)) =
      SmtValue.Boolean false := by
    rw [__smtx_model_eval.eq_def]
    exact dif_neg hNo
  rw [slhs, __smtx_model_eval.eq_def]
  simp [hExists, __smtx_model_eval_not, SmtEval.native_not]

theorem translation : __eo_to_smt formula = SmtTerm.eq slhs (SmtTerm.Boolean false) := by
  native_decide

/-- The rejected conclusion is false in every model, including every well-formed model. -/
theorem conclusion_false (M : SmtModel) :
    __smtx_model_eval M (__eo_to_smt formula) = SmtValue.Boolean false := by
  rw [translation, __smtx_model_eval.eq_def]
  simp [lhs_true, __smtx_model_eval, __smtx_model_eval_eq, native_veq]

end QuantVarElimIneqCounterexample
