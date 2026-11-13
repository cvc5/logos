module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
import Cpc.Proofs.RuleSupport.CongSupport
import Cpc.Proofs.RuleSupport.StrEqReplSupport
import Cpc.Proofs.RuleSupport.StrReplaceAllSupport
public import Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Init.Data.Repr
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringToInt
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringToInt

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

theorem EvaluateProofInternal.eo_typeof_ite_args_of_ne_stuck
    (cTy tTy eTy : Term) :
    __eo_typeof_ite cTy tTy eTy ≠ Term.Stuck ->
      cTy = Term.Bool ∧ tTy = eTy ∧ tTy ≠ Term.Stuck := by
  intro h
  cases cTy <;> cases tTy <;> cases eTy <;>
    simp [__eo_typeof_ite, __eo_requires, __eo_eq, native_ite,
      native_not, native_teq] at h ⊢ <;>
    simp_all

theorem EvaluateProofInternal.eo_typeof_ite_bool_same_of_ne_stuck
    (T : Term) :
    T ≠ Term.Stuck ->
      __eo_typeof_ite Term.Bool T T = T := by
  intro hT
  cases T <;>
    simp [__eo_typeof_ite, __eo_requires, __eo_eq, native_ite,
      native_not, native_teq] at hT ⊢

theorem EvaluateProofInternal.eo_ite_selected_type_of_typeof
    (c t e T : Term) :
    __eo_typeof (__eo_ite c t e) = T ->
      T ≠ Term.Stuck ->
        ∃ b : Bool, c = Term.Boolean b ∧
          (if b then __eo_typeof t = T else __eo_typeof e = T) := by
  cases c <;> intro h hT <;> simp [__eo_ite, native_ite, native_teq] at h
  case Boolean b =>
    cases b
    · exact ⟨false, rfl, h⟩
    · exact ⟨true, rfl, h⟩
  all_goals
    exfalso
    change Term.Stuck = T at h
    exact hT h.symm

theorem EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
    (c t e : Term) :
    __eo_ite c t e ≠ Term.Stuck ->
      ∃ b : Bool, c = Term.Boolean b ∧
        (if b then t ≠ Term.Stuck else e ≠ Term.Stuck) := by
  cases c <;> intro h <;> simp [__eo_ite, native_ite, native_teq] at h
  case Boolean b =>
    cases b
    · exact ⟨false, rfl, h⟩
    · exact ⟨true, rfl, h⟩
  all_goals
    contradiction

theorem EvaluateProofInternal.eo_typeof_str_concat_args_of_seq_char
    (x y : Term)
    (h :
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_typeof x =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ∧
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  change __eo_typeof_str_concat (__eo_typeof x) (__eo_typeof y) =
    Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) at h
  cases hx : __eo_typeof x <;> cases hy : __eo_typeof y <;>
    simp [__eo_typeof_str_concat, hx, hy] at h ⊢
  case Apply f a g b =>
    cases f <;>
      try
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) at h
        cases h
    case UOp op =>
      cases op <;>
        try
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) at h
          cases h
      case Seq =>
        cases g <;>
          try
            change Term.Stuck =
              Term.Apply (Term.UOp UserOp.Seq)
                (Term.UOp UserOp.Char) at h
            cases h
        case UOp op' =>
          cases op' <;>
            try
              change Term.Stuck =
                Term.Apply (Term.UOp UserOp.Seq)
                  (Term.UOp UserOp.Char) at h
              cases h
          case Seq =>
            change
              __eo_requires (__eo_eq a b) (Term.Boolean true)
                  (Term.Apply (Term.UOp UserOp.Seq) a) =
                Term.Apply (Term.UOp UserOp.Seq)
                  (Term.UOp UserOp.Char) at h
            cases hReq :
              native_teq (__eo_eq a b) (Term.Boolean true)
            · simp [__eo_requires, hReq, native_ite] at h
            · have hEqBoolAB : __eo_eq a b = Term.Boolean true := by
                simpa [native_teq] using hReq
              rw [hEqBoolAB] at h
              simp [__eo_requires, native_ite, native_teq, native_not] at h
              cases h
              have hEqBool : __eo_eq (Term.UOp UserOp.Char) b =
                  Term.Boolean true := by
                simpa using hEqBoolAB
              have hB : b = Term.UOp UserOp.Char :=
                (EvaluateProofInternal.eo_eq_true_eq_local (Term.UOp UserOp.Char) b hEqBool).symm
              constructor
              · simp
              · simp [hB]

theorem EvaluateProofInternal.smt_str_concat_args_of_non_none_local
    (x y : Term)
    (hNN :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y)) ≠
        SmtType.None) :
    ∃ T : SmtType,
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt y) = SmtType.Seq T ∧
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y)) =
            SmtType.Seq T := by
  change
    __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt y)) ≠
      SmtType.None at hNN
  cases hx : __smtx_typeof (__eo_to_smt x)
  case Seq T =>
    cases hy : __smtx_typeof (__eo_to_smt y)
    case Seq U =>
      by_cases hTU : T = U
      · subst U
        exact ⟨T, rfl, rfl, by
          rw [show
              __eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y) =
                SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt y) by
            rfl]
          simp [__smtx_typeof, __smtx_typeof_seq_op_2, hx, hy,
            native_Teq, native_ite]⟩
      · exfalso
        apply hNN
        simp [__smtx_typeof, __smtx_typeof_seq_op_2, hx, hy,
          native_Teq, hTU, native_ite]
    all_goals
      exfalso
      apply hNN
      simp [__smtx_typeof, __smtx_typeof_seq_op_2, hx, hy]
  all_goals
    exfalso
    apply hNN
    simp [__smtx_typeof, __smtx_typeof_seq_op_2, hx]

