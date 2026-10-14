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

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

theorem EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck (f x : Term) :
    __eo_mk_apply f x ≠ Term.Stuck ->
    __eo_mk_apply f x = Term.Apply f x := by
  intro h
  cases f <;> cases x <;> simp [__eo_mk_apply] at h ⊢

theorem EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck (f x : Term) :
    f ≠ Term.Stuck ->
    x ≠ Term.Stuck ->
    __eo_mk_apply f x = Term.Apply f x := by
  intro hf hx
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

theorem EvaluateProofInternal.eo_to_z_arg_ne_stuck {t : Term} :
    __eo_to_z t ≠ Term.Stuck -> t ≠ Term.Stuck := by
  intro h ht
  rw [ht] at h
  simp [__eo_to_z] at h

theorem EvaluateProofInternal.eo_to_q_arg_ne_stuck {t : Term} :
    __eo_to_q t ≠ Term.Stuck -> t ≠ Term.Stuck := by
  intro h ht
  rw [ht] at h
  simp [__eo_to_q] at h

theorem EvaluateProofInternal.eo_eq_left_ne_stuck {a b : Term} :
    __eo_eq a b ≠ Term.Stuck -> a ≠ Term.Stuck := by
  intro h ha
  rw [ha] at h
  cases b <;> simp [__eo_eq] at h

theorem EvaluateProofInternal.eo_eq_right_ne_stuck {a b : Term} :
    __eo_eq a b ≠ Term.Stuck -> b ≠ Term.Stuck := by
  intro h hb
  rw [hb] at h
  cases a <;> simp [__eo_eq] at h

theorem EvaluateProofInternal.eo_ite_cond_ne_stuck {c t e : Term} :
    __eo_ite c t e ≠ Term.Stuck -> c ≠ Term.Stuck := by
  intro h hc
  rw [hc] at h
  simp [__eo_ite, native_ite, native_teq] at h

theorem EvaluateProofInternal.eo_gt_left_ne_stuck {a b : Term} :
    __eo_gt a b ≠ Term.Stuck -> a ≠ Term.Stuck := by
  intro h ha
  rw [ha] at h
  cases b <;> simp [__eo_gt] at h

theorem EvaluateProofInternal.eo_gt_right_ne_stuck {a b : Term} :
    __eo_gt a b ≠ Term.Stuck -> b ≠ Term.Stuck := by
  intro h hb
  rw [hb] at h
  cases a <;> simp [__eo_gt] at h

theorem EvaluateProofInternal.eo_or_left_ne_stuck {a b : Term} :
    __eo_or a b ≠ Term.Stuck -> a ≠ Term.Stuck := by
  intro h ha
  rw [ha] at h
  cases b <;> simp [__eo_or] at h

theorem EvaluateProofInternal.eo_or_right_ne_stuck {a b : Term} :
    __eo_or a b ≠ Term.Stuck -> b ≠ Term.Stuck := by
  intro h hb
  rw [hb] at h
  cases a <;> simp [__eo_or] at h

theorem EvaluateProofInternal.eo_add_left_ne_stuck {a b : Term} :
    __eo_add a b ≠ Term.Stuck -> a ≠ Term.Stuck := by
  intro h ha
  rw [ha] at h
  cases b <;> simp [__eo_add] at h

theorem EvaluateProofInternal.eo_add_right_ne_stuck {a b : Term} :
    __eo_add a b ≠ Term.Stuck -> b ≠ Term.Stuck := by
  intro h hb
  rw [hb] at h
  cases a <;> simp [__eo_add] at h

theorem EvaluateProofInternal.eo_mul_left_ne_stuck {a b : Term} :
    __eo_mul a b ≠ Term.Stuck -> a ≠ Term.Stuck := by
  intro h ha
  rw [ha] at h
  cases b <;> simp [__eo_mul] at h

theorem EvaluateProofInternal.eo_mul_right_ne_stuck {a b : Term} :
    __eo_mul a b ≠ Term.Stuck -> b ≠ Term.Stuck := by
  intro h hb
  rw [hb] at h
  cases a <;> simp [__eo_mul] at h

theorem EvaluateProofInternal.eo_neg_arg_ne_stuck {t : Term} :
    __eo_neg t ≠ Term.Stuck -> t ≠ Term.Stuck := by
  intro h ht
  rw [ht] at h
  simp [__eo_neg] at h

theorem EvaluateProofInternal.eo_is_neg_arg_ne_stuck {t : Term} :
    __eo_is_neg t ≠ Term.Stuck -> t ≠ Term.Stuck := by
  intro h ht
  rw [ht] at h
  simp [__eo_is_neg] at h

theorem EvaluateProofInternal.eo_not_arg_ne_stuck {t : Term} :
    __eo_not t ≠ Term.Stuck -> t ≠ Term.Stuck := by
  intro h ht
  rw [ht] at h
  simp [__eo_not] at h

theorem EvaluateProofInternal.eo_and_left_ne_stuck {a b : Term} :
    __eo_and a b ≠ Term.Stuck -> a ≠ Term.Stuck := by
  intro h ha
  rw [ha] at h
  cases b <;> simp [__eo_and] at h

theorem EvaluateProofInternal.eo_and_right_ne_stuck {a b : Term} :
    __eo_and a b ≠ Term.Stuck -> b ≠ Term.Stuck := by
  intro h hb
  rw [hb] at h
  cases a <;> simp [__eo_and] at h

theorem EvaluateProofInternal.eo_xor_left_ne_stuck {a b : Term} :
    __eo_xor a b ≠ Term.Stuck -> a ≠ Term.Stuck := by
  intro h ha
  rw [ha] at h
  cases b <;> simp [__eo_xor] at h

theorem EvaluateProofInternal.eo_xor_right_ne_stuck {a b : Term} :
    __eo_xor a b ≠ Term.Stuck -> b ≠ Term.Stuck := by
  intro h hb
  rw [hb] at h
  cases a <;> simp [__eo_xor] at h

theorem EvaluateProofInternal.eo_concat_left_ne_stuck {a b : Term} :
    __eo_concat a b ≠ Term.Stuck -> a ≠ Term.Stuck := by
  intro h ha
  rw [ha] at h
  cases b <;> simp [__eo_concat] at h

theorem EvaluateProofInternal.eo_concat_right_ne_stuck {a b : Term} :
    __eo_concat a b ≠ Term.Stuck -> b ≠ Term.Stuck := by
  intro h hb
  rw [hb] at h
  cases a <;> simp [__eo_concat] at h

theorem EvaluateProofInternal.eo_len_arg_ne_stuck {t : Term} :
    __eo_len t ≠ Term.Stuck -> t ≠ Term.Stuck := by
  intro h ht
  rw [ht] at h
  simp [__eo_len] at h

theorem EvaluateProofInternal.eo_extract_target_ne_stuck {s i j : Term} :
    __eo_extract s i j ≠ Term.Stuck -> s ≠ Term.Stuck := by
  intro h hs
  rw [hs] at h
  cases i <;> cases j <;> simp [__eo_extract] at h

theorem EvaluateProofInternal.eo_extract_start_ne_stuck {s i j : Term} :
    __eo_extract s i j ≠ Term.Stuck -> i ≠ Term.Stuck := by
  intro h hi
  rw [hi] at h
  cases s <;> cases j <;> simp [__eo_extract] at h

theorem EvaluateProofInternal.eo_extract_end_ne_stuck {s i j : Term} :
    __eo_extract s i j ≠ Term.Stuck -> j ≠ Term.Stuck := by
  intro h hj
  rw [hj] at h
  cases s <;> cases i <;> simp [__eo_extract] at h

theorem EvaluateProofInternal.eo_find_left_ne_stuck {a b : Term} :
    __eo_find a b ≠ Term.Stuck -> a ≠ Term.Stuck := by
  intro h ha
  rw [ha] at h
  cases b <;> simp [__eo_find] at h

theorem EvaluateProofInternal.eo_find_right_ne_stuck {a b : Term} :
    __eo_find a b ≠ Term.Stuck -> b ≠ Term.Stuck := by
  intro h hb
  rw [hb] at h
  cases a <;> simp [__eo_find] at h

theorem EvaluateProofInternal.eo_to_str_arg_ne_stuck {t : Term} :
    __eo_to_str t ≠ Term.Stuck -> t ≠ Term.Stuck := by
  intro h ht
  rw [ht] at h
  simp [__eo_to_str] at h

theorem EvaluateProofInternal.eo_to_bin_width_ne_stuck {w n : Term} :
    __eo_to_bin w n ≠ Term.Stuck -> w ≠ Term.Stuck := by
  intro h hw
  rw [hw] at h
  cases n <;> simp [__eo_to_bin] at h

theorem EvaluateProofInternal.eo_to_bin_value_ne_stuck {w n : Term} :
    __eo_to_bin w n ≠ Term.Stuck -> n ≠ Term.Stuck := by
  intro h hn
  rw [hn] at h
  cases w <;> simp [__eo_to_bin] at h

theorem EvaluateProofInternal.eo_prog_evaluate_eq_of_ne_stuck (A : Term) :
    __eo_prog_evaluate A ≠ Term.Stuck ->
    __eo_prog_evaluate A =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) (__run_evaluate A) := by
  intro hProg
  cases A <;> simp [__eo_prog_evaluate] at hProg ⊢
  all_goals
    first
    | contradiction
    | exact EvaluateProofInternal.evaluate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hProg

theorem EvaluateProofInternal.eo_prog_evaluate_eq_of_term_and_run_ne_stuck (A : Term) :
    A ≠ Term.Stuck ->
    __run_evaluate A ≠ Term.Stuck ->
    __eo_prog_evaluate A =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) (__run_evaluate A) := by
  intro hA hRun
  cases A
  all_goals
    first
    | exact False.elim (hA rfl)
    | simp only [__eo_prog_evaluate]
      exact EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck _ _
        (by intro h; cases h) hRun

def EvaluateProofInternal.RunEvaluateSoundGoal (M : SmtModel) (A : Term) : Prop :=
  RuleProofs.eo_has_smt_translation A ->
  __eo_typeof (__eo_prog_evaluate A) = Term.Bool ->
  __smtx_typeof (__eo_to_smt A) =
      __smtx_typeof (__eo_to_smt (__run_evaluate A)) ∧
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt A))
      (__smtx_model_eval M (__eo_to_smt (__run_evaluate A)))

theorem EvaluateProofInternal.run_evaluate_sound_of_eq_self
    (M : SmtModel) (A : Term)
    (hRun : __run_evaluate A = A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M A := by
  intro _hATrans _hEvalTy
  rw [hRun]
  exact ⟨rfl, RuleProofs.smt_value_rel_refl _⟩

theorem EvaluateProofInternal.run_evaluate_rec_apply_fun
    (M : SmtModel) (f x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply f x) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M f :=
  rec f (by
    change sizeOf f < 1 + sizeOf f + sizeOf x
    omega)

theorem EvaluateProofInternal.run_evaluate_rec_apply_arg
    (M : SmtModel) (f x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply f x) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M x :=
  rec x (by
    change sizeOf x < 1 + sizeOf f + sizeOf x
    omega)

theorem EvaluateProofInternal.run_evaluate_rec_apply_apply_arg
    (M : SmtModel) (g y x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.Apply g y) x) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M y :=
  rec y (by
    change sizeOf y < 1 + (1 + sizeOf g + sizeOf y) + sizeOf x
    omega)

theorem EvaluateProofInternal.run_evaluate_rec_apply_apply_apply_arg1
    (M : SmtModel) (g z y x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.Apply g z) y) x) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M z :=
  rec z (by
    change sizeOf z < 1 + (1 + (1 + sizeOf g + sizeOf z) + sizeOf y) + sizeOf x
    omega)

theorem EvaluateProofInternal.run_evaluate_rec_apply_apply_apply_arg2
    (M : SmtModel) (g z y x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.Apply g z) y) x) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M y :=
  rec y (by
    change sizeOf y < 1 + (1 + (1 + sizeOf g + sizeOf z) + sizeOf y) + sizeOf x
    omega)

theorem EvaluateProofInternal.run_evaluate_rec_apply_apply_apply_arg3
    (M : SmtModel) (g z y x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.Apply g z) y) x) ->
          EvaluateProofInternal.RunEvaluateSoundGoal M A) :
  EvaluateProofInternal.RunEvaluateSoundGoal M x :=
  rec x (by
    change sizeOf x < 1 + (1 + (1 + sizeOf g + sizeOf z) + sizeOf y) + sizeOf x
    omega)

theorem EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool
    (t : Term) :
    t ≠ Term.Stuck ->
    __eo_typeof t = Term.Bool ->
    __eo_typeof (__run_evaluate t) = Term.Bool ->
    __eo_typeof (__eo_prog_evaluate t) = Term.Bool := by
  intro hTNe hTy hRunTy
  have hRunNe : __run_evaluate t ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hRunTy
  have hProgEq :=
    EvaluateProofInternal.eo_prog_evaluate_eq_of_term_and_run_ne_stuck t hTNe hRunNe
  rw [hProgEq]
  change __eo_typeof_eq (__eo_typeof t) (__eo_typeof (__run_evaluate t)) =
    Term.Bool
  rw [hTy, hRunTy]
  simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
    native_not]

theorem EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof
    (t T : Term) :
    t ≠ Term.Stuck ->
    T ≠ Term.Stuck ->
    __eo_typeof t = T ->
    __eo_typeof (__run_evaluate t) = T ->
    __eo_typeof (__eo_prog_evaluate t) = Term.Bool := by
  intro hTNe hTypeNe hTy hRunTy
  have hRunNe : __run_evaluate t ≠ Term.Stuck := by
    intro hRunStuck
    rw [hRunStuck] at hRunTy
    change Term.Stuck = T at hRunTy
    exact hTypeNe hRunTy.symm
  have hProgEq :=
    EvaluateProofInternal.eo_prog_evaluate_eq_of_term_and_run_ne_stuck t hTNe hRunNe
  rw [hProgEq]
  change __eo_typeof_eq (__eo_typeof t) (__eo_typeof (__run_evaluate t)) =
    Term.Bool
  rw [hTy, hRunTy]
  simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
    native_not]

theorem EvaluateProofInternal.eo_typeof_eq_self_bool_of_has_smt_translation
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t) :
    __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) t) =
      Term.Bool := by
  have hMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t hTrans
  have hTypeNN : __eo_to_smt_type (__eo_typeof t) ≠ SmtType.None := by
    intro hNone
    exact hTrans (hMatch.trans hNone)
  have hTypeNe : __eo_typeof t ≠ Term.Stuck :=
    TranslationProofs.eo_term_ne_stuck_of_smt_type_non_none
      (__eo_typeof t) hTypeNN
  change __eo_typeof_eq (__eo_typeof t) (__eo_typeof t) = Term.Bool
  cases hTy : __eo_typeof t <;>
    first
    | exact False.elim (hTypeNe hTy)
    | simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite,
        native_teq, native_not]

theorem EvaluateProofInternal.eo_to_smt_type_eq_of_top_valid
    {T U : Term}
    (hValid : TranslationProofs.eo_type_valid T)
    (hEq : __eo_to_smt_type T = __eo_to_smt_type U) :
    T = U := by
  cases T
  case UOp op =>
    cases op
    case RegLan =>
      have hUReg : __eo_to_smt_type U = SmtType.RegLan := by
        simpa [__eo_to_smt_type] using hEq.symm
      exact (TranslationProofs.eo_to_smt_type_eq_reglan hUReg).symm
    all_goals
      exact TranslationProofs.eo_to_smt_type_eq_of_valid_rec (refs := [])
        hValid hEq
  all_goals
    exact TranslationProofs.eo_to_smt_type_eq_of_valid_rec (refs := [])
      hValid hEq

theorem EvaluateProofInternal.run_evaluate_typeof_eq_of_same_smt_type
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hSame :
      __smtx_typeof (__eo_to_smt t) =
        __smtx_typeof (__eo_to_smt (__run_evaluate t))) :
    __eo_typeof (__run_evaluate t) = __eo_typeof t := by
  have hRunTrans :
      RuleProofs.eo_has_smt_translation (__run_evaluate t) := by
    intro hNone
    exact hTrans (hSame.trans hNone)
  have hOrigMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t hTrans
  have hRunMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation
      (__run_evaluate t) hRunTrans
  have hOrigValid :=
    TranslationProofs.eo_type_valid_typeof_of_smt_translation t hTrans
  have hEqType :
      __eo_to_smt_type (__eo_typeof t) =
        __eo_to_smt_type (__eo_typeof (__run_evaluate t)) := by
    rw [← hOrigMatch, hSame, hRunMatch]
  exact (EvaluateProofInternal.eo_to_smt_type_eq_of_top_valid hOrigValid hEqType).symm

theorem EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_run_typeof_eq
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hRunTy : __eo_typeof (__run_evaluate t) = __eo_typeof t) :
    __eo_typeof (__eo_prog_evaluate t) = Term.Bool := by
  have hTNe : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTrans
  have hMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t hTrans
  have hTypeNN : __eo_to_smt_type (__eo_typeof t) ≠ SmtType.None := by
    intro hNone
    exact hTrans (hMatch.trans hNone)
  have hTypeNe : __eo_typeof t ≠ Term.Stuck :=
    TranslationProofs.eo_term_ne_stuck_of_smt_type_non_none
      (__eo_typeof t) hTypeNN
  exact EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof t
    (__eo_typeof t) hTNe hTypeNe rfl hRunTy

theorem EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_same_smt_type
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hSame :
      __smtx_typeof (__eo_to_smt t) =
        __smtx_typeof (__eo_to_smt (__run_evaluate t))) :
    __eo_typeof (__eo_prog_evaluate t) = Term.Bool :=
  EvaluateProofInternal.eo_prog_evaluate_typeof_bool_of_run_typeof_eq t hTrans
    (EvaluateProofInternal.run_evaluate_typeof_eq_of_same_smt_type t hTrans hSame)

theorem EvaluateProofInternal.smtx_model_eval_eq_false_of_not_smt_value_rel
    (a b : SmtValue) :
    ¬ RuleProofs.smt_value_rel a b ->
    __smtx_model_eval_eq a b = SmtValue.Boolean false := by
  intro h
  rcases bool_value_canonical (typeof_value_model_eval_eq_value a b) with
    ⟨q, hEq⟩
  rw [hEq]
  cases q with
  | false => rfl
  | true =>
      exact False.elim (h hEq)

theorem EvaluateProofInternal.smt_value_rel_model_eval_eq_congr
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_eq a b) (__smtx_model_eval_eq c d) := by
  intro hac hbd
  have hIff :
      RuleProofs.smt_value_rel a b ↔
        RuleProofs.smt_value_rel c d := by
    constructor
    · intro hab
      exact RuleProofs.smt_value_rel_trans c a d
        (RuleProofs.smt_value_rel_symm a c hac)
        (RuleProofs.smt_value_rel_trans a b d hab hbd)
    · intro hcd
      exact RuleProofs.smt_value_rel_trans a c b hac
        (RuleProofs.smt_value_rel_trans c d b hcd
          (RuleProofs.smt_value_rel_symm b d hbd))
  by_cases hab : RuleProofs.smt_value_rel a b
  · have hcd : RuleProofs.smt_value_rel c d := hIff.mp hab
    unfold RuleProofs.smt_value_rel at hab hcd ⊢
    rw [hab, hcd]
    simp [__smtx_model_eval_eq, native_veq]
  · have hncd : ¬ RuleProofs.smt_value_rel c d := by
      intro hcd
      exact hab (hIff.mpr hcd)
    have habFalse :
        __smtx_model_eval_eq a b = SmtValue.Boolean false :=
      EvaluateProofInternal.smtx_model_eval_eq_false_of_not_smt_value_rel a b hab
    have hcdFalse :
        __smtx_model_eval_eq c d = SmtValue.Boolean false :=
      EvaluateProofInternal.smtx_model_eval_eq_false_of_not_smt_value_rel c d hncd
    rw [habFalse, hcdFalse]
    simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq, native_veq]

theorem EvaluateProofInternal.smtx_typeof_eo_to_smt_eq_bool_of_same_non_none
    (y x : Term)
    (hTy :
      __smtx_typeof (__eo_to_smt y) =
        __smtx_typeof (__eo_to_smt x))
    (hNonNone : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x)) =
      SmtType.Bool := by
  rw [eo_to_smt_eq_eq, Smtm.typeof_eq_eq]
  exact (RuleProofs.smtx_typeof_eq_bool_iff
    (__smtx_typeof (__eo_to_smt y))
    (__smtx_typeof (__eo_to_smt x))).mpr ⟨hTy, hNonNone⟩

theorem EvaluateProofInternal.native_pack_string_injective_early :
    Function.Injective native_pack_string := by
  intro s t h
  have hUnpack := congrArg native_unpack_string h
  simpa [RuleProofs.native_unpack_string_pack_string] using hUnpack

theorem EvaluateProofInternal.native_pack_string_eq_iff_early
    (s t : native_String) :
    native_pack_string s = native_pack_string t ↔ s = t := by
  constructor
  · intro h
    exact EvaluateProofInternal.native_pack_string_injective_early h
  · intro h
    rw [h]

theorem EvaluateProofInternal.eo_to_smt_string_eq_early
    (s : native_String) :
    __eo_to_smt (Term.String s) = SmtTerm.String s := by
  rfl

theorem EvaluateProofInternal.eo_to_smt_binary_eq_early
    (w n : native_Int) :
    __eo_to_smt (Term.Binary w n) = SmtTerm.Binary w n := by
  rfl

theorem EvaluateProofInternal.decide_and_eq_symm
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (a c : α) (b d : β) :
    (decide (a = c) && decide (b = d)) =
      (decide (c = a) && decide (d = b)) := by
  by_cases hac : a = c
  · subst c
    by_cases hbd : b = d
    · subst d
      rfl
    · have hdb : d ≠ b := by
        intro h
        exact hbd h.symm
      simp [hbd, hdb]
  · have hca : c ≠ a := by
      intro h
      exact hac h.symm
    by_cases hbd : b = d
    · subst d
      simp [hac, hca]
    · have hdb : d ≠ b := by
        intro h
        exact hbd h.symm
      simp [hac, hca, hbd, hdb]

theorem EvaluateProofInternal.run_evaluate_apply_eq_smt_type_bool
    (y x : Term)
    (hTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate y)) =
        __smtx_typeof (__eo_to_smt (__run_evaluate x)))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (__run_evaluate y)) ≠ SmtType.None) :
    __smtx_typeof
        (__eo_to_smt
          (__run_evaluate
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x))) =
      SmtType.Bool := by
  have hApply :=
    EvaluateProofInternal.smtx_typeof_eo_to_smt_eq_bool_of_same_non_none
      (__run_evaluate y) (__run_evaluate x) hTy hNonNone
  have hYNe : __run_evaluate y ≠ Term.Stuck := by
    intro hStuck
    apply hNonNone
    rw [hStuck]
    rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl]
    exact TranslationProofs.smtx_typeof_none
  have hXNe : __run_evaluate x ≠ Term.Stuck := by
    intro hStuck
    apply hNonNone
    rw [hTy, hStuck]
    rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl]
    exact TranslationProofs.smtx_typeof_none
  cases hy : __run_evaluate y <;> cases hx : __run_evaluate x <;>
    first
    | simpa [__run_evaluate, hy, hx, __eo_eq, __eo_ite, __eo_and,
        __eo_is_q, __eo_is_q_internal, __eo_is_z, __eo_is_z_internal,
        __eo_is_bin, __eo_is_bin_internal, __eo_is_str,
        __eo_is_str_internal, __eo_is_bool, __eo_is_bool_internal,
        __eo_mk_apply, native_ite, native_and, native_not,
        native_teq] using hApply
    | simp [__run_evaluate, hy, hx, __eo_eq, __eo_ite, __eo_and,
        __eo_is_q, __eo_is_q_internal, __eo_is_z, __eo_is_z_internal,
        __eo_is_bin, __eo_is_bin_internal, __eo_is_str,
        __eo_is_str_internal, __eo_is_bool, __eo_is_bool_internal,
        __eo_mk_apply, native_ite, native_and, native_not, native_teq]
  all_goals
    first
    | simpa [__run_evaluate, hy, hx, __eo_eq, __eo_ite, __eo_and,
        __eo_is_q, __eo_is_q_internal, __eo_is_z, __eo_is_z_internal,
        __eo_is_bin, __eo_is_bin_internal, __eo_is_str,
        __eo_is_str_internal, __eo_is_bool, __eo_is_bool_internal,
        __eo_mk_apply, native_ite, native_and, native_not,
        native_teq] using hApply
    | rw [__smtx_typeof.eq_1]
    | contradiction

theorem EvaluateProofInternal.eo_eq_typeof_bool_of_ne_stuck_early
    (x y : Term)
    (hNe : __eo_eq x y ≠ Term.Stuck) :
    __eo_typeof (__eo_eq x y) = Term.Bool := by
  cases x <;> cases y <;> simp [__eo_eq] at hNe ⊢

theorem EvaluateProofInternal.eo_apply_eq_typeof_bool_of_same_nonstuck_type_early
    (x y : Term)
    (hTy : __eo_typeof x = __eo_typeof y)
    (hTyNe : __eo_typeof x ≠ Term.Stuck) :
    __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) =
      Term.Bool := by
  change __eo_typeof_eq (__eo_typeof x) (__eo_typeof y) = Term.Bool
  rw [← hTy]
  cases hX : __eo_typeof x <;>
    first
    | exact False.elim (hTyNe hX)
    | simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite,
        native_teq, native_not]

theorem EvaluateProofInternal.run_evaluate_apply_eq_typeof_bool_of_run_typeof_eq
    (y x : Term)
    (hTy :
      __eo_typeof (__run_evaluate y) =
        __eo_typeof (__run_evaluate x))
    (hTyNe : __eo_typeof (__run_evaluate y) ≠ Term.Stuck)
    (hNe :
      __run_evaluate
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x) ≠
        Term.Stuck) :
    __eo_typeof
        (__run_evaluate
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x)) =
      Term.Bool := by
  have hFallback :
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (__run_evaluate y)) (__run_evaluate x)) =
        Term.Bool :=
    EvaluateProofInternal.eo_apply_eq_typeof_bool_of_same_nonstuck_type_early
      (__run_evaluate y) (__run_evaluate x) hTy hTyNe
  cases hy : __run_evaluate y <;> cases hx : __run_evaluate x <;>
    simp [__run_evaluate, hy, hx, __eo_eq, __eo_ite, __eo_and,
      __eo_is_q, __eo_is_q_internal, __eo_is_z, __eo_is_z_internal,
      __eo_is_bin, __eo_is_bin_internal, __eo_is_str,
      __eo_is_str_internal, __eo_is_bool, __eo_is_bool_internal,
      __eo_mk_apply, native_ite, native_and, native_not, native_teq]
      at hTy hTyNe hNe hFallback ⊢
  all_goals
    first
    | exact hFallback
    | rfl
    | cases hTy
    | contradiction

theorem EvaluateProofInternal.smt_value_rel_model_eval_eo_to_smt_eq_refl
    (M : SmtModel) (y x : Term) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt y))
        (__smtx_model_eval M (__eo_to_smt x)))
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x))) := by
  rw [eo_to_smt_eq_eq, smtx_eval_eq_term_eq]
  exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.run_evaluate_apply_eq_value_rel
    (M : SmtModel) (y x : Term)
    (hTy :
      __smtx_typeof (__eo_to_smt (__run_evaluate y)) =
        __smtx_typeof (__eo_to_smt (__run_evaluate x)))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (__run_evaluate y)) ≠ SmtType.None) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt (__run_evaluate y)))
        (__smtx_model_eval M (__eo_to_smt (__run_evaluate x))))
      (__smtx_model_eval M
        (__eo_to_smt
          (__run_evaluate
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x)))) := by
  have hApplyRel :=
    EvaluateProofInternal.smt_value_rel_model_eval_eo_to_smt_eq_refl M
      (__run_evaluate y) (__run_evaluate x)
  have hYNe : __run_evaluate y ≠ Term.Stuck := by
    intro hStuck
    apply hNonNone
    rw [hStuck]
    rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl]
    exact TranslationProofs.smtx_typeof_none
  have hXNe : __run_evaluate x ≠ Term.Stuck := by
    intro hStuck
    apply hNonNone
    rw [hTy, hStuck]
    rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl]
    exact TranslationProofs.smtx_typeof_none
  cases hy : __run_evaluate y <;> cases hx : __run_evaluate x <;>
    first
    | simpa [__run_evaluate, hy, hx, __eo_eq, __eo_ite, __eo_and,
        __eo_is_q, __eo_is_q_internal, __eo_is_z, __eo_is_z_internal,
        __eo_is_bin, __eo_is_bin_internal, __eo_is_str,
        __eo_is_str_internal, __eo_is_bool, __eo_is_bool_internal,
        __eo_mk_apply, native_ite, native_and, native_not,
        native_teq] using hApplyRel
    | simp [__run_evaluate, hy, hx, __eo_eq, __eo_ite, __eo_and,
        __eo_is_q, __eo_is_q_internal, __eo_is_z, __eo_is_z_internal,
        __eo_is_bin, __eo_is_bin_internal, __eo_is_str,
        __eo_is_str_internal, __eo_is_bool, __eo_is_bool_internal,
        __eo_mk_apply, RuleProofs.smt_value_rel, __smtx_model_eval_eq,
        eo_to_smt_numeral_eq, eo_to_smt_rational_eq,
        EvaluateProofInternal.eo_to_smt_string_eq_early, EvaluateProofInternal.eo_to_smt_binary_eq_early,
        __smtx_model_eval.eq_1, __smtx_model_eval.eq_2,
        __smtx_model_eval.eq_3, __smtx_model_eval.eq_4,
        __smtx_model_eval.eq_5, native_ite, native_and, native_not,
        native_teq, native_veq, EvaluateProofInternal.native_pack_string_eq_iff_early]
  all_goals
    first
    | simpa [__run_evaluate, hy, hx, __eo_eq, __eo_ite, __eo_and,
        __eo_is_q, __eo_is_q_internal, __eo_is_z, __eo_is_z_internal,
        __eo_is_bin, __eo_is_bin_internal, __eo_is_str,
        __eo_is_str_internal, __eo_is_bool, __eo_is_bool_internal,
        __eo_mk_apply, native_ite, native_and, native_not,
        native_teq] using hApplyRel
    | simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq,
        eo_to_smt_numeral_eq, eo_to_smt_rational_eq,
        EvaluateProofInternal.eo_to_smt_string_eq_early, EvaluateProofInternal.eo_to_smt_binary_eq_early,
        __smtx_model_eval.eq_1, __smtx_model_eval.eq_2,
        __smtx_model_eval.eq_3, __smtx_model_eval.eq_4,
        __smtx_model_eval.eq_5, native_teq, native_veq,
        EvaluateProofInternal.native_pack_string_eq_iff_early]
    | constructor <;> intro h <;> exact h.symm
    | exact EvaluateProofInternal.decide_and_eq_symm _ _ _ _
    | contradiction

