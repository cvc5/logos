module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
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

theorem EvaluateProofInternal.eo_typeof_str_to_lower_eq_seq_char_arg
    {T : Term} :
    __eo_typeof_str_to_lower T =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ->
    T = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  intro h
  cases T <;> simp [__eo_typeof_str_to_lower] at h ⊢
  case Apply f x =>
    cases f <;> cases x <;> simp at h ⊢
    case UOp.UOp op arg =>
      cases op <;> cases arg <;> simp at h ⊢

theorem EvaluateProofInternal.eo_typeof_apply_str_to_lower_eq_seq_char_arg
    (t : Term) :
    __eo_typeof (Term.Apply (Term.UOp UserOp.str_to_lower) t) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ->
    __eo_typeof t =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  intro h
  change __eo_typeof_str_to_lower (__eo_typeof t) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) at h
  exact EvaluateProofInternal.eo_typeof_str_to_lower_eq_seq_char_arg h

theorem EvaluateProofInternal.eo_typeof_apply_str_to_upper_eq_seq_char_arg
    (t : Term) :
    __eo_typeof (Term.Apply (Term.UOp UserOp.str_to_upper) t) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ->
    __eo_typeof t =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  intro h
  change __eo_typeof_str_to_lower (__eo_typeof t) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) at h
  exact EvaluateProofInternal.eo_typeof_str_to_lower_eq_seq_char_arg h

theorem EvaluateProofInternal.eo_str_to_lower_result_arg_typeof_seq_char
    (t : Term) :
    __eo_typeof
        (__eo_ite (__eo_is_str t)
          (__str_case_conv_rec (__str_flatten (__str_nary_intro t))
            (Term.Boolean true))
          (__eo_mk_apply (Term.UOp UserOp.str_to_lower) t)) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ->
    __eo_typeof t =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  intro h
  cases t
  case String s =>
    rfl
  all_goals
    apply EvaluateProofInternal.eo_typeof_apply_str_to_lower_eq_seq_char_arg
    have hsimpa := h
    try simp [__eo_is_str, __eo_is_str_internal, __eo_ite, __eo_mk_apply, native_ite, native_teq, native_and, native_not] at hsimpa ⊢
    exact hsimpa

theorem EvaluateProofInternal.eo_str_to_upper_result_arg_typeof_seq_char
    (t : Term) :
    __eo_typeof
        (__eo_ite (__eo_is_str t)
          (__str_case_conv_rec (__str_flatten (__str_nary_intro t))
            (Term.Boolean false))
          (__eo_mk_apply (Term.UOp UserOp.str_to_upper) t)) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ->
    __eo_typeof t =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  intro h
  cases t
  case String s =>
    rfl
  all_goals
    apply EvaluateProofInternal.eo_typeof_apply_str_to_upper_eq_seq_char_arg
    have hsimpa := h
    try simp [__eo_is_str, __eo_is_str_internal, __eo_ite, __eo_mk_apply, native_ite, native_teq, native_and, native_not] at hsimpa ⊢
    exact hsimpa

theorem EvaluateProofInternal.eo_typeof_seq_char_of_smt_type_seq_char
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char) :
    __eo_typeof t =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  have hMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t hTrans
  exact TranslationProofs.eo_to_smt_type_eq_seq_char
    (hMatch.symm.trans hTy)

theorem EvaluateProofInternal.eo_typeof_seq_of_smt_type_seq
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    {T : SmtType}
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T) :
    ∃ U : Term,
      __eo_typeof t = Term.Apply (Term.UOp UserOp.Seq) U ∧
        __eo_to_smt_type U = T := by
  have hMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t hTrans
  exact TranslationProofs.eo_to_smt_type_eq_seq (hMatch.symm.trans hTy)

theorem EvaluateProofInternal.eo_typeof_str_rev_eq_seq_arg
    {T U : Term} :
    __eo_typeof_str_rev T = Term.Apply (Term.UOp UserOp.Seq) U ->
    T = Term.Apply (Term.UOp UserOp.Seq) U := by
  intro h
  cases T <;> simp [__eo_typeof_str_rev] at h ⊢
  case Apply f x =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      assumption

theorem EvaluateProofInternal.eo_typeof_apply_str_rev_eq_seq_arg
    (t U : Term) :
    __eo_typeof (Term.Apply (Term.UOp UserOp.str_rev) t) =
      Term.Apply (Term.UOp UserOp.Seq) U ->
    __eo_typeof t = Term.Apply (Term.UOp UserOp.Seq) U := by
  intro h
  change __eo_typeof_str_rev (__eo_typeof t) =
      Term.Apply (Term.UOp UserOp.Seq) U at h
  exact EvaluateProofInternal.eo_typeof_str_rev_eq_seq_arg h

theorem EvaluateProofInternal.native_char_valid_lt
    {c : native_Char} (hc : native_char_valid c = true) :
    c < 196608 := by
  change decide (c < 196608) = true at hc
  exact of_decide_eq_true hc

theorem EvaluateProofInternal.native_str_to_code_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    native_str_to_code [c] = (c : Int) := by
  unfold native_str_to_code
  change (if native_char_valid c = true then (c : Int) else -1) = (c : Int)
  rw [hc]
  rfl

theorem EvaluateProofInternal.eo_to_z_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __eo_to_z (Term.String [c]) = Term.Numeral (c : Int) := by
  have hLen : native_zeq 1 (native_str_len [c]) = true := by
    change decide ((1 : Int) = Int.ofNat [c].length) = true
    rfl
  change (if native_zeq 1 (native_str_len [c]) = true then
        Term.Numeral (native_str_to_code [c]) else Term.Stuck) =
      Term.Numeral (c : Int)
  rw [hLen]
  exact congrArg Term.Numeral (EvaluateProofInternal.native_str_to_code_singleton hc)

theorem EvaluateProofInternal.native_str_from_code_of_valid_nat
    {c : native_Char}
    (hc : native_char_valid c = true) :
    native_str_from_code (c : Int) = [c] := by
  have hNonneg : decide ((0 : Int) ≤ (c : Int)) = true :=
    decide_eq_true (Int.natCast_nonneg c)
  have hValid : native_char_valid (Int.toNat (c : Int)) = true := by
    change native_char_valid c = true
    exact hc
  have hCond : ((decide ((0 : Int) ≤ (c : Int))) &&
      native_char_valid (Int.toNat (c : Int))) = true := by
    rw [hNonneg, hValid]
    rfl
  unfold native_str_from_code
  rw [hCond]
  rfl

theorem EvaluateProofInternal.eo_to_str_of_valid_nat
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __eo_to_str (Term.Numeral (c : Int)) = Term.String [c] := by
  have hcLtNat : c < 196608 := EvaluateProofInternal.native_char_valid_lt hc
  have hcLtInt : (c : Int) < 196608 := Int.ofNat_lt.mpr hcLtNat
  have hNonneg : native_zleq 0 (c : Int) = true := by
    change decide ((0 : Int) ≤ (c : Int)) = true
    exact decide_eq_true (Int.natCast_nonneg c)
  have hLt : native_zlt (c : Int) 196608 = true := by
    change decide ((c : Int) < (196608 : Int)) = true
    exact decide_eq_true hcLtInt
  have hCond : native_and (native_zleq 0 (c : Int))
      (native_zlt (c : Int) 196608) = true := by
    change (native_zleq 0 (c : Int) &&
      native_zlt (c : Int) 196608) = true
    rw [hNonneg, hLt]
    rfl
  change (if native_and (native_zleq 0 (c : Int))
      (native_zlt (c : Int) 196608) = true then
        Term.String (native_str_from_code (c : Int)) else Term.Stuck) =
      Term.String [c]
  rw [hCond]
  exact congrArg Term.String (EvaluateProofInternal.native_str_from_code_of_valid_nat hc)

theorem EvaluateProofInternal.native_str_from_code_invalid
    {n : native_Int}
    (hBad : ¬ (0 ≤ n ∧ n < 196608)) :
    native_str_from_code n = [] := by
  unfold native_str_from_code
  by_cases hn0 : 0 ≤ n
  · have hNatLtFalse : ¬ Int.toNat n < 196608 := by
      intro hNatLt
      have hnHi : n < 196608 := (Int.toNat_lt hn0).mp hNatLt
      exact hBad ⟨hn0, hnHi⟩
    have hGuard :
        (decide (0 ≤ n) && native_char_valid (Int.toNat n)) = false := by
      simp [hn0, native_char_valid, hNatLtFalse]
    rw [hGuard]
    rfl
  · have hGuard :
        (decide (0 ≤ n) && native_char_valid (Int.toNat n)) = false := by
      simp [hn0]
    rw [hGuard]
    rfl

def EvaluateProofInternal.eo_eval_str_from_code_rhs (n : Term) : Term :=
  let _v0 := __run_evaluate n
  let _v1 := __eo_is_z _v0
  __eo_ite _v1
    (__eo_ite
      (__eo_ite _v1
      (__eo_ite
        (__eo_ite (__eo_eq (Term.Numeral 196608) _v0)
          (Term.Boolean true) (__eo_gt (Term.Numeral 196608) _v0))
        (__eo_not (__eo_is_neg _v0)) (Term.Boolean false))
      (Term.Boolean false))
      (__eo_to_str n) (Term.String []))
    (Term.Apply (Term.UOp UserOp.str_from_code) n)

theorem EvaluateProofInternal.eo_eval_str_from_code_rhs_numeral_valid
    {n : native_Int}
    (h0 : 0 ≤ n)
    (hlt : n < 196608) :
    EvaluateProofInternal.eo_eval_str_from_code_rhs (Term.Numeral n) =
      Term.String (native_str_from_code n) := by
  have hNotNeg : native_zlt n 0 = false := by
    rw [show native_zlt n 0 = decide (n < 0) by rfl]
    exact decide_eq_false (Int.not_lt.mpr h0)
  have hLt : native_zlt n 196608 = true := by
    rw [show native_zlt n 196608 = decide (n < 196608) by rfl]
    exact decide_eq_true hlt
  have hNonneg : native_zleq 0 n = true := by
    rw [show native_zleq 0 n = decide (0 ≤ n) by rfl]
    exact decide_eq_true h0
  have hNe : n ≠ 196608 := by
    intro hEq
    have hSelf : (196608 : Int) < 196608 := by
      simpa [hEq] using hlt
    have hNotSelf : ¬ (196608 : Int) < 196608 := by
      decide
    exact hNotSelf hSelf
  have hNeSymm : (196608 : Int) ≠ n := by
    intro hEq
    exact hNe hEq.symm
  dsimp [EvaluateProofInternal.eo_eval_str_from_code_rhs]
  rw [show __run_evaluate (Term.Numeral n) = Term.Numeral n by rfl]
  simp [__eo_ite, native_ite, native_teq, __eo_is_z, __eo_eq, __eo_gt,
    __eo_to_str, __eo_is_neg, __eo_not, __eo_is_z_internal,
    native_and, native_not, hNotNeg, hLt, hNonneg, hNe]

theorem EvaluateProofInternal.eo_eval_str_from_code_rhs_numeral_invalid_guard
    {n : native_Int}
    (hBad : ¬ (0 ≤ n ∧ n ≤ 196608)) :
    EvaluateProofInternal.eo_eval_str_from_code_rhs (Term.Numeral n) =
      Term.String (native_str_from_code n) := by
  have hBadLt : ¬ (0 ≤ n ∧ n < 196608) := by
    intro h
    exact hBad ⟨h.1, Int.le_of_lt h.2⟩
  rw [EvaluateProofInternal.native_str_from_code_invalid hBadLt]
  by_cases h0 : 0 ≤ n
  · have hNotNeg : native_zlt n 0 = false := by
      rw [show native_zlt n 0 = decide (n < 0) by rfl]
      exact decide_eq_false (Int.not_lt.mpr h0)
    have hGt : native_zlt n 196608 = false := by
      rw [show native_zlt n 196608 = decide (n < 196608) by rfl]
      exact decide_eq_false (by
        intro hlt
        exact hBad ⟨h0, Int.le_of_lt hlt⟩)
    have hEq : native_zeq 196608 n = false := by
      rw [show native_zeq 196608 n = decide ((196608 : Int) = n) by rfl]
      exact decide_eq_false (by
        intro hEq
        have hnle : n ≤ 196608 := by
          rw [← hEq]
          exact Int.le_refl 196608
        exact hBad ⟨h0, hnle⟩)
    have hNe : n ≠ 196608 := by
      intro hn
      exact hBad ⟨h0, by rw [hn]; exact Int.le_refl 196608⟩
    have hNeSymm : (196608 : Int) ≠ n := by
      intro hn
      exact hNe hn.symm
    dsimp [EvaluateProofInternal.eo_eval_str_from_code_rhs]
    rw [show __run_evaluate (Term.Numeral n) = Term.Numeral n by rfl]
    simp [__eo_ite, native_ite, native_teq, __eo_is_z, __eo_eq, __eo_gt,
      __eo_is_z_internal, native_and, native_not, hGt, hNe]
  · have hNeg : native_zlt n 0 = true := by
      rw [show native_zlt n 0 = decide (n < 0) by rfl]
      exact decide_eq_true (Int.lt_of_not_ge h0)
    have hLt : native_zlt n 196608 = true := by
      rw [show native_zlt n 196608 = decide (n < 196608) by rfl]
      exact decide_eq_true (by
        exact Int.lt_trans (Int.lt_of_not_ge h0) (by decide))
    have hNe : n ≠ 196608 := by
      intro hn
      exact h0 (by rw [hn]; decide)
    have hNeSymm : (196608 : Int) ≠ n := by
      intro hn
      exact hNe hn.symm
    dsimp [EvaluateProofInternal.eo_eval_str_from_code_rhs]
    rw [show __run_evaluate (Term.Numeral n) = Term.Numeral n by rfl]
    simp [__eo_ite, native_ite, native_teq, __eo_is_z, __eo_eq, __eo_gt,
      __eo_is_neg, __eo_not, __eo_is_z_internal, native_and, native_not,
      hNeg, hLt, hNe]

theorem EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_invalid_guard
    {x : Term} {n : native_Int}
    (hRun : __run_evaluate x = Term.Numeral n)
    (hBad : ¬ (0 ≤ n ∧ n ≤ 196608)) :
    EvaluateProofInternal.eo_eval_str_from_code_rhs x =
      Term.String (native_str_from_code n) := by
  have hBadLt : ¬ (0 ≤ n ∧ n < 196608) := by
    intro h
    exact hBad ⟨h.1, Int.le_of_lt h.2⟩
  rw [EvaluateProofInternal.native_str_from_code_invalid hBadLt]
  by_cases h0 : 0 ≤ n
  · have hNotNeg : native_zlt n 0 = false := by
      rw [show native_zlt n 0 = decide (n < 0) by rfl]
      exact decide_eq_false (Int.not_lt.mpr h0)
    have hGt : native_zlt n 196608 = false := by
      rw [show native_zlt n 196608 = decide (n < 196608) by rfl]
      exact decide_eq_false (by
        intro hlt
        exact hBad ⟨h0, Int.le_of_lt hlt⟩)
    have hEq : native_zeq 196608 n = false := by
      rw [show native_zeq 196608 n = decide ((196608 : Int) = n) by rfl]
      exact decide_eq_false (by
        intro hEq
        have hnle : n ≤ 196608 := by
          rw [← hEq]
          exact Int.le_refl 196608
        exact hBad ⟨h0, hnle⟩)
    have hNe : n ≠ 196608 := by
      intro hn
      exact hBad ⟨h0, by rw [hn]; exact Int.le_refl 196608⟩
    have hNeSymm : (196608 : Int) ≠ n := by
      intro hn
      exact hNe hn.symm
    dsimp [EvaluateProofInternal.eo_eval_str_from_code_rhs]
    rw [hRun]
    simp [__eo_ite, native_ite, native_teq, __eo_is_z, __eo_eq, __eo_gt,
      __eo_is_z_internal, native_and, native_not, hGt, hNe]
  · have hNeg : native_zlt n 0 = true := by
      rw [show native_zlt n 0 = decide (n < 0) by rfl]
      exact decide_eq_true (Int.lt_of_not_ge h0)
    have hLt : native_zlt n 196608 = true := by
      rw [show native_zlt n 196608 = decide (n < 196608) by rfl]
      exact decide_eq_true (Int.lt_trans (Int.lt_of_not_ge h0) (by decide))
    have hNe : (196608 : Int) ≠ n := by
      intro hn
      exact h0 (by rw [← hn]; decide)
    dsimp [EvaluateProofInternal.eo_eval_str_from_code_rhs]
    rw [hRun]
    simp [__eo_ite, native_ite, native_teq, __eo_is_z, __eo_eq, __eo_gt,
      __eo_is_neg, __eo_not, __eo_is_z_internal, native_and, native_not,
      hNeg, hLt]

theorem EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_valid
    {x : Term} {n : native_Int}
    (hRun : __run_evaluate x = Term.Numeral n)
    (hXEoInt : __eo_typeof x = Term.UOp UserOp.Int)
    (hRunFromNe : EvaluateProofInternal.eo_eval_str_from_code_rhs x ≠ Term.Stuck)
    (h0 : 0 ≤ n)
    (hlt : n < 196608) :
    EvaluateProofInternal.eo_eval_str_from_code_rhs x =
      Term.String (native_str_from_code n) := by
  have hNotNeg : native_zlt n 0 = false := by
    rw [show native_zlt n 0 = decide (n < 0) by rfl]
    exact decide_eq_false (Int.not_lt.mpr h0)
  have hLt : native_zlt n 196608 = true := by
    rw [show native_zlt n 196608 = decide (n < 196608) by rfl]
    exact decide_eq_true hlt
  have hNonneg : native_zleq 0 n = true := by
    rw [show native_zleq 0 n = decide (0 ≤ n) by rfl]
    exact decide_eq_true h0
  have hNe : n ≠ 196608 := by
    intro hEq
    have hSelf : (196608 : Int) < 196608 := by
      simpa [hEq] using hlt
    exact (by decide : ¬ (196608 : Int) < 196608) hSelf
  have hNeSymm : (196608 : Int) ≠ n := by
    intro hEq
    exact hNe hEq.symm
  cases x
  case Numeral m =>
    change Term.Numeral m = Term.Numeral n at hRun
    cases hRun
    exact EvaluateProofInternal.eo_eval_str_from_code_rhs_numeral_valid h0 hlt
  case String s =>
    change
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) =
        Term.UOp UserOp.Int at hXEoInt
    cases hXEoInt
  all_goals
    exfalso
    apply hRunFromNe
    dsimp [EvaluateProofInternal.eo_eval_str_from_code_rhs]
    rw [hRun]
    simp [__eo_ite, native_ite, native_teq, __eo_is_z, __eo_eq, __eo_gt,
      __eo_is_neg, __eo_not, __eo_is_z_internal, native_and, native_not,
      __eo_to_str, hNotNeg, hLt, hNe]

theorem EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_eq_max_false
    {x : Term}
    (hRun : __run_evaluate x = Term.Numeral 196608)
    (hXEoInt : __eo_typeof x = Term.UOp UserOp.Int)
    (hRunFromNe : EvaluateProofInternal.eo_eval_str_from_code_rhs x ≠ Term.Stuck) :
    False := by
  have hNotNeg : native_zlt (196608 : Int) 0 = false := by
    rw [show native_zlt (196608 : Int) 0 =
      decide ((196608 : Int) < 0) by rfl]
    exact decide_eq_false (by decide)
  have hLtFalse : native_zlt (196608 : Int) 196608 = false := by
    rw [show native_zlt (196608 : Int) 196608 =
      decide ((196608 : Int) < 196608) by rfl]
    exact decide_eq_false (by decide)
  have hNonneg : native_zleq 0 (196608 : Int) = true := by
    rw [show native_zleq 0 (196608 : Int) =
      decide (0 ≤ (196608 : Int)) by rfl]
    exact decide_eq_true (by decide)
  cases x
  case Numeral m =>
    change Term.Numeral m = Term.Numeral 196608 at hRun
    cases hRun
    apply hRunFromNe
    dsimp [EvaluateProofInternal.eo_eval_str_from_code_rhs]
    rw [show __run_evaluate (Term.Numeral (196608 : Int)) =
      Term.Numeral 196608 by rfl]
    simp [__eo_ite, native_ite, native_teq, __eo_is_z, __eo_eq,
      __eo_is_neg, __eo_not, __eo_is_z_internal, native_and, native_not,
      __eo_to_str, hNotNeg, hLtFalse, hNonneg]
  case String s =>
    change
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) =
        Term.UOp UserOp.Int at hXEoInt
    cases hXEoInt
  all_goals
    apply hRunFromNe
    dsimp [EvaluateProofInternal.eo_eval_str_from_code_rhs]
    rw [hRun]
    simp [__eo_ite, native_ite, native_teq, __eo_is_z, __eo_eq,
      __eo_is_neg, __eo_not, __eo_is_z_internal, native_and, native_not,
      __eo_to_str, hNotNeg]

theorem EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_eq
    {x : Term} {n : native_Int}
    (hRun : __run_evaluate x = Term.Numeral n)
    (hXEoInt : __eo_typeof x = Term.UOp UserOp.Int)
    (hRunFromNe : EvaluateProofInternal.eo_eval_str_from_code_rhs x ≠ Term.Stuck) :
    EvaluateProofInternal.eo_eval_str_from_code_rhs x =
      Term.String (native_str_from_code n) := by
  by_cases hGuard : 0 ≤ n ∧ n ≤ 196608
  · rcases hGuard with ⟨h0, hnLe⟩
    by_cases hlt : n < 196608
    · exact EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_valid
        hRun hXEoInt hRunFromNe h0 hlt
    · have hGe : (196608 : Int) ≤ n := Int.le_of_not_gt hlt
      have hEq : n = 196608 := Int.le_antisymm hnLe hGe
      subst n
      exact False.elim
        (EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_eq_max_false
          hRun hXEoInt hRunFromNe)
  · exact EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_invalid_guard hRun hGuard

theorem EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_eq_of_active
    {x : Term} {n : native_Int}
    (hRun : __run_evaluate x = Term.Numeral n)
    (hXEoInt : __eo_typeof x = Term.UOp UserOp.Int)
    (hRunFromNe : EvaluateProofInternal.eo_eval_str_from_code_rhs x ≠ Term.Stuck)
    (hActive :
      EvaluateProofInternal.eo_eval_str_from_code_rhs x ≠
        Term.Apply (Term.UOp UserOp.str_from_code) x) :
    EvaluateProofInternal.eo_eval_str_from_code_rhs x =
      Term.String (native_str_from_code n) := by
  exact EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_eq
    hRun hXEoInt hRunFromNe

def EvaluateProofInternal.eo_eval_str_from_int_rhs (n : Term) : Term :=
  let _v0 := __run_evaluate n
  let _v1 := __eo_add (__eo_log (Term.Numeral 10) _v0) (Term.Numeral 1)
  __eo_ite (__eo_is_z _v0)
    (__eo_ite (__eo_is_neg _v0) (Term.String [])
      (__str_from_int_eval_rec
        (__eo_requires (__eo_is_neg _v1) (Term.Boolean false)
          (__iota_rec
            (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0) _v1)
            (Term.Numeral 0)))
        _v0 (Term.String [])))
    (__eo_mk_apply (Term.UOp UserOp.str_from_int) _v0)

def EvaluateProofInternal.eo_iota_int_list : native_Nat -> native_Int -> Term
  | 0, _ => Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
      (Term.UOp UserOp.Int)
  | fuel + 1, i =>
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral i))
        (EvaluateProofInternal.eo_iota_int_list fuel (native_zplus i 1))

def EvaluateProofInternal.eo_zero_int_list : native_Nat -> Term
  | 0 => Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
      (Term.UOp UserOp.Int)
  | fuel + 1 =>
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0))
        (EvaluateProofInternal.eo_zero_int_list fuel)

theorem EvaluateProofInternal.eo_zero_int_list_ne_stuck :
    ∀ fuel : native_Nat, EvaluateProofInternal.eo_zero_int_list fuel ≠ Term.Stuck
  | 0 => by
      intro h
      cases h
  | fuel + 1 => by
      intro h
      cases h

theorem EvaluateProofInternal.eo_iota_int_list_ne_stuck :
    ∀ (fuel : native_Nat) (i : native_Int),
      EvaluateProofInternal.eo_iota_int_list fuel i ≠ Term.Stuck
  | 0, _ => by
      intro h
      cases h
  | fuel + 1, _ => by
      intro h
      cases h

theorem EvaluateProofInternal.eo_list_repeat_rec_int_zero :
    ∀ fuel : native_Nat,
      __eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0) fuel =
        EvaluateProofInternal.eo_zero_int_list fuel
  | 0 => by
      rfl
  | fuel + 1 => by
      rw [show
        __eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral 0) (fuel + 1) =
          __eo_mk_apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0))
            (__eo_list_repeat_rec
              (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0) fuel) by
        rfl]
      rw [EvaluateProofInternal.eo_list_repeat_rec_int_zero fuel]
      rw [show EvaluateProofInternal.eo_zero_int_list (fuel + 1) =
          Term.Apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0))
            (EvaluateProofInternal.eo_zero_int_list fuel) by
        rfl]
      have hNe := EvaluateProofInternal.eo_zero_int_list_ne_stuck fuel
      cases hList : EvaluateProofInternal.eo_zero_int_list fuel <;>
        simp [__eo_mk_apply, hList] at hNe ⊢

theorem EvaluateProofInternal.eo_iota_zero_int_list :
    ∀ (fuel : native_Nat) (i : native_Int),
      __iota_rec (EvaluateProofInternal.eo_zero_int_list fuel) (Term.Numeral i) =
        EvaluateProofInternal.eo_iota_int_list fuel i
  | 0, _ => by
      rfl
  | fuel + 1, i => by
      rw [show
        __iota_rec (EvaluateProofInternal.eo_zero_int_list (fuel + 1)) (Term.Numeral i) =
          __eo_mk_apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral i))
            (__iota_rec (EvaluateProofInternal.eo_zero_int_list fuel)
              (__eo_add (Term.Numeral i) (Term.Numeral 1))) by
        rfl]
      simp [__eo_add, native_zplus]
      rw [EvaluateProofInternal.eo_iota_zero_int_list fuel (i + 1)]
      rw [show EvaluateProofInternal.eo_iota_int_list (fuel + 1) i =
          Term.Apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral i))
            (EvaluateProofInternal.eo_iota_int_list fuel (i + 1)) by
        rfl]
      have hNe := EvaluateProofInternal.eo_iota_int_list_ne_stuck fuel (i + 1)
      cases hList : EvaluateProofInternal.eo_iota_int_list fuel (i + 1) <;>
        simp [__eo_mk_apply, hList] at hNe ⊢

theorem EvaluateProofInternal.eo_iota_list_repeat_int_of_nonneg
    {k i : native_Int}
    (hNonneg : ¬ k < 0) :
    __iota_rec
        (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0) (Term.Numeral k))
        (Term.Numeral i) =
      EvaluateProofInternal.eo_iota_int_list (native_int_to_nat k) i := by
  have hNegBool : native_zlt k 0 = false := by
    rw [show native_zlt k 0 = decide (k < 0) by rfl]
    exact decide_eq_false hNonneg
  simp [__eo_list_repeat, native_ite, hNegBool,
    EvaluateProofInternal.eo_list_repeat_rec_int_zero, EvaluateProofInternal.eo_iota_zero_int_list]

theorem EvaluateProofInternal.native_digitChar_toNat_of_lt10 {d : Nat} (hd : d < 10) :
    Char.toNat (Nat.digitChar d) = 48 + d := by
  unfold Nat.digitChar
  by_cases h0 : d = 0
  · simp [h0]
  · by_cases h1 : d = 1
    · simp [h1]
    · by_cases h2 : d = 2
      · simp [h2]
      · by_cases h3 : d = 3
        · simp [h3]
        · by_cases h4 : d = 4
          · simp [h4]
          · by_cases h5 : d = 5
            · simp [h5]
            · by_cases h6 : d = 6
              · simp [h6]
              · by_cases h7 : d = 7
                · simp [h7]
                · by_cases h8 : d = 8
                  · simp [h8]
                  · by_cases h9 : d = 9
                    · simp [h9]
                    · have hGe : 10 ≤ d := by omega
                      exact False.elim ((Nat.not_lt_of_ge hGe) hd)

theorem EvaluateProofInternal.eo_str_from_int_digit_term_nat (n : Nat) :
    __eo_to_str
        (__eo_add (Term.Numeral 48)
          (__eo_zmod (Term.Numeral (Int.ofNat n)) (Term.Numeral 10))) =
      Term.String [Char.toNat (Nat.digitChar (n % 10))] := by
  let r : Int := (Int.ofNat n) % 10
  have hRNonneg : 0 ≤ r := by
    exact Int.emod_nonneg _ (by decide : (10 : Int) ≠ 0)
  have hRLt : r < 10 := by
    exact Int.emod_lt_of_pos _ (by decide : 0 < (10 : Int))
  have hCodeNonneg : 0 ≤ (48 : Int) + r := by omega
  have hCodeLt : (48 : Int) + r < 196608 := by omega
  have hCodeToNat :
      Int.toNat ((48 : Int) + r) = 48 + n % 10 := by
    rw [Int.toNat_add (by decide : 0 ≤ (48 : Int)) hRNonneg]
    change Int.toNat (48 : Int) + Int.toNat ((Int.ofNat n) % 10) =
      48 + n % 10
    have hModToNat :
        Int.toNat ((Int.ofNat n) % (10 : Int)) = n % 10 := by
      simpa using
        (Int.toNat_emod (x := Int.ofNat n) (y := (10 : Int))
          (Int.zero_le_ofNat n) (by decide : 0 ≤ (10 : Int)))
    rw [hModToNat]
    simp
  have hToNatLt : Int.toNat ((48 : Int) + r) < 196608 := by
    rw [hCodeToNat]
    have hModLt : n % 10 < 10 := Nat.mod_lt n (by decide)
    omega
  have hCodeValid :
      native_char_valid (Int.toNat ((48 : Int) + r)) = true := by
    rw [show native_char_valid (Int.toNat ((48 : Int) + r)) =
      decide (Int.toNat ((48 : Int) + r) < 196608) by rfl]
    exact decide_eq_true hToNatLt
  have hDigit :
      Int.toNat ((48 : Int) + r) =
        Char.toNat (Nat.digitChar (n % 10)) := by
    rw [EvaluateProofInternal.native_digitChar_toNat_of_lt10 (Nat.mod_lt n (by decide))]
    exact hCodeToNat
  have hCodeNonnegRaw : 0 ≤ (48 : Int) + (Int.ofNat n % 10) := by
    simpa [r] using hCodeNonneg
  have hCodeLtRaw : (48 : Int) + (Int.ofNat n % 10) < 196608 := by
    simpa [r] using hCodeLt
  have hCodeValidRaw :
      native_char_valid (Int.toNat ((48 : Int) + (Int.ofNat n % 10))) =
        true := by
    simpa [r] using hCodeValid
  have hDigitRaw :
      Int.toNat ((48 : Int) + (Int.ofNat n % 10)) =
        Char.toNat (Nat.digitChar (n % 10)) := by
    simpa [r] using hDigit
  -- `native_zleq`/`native_zlt` unfold to `decide (_ < 196608)`, which simp then
  -- tries to evaluate by unary `Nat.rec` and blows the recursion limit.  Leave
  -- them folded; the `rw [if_pos ..]` steps below discharge the guards.
  simp [__eo_zmod, __eo_add, __eo_to_str, native_ite, native_zeq,
    native_zplus, native_mod_total, native_and, native_str_from_code]
  -- both guards are folded `Bool` conjunctions `native_and _ _ = true`, not
  -- `And`s, so an anonymous constructor mis-elaborates; discharge them with the
  -- component facts instead (which also keeps the `196608` literal from being
  -- evaluated unarily)
  rw [if_pos (by
    simp [native_and, native_zleq, native_zlt]
    exact ⟨hCodeNonnegRaw, hCodeLtRaw⟩)]
  rw [if_pos (by
    try simp [native_and, native_zleq]
    exact ⟨hCodeNonnegRaw, hCodeValidRaw⟩)]
  change
    Term.String [Int.toNat ((48 : Int) + (Int.ofNat n % (10 : Int)))] =
      Term.String [Char.toNat (Nat.digitChar (n % 10))]
  rw [hDigitRaw]

theorem EvaluateProofInternal.eo_str_from_int_eval_rec_iota_toDigits :
    ∀ (fuel : native_Nat) (i : native_Int) (n : Nat) (acc : native_String),
      0 < n ->
      (Nat.toDigits 10 n).length ≤ fuel ->
        __str_from_int_eval_rec (EvaluateProofInternal.eo_iota_int_list fuel i)
          (Term.Numeral (Int.ofNat n)) (Term.String acc) =
        Term.String ((Nat.toDigits 10 n).map Char.toNat ++ acc)
  | 0, _i, n, _acc, _hPos, hLen => by
      have hDigitsPos : 0 < (Nat.toDigits 10 n).length :=
        Nat.length_toDigits_pos
      omega
  | fuel + 1, i, n, acc, hPos, hLen => by
      cases n with
      | zero =>
          omega
      | succ n =>
          change
            __str_from_int_eval_rec
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                  (Term.Numeral i))
                (EvaluateProofInternal.eo_iota_int_list fuel (native_zplus i 1)))
              (Term.Numeral (Int.ofNat (n + 1))) (Term.String acc) =
            Term.String
              (List.map Char.toNat (Nat.toDigits 10 (n + 1)) ++ acc)
          rw [__str_from_int_eval_rec.eq_5]
          · have hDivTerm :
                __eo_zdiv (Term.Numeral (Int.ofNat (n + 1)))
                    (Term.Numeral 10) =
                  Term.Numeral (Int.ofNat ((n + 1) / 10)) := by
                simp [__eo_zdiv, native_ite, native_zeq,
                  native_div_total]
            have hDigitConcat :
                __eo_concat
                    (__eo_to_str
                      (__eo_add (Term.Numeral 48)
                        (__eo_zmod (Term.Numeral (Int.ofNat (n + 1)))
                          (Term.Numeral 10))))
                    (Term.String acc) =
                  Term.String
                    ([Char.toNat (Nat.digitChar ((n + 1) % 10))] ++ acc) := by
              rw [EvaluateProofInternal.eo_str_from_int_digit_term_nat (n + 1)]
              rfl
            rw [hDivTerm, hDigitConcat]
            by_cases hDiv : (n + 1) / 10 = 0
            · rw [hDiv]
              have hLt : n + 1 < 10 := by
                have hDiv' := hDiv
                rw [Nat.div_eq_zero_iff] at hDiv'
                rcases hDiv' with hTen | hLt
                · cases hTen
                · exact hLt
              have hDigits :
                  Nat.toDigits 10 (n + 1) =
                    [Nat.digitChar ((n + 1) % 10)] := by
                rw [Nat.toDigits_eq_if (by decide : 1 < 10)]
                rw [if_pos hLt]
                rw [Nat.mod_eq_of_lt hLt]
              rw [hDigits]
              change
                __str_from_int_eval_rec
                    (EvaluateProofInternal.eo_iota_int_list fuel (native_zplus i 1))
                    (Term.Numeral 0)
                    (Term.String
                      (Char.toNat (Nat.digitChar ((n + 1) % 10)) :: acc)) =
                  Term.String
                    (Char.toNat (Nat.digitChar ((n + 1) % 10)) :: acc)
              rw [__str_from_int_eval_rec.eq_4]
              · simp [__eo_eq, __eo_ite, native_ite, native_teq]
              · exact EvaluateProofInternal.eo_iota_int_list_ne_stuck fuel (native_zplus i 1)
              · intro h
                cases h
            · have hTailPos : 0 < (n + 1) / 10 :=
                Nat.pos_iff_ne_zero.mpr hDiv
              have hNotLt : ¬ n + 1 < 10 := by
                intro hLt
                exact hDiv (Nat.div_eq_of_lt hLt)
              have hDigits :
                  Nat.toDigits 10 (n + 1) =
                    Nat.toDigits 10 ((n + 1) / 10) ++
                      [Nat.digitChar ((n + 1) % 10)] := by
                rw [Nat.toDigits_eq_if (by decide : 1 < 10)]
                rw [if_neg hNotLt]
              have hTailLen :
                  (Nat.toDigits 10 ((n + 1) / 10)).length ≤ fuel := by
                rw [hDigits] at hLen
                simp at hLen
                omega
              have ih :=
                EvaluateProofInternal.eo_str_from_int_eval_rec_iota_toDigits fuel
                  (native_zplus i 1) ((n + 1) / 10)
                  ([Char.toNat (Nat.digitChar ((n + 1) % 10))] ++ acc)
                  hTailPos hTailLen
              rw [ih]
              rw [hDigits]
              simp [List.map_append, List.append_assoc]
          · intro h
            cases h
          · intro h
            injection h with hInt
            exact (Int.ne_of_gt (Int.ofNat_lt.mpr (Nat.succ_pos n))) hInt
          · intro h
            cases h

theorem EvaluateProofInternal.native_str_from_int_pos_toDigits
    {n : native_Int} (hPos : 0 < n) :
    native_str_from_int n =
      (Nat.toDigits 10 (Int.toNat n)).map Char.toNat := by
  have hNonneg : 0 ≤ n := Int.le_of_lt hPos
  have hNotNeg : ¬ n < 0 := Int.not_lt_of_ge hNonneg
  unfold native_str_from_int
  rw [if_neg hNotNeg]
  unfold native_string_lit
  have hCast : Int.ofNat (Int.toNat n) = n := Int.toNat_of_nonneg hNonneg
  rw [← hCast]
  change (toString (Int.ofNat (Int.toNat n))).toList.map Char.toNat =
    (Nat.toDigits 10 (Int.toNat n)).map Char.toNat
  rw [show toString (Int.ofNat (Int.toNat n)) = toString (Int.toNat n) by
    rfl]
  rw [Nat.toString_eq_ofList_toDigits (n := Int.toNat n)]
  rw [String.toList_ofList]

theorem EvaluateProofInternal.native_int_log_rec10_pow_bound :
    ∀ fuel remaining : Nat,
      remaining ≤ fuel ->
      0 < remaining ->
        remaining < 10 ^ (impl_native_int_log_rec 10 fuel remaining + 1)
  | 0, remaining, hLe, _hPos => by
      omega
  | fuel + 1, remaining, hLe, hPos => by
      rw [impl_native_int_log_rec]
      by_cases hLt : remaining < 10
      · rw [if_pos hLt]
        simpa using hLt
      · rw [if_neg hLt]
        let q := remaining / 10
        let r := remaining % 10
        have hTenLe : 10 ≤ remaining := Nat.le_of_not_gt hLt
        have hqPos : 0 < q := by
          dsimp [q]
          exact Nat.div_pos_iff.mpr (by omega)
        have hqLtRemaining : q < remaining := by
          dsimp [q]
          exact Nat.div_lt_self hPos (by decide : 1 < 10)
        have hqLeFuel : q ≤ fuel := by
          omega
        have ih := EvaluateProofInternal.native_int_log_rec10_pow_bound fuel q hqLeFuel hqPos
        have hqSucc :
            q + 1 ≤ 10 ^ (impl_native_int_log_rec 10 fuel q + 1) :=
          Nat.succ_le_of_lt ih
        have hRemEq : remaining = 10 * q + r := by
          dsimp [q, r]
          simpa [Nat.mul_comm] using (Nat.div_add_mod remaining 10).symm
        have hrLt : r < 10 := by
          dsimp [r]
          exact Nat.mod_lt remaining (by decide)
        change remaining < 10 ^ (1 + impl_native_int_log_rec 10 fuel q + 1)
        rw [hRemEq]
        calc
          10 * q + r < 10 * (q + 1) := by omega
          _ ≤ 10 * 10 ^ (impl_native_int_log_rec 10 fuel q + 1) := by
            exact Nat.mul_le_mul_left 10 hqSucc
          _ = 10 ^ (impl_native_int_log_rec 10 fuel q + 1) * 10 := by
            rw [Nat.mul_comm]
          _ = 10 ^ (impl_native_int_log_rec 10 fuel q + 1 + 1) := by
            exact (Nat.pow_succ 10 (impl_native_int_log_rec 10 fuel q + 1)).symm
          _ = 10 ^ (1 + impl_native_int_log_rec 10 fuel q + 1) := by
            rw [show impl_native_int_log_rec 10 fuel q + 1 + 1 =
              1 + impl_native_int_log_rec 10 fuel q + 1 by
                simp [Nat.add_comm]]

theorem EvaluateProofInternal.native_int_log10_digit_len_bound
    {n : native_Int} (hPos : 0 < n) :
    (Nat.toDigits 10 (Int.toNat n)).length ≤
      native_int_to_nat (native_zplus (native_int_log 10 n) 1) := by
  have hNonneg : 0 ≤ n := Int.le_of_lt hPos
  have hCast : Int.ofNat (Int.toNat n) = n := Int.toNat_of_nonneg hNonneg
  have hmPos : 0 < Int.toNat n := by
    apply Int.ofNat_lt.mp
    change (0 : Int) < Int.ofNat (Int.toNat n)
    rw [hCast]
    exact hPos
  have hNotLe : ¬ n ≤ 0 := Int.not_le_of_gt hPos
  have hFuel :
      native_int_to_nat (native_zplus (native_int_log 10 n) 1) =
        impl_native_int_log_rec 10 (Int.toNat n) (Int.toNat n) + 1 := by
    unfold native_int_to_nat native_zplus native_int_log
    simp [hNotLe]
  rw [hFuel]
  rw [Nat.length_toDigits_le_iff (b := 10)
    (n := Int.toNat n)
    (k := impl_native_int_log_rec 10 (Int.toNat n) (Int.toNat n) + 1)
    (by decide : 1 < 10)
    (Nat.succ_pos _)]
  exact EvaluateProofInternal.native_int_log_rec10_pow_bound (Int.toNat n) (Int.toNat n)
    (Nat.le_refl _) hmPos

theorem EvaluateProofInternal.eo_eval_str_from_int_rhs_run_numeral_neg
    {x : Term} {n : native_Int}
    (hRun : __run_evaluate x = Term.Numeral n)
    (hNeg : n < 0) :
    EvaluateProofInternal.eo_eval_str_from_int_rhs x = Term.String (native_str_from_int n) := by
  have hNegBool : native_zlt n 0 = true := by
    rw [show native_zlt n 0 = decide (n < 0) by rfl]
    exact decide_eq_true hNeg
  have hNative : native_str_from_int n = [] := by
    unfold native_str_from_int
    rw [if_pos hNeg]
    simp [native_string_lit]
  dsimp [EvaluateProofInternal.eo_eval_str_from_int_rhs]
  rw [hRun]
  simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
    native_ite, native_teq, native_and, native_not, hNegBool, hNative]

theorem EvaluateProofInternal.eo_eval_str_from_int_rhs_run_numeral_zero
    {x : Term}
    (hRun : __run_evaluate x = Term.Numeral 0) :
    EvaluateProofInternal.eo_eval_str_from_int_rhs x = Term.String (native_str_from_int 0) := by
  dsimp [EvaluateProofInternal.eo_eval_str_from_int_rhs]
  rw [hRun]
  native_decide

theorem EvaluateProofInternal.eo_eval_str_from_int_rhs_run_numeral_pos
    {x : Term} {n : native_Int}
    (hRun : __run_evaluate x = Term.Numeral n)
    (hPos : 0 < n) :
    EvaluateProofInternal.eo_eval_str_from_int_rhs x = Term.String (native_str_from_int n) := by
  have hReduced :
      EvaluateProofInternal.eo_eval_str_from_int_rhs x =
        __str_from_int_eval_rec
          (EvaluateProofInternal.eo_iota_int_list
            (native_int_to_nat (native_zplus (native_int_log 10 n) 1)) 0)
          (Term.Numeral n) (Term.String []) := by
    have hNegBool : native_zlt n 0 = false := by
      rw [show native_zlt n 0 = decide (n < 0) by rfl]
      exact decide_eq_false (Int.not_lt_of_ge (Int.le_of_lt hPos))
    have hLogNonneg : 0 ≤ native_int_log 10 n := by
      unfold native_int_log
      by_cases hCond :
          (decide (Int.toNat 10 ≤ 1) || Int.toNat n == 0) = true
      · rw [if_pos hCond]
        decide
      · rw [if_neg hCond]
        exact Int.natCast_nonneg _
    have hFuelNonneg :
        ¬ native_zplus (native_int_log 10 n) 1 < 0 := by
      exact Int.not_lt_of_ge
        (by
          unfold native_zplus
          exact Int.add_nonneg hLogNonneg (by decide))
    have hFuelNegBool :
        native_zlt (native_zplus (native_int_log 10 n) 1) 0 = false := by
      rw [show native_zlt (native_zplus (native_int_log 10 n) 1) 0 =
        decide (native_zplus (native_int_log 10 n) 1 < 0) by rfl]
      exact decide_eq_false hFuelNonneg
    dsimp [EvaluateProofInternal.eo_eval_str_from_int_rhs]
    rw [hRun]
    simp only [__eo_log, __eo_add]
    rw [EvaluateProofInternal.eo_iota_list_repeat_int_of_nonneg (k :=
      native_zplus (native_int_log 10 n) 1) (i := 0) hFuelNonneg]
    simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_requires, native_ite, native_teq, native_and, native_not,
      hNegBool, hFuelNegBool]
  rw [hReduced]
  rw [EvaluateProofInternal.native_str_from_int_pos_toDigits hPos]
  have hNonneg : 0 ≤ n := Int.le_of_lt hPos
  have hCast : Int.ofNat (Int.toNat n) = n := Int.toNat_of_nonneg hNonneg
  have hmPos : 0 < Int.toNat n := by
    apply Int.ofNat_lt.mp
    change (0 : Int) < Int.ofNat (Int.toNat n)
    rw [hCast]
    exact hPos
  have hLen := EvaluateProofInternal.native_int_log10_digit_len_bound hPos
  have hTermCast :
      Term.Numeral (Int.ofNat (Int.toNat n)) = Term.Numeral n := by
    rw [hCast]
  rw [← hTermCast]
  simpa using
    EvaluateProofInternal.eo_str_from_int_eval_rec_iota_toDigits
      (native_int_to_nat (native_zplus (native_int_log 10 n) 1))
      0 (Int.toNat n) [] hmPos hLen

theorem EvaluateProofInternal.eo_eval_str_from_int_rhs_run_numeral
    {x : Term} {n : native_Int}
    (hRun : __run_evaluate x = Term.Numeral n) :
    EvaluateProofInternal.eo_eval_str_from_int_rhs x = Term.String (native_str_from_int n) := by
  by_cases hNeg : n < 0
  · exact EvaluateProofInternal.eo_eval_str_from_int_rhs_run_numeral_neg hRun hNeg
  · by_cases hZero : n = 0
    · subst n
      exact EvaluateProofInternal.eo_eval_str_from_int_rhs_run_numeral_zero hRun
    · have hNonneg : 0 ≤ n := Int.le_of_not_gt hNeg
      have hPos : 0 < n := by
        by_cases hPos : 0 < n
        · exact hPos
        · have hLeZero : n ≤ 0 := Int.le_of_not_gt hPos
          have hEq : n = 0 := Int.le_antisymm hLeZero hNonneg
          exact False.elim (hZero hEq)
      exact EvaluateProofInternal.eo_eval_str_from_int_rhs_run_numeral_pos hRun hPos

theorem EvaluateProofInternal.eo_eval_str_from_int_rhs_run_non_numeral
    {x t : Term}
    (hRun : __run_evaluate x = t)
    (hNotNumeral : ∀ n : native_Int, t ≠ Term.Numeral n)
    (hTNe : t ≠ Term.Stuck) :
    EvaluateProofInternal.eo_eval_str_from_int_rhs x =
      Term.Apply (Term.UOp UserOp.str_from_int) t := by
  dsimp [EvaluateProofInternal.eo_eval_str_from_int_rhs]
  rw [hRun]
  cases t <;>
    simp [__eo_is_z, __eo_is_z_internal, __eo_ite, __eo_mk_apply,
      native_ite, native_teq, native_and, native_not] at hNotNumeral hTNe ⊢

theorem EvaluateProofInternal.str_case_lower_guard_singleton
    (c : native_Char) :
    __eo_and
        (__eo_gt (Term.Numeral 91) (Term.Numeral (c : Int)))
        (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 64)) =
      Term.Boolean ((decide (65 ≤ c)) && (decide (c ≤ 90))) := by
  have hUpper : native_zlt (c : Int) 91 = decide (c ≤ 90) := by
    by_cases h : c ≤ 90
    · have hNat : c < 91 := Nat.lt_succ_of_le h
      have hInt : (c : Int) < (91 : Int) := Int.ofNat_lt.mpr hNat
      rw [show native_zlt (c : Int) 91 = true by
        change decide ((c : Int) < (91 : Int)) = true
        exact decide_eq_true hInt]
      rw [show decide (c ≤ 90) = true by exact decide_eq_true h]
    · have hInt : ¬ (c : Int) < (91 : Int) := by
        intro hInt
        have hNat : c < 91 := Int.ofNat_lt.mp hInt
        exact h (Nat.le_of_lt_succ hNat)
      rw [show native_zlt (c : Int) 91 = false by
        change decide ((c : Int) < (91 : Int)) = false
        exact decide_eq_false hInt]
      rw [show decide (c ≤ 90) = false by exact decide_eq_false h]
  have hLower : native_zlt 64 (c : Int) = decide (65 ≤ c) := by
    by_cases h : 65 ≤ c
    · have hNat : 64 < c := Nat.lt_of_lt_of_le (by decide : 64 < 65) h
      have hInt : (64 : Int) < (c : Int) := Int.ofNat_lt.mpr hNat
      rw [show native_zlt 64 (c : Int) = true by
        change decide ((64 : Int) < (c : Int)) = true
        exact decide_eq_true hInt]
      rw [show decide (65 ≤ c) = true by exact decide_eq_true h]
    · have hInt : ¬ (64 : Int) < (c : Int) := by
        intro hInt
        have hNat : 64 < c := Int.ofNat_lt.mp hInt
        exact h (Nat.succ_le_of_lt hNat)
      rw [show native_zlt 64 (c : Int) = false by
        change decide ((64 : Int) < (c : Int)) = false
        exact decide_eq_false hInt]
      rw [show decide (65 ≤ c) = false by exact decide_eq_false h]
  change Term.Boolean (native_and (native_zlt (c : Int) 91)
    (native_zlt 64 (c : Int))) = _
  rw [hUpper, hLower]
  cases decide (65 ≤ c) <;> cases decide (c ≤ 90) <;> rfl

theorem EvaluateProofInternal.str_case_upper_guard_singleton
    (c : native_Char) :
    __eo_and
        (__eo_gt (Term.Numeral 123) (Term.Numeral (c : Int)))
        (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 96)) =
      Term.Boolean ((decide (97 ≤ c)) && (decide (c ≤ 122))) := by
  have hUpper : native_zlt (c : Int) 123 = decide (c ≤ 122) := by
    by_cases h : c ≤ 122
    · have hNat : c < 123 := Nat.lt_succ_of_le h
      have hInt : (c : Int) < (123 : Int) := Int.ofNat_lt.mpr hNat
      rw [show native_zlt (c : Int) 123 = true by
        change decide ((c : Int) < (123 : Int)) = true
        exact decide_eq_true hInt]
      rw [show decide (c ≤ 122) = true by exact decide_eq_true h]
    · have hInt : ¬ (c : Int) < (123 : Int) := by
        intro hInt
        have hNat : c < 123 := Int.ofNat_lt.mp hInt
        exact h (Nat.le_of_lt_succ hNat)
      rw [show native_zlt (c : Int) 123 = false by
        change decide ((c : Int) < (123 : Int)) = false
        exact decide_eq_false hInt]
      rw [show decide (c ≤ 122) = false by exact decide_eq_false h]
  have hLower : native_zlt 96 (c : Int) = decide (97 ≤ c) := by
    by_cases h : 97 ≤ c
    · have hNat : 96 < c := Nat.lt_of_lt_of_le (by decide : 96 < 97) h
      have hInt : (96 : Int) < (c : Int) := Int.ofNat_lt.mpr hNat
      rw [show native_zlt 96 (c : Int) = true by
        change decide ((96 : Int) < (c : Int)) = true
        exact decide_eq_true hInt]
      rw [show decide (97 ≤ c) = true by exact decide_eq_true h]
    · have hInt : ¬ (96 : Int) < (c : Int) := by
        intro hInt
        have hNat : 96 < c := Int.ofNat_lt.mp hInt
        exact h (Nat.succ_le_of_lt hNat)
      rw [show native_zlt 96 (c : Int) = false by
        change decide ((96 : Int) < (c : Int)) = false
        exact decide_eq_false hInt]
      rw [show decide (97 ≤ c) = false by exact decide_eq_false h]
  change Term.Boolean (native_and (native_zlt (c : Int) 123)
    (native_zlt 96 (c : Int))) = _
  rw [hUpper, hLower]
  cases decide (97 ≤ c) <;> cases decide (c ≤ 122) <;> rfl

theorem EvaluateProofInternal.str_case_conv_rec_lower_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __str_case_conv_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
          (Term.String []))
        (Term.Boolean true) =
      Term.String [impl_native_char_to_lower c] := by
  cases hRange : ((decide (65 ≤ c)) && (decide (c ≤ 90)))
  · have hGuardFalse :
        __eo_and (__eo_gt (Term.Numeral 91) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 64)) =
        Term.Boolean false := by
      rw [EvaluateProofInternal.str_case_lower_guard_singleton c, hRange]
    have hCast : (c : Int) + 0 = (c : Int) := by rw [Int.add_zero]
    unfold __str_case_conv_rec
    rw [EvaluateProofInternal.eo_to_z_singleton hc]
    dsimp
    rw [hGuardFalse]
    change __eo_concat (__eo_to_str (Term.Numeral ((c : Int) + 0)))
      (Term.String []) = Term.String [impl_native_char_to_lower c]
    rw [hCast, EvaluateProofInternal.eo_to_str_of_valid_nat hc]
    unfold impl_native_char_to_lower
    rw [hRange]
    rfl
  · have h90 : c ≤ 90 := by
      cases h65d : decide (65 ≤ c) <;> cases h90d : decide (c ≤ 90) <;>
        simp [h65d, h90d] at hRange
      exact of_decide_eq_true h90d
    have hGuardTrue :
        __eo_and (__eo_gt (Term.Numeral 91) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 64)) =
        Term.Boolean true := by
      rw [EvaluateProofInternal.str_case_lower_guard_singleton c, hRange]
    have hValidLower : native_char_valid (c + 32) = true := by
      change decide (c + 32 < 196608) = true
      exact decide_eq_true
        (Nat.lt_of_le_of_lt (Nat.add_le_add_right h90 32) (by decide))
    have hCast : (c : Int) + 32 = ((c + 32 : Nat) : Int) := by
      rw [Int.natCast_add]
      rfl
    unfold __str_case_conv_rec
    rw [EvaluateProofInternal.eo_to_z_singleton hc]
    dsimp
    rw [hGuardTrue]
    change __eo_concat (__eo_to_str (Term.Numeral ((c : Int) + 32)))
      (Term.String []) = Term.String [impl_native_char_to_lower c]
    rw [hCast, EvaluateProofInternal.eo_to_str_of_valid_nat hValidLower]
    unfold impl_native_char_to_lower
    rw [hRange]
    rfl

theorem EvaluateProofInternal.str_case_conv_rec_upper_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __str_case_conv_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
          (Term.String []))
        (Term.Boolean false) =
      Term.String [impl_native_char_to_upper c] := by
  cases hRange : ((decide (97 ≤ c)) && (decide (c ≤ 122)))
  · have hGuardFalse :
        __eo_and (__eo_gt (Term.Numeral 123) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 96)) =
        Term.Boolean false := by
      rw [EvaluateProofInternal.str_case_upper_guard_singleton c, hRange]
    have hCast : (c : Int) + 0 = (c : Int) := by rw [Int.add_zero]
    unfold __str_case_conv_rec
    rw [EvaluateProofInternal.eo_to_z_singleton hc]
    dsimp
    rw [hGuardFalse]
    change __eo_concat (__eo_to_str (Term.Numeral ((c : Int) + 0)))
      (Term.String []) = Term.String [impl_native_char_to_upper c]
    rw [hCast, EvaluateProofInternal.eo_to_str_of_valid_nat hc]
    unfold impl_native_char_to_upper
    rw [hRange]
    rfl
  · have h97 : 97 ≤ c := by
      cases h97d : decide (97 ≤ c) <;> cases h122d : decide (c ≤ 122) <;>
        simp [h97d, h122d] at hRange
      exact of_decide_eq_true h97d
    have h32 : 32 ≤ c := Nat.le_trans (by decide) h97
    have hGuardTrue :
        __eo_and (__eo_gt (Term.Numeral 123) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 96)) =
        Term.Boolean true := by
      rw [EvaluateProofInternal.str_case_upper_guard_singleton c, hRange]
    have hValidUpper : native_char_valid (c - 32) = true := by
      change decide (c - 32 < 196608) = true
      exact decide_eq_true
        (Nat.lt_of_le_of_lt (Nat.sub_le c 32) (EvaluateProofInternal.native_char_valid_lt hc))
    have hCast : (c : Int) + (-32 : Int) = ((c - 32 : Nat) : Int) := by
      rw [Int.ofNat_sub h32]
      rfl
    unfold __str_case_conv_rec
    rw [EvaluateProofInternal.eo_to_z_singleton hc]
    dsimp
    rw [hGuardTrue]
    change __eo_concat (__eo_to_str (Term.Numeral ((c : Int) + (-32 : Int))))
      (Term.String []) = Term.String [impl_native_char_to_upper c]
    rw [hCast, EvaluateProofInternal.eo_to_str_of_valid_nat hValidUpper]
    unfold impl_native_char_to_upper
    rw [hRange]
    rfl

theorem EvaluateProofInternal.str_flatten_nary_intro_singleton
    (c : native_Char) :
    __str_flatten (__str_nary_intro (Term.String [c])) =
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
        (Term.String []) := by
  rfl

theorem EvaluateProofInternal.str_case_conv_rec_flatten_lower_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __str_case_conv_rec (__str_flatten (__str_nary_intro (Term.String [c])))
        (Term.Boolean true) =
      Term.String [impl_native_char_to_lower c] := by
  rw [EvaluateProofInternal.str_flatten_nary_intro_singleton c]
  exact EvaluateProofInternal.str_case_conv_rec_lower_singleton hc

theorem EvaluateProofInternal.str_case_conv_rec_flatten_upper_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __str_case_conv_rec (__str_flatten (__str_nary_intro (Term.String [c])))
        (Term.Boolean false) =
      Term.String [impl_native_char_to_upper c] := by
  rw [EvaluateProofInternal.str_flatten_nary_intro_singleton c]
  exact EvaluateProofInternal.str_case_conv_rec_upper_singleton hc

def EvaluateProofInternal.strCharChain : native_String -> Term
  | [] => Term.String []
  | c :: cs =>
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
        (EvaluateProofInternal.strCharChain cs)

theorem EvaluateProofInternal.native_string_valid_cons_parts_local
    {c : native_Char} {cs : native_String}
    (h : native_string_valid (c :: cs) = true) :
    native_char_valid c = true ∧ native_string_valid cs = true := by
  simp [native_string_valid] at h
  constructor
  · exact h.1
  · rw [native_string_valid, List.all_eq_true]
    intro x hx
    exact h.2 x hx

theorem EvaluateProofInternal.str_case_conv_lower_head_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __eo_to_str
        (__eo_add (__eo_to_z (Term.String [c]))
          (__eo_ite
            (__eo_and
              (__eo_gt (Term.Numeral 91) (__eo_to_z (Term.String [c])))
              (__eo_gt (__eo_to_z (Term.String [c])) (Term.Numeral 64)))
            (Term.Numeral 32) (Term.Numeral 0))) =
      Term.String [impl_native_char_to_lower c] := by
  cases hRange : ((decide (65 ≤ c)) && (decide (c ≤ 90)))
  · have hGuardFalse :
        __eo_and (__eo_gt (Term.Numeral 91) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 64)) =
        Term.Boolean false := by
      rw [EvaluateProofInternal.str_case_lower_guard_singleton c, hRange]
    have hCast : (c : Int) + 0 = (c : Int) := by rw [Int.add_zero]
    rw [EvaluateProofInternal.eo_to_z_singleton hc]
    rw [hGuardFalse]
    change __eo_to_str (Term.Numeral ((c : Int) + 0)) =
      Term.String [impl_native_char_to_lower c]
    rw [hCast, EvaluateProofInternal.eo_to_str_of_valid_nat hc]
    unfold impl_native_char_to_lower
    rw [hRange]
    rfl
  · have h90 : c ≤ 90 := by
      cases h65d : decide (65 ≤ c) <;> cases h90d : decide (c ≤ 90) <;>
        simp [h65d, h90d] at hRange
      exact of_decide_eq_true h90d
    have hGuardTrue :
        __eo_and (__eo_gt (Term.Numeral 91) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 64)) =
        Term.Boolean true := by
      rw [EvaluateProofInternal.str_case_lower_guard_singleton c, hRange]
    have hValidLower : native_char_valid (c + 32) = true := by
      change decide (c + 32 < 196608) = true
      exact decide_eq_true
        (Nat.lt_of_le_of_lt (Nat.add_le_add_right h90 32) (by decide))
    have hCast : (c : Int) + 32 = ((c + 32 : Nat) : Int) := by
      rw [Int.natCast_add]
      rfl
    rw [EvaluateProofInternal.eo_to_z_singleton hc]
    rw [hGuardTrue]
    change __eo_to_str (Term.Numeral ((c : Int) + 32)) =
      Term.String [impl_native_char_to_lower c]
    rw [hCast, EvaluateProofInternal.eo_to_str_of_valid_nat hValidLower]
    unfold impl_native_char_to_lower
    rw [hRange]
    rfl

theorem EvaluateProofInternal.str_case_conv_upper_head_singleton
    {c : native_Char}
    (hc : native_char_valid c = true) :
    __eo_to_str
        (__eo_add (__eo_to_z (Term.String [c]))
          (__eo_ite
            (__eo_and
              (__eo_gt (Term.Numeral 123) (__eo_to_z (Term.String [c])))
              (__eo_gt (__eo_to_z (Term.String [c])) (Term.Numeral 96)))
            (Term.Numeral (-32 : native_Int)) (Term.Numeral 0))) =
      Term.String [impl_native_char_to_upper c] := by
  cases hRange : ((decide (97 ≤ c)) && (decide (c ≤ 122)))
  · have hGuardFalse :
        __eo_and (__eo_gt (Term.Numeral 123) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 96)) =
        Term.Boolean false := by
      rw [EvaluateProofInternal.str_case_upper_guard_singleton c, hRange]
    have hCast : (c : Int) + 0 = (c : Int) := by rw [Int.add_zero]
    rw [EvaluateProofInternal.eo_to_z_singleton hc]
    rw [hGuardFalse]
    change __eo_to_str (Term.Numeral ((c : Int) + 0)) =
      Term.String [impl_native_char_to_upper c]
    rw [hCast, EvaluateProofInternal.eo_to_str_of_valid_nat hc]
    unfold impl_native_char_to_upper
    rw [hRange]
    rfl
  · have h97 : 97 ≤ c := by
      cases h97d : decide (97 ≤ c) <;> cases h122d : decide (c ≤ 122) <;>
        simp [h97d, h122d] at hRange
      exact of_decide_eq_true h97d
    have h32 : 32 ≤ c := Nat.le_trans (by decide) h97
    have hGuardTrue :
        __eo_and (__eo_gt (Term.Numeral 123) (Term.Numeral (c : Int)))
          (__eo_gt (Term.Numeral (c : Int)) (Term.Numeral 96)) =
        Term.Boolean true := by
      rw [EvaluateProofInternal.str_case_upper_guard_singleton c, hRange]
    have hValidUpper : native_char_valid (c - 32) = true := by
      change decide (c - 32 < 196608) = true
      exact decide_eq_true
        (Nat.lt_of_le_of_lt (Nat.sub_le c 32) (EvaluateProofInternal.native_char_valid_lt hc))
    have hCast : (c : Int) + (-32 : Int) = ((c - 32 : Nat) : Int) := by
      rw [Int.ofNat_sub h32]
      rfl
    rw [EvaluateProofInternal.eo_to_z_singleton hc]
    rw [hGuardTrue]
    change __eo_to_str (Term.Numeral ((c : Int) + (-32 : Int))) =
      Term.String [impl_native_char_to_upper c]
    rw [hCast, EvaluateProofInternal.eo_to_str_of_valid_nat hValidUpper]
    unfold impl_native_char_to_upper
    rw [hRange]
    rfl

theorem EvaluateProofInternal.str_case_conv_rec_lower_char_chain :
    ∀ s : native_String,
      native_string_valid s = true ->
        __str_case_conv_rec (EvaluateProofInternal.strCharChain s) (Term.Boolean true) =
          Term.String (native_str_to_lower s)
  | [], _hs => by
      rfl
  | c :: cs, hs => by
      rcases EvaluateProofInternal.native_string_valid_cons_parts_local hs with ⟨hc, hcs⟩
      have hTail := EvaluateProofInternal.str_case_conv_rec_lower_char_chain cs hcs
      unfold EvaluateProofInternal.strCharChain
      unfold __str_case_conv_rec
      dsimp
      rw [EvaluateProofInternal.str_case_conv_lower_head_singleton hc, hTail]
      rfl

theorem EvaluateProofInternal.str_case_conv_rec_upper_char_chain :
    ∀ s : native_String,
      native_string_valid s = true ->
        __str_case_conv_rec (EvaluateProofInternal.strCharChain s) (Term.Boolean false) =
          Term.String (native_str_to_upper s)
  | [], _hs => by
      rfl
  | c :: cs, hs => by
      rcases EvaluateProofInternal.native_string_valid_cons_parts_local hs with ⟨hc, hcs⟩
      have hTail := EvaluateProofInternal.str_case_conv_rec_upper_char_chain cs hcs
      unfold EvaluateProofInternal.strCharChain
      unfold __str_case_conv_rec
      dsimp
      rw [EvaluateProofInternal.str_case_conv_upper_head_singleton hc, hTail]
      rfl

theorem EvaluateProofInternal.substrWord_zero_eq_strCharChain :
    ∀ s : native_String,
      RuleProofs.substrWord s 0 s.length = EvaluateProofInternal.strCharChain s
  | [] => by
      rfl
  | c :: cs => by
      rw [show (c :: cs).length = cs.length + 1 from rfl]
      change
        Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.String (RuleProofs.extractString (c :: cs) 0)))
            (RuleProofs.substrWord (c :: cs) (0 + 1) cs.length) =
          Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
            (EvaluateProofInternal.strCharChain cs)
      rw [RuleProofs.extractString_zero_cons c cs]
      rw [show (0 : native_Int) + 1 = 1 by rfl]
      rw [RuleProofs.substrWord_cons_tail c cs]
      rw [EvaluateProofInternal.substrWord_zero_eq_strCharChain cs]

theorem EvaluateProofInternal.str_flatten_nary_intro_string_char_chain
    (s : native_String) :
    __str_flatten (__str_nary_intro (Term.String s)) = EvaluateProofInternal.strCharChain s := by
  cases s with
  | nil =>
      rw [RuleProofs.str_flatten_nary_intro_empty]
      rfl
  | cons c cs =>
      rw [RuleProofs.str_flatten_nary_intro_cons c cs]
      exact EvaluateProofInternal.substrWord_zero_eq_strCharChain (c :: cs)

theorem EvaluateProofInternal.str_is_prefix_flat_strCharChain :
    ∀ s pat : native_String,
      __str_is_prefix_flat (EvaluateProofInternal.strCharChain s) (EvaluateProofInternal.strCharChain pat) =
        Term.Boolean (native_string_prefix_eq pat s)
  | [], [] => by
      rfl
  | _c :: _cs, [] => by
      rfl
  | [], _p :: _ps => by
      simp [EvaluateProofInternal.strCharChain, native_string_prefix_eq, __str_is_prefix_flat,
        __eo_l_1___str_is_prefix_flat]
  | c :: cs, d :: ds => by
      by_cases hcd : c = d
      · subst d
        simp [EvaluateProofInternal.strCharChain, native_string_prefix_eq, __str_is_prefix_flat,
          __eo_eq, native_teq, native_ite,
          EvaluateProofInternal.str_is_prefix_flat_strCharChain cs ds]
      · have hdc : d ≠ c := by
          intro h
          exact hcd h.symm
        simp [EvaluateProofInternal.strCharChain, native_string_prefix_eq, __str_is_prefix_flat,
          __eo_l_1___str_is_prefix_flat, __eo_eq, native_teq, native_ite,
          hdc]

def EvaluateProofInternal.native_str_replace_all_chain (pat repl : native_String) :
    Nat -> native_String -> native_String
  | _, [] => []
  | 0, c :: cs =>
      if native_string_prefix_eq pat (c :: cs) then
        repl ++ EvaluateProofInternal.native_str_replace_all_chain pat repl (pat.length - 1) cs
      else
        c :: EvaluateProofInternal.native_str_replace_all_chain pat repl 0 cs
  | skip + 1, _ :: cs =>
      EvaluateProofInternal.native_str_replace_all_chain pat repl skip cs

theorem EvaluateProofInternal.native_str_replace_all_chain_skip_eq_drop
    (pat repl : native_String) :
    ∀ (skip : Nat) (s : native_String),
      EvaluateProofInternal.native_str_replace_all_chain pat repl skip s =
        EvaluateProofInternal.native_str_replace_all_chain pat repl 0 (s.drop skip) := by
  intro skip
  induction skip with
  | zero =>
      intro s
      simp
  | succ skip ih =>
      intro s
      cases s with
      | nil =>
          simp [EvaluateProofInternal.native_str_replace_all_chain]
      | cons _c cs =>
          simpa [EvaluateProofInternal.native_str_replace_all_chain] using ih cs

theorem EvaluateProofInternal.str_eval_replace_all_rec_strCharChain_cons
    (p : native_Char) (ps repl : native_String) :
    ∀ (s : native_String) (skip : Nat),
      __str_eval_replace_all_rec (EvaluateProofInternal.strCharChain s) (EvaluateProofInternal.strCharChain (p :: ps))
          (Term.String repl) (Term.Numeral (skip : native_Int))
          (Term.Numeral ((p :: ps).length : native_Int)) =
        Term.String (EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl skip s)
  | [], _skip => by
      simp [EvaluateProofInternal.strCharChain, EvaluateProofInternal.native_str_replace_all_chain,
        __str_eval_replace_all_rec]
  | c :: cs, 0 => by
      rw [show EvaluateProofInternal.strCharChain (c :: cs) =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
          (EvaluateProofInternal.strCharChain cs) by
        rfl]
      change
        __eo_ite
            (__str_is_prefix_flat
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                (EvaluateProofInternal.strCharChain cs))
              (EvaluateProofInternal.strCharChain (p :: ps)))
            (__eo_concat (Term.String repl)
              (__str_eval_replace_all_rec (EvaluateProofInternal.strCharChain cs)
                (EvaluateProofInternal.strCharChain (p :: ps)) (Term.String repl)
                (__eo_add
                  (Term.Numeral ((p :: ps).length : native_Int))
                  (Term.Numeral (-1 : native_Int)))
                (Term.Numeral ((p :: ps).length : native_Int))))
            (__eo_concat (Term.String [c])
              (__str_eval_replace_all_rec (EvaluateProofInternal.strCharChain cs)
                (EvaluateProofInternal.strCharChain (p :: ps)) (Term.String repl)
                (Term.Numeral 0)
                (Term.Numeral ((p :: ps).length : native_Int)))) =
          Term.String (EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl 0 (c :: cs))
      rw [show
          __str_is_prefix_flat
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                (EvaluateProofInternal.strCharChain cs))
              (EvaluateProofInternal.strCharChain (p :: ps)) =
            __str_is_prefix_flat (EvaluateProofInternal.strCharChain (c :: cs))
              (EvaluateProofInternal.strCharChain (p :: ps)) by
        rfl]
      rw [EvaluateProofInternal.str_is_prefix_flat_strCharChain (c :: cs) (p :: ps)]
      by_cases hPref : native_string_prefix_eq (p :: ps) (c :: cs) = true
      · rw [hPref]
        rw [eo_ite_true]
        have hLenSub :
            (ps.length : native_Int) + 1 + (-1 : native_Int) =
              (ps.length : native_Int) := by
          rw [Int.add_assoc]
          simp
        rw [show
            __eo_add (Term.Numeral ((p :: ps).length : native_Int))
                (Term.Numeral (-1 : native_Int)) =
              Term.Numeral (((p :: ps).length - 1 : Nat) : native_Int) by
          simp [__eo_add, native_zplus, hLenSub]]
        rw [EvaluateProofInternal.str_eval_replace_all_rec_strCharChain_cons p ps repl cs
          ((p :: ps).length - 1)]
        simp [EvaluateProofInternal.native_str_replace_all_chain, hPref, __eo_concat,
          native_str_concat]
      · have hPrefFalse :
            native_string_prefix_eq (p :: ps) (c :: cs) = false :=
          by
            cases hp : native_string_prefix_eq (p :: ps) (c :: cs) <;>
              simp [hp] at hPref ⊢
        rw [hPrefFalse]
        rw [eo_ite_false]
        rw [show
            __str_eval_replace_all_rec (EvaluateProofInternal.strCharChain cs)
                (EvaluateProofInternal.strCharChain (p :: ps)) (Term.String repl)
                (Term.Numeral 0)
                (Term.Numeral ((p :: ps).length : native_Int)) =
              Term.String
                (EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl 0 cs) by
          simpa using
            EvaluateProofInternal.str_eval_replace_all_rec_strCharChain_cons p ps repl cs 0]
        simp [EvaluateProofInternal.native_str_replace_all_chain, hPrefFalse, __eo_concat,
          native_str_concat]
  | c :: cs, skip + 1 => by
      rw [show EvaluateProofInternal.strCharChain (c :: cs) =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
          (EvaluateProofInternal.strCharChain cs) by
        rfl]
      change
        __str_eval_replace_all_rec (EvaluateProofInternal.strCharChain cs)
            (EvaluateProofInternal.strCharChain (p :: ps)) (Term.String repl)
            (__eo_add
              (Term.Numeral ((skip + 1 : Nat) : native_Int))
              (Term.Numeral (-1 : native_Int)))
            (Term.Numeral ((p :: ps).length : native_Int)) =
          Term.String
            (EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl (skip + 1) (c :: cs))
      have hSkipSub :
          (skip : native_Int) + 1 + (-1 : native_Int) =
            (skip : native_Int) := by
        rw [Int.add_assoc]
        simp
      rw [show
          __eo_add (Term.Numeral ((skip + 1 : Nat) : native_Int))
              (Term.Numeral (-1 : native_Int)) =
            Term.Numeral (skip : native_Int) by
        simp [__eo_add, native_zplus, hSkipSub]]
      simpa [EvaluateProofInternal.native_str_replace_all_chain] using
        EvaluateProofInternal.str_eval_replace_all_rec_strCharChain_cons p ps repl cs skip

theorem EvaluateProofInternal.str_replace_all_result_strings_empty
    (s repl : native_String) :
    __eo_ite
        (__eo_and
          (__eo_and (__eo_is_str (Term.String s))
            (__eo_is_str (Term.String [])))
          (__eo_is_str (Term.String repl)))
        (__eo_ite (__eo_eq (Term.String []) (Term.String []))
          (Term.String s)
          (__str_eval_replace_all_rec
            (__str_flatten (__str_nary_intro (Term.String s)))
            (__str_flatten (__str_nary_intro (Term.String [])))
            (Term.String repl) (Term.Numeral 0)
            (__eo_len (Term.String []))))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_replace_all) (Term.String s))
            (Term.String []))
          (Term.String repl)) =
      Term.String s := by
  simp [__eo_is_str, __eo_is_str_internal, __eo_and, __eo_eq, __eo_ite,
    native_and, native_teq, native_not, native_ite]

theorem EvaluateProofInternal.str_replace_all_result_strings_cons
    (s repl : native_String) (p : native_Char) (ps : native_String) :
    __eo_ite
        (__eo_and
          (__eo_and (__eo_is_str (Term.String s))
            (__eo_is_str (Term.String (p :: ps))))
          (__eo_is_str (Term.String repl)))
        (__eo_ite (__eo_eq (Term.String (p :: ps)) (Term.String []))
          (Term.String s)
          (__str_eval_replace_all_rec
            (__str_flatten (__str_nary_intro (Term.String s)))
            (__str_flatten (__str_nary_intro (Term.String (p :: ps))))
            (Term.String repl) (Term.Numeral 0)
            (__eo_len (Term.String (p :: ps)))))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_replace_all) (Term.String s))
            (Term.String (p :: ps)))
          (Term.String repl)) =
      Term.String (EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl 0 s) := by
  have hGuard :
      __eo_and
          (__eo_and (__eo_is_str (Term.String s))
            (__eo_is_str (Term.String (p :: ps))))
          (__eo_is_str (Term.String repl)) =
        Term.Boolean true := by
    simp [__eo_is_str, __eo_is_str_internal, __eo_and, native_and,
      native_teq, native_not]
  rw [hGuard, eo_ite_true]
  have hPatNe :
      __eo_eq (Term.String (p :: ps)) (Term.String []) =
        Term.Boolean false := by
    simp [__eo_eq, native_teq]
  rw [hPatNe, eo_ite_false]
  rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain s]
  rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain (p :: ps)]
  simpa [__eo_len, native_str_len] using
    EvaluateProofInternal.str_eval_replace_all_rec_strCharChain_cons p ps repl s 0

theorem EvaluateProofInternal.run_evaluate_typeof_eq_str_replace_all
    (b y x : Term) :
    __eo_typeof
        (__run_evaluate
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_replace_all) b) y) x)) =
      __eo_typeof
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_replace_all) b) y) x) := by
  cases b
  case String sb =>
    cases y
    case String sy =>
      cases x
      case String sx =>
        cases sy with
        | nil =>
          change
            __eo_typeof
                (__eo_ite
                  (__eo_and
                    (__eo_and (__eo_is_str (Term.String sb))
                      (__eo_is_str (Term.String [])))
                    (__eo_is_str (Term.String sx)))
                  (__eo_ite (__eo_eq (Term.String []) (Term.String []))
                    (Term.String sb)
                    (__str_eval_replace_all_rec
                      (__str_flatten (__str_nary_intro (Term.String sb)))
                      (__str_flatten (__str_nary_intro (Term.String [])))
                      (Term.String sx) (Term.Numeral 0)
                      (__eo_len (Term.String []))))
                  (Term.Apply
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_replace_all)
                        (Term.String sb))
                      (Term.String []))
                    (Term.String sx))) =
              __eo_typeof
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_replace_all)
                      (Term.String sb))
                    (Term.String []))
                  (Term.String sx))
          conv =>
            lhs
            rw [EvaluateProofInternal.str_replace_all_result_strings_empty sb sx]
          change
            Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) =
              __eo_typeof_str_replace
                (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
                (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
                (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
          simp [__eo_typeof_str_replace, __eo_requires, __eo_and, __eo_eq,
            native_and, native_ite, native_teq, native_not]
        | cons p ps =>
          change
            __eo_typeof
                (__eo_ite
                  (__eo_and
                    (__eo_and (__eo_is_str (Term.String sb))
                      (__eo_is_str (Term.String (p :: ps))))
                    (__eo_is_str (Term.String sx)))
                  (__eo_ite (__eo_eq (Term.String (p :: ps))
                      (Term.String []))
                    (Term.String sb)
                    (__str_eval_replace_all_rec
                      (__str_flatten (__str_nary_intro (Term.String sb)))
                      (__str_flatten
                        (__str_nary_intro (Term.String (p :: ps))))
                      (Term.String sx) (Term.Numeral 0)
                      (__eo_len (Term.String (p :: ps)))))
                  (Term.Apply
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_replace_all)
                        (Term.String sb))
                      (Term.String (p :: ps)))
                    (Term.String sx))) =
              __eo_typeof
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_replace_all)
                      (Term.String sb))
                    (Term.String (p :: ps)))
                  (Term.String sx))
          conv =>
            lhs
            rw [EvaluateProofInternal.str_replace_all_result_strings_cons sb sx p ps]
          change
            Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) =
              __eo_typeof_str_replace
                (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
                (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
                (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
          simp [__eo_typeof_str_replace, __eo_requires, __eo_and, __eo_eq,
            native_and, native_ite, native_teq, native_not]
      all_goals
        simp [__run_evaluate, __eo_is_str, __eo_is_str_internal,
          __eo_and, __eo_ite, __eo_eq, __eo_typeof_str_replace,
          __eo_requires, native_and, native_ite, native_teq, native_not]
    all_goals
      simp [__run_evaluate, __eo_is_str, __eo_is_str_internal,
        __eo_and, __eo_ite, __eo_eq, __eo_typeof_str_replace,
        __eo_requires, native_and, native_ite, native_teq, native_not]
  all_goals
    simp [__run_evaluate, __eo_is_str, __eo_is_str_internal,
      __eo_and, __eo_ite, __eo_eq, __eo_typeof_str_replace,
      __eo_requires, native_and, native_ite, native_teq, native_not]

theorem EvaluateProofInternal.native_string_valid_replace_all_chain
    (pat repl : native_String) :
    ∀ (s : native_String) (skip : Nat),
      native_string_valid s = true ->
      native_string_valid repl = true ->
        native_string_valid
          (EvaluateProofInternal.native_str_replace_all_chain pat repl skip s) = true
  | [], _skip, _hs, _hrepl => by
      rfl
  | c :: cs, 0, hs, hrepl => by
      rcases EvaluateProofInternal.native_string_valid_cons_parts_local hs with ⟨hc, hcs⟩
      by_cases hPref : native_string_prefix_eq pat (c :: cs) = true
      · simp [EvaluateProofInternal.native_str_replace_all_chain, hPref]
        exact native_string_valid_append hrepl
          (EvaluateProofInternal.native_string_valid_replace_all_chain pat repl cs
            (pat.length - 1) hcs hrepl)
      · have hPrefFalse :
            native_string_prefix_eq pat (c :: cs) = false := by
          cases hp : native_string_prefix_eq pat (c :: cs) <;>
            simp [hp] at hPref ⊢
        have hTail :
            native_string_valid
              (EvaluateProofInternal.native_str_replace_all_chain pat repl 0 cs) = true :=
          EvaluateProofInternal.native_string_valid_replace_all_chain pat repl cs 0 hcs hrepl
        rw [native_string_valid, List.all_eq_true] at hTail
        simp [EvaluateProofInternal.native_str_replace_all_chain, hPrefFalse, native_string_valid,
          hc]
        exact hTail
  | c :: cs, skip + 1, hs, hrepl => by
      rcases EvaluateProofInternal.native_string_valid_cons_parts_local hs with ⟨_hc, hcs⟩
      simpa [EvaluateProofInternal.native_str_replace_all_chain] using
        EvaluateProofInternal.native_string_valid_replace_all_chain pat repl cs skip hcs hrepl

theorem EvaluateProofInternal.smtx_typeof_eo_string_seq_char_valid
    (s : native_String) (T : SmtType)
    (hTy : __smtx_typeof (__eo_to_smt (Term.String s)) =
      SmtType.Seq T) :
    T = SmtType.Char ∧ native_string_valid s = true := by
  change __smtx_typeof (SmtTerm.String s) = SmtType.Seq T at hTy
  cases hValid : native_string_valid s
  · simp [__smtx_typeof, hValid, native_ite] at hTy
  · simp [__smtx_typeof, hValid, native_ite] at hTy
    cases hTy
    exact ⟨rfl, rfl⟩

theorem EvaluateProofInternal.strCharChain_get_nil :
    ∀ s : native_String,
      __eo_get_nil_rec (Term.UOp UserOp.str_concat)
        (EvaluateProofInternal.strCharChain s) = Term.String []
  | [] => by
      simp [EvaluateProofInternal.strCharChain, __eo_get_nil_rec, __eo_is_list_nil,
        __eo_is_list_nil_str_concat, __eo_eq, __eo_requires,
        native_ite, native_teq, native_not]
  | _c :: cs => by
      simp [EvaluateProofInternal.strCharChain, __eo_get_nil_rec, __eo_requires,
        native_ite, native_teq, native_not]
      exact EvaluateProofInternal.strCharChain_get_nil cs

theorem EvaluateProofInternal.strCharChain_ne_stuck :
    ∀ s : native_String, EvaluateProofInternal.strCharChain s ≠ Term.Stuck
  | [] => by
      intro h
      cases h
  | _ :: _ => by
      intro h
      cases h

theorem EvaluateProofInternal.strCharChain_is_list :
    ∀ s : native_String,
      __eo_is_list (Term.UOp UserOp.str_concat)
        (EvaluateProofInternal.strCharChain s) = Term.Boolean true
  | [] => by
      change
        __eo_is_ok
            (__eo_get_nil_rec (Term.UOp UserOp.str_concat) (Term.String [])) =
          Term.Boolean true
      rw [show __eo_get_nil_rec (Term.UOp UserOp.str_concat)
          (Term.String []) = Term.String [] by
        exact EvaluateProofInternal.strCharChain_get_nil []]
      exact eo_is_ok_true_of_ne_stuck _ (by intro h; cases h)
  | c :: cs => by
      change
        __eo_is_ok
            (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                (EvaluateProofInternal.strCharChain cs))) =
          Term.Boolean true
      rw [show __eo_get_nil_rec (Term.UOp UserOp.str_concat)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
            (EvaluateProofInternal.strCharChain cs)) = Term.String [] by
        exact EvaluateProofInternal.strCharChain_get_nil (c :: cs)]
      exact eo_is_ok_true_of_ne_stuck _ (by intro h; cases h)

theorem EvaluateProofInternal.eo_list_rev_rec_strCharChain :
    ∀ s t : native_String,
      __eo_list_rev_rec (EvaluateProofInternal.strCharChain s) (EvaluateProofInternal.strCharChain t) =
        EvaluateProofInternal.strCharChain (s.reverse ++ t)
  | [], t => by
      cases t <;> rfl
  | c :: cs, t => by
      rw [show EvaluateProofInternal.strCharChain (c :: cs) =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
          (EvaluateProofInternal.strCharChain cs) by
        rfl]
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.str_concat)
        (Term.String [c]) (EvaluateProofInternal.strCharChain cs) (EvaluateProofInternal.strCharChain t)
        (EvaluateProofInternal.strCharChain_ne_stuck t)]
      rw [show
        Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
            (Term.String [c])) (EvaluateProofInternal.strCharChain t) =
          EvaluateProofInternal.strCharChain (c :: t) by
        rfl]
      rw [EvaluateProofInternal.eo_list_rev_rec_strCharChain cs (c :: t)]
      simp [List.reverse_cons, List.append_assoc]

theorem EvaluateProofInternal.eo_list_rev_strCharChain :
    ∀ s : native_String,
      __eo_list_rev (Term.UOp UserOp.str_concat) (EvaluateProofInternal.strCharChain s) =
        EvaluateProofInternal.strCharChain s.reverse
  | s => by
      change
        __eo_requires
          (__eo_is_list (Term.UOp UserOp.str_concat) (EvaluateProofInternal.strCharChain s))
          (Term.Boolean true)
          (__eo_list_rev_rec (EvaluateProofInternal.strCharChain s)
            (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
              (EvaluateProofInternal.strCharChain s))) =
        EvaluateProofInternal.strCharChain s.reverse
      rw [EvaluateProofInternal.strCharChain_is_list s]
      simp [__eo_requires, native_ite, native_teq, native_not]
      rw [EvaluateProofInternal.strCharChain_get_nil s]
      simpa [EvaluateProofInternal.strCharChain, List.append_nil] using
        EvaluateProofInternal.eo_list_rev_rec_strCharChain s []

theorem EvaluateProofInternal.str_collect_strCharChain :
    ∀ s : native_String,
      __str_collect (EvaluateProofInternal.strCharChain s) =
        match s with
        | [] => Term.String []
        | _ =>
            Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat) (Term.String s))
              (Term.String [])
  | [] => by
      change
        __eo_requires (Term.String [])
          (__seq_empty (__eo_typeof (Term.String []))) (Term.String []) =
        Term.String []
      change __eo_requires (Term.String []) (Term.String []) (Term.String []) =
        Term.String []
      exact eo_requires_self_eq_of_ne_stuck _ _
        (by intro h; cases h)
  | c :: cs => by
      have hLen :
          __eo_is_eq (__eo_len (Term.String [c])) (Term.Numeral 1) =
            Term.Boolean true := by
        rfl
      cases cs with
      | nil =>
          change
            __eo_ite
                (__eo_is_eq (__eo_len (Term.String [c])) (Term.Numeral 1))
                (__str_collect_merge (Term.String [c])
                  (__str_collect (Term.String [])))
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                  (__str_collect (Term.String []))) =
              Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                (Term.String [])
          rw [hLen, eo_ite_true]
          have hCollectEmpty :
              __str_collect (Term.String []) = Term.String [] := by
            change
              __eo_requires (Term.String [])
                (__seq_empty (__eo_typeof (Term.String []))) (Term.String []) =
              Term.String []
            change
              __eo_requires (Term.String []) (Term.String []) (Term.String []) =
              Term.String []
            exact eo_requires_self_eq_of_ne_stuck _ _
              (by intro h; cases h)
          rw [hCollectEmpty]
          rfl
      | cons d ds =>
          change
            __eo_ite
                (__eo_is_eq (__eo_len (Term.String [c])) (Term.Numeral 1))
                (__str_collect_merge (Term.String [c])
                  (__str_collect (EvaluateProofInternal.strCharChain (d :: ds))))
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                  (__str_collect (EvaluateProofInternal.strCharChain (d :: ds)))) =
              Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat)
                  (Term.String (c :: d :: ds)))
                (Term.String [])
          rw [hLen, eo_ite_true]
          rw [EvaluateProofInternal.str_collect_strCharChain (d :: ds)]
          change
            __eo_ite (__eo_is_str (Term.String (d :: ds)))
                (__eo_mk_apply
                  (__eo_mk_apply (Term.UOp UserOp.str_concat)
                    (__eo_concat (Term.String [c]) (Term.String (d :: ds))))
                  (Term.String []))
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_concat)
                      (Term.String (d :: ds)))
                    (Term.String []))) =
              Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat)
                  (Term.String (c :: d :: ds)))
                (Term.String [])
          rw [show __eo_is_str (Term.String (d :: ds)) = Term.Boolean true by
            rfl]
          rw [eo_ite_true]
          rfl

theorem EvaluateProofInternal.str_collect_elim_strCharChain :
    ∀ s : native_String,
      __str_nary_elim (__str_collect (EvaluateProofInternal.strCharChain s)) =
        Term.String s
  | [] => by
      rw [EvaluateProofInternal.str_collect_strCharChain []]
      change
        __eo_requires (Term.String [])
          (__seq_empty (__eo_typeof (Term.String []))) (Term.String []) =
        Term.String []
      change __eo_requires (Term.String []) (Term.String []) (Term.String []) =
        Term.String []
      exact eo_requires_self_eq_of_ne_stuck _ _
        (by intro h; cases h)
  | c :: cs => by
      rw [EvaluateProofInternal.str_collect_strCharChain (c :: cs)]
      change
        __eo_ite
            (__eo_eq (Term.String [])
              (__seq_empty (__eo_typeof (Term.String (c :: cs)))))
            (Term.String (c :: cs))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_concat)
                (Term.String (c :: cs)))
              (Term.String [])) =
          Term.String (c :: cs)
      have hEq :
          __eo_eq (Term.String [])
              (__seq_empty (__eo_typeof (Term.String (c :: cs)))) =
            Term.Boolean true := by
        rfl
      rw [hEq, eo_ite_true]

theorem EvaluateProofInternal.str_rev_string_char_chain :
    ∀ s : native_String,
      __str_nary_elim
          (__str_collect
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (EvaluateProofInternal.strCharChain s))) =
        Term.String s.reverse
  | s => by
      rw [EvaluateProofInternal.eo_list_rev_strCharChain s]
      exact EvaluateProofInternal.str_collect_elim_strCharChain s.reverse

theorem EvaluateProofInternal.str_leq_eval_rec_strCharChain :
    ∀ s t : native_String,
      native_string_valid s = true ->
      native_string_valid t = true ->
        __str_leq_eval_rec (EvaluateProofInternal.strCharChain s) (EvaluateProofInternal.strCharChain t) =
          Term.Boolean (native_or (decide (s = t)) (native_str_lt s t))
  | [], [], _hs, _ht => by
      rfl
  | [], _d :: _ds, _hs, _ht => by
      rfl
  | _c :: _cs, [], _hs, _ht => by
      rfl
  | c :: cs, d :: ds, hs, ht => by
      rcases EvaluateProofInternal.native_string_valid_cons_parts_local hs with ⟨hc, hcs⟩
      rcases EvaluateProofInternal.native_string_valid_cons_parts_local ht with ⟨hd, hds⟩
      have hTail := EvaluateProofInternal.str_leq_eval_rec_strCharChain cs ds hcs hds
      rw [show EvaluateProofInternal.strCharChain (c :: cs) =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [c]))
          (EvaluateProofInternal.strCharChain cs) by
        rfl]
      rw [show EvaluateProofInternal.strCharChain (d :: ds) =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [d]))
          (EvaluateProofInternal.strCharChain ds) by
        rfl]
      unfold __str_leq_eval_rec
      rw [EvaluateProofInternal.eo_to_z_singleton hc, EvaluateProofInternal.eo_to_z_singleton hd]
      by_cases hcd : c = d
      · subst d
        simp [__eo_eq, native_teq, native_ite, native_or, native_str_lt,
          hTail]
      · have hdcNe : ¬ d = c := by
          intro h
          exact hcd h.symm
        have hNeList : c :: cs ≠ d :: ds := by
          intro h
          exact hcd (List.cons.inj h).1
        by_cases hlt : c < d
        · have hltInt : (c : Int) < (d : Int) := Int.ofNat_lt.mpr hlt
          simp [__eo_eq, __eo_gt, native_teq, native_ite, native_or,
            native_str_lt, List.cons_lt_cons_iff, hcd, hdcNe, hNeList,
            hlt]
          change decide ((c : Int) < (d : Int)) = true
          exact decide_eq_true hltInt
        · have hdc : d < c := by
            rcases Nat.lt_trichotomy c d with h | h | h
            · exact False.elim (hlt h)
            · exact False.elim (hcd h)
            · exact h
          have hnotInt : ¬ (c : Int) < (d : Int) := by
            intro hInt
            exact hlt (Int.ofNat_lt.mp hInt)
          simp [__eo_eq, __eo_gt, native_teq, native_ite, native_or,
            native_str_lt, List.cons_lt_cons_iff, hcd, hdcNe, hNeList,
            hlt]
          change decide ((c : Int) < (d : Int)) = false
          exact decide_eq_false hnotInt

theorem EvaluateProofInternal.eo_is_str_false_of_not_string
    (t : Term)
    (hNotString : ∀ s : native_String, t ≠ Term.String s) :
    __eo_is_str t = Term.Boolean false := by
  cases t <;>
    simp [__eo_is_str, __eo_is_str_internal, native_teq, native_and,
      native_not] at hNotString ⊢

theorem EvaluateProofInternal.str_rev_result_string
    {s : native_String} :
    __eo_ite (__eo_is_str (Term.String s))
        (__str_nary_elim
          (__str_collect
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__str_nary_intro (Term.String s))))))
        (__eo_mk_apply (Term.UOp UserOp.str_rev) (Term.String s)) =
      Term.String s.reverse := by
  have hIsStr :
      __eo_is_str (Term.String s) = Term.Boolean true := by
    rfl
  rw [hIsStr, eo_ite_true]
  rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain]
  exact EvaluateProofInternal.str_rev_string_char_chain s

theorem EvaluateProofInternal.str_rev_result_non_string
    {t : Term}
    (hNotString : ∀ s : native_String, t ≠ Term.String s)
    (hTNe : t ≠ Term.Stuck) :
    __eo_ite (__eo_is_str t)
        (__str_nary_elim
          (__str_collect
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__str_nary_intro t)))))
        (__eo_mk_apply (Term.UOp UserOp.str_rev) t) =
      Term.Apply (Term.UOp UserOp.str_rev) t := by
  rw [EvaluateProofInternal.eo_is_str_false_of_not_string t hNotString, eo_ite_false]
  exact EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck _ _
    (by intro h; cases h) hTNe

theorem EvaluateProofInternal.str_leq_result_strings
    {s t : native_String}
    (hs : native_string_valid s = true)
    (ht : native_string_valid t = true) :
    __eo_ite
        (__eo_and (__eo_is_str (Term.String s))
          (__eo_is_str (Term.String t)))
        (__str_leq_eval_rec
          (__str_flatten (__str_nary_intro (Term.String s)))
          (__str_flatten (__str_nary_intro (Term.String t))))
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_leq) (Term.String s))
          (Term.String t)) =
      Term.Boolean (native_or (decide (s = t)) (native_str_lt s t)) := by
  have hGuard :
      __eo_and (__eo_is_str (Term.String s))
          (__eo_is_str (Term.String t)) =
        Term.Boolean true := by
    simp [__eo_is_str, __eo_is_str_internal, __eo_and, native_teq,
      native_and, native_not]
  rw [hGuard, eo_ite_true]
  rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain s]
  rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain t]
  exact EvaluateProofInternal.str_leq_eval_rec_strCharChain s t hs ht

theorem EvaluateProofInternal.str_leq_result_non_strings
    {s t : Term}
    (hNotBoth :
      ¬ ∃ sx sy : native_String, s = Term.String sx ∧ t = Term.String sy)
    (hsNe : s ≠ Term.Stuck)
    (htNe : t ≠ Term.Stuck) :
    __eo_ite (__eo_and (__eo_is_str s) (__eo_is_str t))
        (__str_leq_eval_rec (__str_flatten (__str_nary_intro s))
          (__str_flatten (__str_nary_intro t)))
        (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_leq) s) t) =
      Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) s) t := by
  have hGuard :
      __eo_and (__eo_is_str s) (__eo_is_str t) =
        Term.Boolean false := by
    cases s <;> cases t <;>
      simp [__eo_is_str, __eo_is_str_internal, __eo_and, native_teq,
        native_and, native_not] at hNotBoth hsNe htNe ⊢
  rw [hGuard, eo_ite_false]
  rw [EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck
    (Term.UOp UserOp.str_leq) s (by intro h; cases h) hsNe]
  exact EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck
    (Term.Apply (Term.UOp UserOp.str_leq) s) t
    (by intro h; cases h) htNe

theorem EvaluateProofInternal.eo_str_rev_result_arg_typeof_seq
    (t U : Term) :
    __eo_typeof
        (__eo_ite (__eo_is_str t)
          (__str_nary_elim
            (__str_collect
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_flatten (__str_nary_intro t)))))
          (__eo_mk_apply (Term.UOp UserOp.str_rev) t)) =
      Term.Apply (Term.UOp UserOp.Seq) U ->
    __eo_typeof t = Term.Apply (Term.UOp UserOp.Seq) U := by
  intro h
  cases t
  case String s =>
    rw [EvaluateProofInternal.str_rev_result_string] at h
    exact h
  all_goals
    apply EvaluateProofInternal.eo_typeof_apply_str_rev_eq_seq_arg
    have hsimpa := h
    try simp [__eo_is_str, __eo_is_str_internal, __eo_ite, __eo_mk_apply, native_ite, native_teq, native_and, native_not] at hsimpa ⊢
    exact hsimpa

theorem EvaluateProofInternal.str_to_lower_result_string
    {s : native_String}
    (hValid : native_string_valid s = true) :
    __eo_ite (__eo_is_str (Term.String s))
        (__str_case_conv_rec (__str_flatten (__str_nary_intro (Term.String s)))
          (Term.Boolean true))
        (__eo_mk_apply (Term.UOp UserOp.str_to_lower) (Term.String s)) =
      Term.String (native_str_to_lower s) := by
  have hIsStr :
      __eo_is_str (Term.String s) = Term.Boolean true := by
    simp [__eo_is_str, __eo_is_str_internal, native_teq, native_and,
      native_not]
  rw [hIsStr, eo_ite_true]
  rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain]
  exact EvaluateProofInternal.str_case_conv_rec_lower_char_chain s hValid

theorem EvaluateProofInternal.str_to_upper_result_string
    {s : native_String}
    (hValid : native_string_valid s = true) :
    __eo_ite (__eo_is_str (Term.String s))
        (__str_case_conv_rec (__str_flatten (__str_nary_intro (Term.String s)))
          (Term.Boolean false))
        (__eo_mk_apply (Term.UOp UserOp.str_to_upper) (Term.String s)) =
      Term.String (native_str_to_upper s) := by
  have hIsStr :
      __eo_is_str (Term.String s) = Term.Boolean true := by
    simp [__eo_is_str, __eo_is_str_internal, native_teq, native_and,
      native_not]
  rw [hIsStr, eo_ite_true]
  rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain]
  exact EvaluateProofInternal.str_case_conv_rec_upper_char_chain s hValid

theorem EvaluateProofInternal.str_to_lower_result_non_string
    {t : Term}
    (hNotString : ∀ s : native_String, t ≠ Term.String s)
    (hTNe : t ≠ Term.Stuck) :
    __eo_ite (__eo_is_str t)
        (__str_case_conv_rec (__str_flatten (__str_nary_intro t))
          (Term.Boolean true))
        (__eo_mk_apply (Term.UOp UserOp.str_to_lower) t) =
      Term.Apply (Term.UOp UserOp.str_to_lower) t := by
  rw [EvaluateProofInternal.eo_is_str_false_of_not_string t hNotString, eo_ite_false]
  exact EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck _ _
    (by intro h; cases h) hTNe

theorem EvaluateProofInternal.str_to_upper_result_non_string
    {t : Term}
    (hNotString : ∀ s : native_String, t ≠ Term.String s)
    (hTNe : t ≠ Term.Stuck) :
    __eo_ite (__eo_is_str t)
        (__str_case_conv_rec (__str_flatten (__str_nary_intro t))
          (Term.Boolean false))
        (__eo_mk_apply (Term.UOp UserOp.str_to_upper) t) =
      Term.Apply (Term.UOp UserOp.str_to_upper) t := by
  rw [EvaluateProofInternal.eo_is_str_false_of_not_string t hNotString, eo_ite_false]
  exact EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck _ _
    (by intro h; cases h) hTNe

theorem EvaluateProofInternal.smt_value_rel_model_eval_not_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_not a) (__smtx_model_eval_not b) := by
  intro hRel
  unfold RuleProofs.smt_value_rel at hRel ⊢
  cases a <;> cases b <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_not, native_veq] at hRel ⊢
  case Boolean b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp at hRel ⊢

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_to_lower_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_to_lower a) (__smtx_model_eval_str_to_lower b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_to_lower, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_to_upper_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_to_upper a) (__smtx_model_eval_str_to_upper b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_to_upper, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_rev_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_rev a) (__smtx_model_eval_str_rev b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_rev, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_leq_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_leq a b)
      (__smtx_model_eval_str_leq c d) := by
  intro hRelA hRelB
  by_cases hRegA :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ c = SmtValue.RegLan r2
  · rcases hRegA with ⟨r1, r2, rfl, rfl⟩
    cases b <;> cases d <;>
      simp [__smtx_model_eval_str_leq, __smtx_model_eval_str_lt,
        __smtx_model_eval_or, RuleProofs.smt_value_rel_refl]
  · have hAEq := (RuleProofs.smt_value_rel_iff_eq a c hRegA).mp hRelA
    subst c
    by_cases hRegB :
        ∃ r1 r2, b = SmtValue.RegLan r1 ∧ d = SmtValue.RegLan r2
    · rcases hRegB with ⟨r1, r2, rfl, rfl⟩
      cases a <;>
        simp [__smtx_model_eval_str_leq, __smtx_model_eval_str_lt,
          __smtx_model_eval_or, RuleProofs.smt_value_rel_refl]
    · have hBEq := (RuleProofs.smt_value_rel_iff_eq b d hRegB).mp hRelB
      subst d
      exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_replace_of_rel
    (a b c d e f : SmtValue) :
    RuleProofs.smt_value_rel a d ->
    RuleProofs.smt_value_rel b e ->
    RuleProofs.smt_value_rel c f ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_replace a b c)
      (__smtx_model_eval_str_replace d e f) := by
  intro hRelA hRelB hRelC
  by_cases hRegA :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ d = SmtValue.RegLan r2
  · rcases hRegA with ⟨r1, r2, rfl, rfl⟩
    cases b <;> cases e <;> cases c <;> cases f <;>
      simp [__smtx_model_eval_str_replace, RuleProofs.smt_value_rel_refl]
  · have hAEq := (RuleProofs.smt_value_rel_iff_eq a d hRegA).mp hRelA
    subst d
    by_cases hRegB :
        ∃ r1 r2, b = SmtValue.RegLan r1 ∧ e = SmtValue.RegLan r2
    · rcases hRegB with ⟨r1, r2, rfl, rfl⟩
      cases a <;> cases c <;> cases f <;>
        simp [__smtx_model_eval_str_replace, RuleProofs.smt_value_rel_refl]
    · have hBEq := (RuleProofs.smt_value_rel_iff_eq b e hRegB).mp hRelB
      subst e
      by_cases hRegC :
          ∃ r1 r2, c = SmtValue.RegLan r1 ∧ f = SmtValue.RegLan r2
      · rcases hRegC with ⟨r1, r2, rfl, rfl⟩
        cases a <;> cases b <;>
          simp [__smtx_model_eval_str_replace, RuleProofs.smt_value_rel_refl]
      · have hCEq := (RuleProofs.smt_value_rel_iff_eq c f hRegC).mp hRelC
        subst f
        exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_indexof_of_rel
    (a b c d e f : SmtValue) :
    RuleProofs.smt_value_rel a d ->
    RuleProofs.smt_value_rel b e ->
    RuleProofs.smt_value_rel c f ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_indexof a b c)
      (__smtx_model_eval_str_indexof d e f) := by
  intro hRelA hRelB hRelC
  by_cases hRegA :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ d = SmtValue.RegLan r2
  · rcases hRegA with ⟨r1, r2, rfl, rfl⟩
    cases b <;> cases e <;> cases c <;> cases f <;>
      simp [__smtx_model_eval_str_indexof, RuleProofs.smt_value_rel_refl]
  · have hAEq := (RuleProofs.smt_value_rel_iff_eq a d hRegA).mp hRelA
    subst d
    by_cases hRegB :
        ∃ r1 r2, b = SmtValue.RegLan r1 ∧ e = SmtValue.RegLan r2
    · rcases hRegB with ⟨r1, r2, rfl, rfl⟩
      cases a <;> cases c <;> cases f <;>
        simp [__smtx_model_eval_str_indexof, RuleProofs.smt_value_rel_refl]
    · have hBEq := (RuleProofs.smt_value_rel_iff_eq b e hRegB).mp hRelB
      subst e
      by_cases hRegC :
          ∃ r1 r2, c = SmtValue.RegLan r1 ∧ f = SmtValue.RegLan r2
      · rcases hRegC with ⟨r1, r2, rfl, rfl⟩
        cases a <;> cases b <;>
          simp [__smtx_model_eval_str_indexof, RuleProofs.smt_value_rel_refl]
      · have hCEq := (RuleProofs.smt_value_rel_iff_eq c f hRegC).mp hRelC
        subst f
        exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_update_of_rel
    (a b c d e f : SmtValue) :
    RuleProofs.smt_value_rel a d ->
    RuleProofs.smt_value_rel b e ->
    RuleProofs.smt_value_rel c f ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_update a b c)
      (__smtx_model_eval_str_update d e f) := by
  intro hRelA hRelB hRelC
  by_cases hRegA :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ d = SmtValue.RegLan r2
  · rcases hRegA with ⟨r1, r2, rfl, rfl⟩
    cases b <;> cases e <;> cases c <;> cases f <;>
      simp [__smtx_model_eval_str_update, RuleProofs.smt_value_rel_refl]
  · have hAEq := (RuleProofs.smt_value_rel_iff_eq a d hRegA).mp hRelA
    subst d
    by_cases hRegB :
        ∃ r1 r2, b = SmtValue.RegLan r1 ∧ e = SmtValue.RegLan r2
    · rcases hRegB with ⟨r1, r2, rfl, rfl⟩
      cases a <;> cases c <;> cases f <;>
        simp [__smtx_model_eval_str_update, RuleProofs.smt_value_rel_refl]
    · have hBEq := (RuleProofs.smt_value_rel_iff_eq b e hRegB).mp hRelB
      subst e
      by_cases hRegC :
          ∃ r1 r2, c = SmtValue.RegLan r1 ∧ f = SmtValue.RegLan r2
      · rcases hRegC with ⟨r1, r2, rfl, rfl⟩
        cases a <;> cases b <;>
          simp [__smtx_model_eval_str_update, RuleProofs.smt_value_rel_refl]
      · have hCEq := (RuleProofs.smt_value_rel_iff_eq c f hRegC).mp hRelC
        subst f
        exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_replace_all_of_rel
    (a b c d e f : SmtValue) :
    RuleProofs.smt_value_rel a d ->
    RuleProofs.smt_value_rel b e ->
    RuleProofs.smt_value_rel c f ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_replace_all a b c)
      (__smtx_model_eval_str_replace_all d e f) := by
  intro hRelA hRelB hRelC
  by_cases hRegA :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ d = SmtValue.RegLan r2
  · rcases hRegA with ⟨r1, r2, rfl, rfl⟩
    cases b <;> cases e <;> cases c <;> cases f <;>
      simp [__smtx_model_eval_str_replace_all,
        RuleProofs.smt_value_rel_refl]
  · have hAEq := (RuleProofs.smt_value_rel_iff_eq a d hRegA).mp hRelA
    subst d
    by_cases hRegB :
        ∃ r1 r2, b = SmtValue.RegLan r1 ∧ e = SmtValue.RegLan r2
    · rcases hRegB with ⟨r1, r2, rfl, rfl⟩
      cases a <;> cases c <;> cases f <;>
        simp [__smtx_model_eval_str_replace_all,
          RuleProofs.smt_value_rel_refl]
    · have hBEq := (RuleProofs.smt_value_rel_iff_eq b e hRegB).mp hRelB
      subst e
      by_cases hRegC :
          ∃ r1 r2, c = SmtValue.RegLan r1 ∧ f = SmtValue.RegLan r2
      · rcases hRegC with ⟨r1, r2, rfl, rfl⟩
        cases a <;> cases b <;>
          simp [__smtx_model_eval_str_replace_all,
            RuleProofs.smt_value_rel_refl]
      · have hCEq := (RuleProofs.smt_value_rel_iff_eq c f hRegC).mp hRelC
        subst f
        exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_len_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_len a) (__smtx_model_eval_str_len b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_len, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_to_code_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_to_code a) (__smtx_model_eval_str_to_code b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_to_code, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_to_int_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_to_int a) (__smtx_model_eval_str_to_int b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_to_int, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_from_code_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_from_code a) (__smtx_model_eval_str_from_code b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_from_code, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_from_int_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_from_int a) (__smtx_model_eval_str_from_int b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_from_int, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_sbv_to_int_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_sbv_to_int a) (__smtx_model_eval_sbv_to_int b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_sbv_to_int, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_bvashr_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_bvashr a b) (__smtx_model_eval_bvashr c d) := by
  intro hRelA hRelB
  by_cases hRegA :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ c = SmtValue.RegLan r2
  · rcases hRegA with ⟨r1, r2, rfl, rfl⟩
    cases b <;> cases d <;>
      simp [__smtx_model_eval_bvashr, __smtx_model_eval_bvlshr,
        __smtx_model_eval_bvnot, __smtx_model_eval_extract,
        __smtx_model_eval__, __smtx_model_eval_ite,
        RuleProofs.smt_value_rel_refl]
  · have hAEq := (RuleProofs.smt_value_rel_iff_eq a c hRegA).mp hRelA
    subst c
    by_cases hRegB :
        ∃ r1 r2, b = SmtValue.RegLan r1 ∧ d = SmtValue.RegLan r2
    · rcases hRegB with ⟨r1, r2, rfl, rfl⟩
      cases a <;>
        simp [__smtx_model_eval_bvashr, __smtx_model_eval_bvlshr,
          __smtx_model_eval_bvnot, __smtx_model_eval_extract,
          __smtx_model_eval__, __smtx_model_eval_ite,
          RuleProofs.smt_value_rel_refl]
    · have hBEq := (RuleProofs.smt_value_rel_iff_eq b d hRegB).mp hRelB
      subst d
      exact RuleProofs.smt_value_rel_refl _

theorem EvaluateProofInternal.smt_value_rel_model_eval_and_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_and a b) (__smtx_model_eval_and c d) := by
  intro hAC hBD
  unfold RuleProofs.smt_value_rel at hAC hBD ⊢
  cases a <;> cases c <;> cases b <;> cases d <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_and, native_veq] at hAC hBD ⊢
  case Boolean b₁ b₂ b₃ b₄ =>
    cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;>
      simp [native_and] at hAC hBD ⊢

theorem EvaluateProofInternal.smt_value_rel_model_eval_or_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_or a b) (__smtx_model_eval_or c d) := by
  intro hAC hBD
  unfold RuleProofs.smt_value_rel at hAC hBD ⊢
  cases a <;> cases c <;> cases b <;> cases d <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_or, native_veq] at hAC hBD ⊢
  case Boolean b₁ b₂ b₃ b₄ =>
    cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;>
      simp [native_or] at hAC hBD ⊢

theorem EvaluateProofInternal.smt_value_rel_model_eval_imp_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_imp a b) (__smtx_model_eval_imp c d) := by
  intro hAC hBD
  unfold __smtx_model_eval_imp
  exact EvaluateProofInternal.smt_value_rel_model_eval_or_of_rel
    (__smtx_model_eval_not a) b (__smtx_model_eval_not c) d
    (EvaluateProofInternal.smt_value_rel_model_eval_not_of_rel a c hAC) hBD

theorem EvaluateProofInternal.smt_value_rel_model_eval_int_pow2_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_int_pow2 a) (__smtx_model_eval_int_pow2 b) := by
  intro hRel
  unfold RuleProofs.smt_value_rel at hRel ⊢
  cases a <;> cases b <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_int_pow2,
      native_veq] at hRel ⊢
  case Numeral n m =>
    subst m
    rfl

theorem EvaluateProofInternal.smt_value_rel_model_eval_int_log2_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_int_log2 a) (__smtx_model_eval_int_log2 b) := by
  intro hRel
  unfold RuleProofs.smt_value_rel at hRel ⊢
  cases a <;> cases b <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_int_log2,
      native_veq] at hRel ⊢
  case Numeral n m =>
    subst m
    rfl

theorem EvaluateProofInternal.smt_typeof_int_ispow2_formula_eq_bool
    (t : SmtTerm) :
    __smtx_typeof t = SmtType.Int ->
    __smtx_typeof
        (SmtTerm.and
          (SmtTerm.geq t (SmtTerm.Numeral 0))
          (SmtTerm.eq t
            (SmtTerm.int_pow2 (SmtTerm.int_log2 t)))) =
      SmtType.Bool := by
  intro hTy
  rw [typeof_and_eq, typeof_geq_eq, typeof_eq_eq,
    typeof_int_pow2_eq, typeof_int_log2_eq, hTy, __smtx_typeof.eq_2]
  simp [__smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq,
    __smtx_typeof_guard, native_ite, native_Teq]

theorem EvaluateProofInternal.smt_value_rel_boolean_eq
    (v : SmtValue) (b : Bool) :
    RuleProofs.smt_value_rel v (SmtValue.Boolean b) ->
    v = SmtValue.Boolean b := by
  intro hRel
  unfold RuleProofs.smt_value_rel at hRel
  cases v <;> simp [__smtx_model_eval_eq, native_veq] at hRel
  case Boolean b' =>
    cases b <;> cases b' <;> simp at hRel ⊢

theorem EvaluateProofInternal.smt_value_rel_numeral_eq
    (v : SmtValue) (n : native_Int) :
    RuleProofs.smt_value_rel v (SmtValue.Numeral n) ->
    v = SmtValue.Numeral n := by
  intro hRel
  exact (RuleProofs.smt_value_rel_iff_eq
    v (SmtValue.Numeral n) (by
      rintro ⟨r1, r2, _hv, hNum⟩
      cases hNum)).mp hRel

theorem EvaluateProofInternal.smt_value_rel_rational_eq
    (v : SmtValue) (q : native_Rat) :
    RuleProofs.smt_value_rel v (SmtValue.Rational q) ->
    v = SmtValue.Rational q := by
  intro hRel
  exact (RuleProofs.smt_value_rel_iff_eq
    v (SmtValue.Rational q) (by
      rintro ⟨r1, r2, _hv, hRat⟩
      cases hRat)).mp hRel

theorem EvaluateProofInternal.smt_value_rel_binary_eq
    (v : SmtValue) (w n : native_Int) :
    RuleProofs.smt_value_rel v (SmtValue.Binary w n) ->
    v = SmtValue.Binary w n := by
  intro hRel
  exact (RuleProofs.smt_value_rel_iff_eq
    v (SmtValue.Binary w n) (by
      rintro ⟨r1, r2, _hv, hBin⟩
      cases hBin)).mp hRel

theorem EvaluateProofInternal.smtx_typeof_binary_mod_nat_to_int
    (w : native_Nat) (n : native_Int) :
    __smtx_typeof
        (SmtTerm.Binary (native_nat_to_int w)
          (native_mod_total n (native_int_pow2 (native_nat_to_int w)))) =
      SmtType.BitVec w := by
  have hNN :
      __smtx_typeof
          (SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total n (native_int_pow2 (native_nat_to_int w)))) ≠
        SmtType.None := by
    unfold __smtx_typeof
    have hWidth :
        native_zleq 0 (native_nat_to_int w) = true := by
      simp [SmtEval.native_zleq, Smtm.native_nat_to_int]
    have hMod :
        native_zeq
            (native_mod_total n (native_int_pow2 (native_nat_to_int w)))
            (native_mod_total
              (native_mod_total n (native_int_pow2 (native_nat_to_int w)))
              (native_int_pow2 (native_nat_to_int w))) =
          true :=
      native_mod_total_canonical (native_nat_to_int w) n
    simp [SmtEval.native_and, hWidth, hMod, native_ite]
  simpa [SmtEval.native_int_to_nat, Smtm.native_nat_to_int]
    using
      TranslationProofs.smtx_typeof_binary_of_non_none
        (native_nat_to_int w)
        (native_mod_total n (native_int_pow2 (native_nat_to_int w))) hNN

theorem EvaluateProofInternal.smtx_typeof_binary_mod_of_nonneg
    (w n : native_Int)
    (hWidth : native_zleq 0 w = true) :
    __smtx_typeof
        (SmtTerm.Binary w
          (native_mod_total n (native_int_pow2 w))) =
      SmtType.BitVec (native_int_to_nat w) := by
  have hNN :
      __smtx_typeof
          (SmtTerm.Binary w
            (native_mod_total n (native_int_pow2 w))) ≠
        SmtType.None := by
    unfold __smtx_typeof
    have hMod :
        native_zeq
            (native_mod_total n (native_int_pow2 w))
            (native_mod_total
              (native_mod_total n (native_int_pow2 w))
              (native_int_pow2 w)) =
          true :=
      native_mod_total_canonical w n
    simp [SmtEval.native_and, hWidth, hMod, native_ite]
  exact
    TranslationProofs.smtx_typeof_binary_of_non_none
      w (native_mod_total n (native_int_pow2 w)) hNN

theorem EvaluateProofInternal.smtx_typeof_binary_of_nonneg_and_canonical
    (w n : native_Int)
    (hWidth : native_zleq 0 w = true)
    (hCanon :
      native_zeq n (native_mod_total n (native_int_pow2 w)) = true) :
    __smtx_typeof (SmtTerm.Binary w n) =
      SmtType.BitVec (native_int_to_nat w) := by
  have hNN :
      __smtx_typeof (SmtTerm.Binary w n) ≠ SmtType.None := by
    unfold __smtx_typeof
    simp [SmtEval.native_and, hWidth, hCanon, native_ite]
  exact TranslationProofs.smtx_typeof_binary_of_non_none w n hNN

theorem EvaluateProofInternal.smtx_typeof_binary_eq_bitvec_parts
    {w n : native_Int} {u : native_Nat}
    (hTy : __smtx_typeof (SmtTerm.Binary w n) = SmtType.BitVec u) :
    native_zleq 0 w = true ∧
      native_zeq n (native_mod_total n (native_int_pow2 w)) = true ∧
        native_int_to_nat w = u := by
  unfold __smtx_typeof at hTy
  cases hWidth : native_zleq 0 w <;>
    cases hCanon :
      native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
      simp [SmtEval.native_and, hWidth, hCanon, native_ite] at hTy
  all_goals
    try cases hTy
    simp

theorem EvaluateProofInternal.native_nat_to_int_of_int_to_nat_eq
    {w : native_Int} {u : native_Nat}
    (hWidth : native_zleq 0 w = true)
    (hNat : native_int_to_nat w = u) :
    w = native_nat_to_int u := by
  have hw0 : 0 <= w := by
    simpa [native_zleq, SmtEval.native_zleq] using hWidth
  have hToNat : Int.toNat w = u := by
    simpa [native_int_to_nat, SmtEval.native_int_to_nat] using hNat
  rw [← hToNat]
  simp [native_nat_to_int, Smtm.native_nat_to_int,
    Int.toNat_of_nonneg hw0]

theorem EvaluateProofInternal.model_eval_bitvec_term_binary
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (w : native_Nat)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w) :
    ∃ n : native_Int,
      __smtx_model_eval M (__eo_to_smt t) =
        SmtValue.Binary (native_nat_to_int w) n ∧
      0 <= n ∧ n < native_int_pow2 (native_nat_to_int w) := by
  have hNN : term_has_non_none_type (__eo_to_smt t) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.BitVec w := by
    simpa [hTy] using
      Smtm.smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt t) hNN
  rcases Smtm.bitvec_value_canonical hEvalTy with ⟨n, hv⟩
  have hWidth : native_zleq 0 (native_nat_to_int w) = true :=
    Smtm.bitvec_width_nonneg (by simpa [hv] using hEvalTy)
  have hMod :
      native_zeq n
          (native_mod_total n (native_int_pow2 (native_nat_to_int w))) =
        true :=
    Smtm.bitvec_payload_canonical (by simpa [hv] using hEvalTy)
  exact ⟨n, hv, Smtm.bitvec_payload_range_of_canonical hWidth hMod⟩

theorem EvaluateProofInternal.has_bool_type_not_of_has_translation
    (b : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp UserOp.not) b) ->
    RuleProofs.eo_has_bool_type (Term.Apply (Term.UOp UserOp.not) b) := by
  intro hTrans
  have hTrans' :
      __smtx_typeof (SmtTerm.not (__eo_to_smt b)) ≠ SmtType.None := by
    have hsimpa := hTrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.not (__eo_to_smt b)) = SmtType.Bool
  rw [typeof_not_eq]
  rw [typeof_not_eq] at hTrans'
  cases hTy : __smtx_typeof (__eo_to_smt b) <;>
    simp [hTy, native_ite, native_Teq] at hTrans' ⊢

theorem EvaluateProofInternal.has_bool_type_and_of_has_translation
    (a b : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) := by
  intro hTrans
  have hTrans' :
      __smtx_typeof (SmtTerm.and (__eo_to_smt a) (__eo_to_smt b)) ≠
        SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hTrans
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.and (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool
  rw [typeof_and_eq]
  rw [typeof_and_eq] at hTrans'
  cases hA : __smtx_typeof (__eo_to_smt a) <;>
    cases hB : __smtx_typeof (__eo_to_smt b) <;>
      simp [hA, hB, native_ite, native_Teq] at hTrans' ⊢

theorem EvaluateProofInternal.has_bool_type_or_of_has_translation
    (a b : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) := by
  intro hTrans
  have hTrans' :
      __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) ≠
        SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hTrans
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool
  rw [typeof_or_eq]
  rw [typeof_or_eq] at hTrans'
  cases hA : __smtx_typeof (__eo_to_smt a) <;>
    cases hB : __smtx_typeof (__eo_to_smt b) <;>
      simp [hA, hB, native_ite, native_Teq] at hTrans' ⊢

theorem EvaluateProofInternal.has_bool_type_xor_of_has_translation
    (a b : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) := by
  intro hTrans
  have hTrans' :
      __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) ≠
        SmtType.None := by
    have hsimpa := hTrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool
  rw [typeof_xor_eq]
  rw [typeof_xor_eq] at hTrans'
  cases hA : __smtx_typeof (__eo_to_smt a) <;>
    cases hB : __smtx_typeof (__eo_to_smt b) <;>
      simp [hA, hB, native_ite, native_Teq] at hTrans' ⊢

theorem EvaluateProofInternal.has_bool_type_imp_of_has_translation
    (a b : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) := by
  intro hTrans
  have hTrans' :
      __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) ≠
        SmtType.None := by
    have hsimpa := hTrans
    try simp [RuleProofs.eo_has_smt_translation] at hsimpa ⊢
    exact hsimpa
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool
  rw [typeof_imp_eq]
  rw [typeof_imp_eq] at hTrans'
  cases hA : __smtx_typeof (__eo_to_smt a) <;>
    cases hB : __smtx_typeof (__eo_to_smt b) <;>
      simp [hA, hB, native_ite, native_Teq] at hTrans' ⊢

theorem EvaluateProofInternal.has_bool_type_imp_left
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) ->
    RuleProofs.eo_has_bool_type a := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
    (typeof_imp_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).1

theorem EvaluateProofInternal.has_bool_type_imp_right
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) ->
    RuleProofs.eo_has_bool_type b := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
    (typeof_imp_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).2

theorem EvaluateProofInternal.has_bool_type_xor_left
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) ->
    RuleProofs.eo_has_bool_type a := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.xor)
    (typeof_xor_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).1

theorem EvaluateProofInternal.has_bool_type_xor_right
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) ->
    RuleProofs.eo_has_bool_type b := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.xor)
    (typeof_xor_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).2

theorem EvaluateProofInternal.has_bool_type_or_left
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) ->
    RuleProofs.eo_has_bool_type a := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.or)
    (typeof_or_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).1

theorem EvaluateProofInternal.has_bool_type_or_right
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) ->
    RuleProofs.eo_has_bool_type b := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.or)
    (typeof_or_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).2

theorem EvaluateProofInternal.evaluate_eo_typeof_eq_bool_operands_eq
    (A B : Term)
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

theorem EvaluateProofInternal.evaluate_apply_eq_typeof_bool_operands_eq
    (x y : Term)
    (h : __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) = Term.Bool) :
    __eo_typeof x = __eo_typeof y := by
  change __eo_typeof_eq (__eo_typeof x) (__eo_typeof y) = Term.Bool at h
  exact EvaluateProofInternal.evaluate_eo_typeof_eq_bool_operands_eq
    (__eo_typeof x) (__eo_typeof y) h

theorem EvaluateProofInternal.eo_not_arg_boolean_of_typeof_bool
    (t : Term) :
    __eo_typeof (__eo_not t) = Term.Bool ->
    ∃ b : Bool, t = Term.Boolean b := by
  cases t <;> intro h
  case Boolean b =>
    exact ⟨b, rfl⟩
  case Binary w n =>
    change Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) =
      Term.Bool at h
    cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.Bool at h
    change Term.Stuck = Term.Bool at h
    cases h

theorem EvaluateProofInternal.eo_or_typeof_bool_of_args_bool
    (x y : Term)
    (hX : __eo_typeof x = Term.Bool)
    (hY : __eo_typeof y = Term.Bool)
    (hNe : __eo_or x y ≠ Term.Stuck) :
    __eo_typeof (__eo_or x y) = Term.Bool := by
  cases x <;> cases y <;> simp [__eo_or] at hX hY hNe ⊢
  all_goals
    first
    | contradiction
    | cases hX
    | cases hY

theorem EvaluateProofInternal.eo_and_typeof_bool_of_args_bool
    (x y : Term)
    (hX : __eo_typeof x = Term.Bool)
    (hY : __eo_typeof y = Term.Bool)
    (hNe : __eo_and x y ≠ Term.Stuck) :
    __eo_typeof (__eo_and x y) = Term.Bool := by
  cases x <;> cases y <;> simp [__eo_and] at hX hY hNe ⊢
  all_goals
    first
    | contradiction
    | cases hX
    | cases hY

theorem EvaluateProofInternal.eo_xor_typeof_bool_of_args_bool
    (x y : Term)
    (hX : __eo_typeof x = Term.Bool)
    (hY : __eo_typeof y = Term.Bool)
    (hNe : __eo_xor x y ≠ Term.Stuck) :
    __eo_typeof (__eo_xor x y) = Term.Bool := by
  cases x <;> cases y <;> simp [__eo_xor] at hX hY hNe ⊢
  all_goals
    first
    | contradiction
    | cases hX
    | cases hY

theorem EvaluateProofInternal.eo_not_typeof_bool_of_arg_bool
    (x : Term)
    (hX : __eo_typeof x = Term.Bool)
    (hNe : __eo_not x ≠ Term.Stuck) :
    __eo_typeof (__eo_not x) = Term.Bool := by
  cases x <;> simp [__eo_not] at hX hNe ⊢
  all_goals
    first
    | contradiction
    | cases hX

theorem EvaluateProofInternal.eo_not_arg_binary_of_typeof_bitvec
    (t : Term) (w : native_Int) :
    __eo_typeof (__eo_not t) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ n : native_Int, t = Term.Binary w n := by
  cases t <;> intro h
  case Binary wt n =>
    change
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wt) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
    exact ⟨n, rfl⟩
  case Boolean b =>
    change Term.Bool =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

theorem EvaluateProofInternal.eo_and_args_boolean_of_typeof_bool
    (x y : Term) :
    __eo_typeof (__eo_and x y) = Term.Bool ->
    ∃ bx : Bool, ∃ by' : Bool,
      x = Term.Boolean bx ∧ y = Term.Boolean by' := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_and] at h
    case Boolean by' =>
      exact ⟨bx, by', rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_and] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_and wx nx ny)
                  (native_int_pow2 wx)))) =
          Term.Bool at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.Bool at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · simp [hWidth] at h
          change Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wy) =
            Term.Bool at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.Bool at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.Bool at h
    change Term.Stuck = Term.Bool at h
    cases h

theorem EvaluateProofInternal.eo_and_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_and x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_and] at h
    case Boolean by' =>
      change Term.Bool =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_and] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_and wx nx ny)
                  (native_int_pow2 wx)))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          cases h
          exact ⟨nx, ny, rfl, rfl⟩
        · simp [hWidth] at h
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

theorem EvaluateProofInternal.eo_or_args_boolean_of_typeof_bool
    (x y : Term) :
    __eo_typeof (__eo_or x y) = Term.Bool ->
    ∃ bx : Bool, ∃ by' : Bool,
      x = Term.Boolean bx ∧ y = Term.Boolean by' := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_or] at h
    case Boolean by' =>
      exact ⟨bx, by', rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_or] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_or wx nx ny)
                  (native_int_pow2 wx)))) =
          Term.Bool at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.Bool at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · simp [hWidth] at h
          change Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wy) =
            Term.Bool at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.Bool at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.Bool at h
    change Term.Stuck = Term.Bool at h
    cases h

theorem EvaluateProofInternal.eo_or_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_or x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_or] at h
    case Boolean by' =>
      change Term.Bool =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_or] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_or wx nx ny)
                  (native_int_pow2 wx)))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          cases h
          exact ⟨nx, ny, rfl, rfl⟩
        · simp [hWidth] at h
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

theorem EvaluateProofInternal.eo_xor_args_boolean_of_typeof_bool
    (x y : Term) :
    __eo_typeof (__eo_xor x y) = Term.Bool ->
    ∃ bx : Bool, ∃ by' : Bool,
      x = Term.Boolean bx ∧ y = Term.Boolean by' := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_xor] at h
    case Boolean by' =>
      exact ⟨bx, by', rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_xor] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_xor wx nx ny)
                  (native_int_pow2 wx)))) =
          Term.Bool at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.Bool at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · simp [hWidth] at h
          change Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wy) =
            Term.Bool at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.Bool at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.Bool at h
    change Term.Stuck = Term.Bool at h
    cases h

theorem EvaluateProofInternal.eo_xor_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_xor x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_xor] at h
    case Boolean by' =>
      change Term.Bool =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_xor] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_xor wx nx ny)
                  (native_int_pow2 wx)))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          cases h
          exact ⟨nx, ny, rfl, rfl⟩
        · simp [hWidth] at h
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

theorem EvaluateProofInternal.eo_add_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_add x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_add] at h
    case Numeral ny =>
      change Term.UOp UserOp.Int =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Rational rx =>
    cases y <;> simp only [__eo_add] at h
    case Rational ry =>
      change Term.UOp UserOp.Real =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_add] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_zplus nx ny)
                  (native_int_pow2 wx)))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          cases h
          exact ⟨nx, ny, rfl, rfl⟩
        · simp [hWidth] at h
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

theorem EvaluateProofInternal.eo_add_args_numeral_of_typeof_int
    (x y : Term) :
    __eo_typeof (__eo_add x y) = Term.UOp UserOp.Int ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Numeral nx ∧ y = Term.Numeral ny := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_add] at h
    case Numeral ny =>
      exact ⟨nx, ny, rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  case Rational rx =>
    cases y <;> simp only [__eo_add] at h
    case Rational ry =>
      change Term.UOp UserOp.Real = Term.UOp UserOp.Int at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_add] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_zplus nx ny)
                  (native_int_pow2 wx)))) =
          Term.UOp UserOp.Int at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Int at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          change
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
              Term.UOp UserOp.Int at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.UOp UserOp.Int at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
    change Term.Stuck = Term.UOp UserOp.Int at h
    cases h

theorem EvaluateProofInternal.eo_add_typeof_int_of_args_int
    (x y : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Int)
    (hY : __eo_typeof y = Term.UOp UserOp.Int)
    (hNe : __eo_add x y ≠ Term.Stuck) :
    __eo_typeof (__eo_add x y) = Term.UOp UserOp.Int := by
  cases x <;> cases y <;> simp [__eo_add] at hX hY hNe ⊢
  case Numeral.Numeral nx ny =>
    rfl
  all_goals
    first
    | contradiction
    | cases hX
    | cases hY
    | contradiction

theorem EvaluateProofInternal.eo_add_int_args_numeral_of_nonstuck
    (x y : Term)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (_hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Int) :
    __eo_add x y ≠ Term.Stuck ->
      ∃ nx ny : native_Int, x = Term.Numeral nx ∧ y = Term.Numeral ny := by
  intro hNe
  cases x <;> cases y <;> simp only [__eo_add] at hNe
  case Numeral.Numeral nx ny =>
    exact ⟨nx, ny, rfl, rfl⟩
  case Rational.Rational rx _ry =>
    change __smtx_typeof (SmtTerm.Rational rx) = SmtType.Int at hxTy
    rw [__smtx_typeof.eq_3] at hxTy
    cases hxTy
  case Binary.Binary wx nx _wy _ny =>
    change __smtx_typeof (SmtTerm.Binary wx nx) = SmtType.Int at hxTy
    rw [__smtx_typeof.eq_5] at hxTy
    cases hValid :
        native_and (native_zleq 0 wx)
          (native_zeq nx (native_mod_total nx (native_int_pow2 wx))) <;>
      simp [native_ite, hValid] at hxTy
  all_goals
    contradiction

theorem EvaluateProofInternal.eo_add_args_rational_of_typeof_real
    (x y : Term) :
    __eo_typeof (__eo_add x y) = Term.UOp UserOp.Real ->
    ∃ rx : native_Rat, ∃ ry : native_Rat,
      x = Term.Rational rx ∧ y = Term.Rational ry := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_add] at h
    case Numeral ny =>
      change Term.UOp UserOp.Int = Term.UOp UserOp.Real at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
      change Term.Stuck = Term.UOp UserOp.Real at h
      cases h
  case Rational rx =>
    cases y <;> simp only [__eo_add] at h
    case Rational ry =>
      exact ⟨rx, ry, rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
      change Term.Stuck = Term.UOp UserOp.Real at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_add] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_zplus nx ny)
                  (native_int_pow2 wx)))) =
          Term.UOp UserOp.Real at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Real at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          change
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
              Term.UOp UserOp.Real at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.UOp UserOp.Real at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
      change Term.Stuck = Term.UOp UserOp.Real at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
    change Term.Stuck = Term.UOp UserOp.Real at h
    cases h

theorem EvaluateProofInternal.eo_add_typeof_real_of_args_real
    (x y : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Real)
    (hY : __eo_typeof y = Term.UOp UserOp.Real)
    (hNe : __eo_add x y ≠ Term.Stuck) :
    __eo_typeof (__eo_add x y) = Term.UOp UserOp.Real := by
  cases x <;> cases y <;> simp [__eo_add] at hX hY hNe ⊢
  case Rational.Rational rx ry =>
    rfl
  all_goals
    first
    | contradiction
    | cases hX
    | cases hY
    | contradiction

theorem EvaluateProofInternal.eo_mul_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_mul x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_mul] at h
    case Numeral ny =>
      change Term.UOp UserOp.Int =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Rational rx =>
    cases y <;> simp only [__eo_mul] at h
    case Rational ry =>
      change Term.UOp UserOp.Real =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_mul] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_zmult nx ny)
                  (native_int_pow2 wx)))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          cases h
          exact ⟨nx, ny, rfl, rfl⟩
        · simp [hWidth] at h
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

theorem EvaluateProofInternal.eo_mul_args_numeral_of_typeof_int
    (x y : Term) :
    __eo_typeof (__eo_mul x y) = Term.UOp UserOp.Int ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Numeral nx ∧ y = Term.Numeral ny := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_mul] at h
    case Numeral ny =>
      exact ⟨nx, ny, rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  case Rational rx =>
    cases y <;> simp only [__eo_mul] at h
    case Rational ry =>
      change Term.UOp UserOp.Real = Term.UOp UserOp.Int at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_mul] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_zmult nx ny)
                  (native_int_pow2 wx)))) =
          Term.UOp UserOp.Int at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Int at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          change
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
              Term.UOp UserOp.Int at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.UOp UserOp.Int at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
    change Term.Stuck = Term.UOp UserOp.Int at h
    cases h

theorem EvaluateProofInternal.eo_mul_typeof_int_of_args_int
    (x y : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Int)
    (hY : __eo_typeof y = Term.UOp UserOp.Int)
    (hNe : __eo_mul x y ≠ Term.Stuck) :
    __eo_typeof (__eo_mul x y) = Term.UOp UserOp.Int := by
  cases x <;> cases y <;> simp [__eo_mul] at hX hY hNe ⊢
  case Numeral.Numeral nx ny =>
    rfl
  all_goals
    first
    | cases hX
    | cases hY
    | contradiction

theorem EvaluateProofInternal.eo_mul_args_rational_of_typeof_real
    (x y : Term) :
    __eo_typeof (__eo_mul x y) = Term.UOp UserOp.Real ->
    ∃ rx : native_Rat, ∃ ry : native_Rat,
      x = Term.Rational rx ∧ y = Term.Rational ry := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_mul] at h
    case Numeral ny =>
      change Term.UOp UserOp.Int = Term.UOp UserOp.Real at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
      change Term.Stuck = Term.UOp UserOp.Real at h
      cases h
  case Rational rx =>
    cases y <;> simp only [__eo_mul] at h
    case Rational ry =>
      exact ⟨rx, ry, rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
      change Term.Stuck = Term.UOp UserOp.Real at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_mul] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_zmult nx ny)
                  (native_int_pow2 wx)))) =
          Term.UOp UserOp.Real at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Real at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          change
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
              Term.UOp UserOp.Real at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.UOp UserOp.Real at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
      change Term.Stuck = Term.UOp UserOp.Real at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
    change Term.Stuck = Term.UOp UserOp.Real at h
    cases h

theorem EvaluateProofInternal.eo_mul_typeof_real_of_args_real
    (x y : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Real)
    (hY : __eo_typeof y = Term.UOp UserOp.Real)
    (hNe : __eo_mul x y ≠ Term.Stuck) :
    __eo_typeof (__eo_mul x y) = Term.UOp UserOp.Real := by
  cases x <;> cases y <;> simp [__eo_mul] at hX hY hNe ⊢
  case Rational.Rational rx ry =>
    rfl
  all_goals
    first
    | cases hX
    | cases hY
    | contradiction

theorem EvaluateProofInternal.eo_neg_arg_binary_of_eq_binary
    (x : Term) (w n : native_Int) :
    __eo_neg x = Term.Binary w n ->
    ∃ nx : native_Int, x = Term.Binary w nx := by
  cases x <;> intro h <;> simp [__eo_neg] at h
  case Binary wx nx =>
    rcases h with ⟨hW, _⟩
    cases hW
    exact ⟨nx, rfl⟩

theorem EvaluateProofInternal.eo_neg_arg_numeral_of_typeof_int
    (x : Term) :
    __eo_typeof (__eo_neg x) = Term.UOp UserOp.Int ->
    ∃ nx : native_Int, x = Term.Numeral nx := by
  cases x <;> intro h
  case Numeral nx =>
    exact ⟨nx, rfl⟩
  case Rational q =>
    simp only [__eo_neg] at h
    change Term.UOp UserOp.Real = Term.UOp UserOp.Int at h
    cases h
  case Binary w n =>
    simp only [__eo_neg] at h
    change
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) =
        Term.UOp UserOp.Int at h
    cases h
  all_goals
    simp only [__eo_neg] at h
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
    change Term.Stuck = Term.UOp UserOp.Int at h
    cases h

theorem EvaluateProofInternal.eo_neg_typeof_int_of_arg_int
    (x : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Int)
    (hNe : __eo_neg x ≠ Term.Stuck) :
    __eo_typeof (__eo_neg x) = Term.UOp UserOp.Int := by
  cases x <;> simp [__eo_neg] at hX hNe ⊢
  case Numeral n =>
    rfl
  all_goals
    first
    | cases hX
    | contradiction

theorem EvaluateProofInternal.eo_neg_arg_rational_of_typeof_real
    (x : Term) :
    __eo_typeof (__eo_neg x) = Term.UOp UserOp.Real ->
    ∃ q : native_Rat, x = Term.Rational q := by
  cases x <;> intro h
  case Rational q =>
    exact ⟨q, rfl⟩
  case Numeral nx =>
    simp only [__eo_neg] at h
    change Term.UOp UserOp.Int = Term.UOp UserOp.Real at h
    cases h
  case Binary w n =>
    simp only [__eo_neg] at h
    change
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) =
        Term.UOp UserOp.Real at h
    cases h
  all_goals
    simp only [__eo_neg] at h
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Real at h
    change Term.Stuck = Term.UOp UserOp.Real at h
    cases h

theorem EvaluateProofInternal.eo_neg_typeof_real_of_arg_real
    (x : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Real)
    (hNe : __eo_neg x ≠ Term.Stuck) :
    __eo_typeof (__eo_neg x) = Term.UOp UserOp.Real := by
  cases x <;> simp [__eo_neg] at hX hNe ⊢
  case Rational q =>
    rfl
  all_goals
    first
    | cases hX
    | contradiction

theorem EvaluateProofInternal.eo_is_neg_arg_arith_of_typeof_bool
    (x : Term) :
    __eo_typeof (__eo_is_neg x) = Term.Bool ->
      (∃ n : native_Int, x = Term.Numeral n) ∨
        (∃ q : native_Rat, x = Term.Rational q) := by
  cases x <;> intro h
  case Numeral n =>
    exact Or.inl ⟨n, rfl⟩
  case Rational q =>
    exact Or.inr ⟨q, rfl⟩
  all_goals
    simp only [__eo_is_neg] at h
    change __eo_typeof Term.Stuck = Term.Bool at h
    change Term.Stuck = Term.Bool at h
    cases h

theorem EvaluateProofInternal.eo_is_neg_typeof_bool_of_arg_int
    (x : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Int)
    (hNe : __eo_is_neg x ≠ Term.Stuck) :
    __eo_typeof (__eo_is_neg x) = Term.Bool := by
  cases x <;> simp [__eo_is_neg] at hX hNe ⊢
  all_goals
    first
    | contradiction
    | cases hX

theorem EvaluateProofInternal.eo_is_neg_typeof_bool_of_arg_real
    (x : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Real)
    (hNe : __eo_is_neg x ≠ Term.Stuck) :
    __eo_typeof (__eo_is_neg x) = Term.Bool := by
  cases x <;> simp [__eo_is_neg] at hX hNe ⊢
  all_goals
    first
    | contradiction
    | cases hX

theorem EvaluateProofInternal.eo_is_neg_arg_arith_of_nonstuck
    (x : Term) :
    __eo_is_neg x ≠ Term.Stuck ->
      (∃ n : native_Int, x = Term.Numeral n) ∨
        (∃ q : native_Rat, x = Term.Rational q) := by
  cases x <;> intro h
  case Numeral n =>
    exact Or.inl ⟨n, rfl⟩
  case Rational q =>
    exact Or.inr ⟨q, rfl⟩
  all_goals
    simp only [__eo_is_neg] at h
    contradiction

theorem EvaluateProofInternal.eo_is_neg_int_arg_numeral_of_nonstuck
    (x : Term)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_is_neg x ≠ Term.Stuck ->
      ∃ n : native_Int, x = Term.Numeral n := by
  intro hNe
  rcases EvaluateProofInternal.eo_is_neg_arg_arith_of_nonstuck x hNe with
    ⟨n, hn⟩ | ⟨q, hq⟩
  · exact ⟨n, hn⟩
  · subst x
    change __smtx_typeof (SmtTerm.Rational q) = SmtType.Int at hxTy
    rw [__smtx_typeof.eq_3] at hxTy
    cases hxTy

theorem EvaluateProofInternal.eo_gt_int_args_numeral_of_nonstuck
    (x y : Term)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Int) :
    __eo_gt x y ≠ Term.Stuck ->
      ∃ nx ny : native_Int, x = Term.Numeral nx ∧ y = Term.Numeral ny := by
  intro hNe
  cases x <;> cases y <;> simp only [__eo_gt] at hNe
  case Numeral.Numeral nx ny =>
    exact ⟨nx, ny, rfl, rfl⟩
  case Rational.Rational qx qy =>
    change __smtx_typeof (SmtTerm.Rational qx) = SmtType.Int at hxTy
    rw [__smtx_typeof.eq_3] at hxTy
    cases hxTy
  case Binary.Binary wx nx wy ny =>
    change __smtx_typeof (SmtTerm.Binary wx nx) = SmtType.Int at hxTy
    rw [__smtx_typeof.eq_5] at hxTy
    cases hValid :
        native_and (native_zleq 0 wx)
          (native_zeq nx (native_mod_total nx (native_int_pow2 wx))) <;>
      simp [native_ite, hValid] at hxTy
  all_goals
    contradiction

theorem EvaluateProofInternal.native_zsub_lt_zero_eq_eval
    (n1 n2 : native_Int) :
    native_zlt (native_zplus n1 (native_zneg n2)) 0 =
      native_zlt n1 n2 := by
  exact native_zsub_lt_zero_eq n1 n2

theorem EvaluateProofInternal.native_qsub_lt_zero_eq_eval
    (q1 q2 : native_Rat) :
    native_qlt (native_qplus q1 (native_qneg q2))
        (native_mk_rational 0 1) =
      native_qlt q1 q2 := by
  exact native_qsub_lt_zero_eq q1 q2

theorem EvaluateProofInternal.eo_leq_int_result_eq
    (n1 n2 : native_Int) :
    __eo_or
        (__eo_is_neg
          (__eo_add (Term.Numeral n1) (__eo_neg (Term.Numeral n2))))
        (__eo_eq
          (__eo_to_q
            (__eo_add (Term.Numeral n1) (__eo_neg (Term.Numeral n2))))
          (Term.Rational (native_mk_rational 0 1))) =
      Term.Boolean (native_zleq n1 n2) := by
  unfold __eo_neg __eo_add __eo_is_neg __eo_to_q __eo_eq __eo_or
  simp only [native_teq, native_or]
  rw [native_zsub_lt_zero_eq]
  have hEq :
      decide
          (Term.Rational (native_mk_rational 0 1) =
            Term.Rational
              (native_to_real (native_zplus n1 (native_zneg n2)))) =
        native_zeq n1 n2 := by
    rw [show
        decide
            (Term.Rational (native_mk_rational 0 1) =
              Term.Rational
                (native_to_real (native_zplus n1 (native_zneg n2)))) =
          native_qeq
            (native_to_real (native_zplus n1 (native_zneg n2)))
            (native_mk_rational 0 1) by
      unfold native_qeq
      by_cases h :
          native_mk_rational 0 1 =
            native_to_real (native_zplus n1 (native_zneg n2))
      · have h' :
            native_to_real (native_zplus n1 (native_zneg n2)) =
              native_mk_rational 0 1 := h.symm
        have hTerm :
            Term.Rational (native_mk_rational 0 1) =
              Term.Rational
                (native_to_real (native_zplus n1 (native_zneg n2))) := by
          rw [h]
        simp only [hTerm, h', decide_true]
      · have h' :
            ¬ native_to_real (native_zplus n1 (native_zneg n2)) =
              native_mk_rational 0 1 := fun h' => h h'.symm
        have hTerm :
            ¬ Term.Rational (native_mk_rational 0 1) =
              Term.Rational
                (native_to_real (native_zplus n1 (native_zneg n2))) := by
          intro hTerm
          injection hTerm with hRat
          exact h hRat
        simp only [hTerm, h', decide_false]]
    rw [native_to_real_eq_zero_eq, native_zsub_eq_zero_eq]
  rw [hEq]
  unfold native_zlt native_zeq native_zleq
  by_cases hlt : n1 < n2
  · have hle : n1 ≤ n2 := by grind
    simp [hlt, hle]
  · by_cases heq : n1 = n2
    · have hle : n1 ≤ n2 := by grind
      simp [heq]
    · have hle : ¬ n1 ≤ n2 := by grind
      simp [hlt, heq, hle]

theorem EvaluateProofInternal.eo_leq_real_result_eq
    (q1 q2 : native_Rat) :
    __eo_or
        (__eo_is_neg
          (__eo_add (Term.Rational q1) (__eo_neg (Term.Rational q2))))
        (__eo_eq
          (__eo_to_q
            (__eo_add (Term.Rational q1) (__eo_neg (Term.Rational q2))))
          (Term.Rational (native_mk_rational 0 1))) =
      Term.Boolean (native_qleq q1 q2) := by
  unfold __eo_neg __eo_add __eo_is_neg __eo_to_q __eo_eq __eo_or
  simp only [native_teq, native_or]
  rw [native_qsub_lt_zero_eq]
  have hEq :
      decide
          (Term.Rational (native_mk_rational 0 1) =
            Term.Rational (native_qplus q1 (native_qneg q2))) =
        native_qeq q1 q2 := by
    rw [show
        decide
            (Term.Rational (native_mk_rational 0 1) =
              Term.Rational (native_qplus q1 (native_qneg q2))) =
          native_qeq (native_qplus q1 (native_qneg q2))
            (native_mk_rational 0 1) by
      unfold native_qeq
      by_cases h :
          native_mk_rational 0 1 =
            native_qplus q1 (native_qneg q2)
      · have h' :
            native_qplus q1 (native_qneg q2) =
              native_mk_rational 0 1 := h.symm
        have hTerm :
            Term.Rational (native_mk_rational 0 1) =
              Term.Rational (native_qplus q1 (native_qneg q2)) := by
          rw [h]
        simp only [hTerm, h', decide_true]
      · have h' :
            ¬ native_qplus q1 (native_qneg q2) =
              native_mk_rational 0 1 := fun h' => h h'.symm
        have hTerm :
            ¬ Term.Rational (native_mk_rational 0 1) =
              Term.Rational (native_qplus q1 (native_qneg q2)) := by
          intro hTerm
          injection hTerm with hRat
          exact h hRat
        simp only [hTerm, h', decide_false]]
    rw [native_qsub_eq_zero_eq]
  rw [hEq]
  unfold native_qlt native_qeq native_qleq
  by_cases hlt : q1 < q2
  · have hle : q1 ≤ q2 := by grind
    simp [hlt, hle]
  · by_cases heq : q1 = q2
    · have hle : q1 ≤ q2 := by grind
      simp [heq]
    · have hle : ¬ q1 ≤ q2 := by
        grind
      simp [hlt, heq, hle]

theorem EvaluateProofInternal.eo_to_q_int_arg_of_nonstuck
    (x : Term)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hNe : __eo_to_q x ≠ Term.Stuck) :
    ∃ n : native_Int, x = Term.Numeral n := by
  cases x <;> try simp [__eo_to_q] at hNe
  case Numeral n =>
    exact ⟨n, rfl⟩
  case Rational q =>
    change __smtx_typeof (SmtTerm.Rational q) = SmtType.Int at hxTy
    rw [__smtx_typeof.eq_3] at hxTy
    cases hxTy

theorem EvaluateProofInternal.eo_to_q_real_arg_of_nonstuck
    (x : Term)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Real)
    (hNe : __eo_to_q x ≠ Term.Stuck) :
    ∃ q : native_Rat, x = Term.Rational q := by
  cases x <;> try simp [__eo_to_q] at hNe
  case Numeral n =>
    change __smtx_typeof (SmtTerm.Numeral n) = SmtType.Real at hxTy
    rw [__smtx_typeof.eq_2] at hxTy
    cases hxTy
  case Rational q =>
    exact ⟨q, rfl⟩

theorem EvaluateProofInternal.eo_to_z_real_arg_of_nonstuck
    (x : Term)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Real)
    (hNe : __eo_to_z x ≠ Term.Stuck) :
    ∃ q : native_Rat, x = Term.Rational q := by
  cases x <;> try simp [__eo_to_z] at hNe
  case Numeral n =>
    change __smtx_typeof (SmtTerm.Numeral n) = SmtType.Real at hxTy
    rw [__smtx_typeof.eq_2] at hxTy
    cases hxTy
  case Rational q =>
    exact ⟨q, rfl⟩
  case String s =>
    change __smtx_typeof (SmtTerm.String s) = SmtType.Real at hxTy
    rw [__smtx_typeof.eq_4] at hxTy
    cases hValid : native_string_valid s <;>
      simp [native_ite, hValid] at hxTy
  case Binary w n =>
    change __smtx_typeof (SmtTerm.Binary w n) = SmtType.Real at hxTy
    rw [__smtx_typeof.eq_5] at hxTy
    cases hValid :
        native_and (native_zleq 0 w)
          (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
      simp [native_ite, hValid] at hxTy

theorem EvaluateProofInternal.eo_is_int_result_rel
    (M : SmtModel) (q : native_Rat) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_is_int (SmtValue.Rational q))
      (__smtx_model_eval M
        (__eo_to_smt
          (__eo_eq (__eo_to_q (__eo_to_z (Term.Rational q)))
            (__eo_to_q (Term.Rational q))))) := by
  by_cases hWhole : native_to_real (native_to_int q) = q
  · simp [RuleProofs.smt_value_rel, __smtx_model_eval_is_int,
      __smtx_model_eval_to_int, __smtx_model_eval_to_real,
      __smtx_model_eval_eq, native_veq, __eo_to_z, __eo_to_q,
      __eo_eq, native_teq, hWhole]
    rw [__smtx_model_eval.eq_1]
  · have hWhole' : q ≠ native_to_real (native_to_int q) := by
      intro h
      exact hWhole h.symm
    simp [RuleProofs.smt_value_rel, __smtx_model_eval_is_int,
      __smtx_model_eval_to_int, __smtx_model_eval_to_real,
      __smtx_model_eval_eq, native_veq, __eo_to_z, __eo_to_q,
      __eo_eq, native_teq, hWhole, hWhole']
    rw [__smtx_model_eval.eq_1]

theorem EvaluateProofInternal.eo_lt_int_run_args_of_nonstuck
    (x y : Term)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hNe : __eo_is_neg (__eo_add x (__eo_neg y)) ≠ Term.Stuck) :
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Numeral nx ∧ y = Term.Numeral ny := by
  rcases EvaluateProofInternal.eo_is_neg_arg_arith_of_nonstuck
      (__eo_add x (__eo_neg y)) hNe with
    hInnerInt | hInnerReal
  · rcases hInnerInt with ⟨n, hInner⟩
    have hInnerTy :
        __eo_typeof (__eo_add x (__eo_neg y)) =
          Term.UOp UserOp.Int := by
      rw [hInner]
      rfl
    rcases EvaluateProofInternal.eo_add_args_numeral_of_typeof_int x (__eo_neg y)
        hInnerTy with
      ⟨nx, nNegY, hx, hNegY⟩
    have hNegYTy : __eo_typeof (__eo_neg y) =
        Term.UOp UserOp.Int := by
      rw [hNegY]
      rfl
    rcases EvaluateProofInternal.eo_neg_arg_numeral_of_typeof_int y hNegYTy with
      ⟨ny, hy⟩
    exact ⟨nx, ny, hx, hy⟩
  · rcases hInnerReal with ⟨q, hInner⟩
    have hInnerTy :
        __eo_typeof (__eo_add x (__eo_neg y)) =
          Term.UOp UserOp.Real := by
      rw [hInner]
      rfl
    rcases EvaluateProofInternal.eo_add_args_rational_of_typeof_real x (__eo_neg y)
        hInnerTy with
      ⟨qx, _qNegY, hx, _hNegY⟩
    rw [hx] at hxTy
    change __smtx_typeof (SmtTerm.Rational qx) = SmtType.Int at hxTy
    rw [__smtx_typeof.eq_3] at hxTy
    cases hxTy

theorem EvaluateProofInternal.eo_lt_real_run_args_of_nonstuck
    (x y : Term)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Real)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Real)
    (hNe : __eo_is_neg (__eo_add x (__eo_neg y)) ≠ Term.Stuck) :
    ∃ qx : native_Rat, ∃ qy : native_Rat,
      x = Term.Rational qx ∧ y = Term.Rational qy := by
  rcases EvaluateProofInternal.eo_is_neg_arg_arith_of_nonstuck
      (__eo_add x (__eo_neg y)) hNe with
    hInnerInt | hInnerReal
  · rcases hInnerInt with ⟨n, hInner⟩
    have hInnerTy :
        __eo_typeof (__eo_add x (__eo_neg y)) =
          Term.UOp UserOp.Int := by
      rw [hInner]
      rfl
    rcases EvaluateProofInternal.eo_add_args_numeral_of_typeof_int x (__eo_neg y)
        hInnerTy with
      ⟨nx, _nNegY, hx, _hNegY⟩
    rw [hx] at hxTy
    change __smtx_typeof (SmtTerm.Numeral nx) = SmtType.Real at hxTy
    rw [__smtx_typeof.eq_2] at hxTy
    cases hxTy
  · rcases hInnerReal with ⟨q, hInner⟩
    have hInnerTy :
        __eo_typeof (__eo_add x (__eo_neg y)) =
          Term.UOp UserOp.Real := by
      rw [hInner]
      rfl
    rcases EvaluateProofInternal.eo_add_args_rational_of_typeof_real x (__eo_neg y)
        hInnerTy with
      ⟨qx, qNegY, hx, hNegY⟩
    have hNegYTy : __eo_typeof (__eo_neg y) =
        Term.UOp UserOp.Real := by
      rw [hNegY]
      rfl
    rcases EvaluateProofInternal.eo_neg_arg_rational_of_typeof_real y hNegYTy with
      ⟨qy, hy⟩
    exact ⟨qx, qy, hx, hy⟩

theorem EvaluateProofInternal.eo_zdiv_args_numeral_of_typeof_int
    (x y : Term) :
    __eo_typeof (__eo_zdiv x y) = Term.UOp UserOp.Int ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Numeral nx ∧ y = Term.Numeral ny ∧
        native_zeq 0 ny = false := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_zdiv] at h
    case Numeral ny =>
      cases hZero : native_zeq 0 ny
      · exact ⟨nx, ny, rfl, rfl, hZero⟩
      · simp [hZero, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Int at h
        cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_zdiv] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (native_ite (native_zeq 0 ny)
                (Term.Binary wx (native_binary_max wx))
                (Term.Binary wx
                  (native_mod_total (native_div_total nx ny)
                    (native_int_pow2 wx))))) =
          Term.UOp UserOp.Int at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [__eo_requires, hReq, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Int at h
        cases h
      · simp [__eo_requires, native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          cases hZero : native_zeq 0 ny <;> simp [hZero] at h
          all_goals
            change
              Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
                Term.UOp UserOp.Int at h
            cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.UOp UserOp.Int at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
    change Term.Stuck = Term.UOp UserOp.Int at h
    cases h

theorem EvaluateProofInternal.eo_zmod_args_numeral_of_typeof_int
    (x y : Term) :
    __eo_typeof (__eo_zmod x y) = Term.UOp UserOp.Int ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Numeral nx ∧ y = Term.Numeral ny ∧
        native_zeq 0 ny = false := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_zmod] at h
    case Numeral ny =>
      cases hZero : native_zeq 0 ny
      · exact ⟨nx, ny, rfl, rfl, hZero⟩
      · simp [hZero, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Int at h
        cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_zmod] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (native_ite (native_zeq 0 ny)
                (Term.Binary wx nx)
                (Term.Binary wx
                  (native_mod_total (native_mod_total nx ny)
                    (native_int_pow2 wx))))) =
          Term.UOp UserOp.Int at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [__eo_requires, hReq, native_ite] at h
        change Term.Stuck = Term.UOp UserOp.Int at h
        cases h
      · simp [__eo_requires, native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          cases hZero : native_zeq 0 ny <;> simp [hZero] at h
          all_goals
            change
              Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
                Term.UOp UserOp.Int at h
            cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.UOp UserOp.Int at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
      change Term.Stuck = Term.UOp UserOp.Int at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.UOp UserOp.Int at h
    change Term.Stuck = Term.UOp UserOp.Int at h
    cases h

theorem EvaluateProofInternal.eo_zdiv_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_zdiv x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_zdiv] at h
    case Numeral ny =>
      cases hZero : native_zeq 0 ny
      · simp [hZero, native_ite] at h
        change Term.UOp UserOp.Int =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [hZero, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_zdiv] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (native_ite (native_zeq 0 ny)
                (Term.Binary wx (native_binary_max wx))
                (Term.Binary wx
                  (native_mod_total (native_div_total nx ny)
                    (native_int_pow2 wx))))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [__eo_requires, hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [__eo_requires, native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          cases hZero : native_zeq 0 ny <;> simp [hZero] at h
          all_goals
            cases h
            exact ⟨nx, ny, rfl, rfl⟩
        · simp [hWidth] at h
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

theorem EvaluateProofInternal.eo_zmod_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_zmod x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_zmod] at h
    case Numeral ny =>
      cases hZero : native_zeq 0 ny
      · simp [hZero, native_ite] at h
        change Term.UOp UserOp.Int =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [hZero, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_zmod] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (native_ite (native_zeq 0 ny)
                (Term.Binary wx nx)
                (Term.Binary wx
                  (native_mod_total (native_mod_total nx ny)
                    (native_int_pow2 wx))))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [__eo_requires, hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [__eo_requires, native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          cases hZero : native_zeq 0 ny <;> simp [hZero] at h
          all_goals
            cases h
            exact ⟨nx, ny, rfl, rfl⟩
        · simp [hWidth] at h
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

theorem EvaluateProofInternal.eo_zero_extend_literal_arg_binary_of_typeof_bitvec
    (x : Term) (i w : native_Int) :
    __eo_typeof
        (__eo_to_bin
          (__eo_add (__bv_bitwidth (__eo_typeof x)) (Term.Numeral i))
          (__eo_to_z x)) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ wx : native_Int, ∃ nx : native_Int,
      x = Term.Binary wx nx ∧ w = native_zplus wx i ∧
        __eo_to_bin
            (__eo_add (__bv_bitwidth (__eo_typeof x)) (Term.Numeral i))
            (__eo_to_z x) =
          Term.Binary (native_zplus wx i)
            (native_mod_total nx (native_int_pow2 (native_zplus wx i))) := by
  cases x <;> intro h
  case Binary wx nx =>
    change
      __eo_typeof
          (__eo_to_bin (Term.Numeral (native_zplus wx i))
            (Term.Numeral nx)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change
      __eo_typeof
          (native_ite (native_zleq (native_zplus wx i) 4294967296)
            (__eo_mk_binary (native_zplus wx i) nx) Term.Stuck) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases hLeMax : native_zleq (native_zplus wx i) 4294967296
    · simp [hLeMax, native_ite] at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    · simp [hLeMax, native_ite, __eo_mk_binary] at h
      cases hNonneg : native_zleq 0 (native_zplus wx i)
      · simp [hNonneg] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [hNonneg] at h
        cases h
        refine ⟨wx, nx, rfl, rfl, ?_⟩
        change
          __eo_to_bin (Term.Numeral (native_zplus wx i))
              (Term.Numeral nx) =
            Term.Binary (native_zplus wx i)
              (native_mod_total nx (native_int_pow2 (native_zplus wx i)))
        simp [__eo_to_bin, __eo_mk_binary, hLeMax, hNonneg, native_ite]
  all_goals
    simp [__eo_to_bin, __eo_add, __bv_bitwidth, __eo_to_z] at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

def EvaluateProofInternal.eo_eval_sign_extend_rhs (x n : Term) : Term :=
  let bw := __bv_bitwidth (__eo_typeof x)
  let low := __eo_to_z (__eo_extract x (Term.Numeral 0)
    (__eo_add bw (Term.Numeral (-2 : native_Int))))
  let msb := __eo_add bw (Term.Numeral (-1 : native_Int))
  __eo_to_bin (__eo_add bw n)
    (__eo_ite (__eo_eq (__eo_extract x msb msb) (Term.Binary 1 1))
      (__eo_add
        (__eo_neg
          (__eo_ite (__eo_is_z msb)
            (__eo_ite (__eo_is_neg msb) (Term.Numeral 0)
              (__eo_pow (Term.Numeral 2) msb))
            (__eo_mk_apply (Term.UOp UserOp.int_pow2) msb)))
        low)
      low)

def EvaluateProofInternal.eo_signed_bv_value (x : Term) : Term :=
  let bw := __bv_bitwidth (__eo_typeof x)
  let low := __eo_to_z (__eo_extract x (Term.Numeral 0)
    (__eo_add bw (Term.Numeral (-2 : native_Int))))
  let msb := __eo_add bw (Term.Numeral (-1 : native_Int))
  __eo_ite (__eo_eq (__eo_extract x msb msb) (Term.Binary 1 1))
    (__eo_add
      (__eo_neg
        (__eo_ite (__eo_is_z msb)
          (__eo_ite (__eo_is_neg msb) (Term.Numeral 0)
            (__eo_pow (Term.Numeral 2) msb))
          (__eo_mk_apply (Term.UOp UserOp.int_pow2) msb)))
      low)
    low

def EvaluateProofInternal.eo_sign_extend_low_payload
    (w n : native_Int) : native_Int :=
  if native_zlt (native_zplus w (native_zneg 2)) 0 then
    0
  else
    native_mod_total n
      (native_int_pow2 (native_zplus w (native_zneg 1)))

def EvaluateProofInternal.eo_sign_extend_msb_set
    (w n : native_Int) : native_Bool :=
  if native_zlt (native_zplus w (native_zneg 1)) 0 then
    false
  else
    native_zeq
      (native_mod_total
        (native_div_total n
          (native_int_pow2 (native_zplus w (native_zneg 1))))
        2) 1

def EvaluateProofInternal.eo_sign_extend_payload (w n : native_Int) : native_Int :=
  if EvaluateProofInternal.eo_sign_extend_msb_set w n then
    native_zplus
      (native_zneg
        (native_int_pow2 (native_zplus w (native_zneg 1))))
      (EvaluateProofInternal.eo_sign_extend_low_payload w n)
  else
    EvaluateProofInternal.eo_sign_extend_low_payload w n

theorem EvaluateProofInternal.eo_to_bin_literal_width_of_typeof_bitvec
    (y : Term) (wi w : native_Int) :
    __eo_typeof (__eo_to_bin (Term.Numeral wi) y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    w = wi := by
  cases y <;> intro h <;>
    simp [__eo_to_bin, __eo_mk_binary, native_ite] at h
  case Numeral n =>
    cases hLe : native_zleq wi 4294967296 <;> simp [hLe] at h
    · change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    · cases hNonneg : native_zleq 0 wi <;> simp [hNonneg] at h
      · change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · cases h
        rfl
  case Binary wb nb =>
    cases hLe : native_zleq wi 4294967296 <;> simp [hLe] at h
    · change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    · cases hNonneg : native_zleq 0 wi <;> simp [hNonneg] at h
      · change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · cases h
        rfl
  all_goals
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

theorem EvaluateProofInternal.eo_to_bin_numeral_eq_of_typeof_bitvec
    (p wi w : native_Int) :
    __eo_typeof (__eo_to_bin (Term.Numeral wi) (Term.Numeral p)) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    __eo_to_bin (Term.Numeral wi) (Term.Numeral p) =
      Term.Binary wi
        (native_mod_total p (native_int_pow2 wi)) := by
  intro h
  change
    __eo_typeof
        (native_ite (native_zleq wi 4294967296)
          (__eo_mk_binary wi p) Term.Stuck) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
  cases hLe : native_zleq wi 4294967296
  · simp [hLe, native_ite] at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
  · simp [hLe, native_ite, __eo_mk_binary] at h
    cases hNonneg : native_zleq 0 wi
    · simp [hNonneg] at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    · simp [hNonneg] at h
      simp [__eo_to_bin, __eo_mk_binary, hLe, hNonneg, native_ite]

theorem EvaluateProofInternal.eo_eval_sign_extend_rhs_binary_of_typeof_bitvec
    (x : Term) (i w : native_Int) :
    __eo_typeof (EvaluateProofInternal.eo_eval_sign_extend_rhs x (Term.Numeral i)) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ wx : native_Int, ∃ nx : native_Int,
      x = Term.Binary wx nx ∧ w = native_zplus wx i := by
  cases x <;> intro h
  case Binary wx nx =>
    change
      __eo_typeof
          (__eo_to_bin (Term.Numeral (native_zplus wx i)) _) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    have hW :=
      EvaluateProofInternal.eo_to_bin_literal_width_of_typeof_bitvec _
        (native_zplus wx i) w h
    exact ⟨wx, nx, rfl, hW⟩
  all_goals
    dsimp [EvaluateProofInternal.eo_eval_sign_extend_rhs] at h
    simp only [__eo_extract, __eo_eq, __eo_ite, __eo_to_bin,
      __eo_to_z] at h
    first
    | change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    | have hTrue :
          native_teq Term.Stuck (Term.Boolean true) = false := by
        native_decide
      have hFalse :
          native_teq Term.Stuck (Term.Boolean false) = false := by
        native_decide
      rw [hTrue, hFalse] at h
      simp [native_ite] at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h

theorem EvaluateProofInternal.eo_extract_literal_arg_binary_of_typeof_bitvec
    (x : Term) (i j w : native_Int)
    (hj0 : native_zleq 0 j = true)
    (hWidth : native_zlt 0
      (native_zplus (native_zplus i 1) (native_zneg j)) = true) :
    __eo_typeof (__eo_extract x (Term.Numeral j) (Term.Numeral i)) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ wx : native_Int, ∃ nx : native_Int,
      x = Term.Binary wx nx ∧
        w = native_zplus (native_zplus i (native_zneg j)) 1 ∧
        __eo_extract x (Term.Numeral j) (Term.Numeral i) =
          Term.Binary (native_zplus (native_zplus i (native_zneg j)) 1)
            (native_mod_total (native_binary_extract wx nx i j)
              (native_int_pow2
                (native_zplus (native_zplus i (native_zneg j)) 1))) := by
  cases x <;> intro h
  case Binary wx nx =>
    have hjNonneg : 0 <= j := by
      simpa [native_zleq, SmtEval.native_zleq] using hj0
    have hjNotNeg : native_zlt j 0 = false := by
      simpa [native_zlt, SmtEval.native_zlt] using
        Int.not_lt_of_ge hjNonneg
    have hWidthAssoc :
        native_zplus (native_zplus i 1) (native_zneg j) =
          native_zplus (native_zplus i (native_zneg j)) 1 := by
      simp [native_zplus, SmtEval.native_zplus, native_zneg,
        SmtEval.native_zneg, Int.add_assoc, Int.add_comm,
        Int.add_left_comm]
    have hWidthPosNative :
        native_zlt 0
          (native_zplus (native_zplus i (native_zneg j)) 1) = true := by
      simpa [hWidthAssoc] using hWidth
    have hWidthNonnegNative :
        native_zleq 0
          (native_zplus (native_zplus i (native_zneg j)) 1) = true := by
      have hPos :
          (0 : native_Int) <
            native_zplus (native_zplus i (native_zneg j)) 1 := by
        simpa [native_zlt, SmtEval.native_zlt] using hWidthPosNative
      simpa [native_zleq, SmtEval.native_zleq] using Int.le_of_lt hPos
    change
      __eo_typeof
          (native_ite
            (native_or (native_zlt j 0) (native_zlt (i + -j) 0))
            (Term.Binary 0 0)
            (__eo_mk_binary (native_zplus (i + -j) 1)
              (native_binary_extract wx nx i j))) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases hDeltaNeg :
        native_zlt (native_zplus i (native_zneg j)) 0
    · have hDeltaNotLt : ¬ i + -j < 0 := by
        have hsimpa := hDeltaNeg
        try simp [native_zlt, SmtEval.native_zlt, native_zplus, SmtEval.native_zplus, native_zneg, SmtEval.native_zneg] at hsimpa ⊢
        exact Int.not_lt.mp (of_decide_eq_false hsimpa)
      have hDeltaNonneg : 0 <= i + -j :=
        Int.le_of_not_gt hDeltaNotLt
      have hWidthNonneg : native_zleq 0 (i + -j + 1) = true := by
        have hNonneg : 0 <= i + -j + 1 :=
          Int.add_nonneg hDeltaNonneg (by decide)
        simpa [native_zleq, SmtEval.native_zleq] using hNonneg
      have hDeltaNotNegNative : native_zlt (i + -j) 0 = false := by
        simpa [native_zlt, SmtEval.native_zlt] using
          Int.not_lt_of_ge hDeltaNonneg
      simp [hjNotNeg, hDeltaNotNegNative, native_zneg, SmtEval.native_zneg,
        native_or, native_ite, __eo_mk_binary, hWidthNonneg,
        native_zplus, SmtEval.native_zplus] at h
      have hW : w = native_zplus (native_zplus i (native_zneg j)) 1 :=
        (Term.Numeral.inj ((Term.Apply.inj h).2)).symm
      refine ⟨wx, nx, rfl, hW, ?_⟩
      change
        native_ite
            (native_or (native_zlt j 0)
              (native_zlt (i + native_zneg j) 0))
            (Term.Binary 0 0)
            (__eo_mk_binary (native_zplus (i + native_zneg j) 1)
              (native_binary_extract wx nx i j)) =
          Term.Binary (native_zplus (native_zplus i (native_zneg j)) 1)
            (native_mod_total (native_binary_extract wx nx i j)
              (native_int_pow2
                (native_zplus (native_zplus i (native_zneg j)) 1)))
      simp [hjNotNeg, hDeltaNotNegNative, hWidthNonneg,
        __eo_mk_binary, native_or, native_ite, native_zplus,
        SmtEval.native_zplus, native_zneg, SmtEval.native_zneg]
    · have hDeltaLt : i + -j < 0 := by
        have hsimpa := hDeltaNeg
        try simp [native_zlt, SmtEval.native_zlt, native_zplus, SmtEval.native_zplus, native_zneg, SmtEval.native_zneg] at hsimpa ⊢
        exact of_decide_eq_true hsimpa
      have hWidthGe : 0 <= i + -j + 1 := by
        simpa [native_zleq, SmtEval.native_zleq, native_zplus,
          SmtEval.native_zplus, native_zneg, SmtEval.native_zneg,
          Int.add_assoc] using hWidthNonnegNative
      have hWidthZeroInt : i + -j + 1 = 0 :=
        Int.le_antisymm (Int.add_one_le_iff.mpr hDeltaLt) hWidthGe
      have hWidthZero :
          native_zplus (native_zplus i (native_zneg j)) 1 = 0 := by
        simpa [native_zplus, SmtEval.native_zplus, native_zneg,
          SmtEval.native_zneg, Int.add_assoc] using hWidthZeroInt
      have hDeltaNegNative : native_zlt (i + -j) 0 = true := by
        simpa [native_zlt, SmtEval.native_zlt] using hDeltaLt
      simp [hjNotNeg, hDeltaNegNative, native_zneg, SmtEval.native_zneg,
        native_or, native_ite, __eo_lit_type_Binary, __eo_len,
        __eo_mk_apply] at h
      have hW : w = 0 :=
        (Term.Numeral.inj ((Term.Apply.inj h).2)).symm
      refine ⟨wx, nx, rfl, hW.trans hWidthZero.symm, ?_⟩
      change
        native_ite
            (native_or (native_zlt j 0)
              (native_zlt (i + native_zneg j) 0))
            (Term.Binary 0 0)
            (__eo_mk_binary (native_zplus (i + native_zneg j) 1)
              (native_binary_extract wx nx i j)) =
          Term.Binary (native_zplus (native_zplus i (native_zneg j)) 1)
            (native_mod_total (native_binary_extract wx nx i j)
              (native_int_pow2
                (native_zplus (native_zplus i (native_zneg j)) 1)))
      simp [hjNotNeg, hDeltaNegNative, hWidthZero, native_or, native_ite,
        native_mod_total, native_int_pow2, native_zexp_total, native_zplus,
        SmtEval.native_zplus, native_zneg, SmtEval.native_zneg]
      constructor
      · exact hWidthZeroInt.symm
      · -- `rw` cannot abstract a term the `Decidable` instance depends on
        simp only [hWidthZeroInt]
        simp [native_mod_total, native_int_pow2, native_zexp_total]
  case String s =>
    change
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

theorem EvaluateProofInternal.eo_sign_extend_low_payload_eq
    (w n : native_Int) :
    __eo_to_z
        (__eo_extract (Term.Binary w n) (Term.Numeral 0)
          (Term.Numeral (native_zplus w (native_zneg 2)))) =
      Term.Numeral (EvaluateProofInternal.eo_sign_extend_low_payload w n) := by
  by_cases hNeg :
      native_zlt (native_zplus w (native_zneg 2)) 0 = true
  · have hNegPrime : native_zlt (w + -2) 0 = true := by
      simpa [native_zplus, SmtEval.native_zplus, native_zneg,
        SmtEval.native_zneg] using hNeg
    simp [__eo_extract, __eo_to_z, EvaluateProofInternal.eo_sign_extend_low_payload,
      hNegPrime, native_ite, native_or, native_zplus,
      SmtEval.native_zplus, native_zneg, SmtEval.native_zneg]
  · have hNegFalse :
        native_zlt (native_zplus w (native_zneg 2)) 0 = false := by
      cases h : native_zlt (native_zplus w (native_zneg 2)) 0 <;>
        simp [h] at hNeg ⊢
    have hNegPrime : native_zlt (w + -2) 0 = false := by
      simpa [native_zplus, SmtEval.native_zplus, native_zneg,
        SmtEval.native_zneg] using hNegFalse
    have hGe : 0 <= w + -2 := by
      simpa [native_zlt, SmtEval.native_zlt] using hNegPrime
    have hNonnegPred : 0 <= w + -2 + 1 :=
      Int.add_nonneg hGe (by decide)
    have hPowArg : w + -2 + 1 = w + -1 := by
      rw [Int.add_assoc]
      have hConst : (-2 : native_Int) + 1 = -1 := by
        native_decide
      rw [hConst]
    have hLe : native_zleq 0 (w + -1) = true := by
      have hTmp : native_zleq 0 (w + -2 + 1) = true := by
        simpa [native_zleq, SmtEval.native_zleq] using hNonnegPred
      simpa [hPowArg] using hTmp
    have hDiv : native_div_total n (native_int_pow2 0) = n := by
      simp [native_div_total, native_int_pow2, native_zexp_total]
    have hZlt00 : native_zlt 0 0 = false := by
      native_decide
    simp [__eo_extract, __eo_to_z, __eo_mk_binary,
      EvaluateProofInternal.eo_sign_extend_low_payload, hNegPrime, hLe, hDiv, hPowArg,
      hZlt00, native_binary_extract, native_ite, native_or,
      native_zplus, SmtEval.native_zplus, native_zneg,
      SmtEval.native_zneg]

theorem EvaluateProofInternal.eo_sign_extend_msb_eq
    (w n : native_Int) :
    __eo_eq
        (__eo_extract (Term.Binary w n)
          (Term.Numeral (native_zplus w (native_zneg 1)))
          (Term.Numeral (native_zplus w (native_zneg 1))))
        (Term.Binary 1 1) =
      Term.Boolean (EvaluateProofInternal.eo_sign_extend_msb_set w n) := by
  by_cases hNeg :
      native_zlt (native_zplus w (native_zneg 1)) 0 = true
  · have hNegPrime : native_zlt (w + -1) 0 = true := by
      simpa [native_zplus, SmtEval.native_zplus, native_zneg,
        SmtEval.native_zneg] using hNeg
    simp [__eo_extract, __eo_eq, EvaluateProofInternal.eo_sign_extend_msb_set,
      hNegPrime, native_ite, native_or, native_teq,
      native_zplus, SmtEval.native_zplus, native_zneg,
      SmtEval.native_zneg]
  · have hNegFalse :
        native_zlt (native_zplus w (native_zneg 1)) 0 = false := by
      cases h : native_zlt (native_zplus w (native_zneg 1)) 0 <;>
        simp [h] at hNeg ⊢
    have hNegPrime : native_zlt (w + -1) 0 = false := by
      simpa [native_zplus, SmtEval.native_zplus, native_zneg,
        SmtEval.native_zneg] using hNegFalse
    have hDelta : w + -1 + -(w + -1) = 0 :=
      Int.add_right_neg (w + -1)
    have hWidth : w + -1 + -(w + -1) + 1 = 1 := by
      rw [hDelta]
      rfl
    have hLe1 : native_zleq 0 (1 : native_Int) = true := by
      native_decide
    have hPow1 : native_int_pow2 (1 : native_Int) = 2 := by
      native_decide
    have hZlt00 : native_zlt 0 0 = false := by
      native_decide
    simp [__eo_extract, __eo_eq, __eo_mk_binary,
      EvaluateProofInternal.eo_sign_extend_msb_set, hNegPrime, hDelta,
      hLe1, hPow1, hZlt00, native_binary_extract,
      native_ite, native_or, native_teq, native_zeq,
      SmtEval.native_zeq, native_zplus, SmtEval.native_zplus,
      native_zneg, SmtEval.native_zneg]
    -- simp now leaves the goal as `decide _ = decide _` rather than an `Iff`
    exact decide_eq_decide.mpr ⟨fun h => h.symm, fun h => h.symm⟩

theorem EvaluateProofInternal.eo_sbv_to_int_msb_zero_eq_of_pos
    {w n : native_Int} (hwpos : 0 < w) :
    __eo_eq
        (__eo_extract (Term.Binary w n)
          (Term.Numeral (native_zplus w (native_zneg 1)))
          (Term.Numeral (native_zplus w (native_zneg 1))))
        (Term.Binary 1 0) =
      Term.Boolean
        (native_zeq
          (native_mod_total
            (native_div_total n
              (native_int_pow2 (w - 1))) 2)
          0) := by
  have hNegPrime : native_zlt (w + -1) 0 = false := by
    have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
    have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
    simpa [native_zlt, SmtEval.native_zlt, Int.sub_eq_add_neg] using
      Int.not_lt_of_ge hwp0
  have hNeg :
      native_zlt (native_zplus w (native_zneg 1)) 0 = false := by
    simpa [native_zplus, SmtEval.native_zplus, native_zneg,
      SmtEval.native_zneg] using hNegPrime
  have hDelta : w + -1 + -(w + -1) = 0 :=
    Int.add_right_neg (w + -1)
  have hWidth : w + -1 + -(w + -1) + 1 = 1 := by
    rw [hDelta]
    rfl
  have hLe1 : native_zleq 0 (1 : native_Int) = true := by
    native_decide
  have hPow1 : native_int_pow2 (1 : native_Int) = 2 := by
    native_decide
  have hZlt00 : native_zlt 0 0 = false := by
    native_decide
  simp [__eo_extract, __eo_eq, __eo_mk_binary, hNegPrime,
    hDelta, hLe1, hPow1, hZlt00, native_binary_extract,
    native_ite, native_or, native_teq, native_zeq,
    SmtEval.native_zeq, native_zplus, SmtEval.native_zplus,
    native_zneg, SmtEval.native_zneg, Int.sub_eq_add_neg]
  constructor <;> intro h <;> exact h.symm

theorem EvaluateProofInternal.eo_int_pow2_literal_eq (k : native_Int) :
    __eo_ite (__eo_is_z (Term.Numeral k))
      (__eo_ite (__eo_is_neg (Term.Numeral k)) (Term.Numeral 0)
        (__eo_pow (Term.Numeral 2) (Term.Numeral k)))
      (__eo_mk_apply (Term.UOp UserOp.int_pow2) (Term.Numeral k)) =
    Term.Numeral (native_int_pow2 k) := by
  by_cases hk : k < 0
  · have hlt : native_zlt k 0 = true := by
      simpa [native_zlt, SmtEval.native_zlt] using hk
    simp [__eo_ite, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
      native_ite, native_teq, native_and, native_not,
      hlt, native_int_pow2, native_zexp_total, hk]
  · have hlt : native_zlt k 0 = false := by
      simpa [native_zlt, SmtEval.native_zlt] using hk
    simp [__eo_ite, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
      __eo_pow, native_ite, native_teq, native_and, native_not,
      hlt, native_int_pow2, native_zexp_total, hk]

theorem EvaluateProofInternal.eo_eval_sign_extend_rhs_binary_to_bin
    (w n i : native_Int) :
    EvaluateProofInternal.eo_eval_sign_extend_rhs (Term.Binary w n) (Term.Numeral i) =
      __eo_to_bin (Term.Numeral (native_zplus w i))
        (Term.Numeral (EvaluateProofInternal.eo_sign_extend_payload w n)) := by
  dsimp [EvaluateProofInternal.eo_eval_sign_extend_rhs]
  change
    __eo_to_bin (Term.Numeral (native_zplus w i))
      (__eo_ite
        (__eo_eq
          (__eo_extract (Term.Binary w n)
            (Term.Numeral (native_zplus w (native_zneg 1)))
            (Term.Numeral (native_zplus w (native_zneg 1))))
          (Term.Binary 1 1))
        (__eo_add
          (__eo_neg
            (__eo_ite
              (__eo_is_z
                (Term.Numeral (native_zplus w (native_zneg 1))))
              (__eo_ite
                (__eo_is_neg
                  (Term.Numeral (native_zplus w (native_zneg 1))))
                (Term.Numeral 0)
                (__eo_pow (Term.Numeral 2)
                  (Term.Numeral (native_zplus w (native_zneg 1)))))
              (__eo_mk_apply (Term.UOp UserOp.int_pow2)
                (Term.Numeral (native_zplus w (native_zneg 1))))))
          (__eo_to_z
            (__eo_extract (Term.Binary w n) (Term.Numeral 0)
              (Term.Numeral (native_zplus w (native_zneg 2))))))
        (__eo_to_z
          (__eo_extract (Term.Binary w n) (Term.Numeral 0)
            (Term.Numeral (native_zplus w (native_zneg 2)))))) =
      _
  rw [EvaluateProofInternal.eo_sign_extend_msb_eq, EvaluateProofInternal.eo_sign_extend_low_payload_eq,
    EvaluateProofInternal.eo_int_pow2_literal_eq]
  cases hMsb : EvaluateProofInternal.eo_sign_extend_msb_set w n
  · simp [EvaluateProofInternal.eo_sign_extend_payload, hMsb, __eo_ite, native_ite,
      native_teq]
  · simp [EvaluateProofInternal.eo_sign_extend_payload, hMsb, __eo_ite, __eo_add,
      __eo_neg, native_ite, native_teq]

theorem EvaluateProofInternal.native_int_pow2_succ_pred
    {w : native_Int} (hwpos : 0 < w) :
    native_int_pow2 w = 2 * native_int_pow2 (w - 1) := by
  have hw0 : 0 <= w := Int.le_of_lt hwpos
  have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
  have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
  have hnotW : ¬ w < 0 := Int.not_lt_of_ge hw0
  have hnotP : ¬ w - 1 < 0 := Int.not_lt_of_ge hwp0
  have hNat : w.toNat = (w - 1).toNat + 1 := by
    apply Int.ofNat_inj.mp
    rw [Int.natCast_add, Int.natCast_one]
    rw [Int.toNat_of_nonneg hw0, Int.toNat_of_nonneg hwp0]
    omega
  rw [native_int_pow2, native_int_pow2, native_zexp_total,
    native_zexp_total]
  simp [hnotW, hnotP]
  rw [hNat]
  have hSub : (w - 1).toNat + 1 - 1 = (w - 1).toNat :=
    Nat.add_sub_cancel (w - 1).toNat 1
  rw [hSub]
  rw [← Nat.succ_eq_add_one]
  rw [Int.pow_succ]
  rw [Int.mul_comm]

theorem EvaluateProofInternal.native_int_pow2_add_of_nonneg
    {a b : native_Int} (ha : 0 <= a) (hb : 0 <= b) :
    native_int_pow2 (a + b) = native_int_pow2 a * native_int_pow2 b := by
  have hna : ¬ a < 0 := Int.not_lt_of_ge ha
  have hnb : ¬ b < 0 := Int.not_lt_of_ge hb
  have hab : ¬ a + b < 0 := Int.not_lt_of_ge (Int.add_nonneg ha hb)
  have hto : Int.toNat (a + b) = Int.toNat a + Int.toNat b :=
    Int.toNat_add ha hb
  rw [native_int_pow2, native_int_pow2, native_int_pow2,
    native_zexp_total, native_zexp_total, native_zexp_total]
  simp [hna, hnb, hab, hto]
  exact Int.pow_add 2 (Int.toNat a) (Int.toNat b)

theorem EvaluateProofInternal.native_int_pow2_pos_of_nonneg
    {w : native_Int} (hw : 0 <= w) :
    0 < native_int_pow2 w := by
  have hnot : ¬ w < 0 := Int.not_lt_of_ge hw
  simp [native_int_pow2, native_zexp_total, hnot]
  exact Int.pow_pos (by decide)

theorem EvaluateProofInternal.native_int_pow2_lt_of_lt_nonneg
    {w k : native_Int} (hw : 0 <= w) (hlt : w < k) :
    native_int_pow2 w < native_int_pow2 k := by
  let d : native_Int := k - w
  have hdpos : 0 < d := by
    dsimp [d]
    exact Int.sub_pos.mpr hlt
  have hd : 0 <= d := Int.le_of_lt hdpos
  have hkEq : k = w + d := by
    dsimp [d]
    symm
    calc
      w + (k - w) = w + k - w := by
        rw [Int.add_sub_assoc]
      _ = k + w - w := by
        rw [Int.add_comm w k]
      _ = k := by
        rw [Int.add_sub_cancel]
  have hPow : native_int_pow2 k = native_int_pow2 w * native_int_pow2 d := by
    rw [hkEq]
    exact EvaluateProofInternal.native_int_pow2_add_of_nonneg hw hd
  have hWPos : 0 < native_int_pow2 w :=
    EvaluateProofInternal.native_int_pow2_pos_of_nonneg hw
  have hDOne : 1 < native_int_pow2 d := by
    have hnot : ¬ d < 0 := Int.not_lt_of_ge hd
    have hdNatNe : Int.toNat d ≠ 0 := by
      intro hZero
      have hdle : d <= 0 := Int.toNat_eq_zero.mp hZero
      exact (Int.not_le_of_gt hdpos) hdle
    have hNat : 1 < (2 : Nat) ^ Int.toNat d :=
      Nat.one_lt_pow hdNatNe (by decide : 1 < (2 : Nat))
    rw [native_int_pow2, native_zexp_total]
    simp [hnot]
    exact_mod_cast hNat
  rw [hPow]
  have hMul := Int.mul_lt_mul_of_pos_left hDOne hWPos
  simpa using hMul

theorem EvaluateProofInternal.native_mod_zmult_pow2_eq_zero_of_lt
    {w k x : native_Int} (hw : 0 <= w) (hlt : w < k) :
    native_mod_total (native_zmult x (native_int_pow2 k))
        (native_int_pow2 w) =
      0 := by
  let d : native_Int := k - w
  have hd : 0 <= d := by
    dsimp [d]
    exact Int.sub_nonneg.mpr (Int.le_of_lt hlt)
  have hkEq : k = w + d := by
    dsimp [d]
    symm
    calc
      w + (k - w) = w + k - w := by
        rw [Int.add_sub_assoc]
      _ = k + w - w := by
        rw [Int.add_comm w k]
      _ = k := by
        rw [Int.add_sub_cancel]
  have hPow : native_int_pow2 k = native_int_pow2 w * native_int_pow2 d := by
    rw [hkEq]
    exact EvaluateProofInternal.native_int_pow2_add_of_nonneg hw hd
  rw [hPow]
  simp [native_mod_total, native_zmult]
  have hAssoc :
      x * (native_int_pow2 w * native_int_pow2 d) =
        native_int_pow2 w * (x * native_int_pow2 d) := by
    calc
      x * (native_int_pow2 w * native_int_pow2 d) =
          (x * native_int_pow2 w) * native_int_pow2 d := by
        rw [← Int.mul_assoc]
      _ = (native_int_pow2 w * x) * native_int_pow2 d := by
        rw [Int.mul_comm x (native_int_pow2 w)]
      _ = native_int_pow2 w * (x * native_int_pow2 d) := by
        rw [Int.mul_assoc]
  rw [hAssoc]
  exact Int.mul_emod_right (native_int_pow2 w) (x * native_int_pow2 d)

theorem EvaluateProofInternal.native_mod_div_pow2_eq_zero_of_lt
    {w k x : native_Int} (hw : 0 <= w) (hlt : w < k)
    (hx0 : 0 <= x) (hxlt : x < native_int_pow2 w) :
    native_mod_total (native_div_total x (native_int_pow2 k))
        (native_int_pow2 w) =
      0 := by
  have hPowLt : native_int_pow2 w < native_int_pow2 k :=
    EvaluateProofInternal.native_int_pow2_lt_of_lt_nonneg hw hlt
  have hDivZero : native_div_total x (native_int_pow2 k) = 0 := by
    rw [native_div_total]
    exact Int.ediv_eq_zero_of_lt hx0 (Int.lt_trans hxlt hPowLt)
  rw [hDivZero]
  simp [native_mod_total]

theorem EvaluateProofInternal.eo_sign_extend_low_payload_eq_mod_of_pos
    {w n : native_Int} (hwpos : 0 < w) :
    EvaluateProofInternal.eo_sign_extend_low_payload w n =
      native_mod_total n
        (native_int_pow2 (native_zplus w (native_zneg 1))) := by
  by_cases hNeg :
      native_zlt (native_zplus w (native_zneg 2)) 0 = true
  · have hlt : w + -2 < 0 := by
      have hsimpa :=
        hNeg
      try simp [native_zlt, SmtEval.native_zlt, native_zplus, SmtEval.native_zplus, native_zneg, SmtEval.native_zneg] at hsimpa ⊢
      exact of_decide_eq_true hsimpa
    have hwEq : w = 1 := by
      have hlt2 : w < 2 := by
        have h := Int.add_lt_add_right hlt 2
        have hLeft : w + -2 + 2 = w := by
          rw [Int.add_assoc]
          have hc : (-2 : Int) + 2 = 0 := by
            native_decide
          rw [hc, Int.add_zero]
        have hRight : (0 : Int) + 2 = 2 := by
          rfl
        simpa [hLeft, hRight] using h
      have hle1 : w <= 1 := Int.le_of_lt_add_one hlt2
      have hge1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
      exact Int.le_antisymm hle1 hge1
    subst w
    simp [EvaluateProofInternal.eo_sign_extend_low_payload, native_zplus,
      SmtEval.native_zplus, native_zneg, SmtEval.native_zneg,
      native_zlt, SmtEval.native_zlt, native_int_pow2,
      native_zexp_total, native_mod_total]
  · have hNegFalse :
        native_zlt (native_zplus w (native_zneg 2)) 0 = false := by
      cases h : native_zlt (native_zplus w (native_zneg 2)) 0 <;>
        simp [h] at hNeg ⊢
    simp [EvaluateProofInternal.eo_sign_extend_low_payload, hNegFalse]

theorem EvaluateProofInternal.sign_payload_eq_uts_core
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true) :
    (if native_zeq
          (native_mod_total
            (native_div_total n (native_int_pow2 (w - 1))) 2)
          1 then
        native_zplus (native_zneg (native_int_pow2 (w - 1)))
          (native_mod_total n (native_int_pow2 (w - 1)))
      else
        native_mod_total n (native_int_pow2 (w - 1))) =
      native_binary_uts w n := by
  by_cases hwpos : 0 < w
  · let p := native_int_pow2 (w - 1)
    let q := native_div_total n p
    let r := native_mod_total n p
    have hpPos : 0 < p := by
      have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
      have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
      have hnot : ¬ w - 1 < 0 := Int.not_lt_of_ge hwp0
      simp [p, native_int_pow2, native_zexp_total, hnot]
      exact Int.pow_pos (by decide)
    have hRange := bitvec_payload_range_of_canonical hw0 hCanon
    have hPow : native_int_pow2 w = 2 * p := by
      simpa [p] using EvaluateProofInternal.native_int_pow2_succ_pred (w := w) hwpos
    have hqNonneg : 0 <= q :=
      Int.ediv_nonneg hRange.1 (Int.le_of_lt hpPos)
    have hqLt2 : q < 2 := by
      have hlt : n < 2 * p := by
        simpa [hPow] using hRange.2
      exact Int.ediv_lt_of_lt_mul hpPos hlt
    have hqCases : q = 0 ∨ q = 1 := by
      by_cases hq0 : q = 0
      · exact Or.inl hq0
      · have hqPos : 0 < q := by
          rcases Int.lt_or_eq_of_le hqNonneg with hlt | heq
          · exact hlt
          · exact False.elim (hq0 heq.symm)
        have hqGe1 : 1 <= q := (Int.add_one_le_iff).mpr hqPos
        have hqLe1 : q <= 1 := Int.le_of_lt_add_one hqLt2
        exact Or.inr (Int.le_antisymm hqLe1 hqGe1)
    have hDivMod : p * q + r = n := by
      simpa [q, r, p, native_div_total, native_mod_total] using
        Int.mul_ediv_add_emod n p
    have hNMod : native_mod_total n p = r := by
      rfl
    rcases hqCases with hq | hq
    · have hSign : native_zeq (native_mod_total q 2) 1 = false := by
        simp [hq, native_zeq, native_mod_total]
      have hnEq : n = r := by
        rw [hq] at hDivMod
        simp at hDivMod
        exact hDivMod.symm
      have hCond :
          native_zeq
              (native_mod_total
                (native_div_total n (native_int_pow2 (w - 1))) 2)
              1 =
            false := by
        simpa [q, p] using hSign
      rw [hCond]
      change native_mod_total n p = native_binary_uts w n
      rw [native_binary_uts]
      change native_mod_total n p =
        native_zplus (native_zmult 2 (native_mod_total n p))
          (native_zneg n)
      rw [hnEq] at hNMod
      rw [hnEq, hNMod]
      simp [native_zplus, native_zmult, native_zneg]
      rw [Int.two_mul]
      rw [Int.add_assoc]
      rw [Int.add_right_neg]
      rw [Int.add_zero]
    · have hSign : native_zeq (native_mod_total q 2) 1 = true := by
        simp [hq, native_zeq, native_mod_total]
      have hnEq : n = p + r := by
        rw [hq] at hDivMod
        simp at hDivMod
        exact hDivMod.symm
      have hCond :
          native_zeq
              (native_mod_total
                (native_div_total n (native_int_pow2 (w - 1))) 2)
              1 =
            true := by
        simpa [q, p] using hSign
      rw [hCond]
      change
        native_zplus (native_zneg p) (native_mod_total n p) =
          native_binary_uts w n
      rw [native_binary_uts]
      change
        native_zplus (native_zneg p) (native_mod_total n p) =
          native_zplus (native_zmult 2 (native_mod_total n p))
            (native_zneg n)
      rw [hnEq] at hNMod
      rw [hnEq, hNMod]
      simp [native_zplus, native_zmult, native_zneg]
      rw [Int.two_mul]
      rw [Int.neg_add]
      rw [Int.add_assoc]
      rw [show r + (-p + -r) = -p by
        calc
          r + (-p + -r) = r + (-r + -p) := by
            rw [Int.add_comm (-p) (-r)]
          _ = r + -r + -p := by
            rw [← Int.add_assoc]
          _ = 0 + -p := by
            rw [Int.add_right_neg]
          _ = -p := by
            rw [Int.zero_add]]
      rw [Int.add_comm]
  · have hw : 0 <= w := by
      simpa [native_zleq, SmtEval.native_zleq] using hw0
    have hwEq : w = 0 :=
      Int.le_antisymm (Int.le_of_not_gt hwpos) hw
    subst w
    have hRange := bitvec_payload_range_of_canonical hw0 hCanon
    have hPow0 : native_int_pow2 0 = 1 := by
      native_decide
    have hnEq : n = 0 := by
      have hlt : n < 1 := by
        simpa [hPow0] using hRange.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange.1
    subst n
    native_decide

theorem EvaluateProofInternal.eo_sign_extend_payload_eq_uts
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true) :
    EvaluateProofInternal.eo_sign_extend_payload w n = native_binary_uts w n := by
  by_cases hwpos : 0 < w
  · have hLow :=
      EvaluateProofInternal.eo_sign_extend_low_payload_eq_mod_of_pos
        (w := w) (n := n) hwpos
    have hMsbNeg :
        native_zlt (native_zplus w (native_zneg 1)) 0 = false := by
      have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
      have hwp0Sub : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
      have hwp0 : 0 <= w + -1 := by
        simpa [Int.sub_eq_add_neg] using hwp0Sub
      have hsimpa :=
        Int.not_lt_of_ge hwp0
      try simp [native_zlt, SmtEval.native_zlt, native_zplus, SmtEval.native_zplus, native_zneg, SmtEval.native_zneg] at hsimpa ⊢
      exact decide_eq_false (Int.not_lt.mpr hsimpa)
    rw [EvaluateProofInternal.eo_sign_extend_payload, EvaluateProofInternal.eo_sign_extend_msb_set, hMsbNeg,
      hLow]
    simpa [native_zplus, SmtEval.native_zplus, native_zneg,
      SmtEval.native_zneg, Int.sub_eq_add_neg] using
      EvaluateProofInternal.sign_payload_eq_uts_core (w := w) (n := n) hw0 hCanon
  · have hw : 0 <= w := by
      simpa [native_zleq, SmtEval.native_zleq] using hw0
    have hwEq : w = 0 :=
      Int.le_antisymm (Int.le_of_not_gt hwpos) hw
    subst w
    have hRange := bitvec_payload_range_of_canonical hw0 hCanon
    have hPow0 : native_int_pow2 0 = 1 := by
      native_decide
    have hnEq : n = 0 := by
      have hlt : n < 1 := by
        simpa [hPow0] using hRange.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange.1
    subst n
    native_decide

theorem EvaluateProofInternal.eo_signed_bv_value_binary_eq_uts
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true) :
    EvaluateProofInternal.eo_signed_bv_value (Term.Binary w n) =
      Term.Numeral (native_binary_uts w n) := by
  dsimp [EvaluateProofInternal.eo_signed_bv_value]
  change
    __eo_ite
        (__eo_eq
          (__eo_extract (Term.Binary w n)
            (Term.Numeral (native_zplus w (native_zneg 1)))
            (Term.Numeral (native_zplus w (native_zneg 1))))
          (Term.Binary 1 1))
        (__eo_add
          (__eo_neg
            (__eo_ite
              (__eo_is_z
                (Term.Numeral (native_zplus w (native_zneg 1))))
              (__eo_ite
                (__eo_is_neg
                  (Term.Numeral (native_zplus w (native_zneg 1))))
                (Term.Numeral 0)
                (__eo_pow (Term.Numeral 2)
                  (Term.Numeral (native_zplus w (native_zneg 1)))))
              (__eo_mk_apply (Term.UOp UserOp.int_pow2)
                (Term.Numeral (native_zplus w (native_zneg 1))))))
          (__eo_to_z
            (__eo_extract (Term.Binary w n) (Term.Numeral 0)
              (Term.Numeral (native_zplus w (native_zneg 2))))))
        (__eo_to_z
          (__eo_extract (Term.Binary w n) (Term.Numeral 0)
            (Term.Numeral (native_zplus w (native_zneg 2))))) =
      Term.Numeral (native_binary_uts w n)
  rw [EvaluateProofInternal.eo_sign_extend_msb_eq, EvaluateProofInternal.eo_sign_extend_low_payload_eq,
    EvaluateProofInternal.eo_int_pow2_literal_eq]
  cases hMsb : EvaluateProofInternal.eo_sign_extend_msb_set w n
  · rw [eo_ite_false]
    exact congrArg Term.Numeral
      (by
        simpa [EvaluateProofInternal.eo_sign_extend_payload, hMsb] using
          EvaluateProofInternal.eo_sign_extend_payload_eq_uts
            (w := w) (n := n) hw0 hCanon)
  · rw [eo_ite_true]
    simp [__eo_add, __eo_neg]
    simpa [EvaluateProofInternal.eo_sign_extend_payload, hMsb] using
      EvaluateProofInternal.eo_sign_extend_payload_eq_uts
        (w := w) (n := n) hw0 hCanon

theorem EvaluateProofInternal.eo_signed_bv_value_eq_stuck_of_not_binary
    (x : Term)
    (hNotBinary : ¬ ∃ w n : native_Int, x = Term.Binary w n)
    (hNotString : ¬ ∃ s : native_String, x = Term.String s) :
    EvaluateProofInternal.eo_signed_bv_value x = Term.Stuck := by
  cases x
  case String s =>
    exact False.elim (hNotString ⟨s, rfl⟩)
  case Binary w n =>
    exact False.elim (hNotBinary ⟨w, n, rfl⟩)
  all_goals
    simp [EvaluateProofInternal.eo_signed_bv_value, __eo_extract, __eo_eq, __eo_ite,
      native_ite, native_teq] at hNotBinary ⊢

theorem EvaluateProofInternal.eo_signed_bv_value_arg_ne_stuck {x : Term} :
    EvaluateProofInternal.eo_signed_bv_value x ≠ Term.Stuck -> x ≠ Term.Stuck := by
  intro h hx
  have hNotBinary : ¬ ∃ w n : native_Int, x = Term.Binary w n := by
    intro hBin
    rcases hBin with ⟨w, n, hEq⟩
    rw [hEq] at hx
    cases hx
  have hNotString : ¬ ∃ s : native_String, x = Term.String s := by
    intro hStr
    rcases hStr with ⟨s, hEq⟩
    rw [hEq] at hx
    cases hx
  exact h (EvaluateProofInternal.eo_signed_bv_value_eq_stuck_of_not_binary x hNotBinary hNotString)

def EvaluateProofInternal.smt_bv_msb_set (w n : native_Int) : native_Bool :=
  native_zeq
    (native_mod_total
      (native_div_total n (native_int_pow2 (w - 1))) 2) 1

theorem EvaluateProofInternal.smtx_model_eval_bvsgt_binary_eq_formula
    (w n1 n2 : native_Int) :
    __smtx_model_eval_bvsgt (SmtValue.Binary w n1) (SmtValue.Binary w n2) =
      SmtValue.Boolean
        (native_or
          (native_and
            (native_not (EvaluateProofInternal.smt_bv_msb_set w n1))
            (EvaluateProofInternal.smt_bv_msb_set w n2))
          (native_and
            (native_veq
              (SmtValue.Boolean (EvaluateProofInternal.smt_bv_msb_set w n1))
              (SmtValue.Boolean (EvaluateProofInternal.smt_bv_msb_set w n2)))
            (native_zlt n2 n1))) := by
  simp [__smtx_model_eval_bvsgt, __smtx_model_eval__,
    __smtx_model_eval_extract, __smtx_model_eval_eq,
    __smtx_model_eval_not, __smtx_model_eval_and,
    __smtx_model_eval_or, __smtx_model_eval_bvugt,
    EvaluateProofInternal.smt_bv_msb_set, __smtx_bv_sizeof_value, native_binary_extract,
    native_zplus, SmtEval.native_zplus, native_zneg,
    SmtEval.native_zneg]
  have hArg : w + -1 = w - 1 := by
    rw [Int.sub_eq_add_neg]
  have hWidth : w + -(w - 1) = 1 := by
    rw [Int.sub_eq_add_neg]
    change w + -(w + -1) = 1
    calc
      w + -(w + -1) = w + (-w + 1) := by
        rw [Int.neg_add, Int.neg_neg]
      _ = w + -w + 1 := by
        rw [← Int.add_assoc]
      _ = 0 + 1 := by
        rw [Int.add_right_neg]
      _ = 1 := by
        rfl
  have hPow1 : native_int_pow2 1 = 2 := by
    native_decide
  simp [hArg, hWidth, hPow1, native_veq, native_zeq,
    SmtEval.native_zeq]

theorem EvaluateProofInternal.smt_bv_msb_false_eq_mod_of_pos
    {w n : native_Int}
    (hwpos : 0 < w)
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true)
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = false) :
    n = native_mod_total n (native_int_pow2 (w - 1)) := by
  let p := native_int_pow2 (w - 1)
  let q := native_div_total n p
  let r := native_mod_total n p
  have hpPos : 0 < p := by
    have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
    have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
    exact EvaluateProofInternal.native_int_pow2_pos_of_nonneg hwp0
  have hRange := bitvec_payload_range_of_canonical hw0 hCanon
  have hPow : native_int_pow2 w = 2 * p := by
    simpa [p] using EvaluateProofInternal.native_int_pow2_succ_pred (w := w) hwpos
  have hqNonneg : 0 <= q :=
    Int.ediv_nonneg hRange.1 (Int.le_of_lt hpPos)
  have hqLt2 : q < 2 := by
    have hlt : n < 2 * p := by
      simpa [hPow] using hRange.2
    exact Int.ediv_lt_of_lt_mul hpPos hlt
  have hqCases : q = 0 ∨ q = 1 := by
    by_cases hq0 : q = 0
    · exact Or.inl hq0
    · have hqPos : 0 < q := by
        rcases Int.lt_or_eq_of_le hqNonneg with hlt | heq
        · exact hlt
        · exact False.elim (hq0 heq.symm)
      have hqGe1 : 1 <= q := (Int.add_one_le_iff).mpr hqPos
      have hqLe1 : q <= 1 := Int.le_of_lt_add_one hqLt2
      exact Or.inr (Int.le_antisymm hqLe1 hqGe1)
  have hDivMod : p * q + r = n := by
    simpa [q, r, p, native_div_total, native_mod_total] using
      Int.mul_ediv_add_emod n p
  rcases hqCases with hq | hq
  · have hnEq : n = r := by
      rw [hq] at hDivMod
      simp at hDivMod
      exact hDivMod.symm
    simpa [r, p] using hnEq
  · have hSignTrue : EvaluateProofInternal.smt_bv_msb_set w n = true := by
      dsimp [EvaluateProofInternal.smt_bv_msb_set, q, p] at hq ⊢
      rw [hq]
      simp [native_mod_total, native_zeq, SmtEval.native_zeq]
    rw [hSign] at hSignTrue
    cases hSignTrue

theorem EvaluateProofInternal.smt_bv_msb_true_eq_pow_add_mod_of_pos
    {w n : native_Int}
    (hwpos : 0 < w)
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true)
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = true) :
    n =
      native_int_pow2 (w - 1) +
        native_mod_total n (native_int_pow2 (w - 1)) := by
  let p := native_int_pow2 (w - 1)
  let q := native_div_total n p
  let r := native_mod_total n p
  have hpPos : 0 < p := by
    have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
    have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
    exact EvaluateProofInternal.native_int_pow2_pos_of_nonneg hwp0
  have hRange := bitvec_payload_range_of_canonical hw0 hCanon
  have hPow : native_int_pow2 w = 2 * p := by
    simpa [p] using EvaluateProofInternal.native_int_pow2_succ_pred (w := w) hwpos
  have hqNonneg : 0 <= q :=
    Int.ediv_nonneg hRange.1 (Int.le_of_lt hpPos)
  have hqLt2 : q < 2 := by
    have hlt : n < 2 * p := by
      simpa [hPow] using hRange.2
    exact Int.ediv_lt_of_lt_mul hpPos hlt
  have hqCases : q = 0 ∨ q = 1 := by
    by_cases hq0 : q = 0
    · exact Or.inl hq0
    · have hqPos : 0 < q := by
        rcases Int.lt_or_eq_of_le hqNonneg with hlt | heq
        · exact hlt
        · exact False.elim (hq0 heq.symm)
      have hqGe1 : 1 <= q := (Int.add_one_le_iff).mpr hqPos
      have hqLe1 : q <= 1 := Int.le_of_lt_add_one hqLt2
      exact Or.inr (Int.le_antisymm hqLe1 hqGe1)
  have hDivMod : p * q + r = n := by
    simpa [q, r, p, native_div_total, native_mod_total] using
      Int.mul_ediv_add_emod n p
  rcases hqCases with hq | hq
  · have hSignFalse : EvaluateProofInternal.smt_bv_msb_set w n = false := by
      dsimp [EvaluateProofInternal.smt_bv_msb_set, q, p] at hq ⊢
      rw [hq]
      simp [native_mod_total, native_zeq, SmtEval.native_zeq]
    rw [hSign] at hSignFalse
    cases hSignFalse
  · have hnEq : n = p + r := by
      rw [hq] at hDivMod
      simp at hDivMod
      exact hDivMod.symm
    simpa [p, r] using hnEq

theorem EvaluateProofInternal.native_mod_pow2_pred_range_of_pos
    {w n : native_Int} (hwpos : 0 < w) :
    0 <= native_mod_total n (native_int_pow2 (w - 1)) ∧
      native_mod_total n (native_int_pow2 (w - 1)) <
        native_int_pow2 (w - 1) := by
  have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
  have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
  have hpPos : 0 < native_int_pow2 (w - 1) :=
    EvaluateProofInternal.native_int_pow2_pos_of_nonneg hwp0
  constructor
  · simpa [native_mod_total] using
      Int.emod_nonneg n (Int.ne_of_gt hpPos)
  · simpa [native_mod_total] using
      Int.emod_lt_of_pos n hpPos

theorem EvaluateProofInternal.smt_bvsgt_formula_eq_signed_gt
    {w n1 n2 : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon1 :
      native_zeq n1
          (native_mod_total n1 (native_int_pow2 w)) =
        true)
    (hCanon2 :
      native_zeq n2
          (native_mod_total n2 (native_int_pow2 w)) =
        true) :
    native_or
        (native_and
          (native_not (EvaluateProofInternal.smt_bv_msb_set w n1))
          (EvaluateProofInternal.smt_bv_msb_set w n2))
        (native_and
          (native_veq
            (SmtValue.Boolean (EvaluateProofInternal.smt_bv_msb_set w n1))
            (SmtValue.Boolean (EvaluateProofInternal.smt_bv_msb_set w n2)))
          (native_zlt n2 n1)) =
      native_zlt (native_binary_uts w n2) (native_binary_uts w n1) := by
  by_cases hwpos : 0 < w
  · let p := native_int_pow2 (w - 1)
    let r1 := native_mod_total n1 p
    let r2 := native_mod_total n2 p
    have hUts1 :
        (if EvaluateProofInternal.smt_bv_msb_set w n1 then
            native_zplus (native_zneg p) r1
          else r1) =
          native_binary_uts w n1 := by
      have hsimpa :=
        EvaluateProofInternal.sign_payload_eq_uts_core (w := w) (n := n1) hw0 hCanon1
      try simp [EvaluateProofInternal.smt_bv_msb_set, p, r1, Int.sub_eq_add_neg] at hsimpa ⊢
      exact hsimpa
    have hUts2 :
        (if EvaluateProofInternal.smt_bv_msb_set w n2 then
            native_zplus (native_zneg p) r2
          else r2) =
          native_binary_uts w n2 := by
      have hsimpa :=
        EvaluateProofInternal.sign_payload_eq_uts_core (w := w) (n := n2) hw0 hCanon2
      try simp [EvaluateProofInternal.smt_bv_msb_set, p, r2, Int.sub_eq_add_neg] at hsimpa ⊢
      exact hsimpa
    have hr1Range :
        0 <= r1 ∧ r1 < p := by
      simpa [r1, p] using
        EvaluateProofInternal.native_mod_pow2_pred_range_of_pos (w := w) (n := n1) hwpos
    have hr2Range :
        0 <= r2 ∧ r2 < p := by
      simpa [r2, p] using
        EvaluateProofInternal.native_mod_pow2_pred_range_of_pos (w := w) (n := n2) hwpos
    cases hSign1 : EvaluateProofInternal.smt_bv_msb_set w n1 <;>
      cases hSign2 : EvaluateProofInternal.smt_bv_msb_set w n2
    · have hN1 :
          n1 = r1 :=
        EvaluateProofInternal.smt_bv_msb_false_eq_mod_of_pos
          (w := w) (n := n1) hwpos hw0 hCanon1 hSign1
      have hN2 :
          n2 = r2 :=
        EvaluateProofInternal.smt_bv_msb_false_eq_mod_of_pos
          (w := w) (n := n2) hwpos hw0 hCanon2 hSign2
      rw [← hUts1, ← hUts2, hSign1, hSign2, hN1, hN2]
      simp
      simp [native_or, native_and, native_not, native_veq]
    · have hN1 :
          n1 = r1 :=
        EvaluateProofInternal.smt_bv_msb_false_eq_mod_of_pos
          (w := w) (n := n1) hwpos hw0 hCanon1 hSign1
      have hr1Nonneg : 0 <= r1 := hr1Range.1
      have hr2Lt : r2 < p := hr2Range.2
      have hLt : native_zplus (native_zneg p) r2 < r1 := by
        change -p + r2 < r1
        have hNeg : -p + r2 < 0 := by
          have hAdd := Int.add_lt_add_right hr2Lt (-p)
          simpa [Int.add_comm, Int.add_right_neg] using hAdd
        exact Int.lt_of_lt_of_le hNeg hr1Nonneg
      rw [← hUts1, ← hUts2, hSign1, hSign2, hN1]
      simp [native_or, native_and, native_not, native_veq,
        native_zlt, SmtEval.native_zlt, hLt]
    · have hN2 :
          n2 = r2 :=
        EvaluateProofInternal.smt_bv_msb_false_eq_mod_of_pos
          (w := w) (n := n2) hwpos hw0 hCanon2 hSign2
      have hr2Nonneg : 0 <= r2 := hr2Range.1
      have hr1Lt : r1 < p := hr1Range.2
      have hNotLt : ¬ r2 < native_zplus (native_zneg p) r1 := by
        change ¬ r2 < -p + r1
        intro hLt
        have hNeg : -p + r1 < 0 := by
          have hAdd := Int.add_lt_add_right hr1Lt (-p)
          simpa [Int.add_comm, Int.add_right_neg] using hAdd
        exact (Int.not_lt_of_ge hr2Nonneg) (Int.lt_trans hLt hNeg)
      rw [← hUts1, ← hUts2, hSign1, hSign2, hN2]
      simp [native_or, native_and, native_not, native_veq,
        native_zlt, SmtEval.native_zlt, hNotLt]
    · have hN1 :
          n1 = p + r1 :=
        EvaluateProofInternal.smt_bv_msb_true_eq_pow_add_mod_of_pos
          (w := w) (n := n1) hwpos hw0 hCanon1 hSign1
      have hN2 :
          n2 = p + r2 :=
        EvaluateProofInternal.smt_bv_msb_true_eq_pow_add_mod_of_pos
          (w := w) (n := n2) hwpos hw0 hCanon2 hSign2
      have hCmp :
          native_zlt (p + r2) (p + r1) =
            native_zlt
              (native_zplus (native_zneg p) r2)
              (native_zplus (native_zneg p) r1) := by
        simp [native_zlt, SmtEval.native_zlt, native_zplus,
          SmtEval.native_zplus, native_zneg, SmtEval.native_zneg]
      rw [← hUts1, ← hUts2, hSign1, hSign2, hN1, hN2, hCmp]
      simp [native_or, native_and, native_not, native_veq]
  · have hw : 0 <= w := by
      simpa [native_zleq, SmtEval.native_zleq] using hw0
    have hwEq : w = 0 :=
      Int.le_antisymm (Int.le_of_not_gt hwpos) hw
    subst w
    have hRange1 := bitvec_payload_range_of_canonical hw0 hCanon1
    have hRange2 := bitvec_payload_range_of_canonical hw0 hCanon2
    have hPow0 : native_int_pow2 0 = 1 := by
      native_decide
    have hn1Eq : n1 = 0 := by
      have hlt : n1 < 1 := by
        simpa [hPow0] using hRange1.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange1.1
    have hn2Eq : n2 = 0 := by
      have hlt : n2 < 1 := by
        simpa [hPow0] using hRange2.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange2.1
    subst n1
    subst n2
    native_decide

theorem EvaluateProofInternal.smtx_model_eval_bvsgt_binary_eq_uts
    {w n1 n2 : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon1 :
      native_zeq n1
          (native_mod_total n1 (native_int_pow2 w)) =
        true)
    (hCanon2 :
      native_zeq n2
          (native_mod_total n2 (native_int_pow2 w)) =
        true) :
    __smtx_model_eval_bvsgt (SmtValue.Binary w n1) (SmtValue.Binary w n2) =
      SmtValue.Boolean
        (native_zlt (native_binary_uts w n2)
          (native_binary_uts w n1)) := by
  rw [EvaluateProofInternal.smtx_model_eval_bvsgt_binary_eq_formula]
  rw [EvaluateProofInternal.smt_bvsgt_formula_eq_signed_gt hw0 hCanon1 hCanon2]

theorem EvaluateProofInternal.native_binary_uts_eq_iff_canonical
    {w n1 n2 : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon1 :
      native_zeq n1
          (native_mod_total n1 (native_int_pow2 w)) =
        true)
    (hCanon2 :
      native_zeq n2
          (native_mod_total n2 (native_int_pow2 w)) =
        true) :
    native_binary_uts w n1 = native_binary_uts w n2 ↔ n1 = n2 := by
  by_cases hwpos : 0 < w
  · let p := native_int_pow2 (w - 1)
    let r1 := native_mod_total n1 p
    let r2 := native_mod_total n2 p
    have hUts1 :
        (if EvaluateProofInternal.smt_bv_msb_set w n1 then
            native_zplus (native_zneg p) r1
          else r1) =
          native_binary_uts w n1 := by
      have hsimpa :=
        EvaluateProofInternal.sign_payload_eq_uts_core (w := w) (n := n1) hw0 hCanon1
      try simp [EvaluateProofInternal.smt_bv_msb_set, p, r1, Int.sub_eq_add_neg] at hsimpa ⊢
      exact hsimpa
    have hUts2 :
        (if EvaluateProofInternal.smt_bv_msb_set w n2 then
            native_zplus (native_zneg p) r2
          else r2) =
          native_binary_uts w n2 := by
      have hsimpa :=
        EvaluateProofInternal.sign_payload_eq_uts_core (w := w) (n := n2) hw0 hCanon2
      try simp [EvaluateProofInternal.smt_bv_msb_set, p, r2, Int.sub_eq_add_neg] at hsimpa ⊢
      exact hsimpa
    have hr1Range :
        0 <= r1 ∧ r1 < p := by
      simpa [r1, p] using
        EvaluateProofInternal.native_mod_pow2_pred_range_of_pos (w := w) (n := n1) hwpos
    have hr2Range :
        0 <= r2 ∧ r2 < p := by
      simpa [r2, p] using
        EvaluateProofInternal.native_mod_pow2_pred_range_of_pos (w := w) (n := n2) hwpos
    cases hSign1 : EvaluateProofInternal.smt_bv_msb_set w n1 <;>
      cases hSign2 : EvaluateProofInternal.smt_bv_msb_set w n2
    · have hN1 :
          n1 = r1 :=
        EvaluateProofInternal.smt_bv_msb_false_eq_mod_of_pos
          (w := w) (n := n1) hwpos hw0 hCanon1 hSign1
      have hN2 :
          n2 = r2 :=
        EvaluateProofInternal.smt_bv_msb_false_eq_mod_of_pos
          (w := w) (n := n2) hwpos hw0 hCanon2 hSign2
      rw [← hUts1, ← hUts2, hSign1, hSign2, hN1, hN2]
      simp
    · have hN1 :
          n1 = r1 :=
        EvaluateProofInternal.smt_bv_msb_false_eq_mod_of_pos
          (w := w) (n := n1) hwpos hw0 hCanon1 hSign1
      have hN2 :
          n2 = p + r2 :=
        EvaluateProofInternal.smt_bv_msb_true_eq_pow_add_mod_of_pos
          (w := w) (n := n2) hwpos hw0 hCanon2 hSign2
      rw [← hUts1, ← hUts2, hSign1, hSign2, hN1, hN2]
      constructor
      · intro hEq
        simp at hEq
        have hNeg : native_zplus (native_zneg p) r2 < 0 := by
          change -p + r2 < 0
          have hAdd := Int.add_lt_add_right hr2Range.2 (-p)
          simpa [Int.add_comm, Int.add_right_neg] using hAdd
        rw [← hEq] at hNeg
        exact False.elim ((Int.not_lt_of_ge hr1Range.1) hNeg)
      · intro hEq
        have hGe : p <= p + r2 :=
          Int.le_add_of_nonneg_right hr2Range.1
        have hLt : p + r2 < p := by
          rw [← hEq]
          exact hr1Range.2
        exact False.elim ((Int.not_lt_of_ge hGe) hLt)
    · have hN1 :
          n1 = p + r1 :=
        EvaluateProofInternal.smt_bv_msb_true_eq_pow_add_mod_of_pos
          (w := w) (n := n1) hwpos hw0 hCanon1 hSign1
      have hN2 :
          n2 = r2 :=
        EvaluateProofInternal.smt_bv_msb_false_eq_mod_of_pos
          (w := w) (n := n2) hwpos hw0 hCanon2 hSign2
      rw [← hUts1, ← hUts2, hSign1, hSign2, hN1, hN2]
      constructor
      · intro hEq
        simp at hEq
        have hNeg : native_zplus (native_zneg p) r1 < 0 := by
          change -p + r1 < 0
          have hAdd := Int.add_lt_add_right hr1Range.2 (-p)
          simpa [Int.add_comm, Int.add_right_neg] using hAdd
        rw [hEq] at hNeg
        exact False.elim ((Int.not_lt_of_ge hr2Range.1) hNeg)
      · intro hEq
        have hGe : p <= p + r1 :=
          Int.le_add_of_nonneg_right hr1Range.1
        have hLt : p + r1 < p := by
          rw [hEq]
          exact hr2Range.2
        exact False.elim ((Int.not_lt_of_ge hGe) hLt)
    · have hN1 :
          n1 = p + r1 :=
        EvaluateProofInternal.smt_bv_msb_true_eq_pow_add_mod_of_pos
          (w := w) (n := n1) hwpos hw0 hCanon1 hSign1
      have hN2 :
          n2 = p + r2 :=
        EvaluateProofInternal.smt_bv_msb_true_eq_pow_add_mod_of_pos
          (w := w) (n := n2) hwpos hw0 hCanon2 hSign2
      rw [← hUts1, ← hUts2, hSign1, hSign2, hN1, hN2]
      simp [native_zplus, native_zneg]
  · have hw : 0 <= w := by
      simpa [native_zleq, SmtEval.native_zleq] using hw0
    have hwEq : w = 0 :=
      Int.le_antisymm (Int.le_of_not_gt hwpos) hw
    subst w
    have hRange1 := bitvec_payload_range_of_canonical hw0 hCanon1
    have hRange2 := bitvec_payload_range_of_canonical hw0 hCanon2
    have hPow0 : native_int_pow2 0 = 1 := by
      native_decide
    have hn1Eq : n1 = 0 := by
      have hlt : n1 < 1 := by
        simpa [hPow0] using hRange1.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange1.1
    have hn2Eq : n2 = 0 := by
      have hlt : n2 < 1 := by
        simpa [hPow0] using hRange2.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange2.1
    subst n1
    subst n2
    native_decide

theorem EvaluateProofInternal.native_veq_binary_eq_signed_teq_of_canonical
    {w n1 n2 : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon1 :
      native_zeq n1
          (native_mod_total n1 (native_int_pow2 w)) =
        true)
    (hCanon2 :
      native_zeq n2
          (native_mod_total n2 (native_int_pow2 w)) =
        true) :
    native_veq (SmtValue.Binary w n1) (SmtValue.Binary w n2) =
      native_teq (Term.Numeral (native_binary_uts w n2))
        (Term.Numeral (native_binary_uts w n1)) := by
  have hIff :=
    EvaluateProofInternal.native_binary_uts_eq_iff_canonical
      (w := w) (n1 := n1) (n2 := n2) hw0 hCanon1 hCanon2
  by_cases hEq : n1 = n2
  · subst n2
    simp [native_veq, native_teq]
  · have hUtsNe :
        native_binary_uts w n2 ≠ native_binary_uts w n1 := by
      intro hUts
      exact hEq (hIff.mp hUts.symm)
    simp [native_veq, native_teq, hEq, hUtsNe]

theorem EvaluateProofInternal.smtx_model_eval_bvsge_binary_eq_uts
    {w n1 n2 : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon1 :
      native_zeq n1
          (native_mod_total n1 (native_int_pow2 w)) =
        true)
    (hCanon2 :
      native_zeq n2
          (native_mod_total n2 (native_int_pow2 w)) =
        true) :
    __smtx_model_eval_bvsge (SmtValue.Binary w n1) (SmtValue.Binary w n2) =
      SmtValue.Boolean
        (native_or
          (native_zlt (native_binary_uts w n2)
            (native_binary_uts w n1))
          (native_teq (Term.Numeral (native_binary_uts w n2))
            (Term.Numeral (native_binary_uts w n1)))) := by
  rw [__smtx_model_eval_bvsge]
  rw [EvaluateProofInternal.smtx_model_eval_bvsgt_binary_eq_uts hw0 hCanon1 hCanon2]
  simp [__smtx_model_eval_or, __smtx_model_eval_eq]
  rw [EvaluateProofInternal.native_veq_binary_eq_signed_teq_of_canonical
    hw0 hCanon1 hCanon2]

theorem EvaluateProofInternal.native_teq_term_numeral_comm
    (n1 n2 : native_Int) :
    native_teq (Term.Numeral n1) (Term.Numeral n2) =
      native_teq (Term.Numeral n2) (Term.Numeral n1) := by
  by_cases hEq : n1 = n2
  · subst n2
    simp [native_teq]
  · have hEq' : n2 ≠ n1 := by
      intro h
      exact hEq h.symm
    simp [native_teq, hEq, hEq']

theorem EvaluateProofInternal.smtx_model_eval_bvsle_binary_eq_uts
    {w n1 n2 : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon1 :
      native_zeq n1
          (native_mod_total n1 (native_int_pow2 w)) =
        true)
    (hCanon2 :
      native_zeq n2
          (native_mod_total n2 (native_int_pow2 w)) =
        true) :
    __smtx_model_eval_bvsle (SmtValue.Binary w n1) (SmtValue.Binary w n2) =
      SmtValue.Boolean
        (native_or
          (native_zlt (native_binary_uts w n1)
            (native_binary_uts w n2))
          (native_teq (Term.Numeral (native_binary_uts w n2))
            (Term.Numeral (native_binary_uts w n1)))) := by
  rw [__smtx_model_eval_bvsle]
  rw [EvaluateProofInternal.smtx_model_eval_bvsge_binary_eq_uts
    (w := w) (n1 := n2) (n2 := n1) hw0 hCanon2 hCanon1]
  rw [EvaluateProofInternal.native_teq_term_numeral_comm]

def EvaluateProofInternal.eo_eval_bvashr_rhs (a b : Term) : Term :=
  let runAmt := __eo_to_z (__run_evaluate b)
  let runA := __run_evaluate a
  let powAmt :=
    __eo_ite (__eo_is_z runAmt)
      (__eo_ite (__eo_is_neg runAmt) (Term.Numeral 0)
        (__eo_pow (Term.Numeral 2) runAmt))
      (__eo_mk_apply (Term.UOp UserOp.int_pow2) runAmt)
  __eo_to_bin (__bv_bitwidth (__eo_typeof a))
    (__eo_zdiv (EvaluateProofInternal.eo_signed_bv_value runA) powAmt)

theorem EvaluateProofInternal.native_mod_two_eq_zero_of_ne_one
    (x : native_Int)
    (hNeOne :
      native_zeq (native_mod_total x 2) 1 = false) :
    native_mod_total x 2 = 0 := by
  let r := native_mod_total x 2
  have hrNonneg : 0 <= r := by
    simpa [r, native_mod_total] using
      Int.emod_nonneg x (by decide : (2 : Int) ≠ 0)
  have hrLt : r < 2 := by
    simpa [r, native_mod_total] using
      Int.emod_lt_of_pos x (by decide : 0 < (2 : Int))
  have hrNeOne : r ≠ 1 := by
    intro h
    have hTrue : native_zeq r 1 = true := by
      simp [native_zeq, SmtEval.native_zeq, h]
    rw [show native_zeq r 1 =
        native_zeq (native_mod_total x 2) 1 by rfl] at hTrue
    rw [hTrue] at hNeOne
    cases hNeOne
  have hrLeOne : r <= 1 := Int.le_of_lt_add_one hrLt
  rcases Int.lt_or_eq_of_le hrLeOne with hrLtOne | hrEqOne
  · have hrLeZero : r <= 0 := Int.le_of_lt_add_one hrLtOne
    exact Int.le_antisymm hrLeZero hrNonneg
  · exact False.elim (hrNeOne hrEqOne)

theorem EvaluateProofInternal.native_mod_two_eq_one_of_eq_one
    (x : native_Int)
    (hOne :
      native_zeq (native_mod_total x 2) 1 = true) :
    native_mod_total x 2 = 1 := by
  simpa [native_zeq, SmtEval.native_zeq] using hOne

theorem EvaluateProofInternal.native_veq_bvashr_msb_zero_of_false
    (w n : native_Int)
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = false) :
    native_veq
        (SmtValue.Binary 1
          (native_mod_total
            (native_div_total n (native_int_pow2 (w - 1))) 2))
        (SmtValue.Binary 1 0) =
      true := by
  have hZero :=
    EvaluateProofInternal.native_mod_two_eq_zero_of_ne_one
      (native_div_total n (native_int_pow2 (w - 1))) hSign
  rw [hZero]
  simp [native_veq]

theorem EvaluateProofInternal.native_veq_bvashr_msb_zero_of_true
    (w n : native_Int)
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = true) :
    native_veq
        (SmtValue.Binary 1
          (native_mod_total
            (native_div_total n (native_int_pow2 (w - 1))) 2))
        (SmtValue.Binary 1 0) =
      false := by
  have hOne :=
    EvaluateProofInternal.native_mod_two_eq_one_of_eq_one
      (native_div_total n (native_int_pow2 (w - 1))) hSign
  rw [hOne]
  simp [native_veq]

theorem EvaluateProofInternal.smtx_model_eval_bvashr_binary_eq_lshr_of_msb_false
    {w n s : native_Int}
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = false) :
    __smtx_model_eval_bvashr (SmtValue.Binary w n) (SmtValue.Binary w s) =
      SmtValue.Binary w
        (native_mod_total
          (native_div_total n (native_int_pow2 s))
          (native_int_pow2 w)) := by
  have hArg :
      native_zplus w (native_zneg 1) = w - 1 := by
    change w + -1 = w - 1
    rw [Int.sub_eq_add_neg]
  have hWidth :
      native_zplus
          (native_zplus (w - 1) 1)
          (native_zneg (w - 1)) =
        1 := by
    change (w - 1) + 1 + -(w - 1) = 1
    calc
      (w - 1) + 1 + -(w - 1) = w + -(w - 1) := by
        have hSub : (w - 1) + 1 = w := by
          rw [Int.sub_eq_add_neg]
          rw [Int.add_assoc]
          have hConst : (-1 : Int) + 1 = 0 := by native_decide
          rw [hConst, Int.add_zero]
        rw [hSub]
      _ = 1 := by
        rw [Int.sub_eq_add_neg]
        change w + -(w + -1) = 1
        rw [Int.neg_add, Int.neg_neg]
        rw [← Int.add_assoc]
        rw [Int.add_right_neg, Int.zero_add]
  have hPow1 : native_int_pow2 1 = 2 := by
    native_decide
  have hMsbZero :=
    EvaluateProofInternal.native_veq_bvashr_msb_zero_of_false w n hSign
  simp [__smtx_model_eval_bvashr, __smtx_model_eval__,
    __smtx_model_eval_extract, __smtx_model_eval_eq,
    __smtx_model_eval_ite, __smtx_model_eval_bvlshr,
    __smtx_bv_sizeof_value, native_binary_extract, hArg, hWidth,
    hPow1, hMsbZero]

theorem EvaluateProofInternal.smtx_model_eval_bvashr_binary_eq_not_lshr_not_of_msb_true
    {w n s : native_Int}
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = true) :
    __smtx_model_eval_bvashr (SmtValue.Binary w n) (SmtValue.Binary w s) =
      SmtValue.Binary w
        (native_mod_total
          (native_binary_not w
            (native_mod_total
              (native_div_total
                (native_mod_total (native_binary_not w n)
                  (native_int_pow2 w))
                (native_int_pow2 s))
              (native_int_pow2 w)))
          (native_int_pow2 w)) := by
  have hArg :
      native_zplus w (native_zneg 1) = w - 1 := by
    change w + -1 = w - 1
    rw [Int.sub_eq_add_neg]
  have hWidth :
      native_zplus
          (native_zplus (w - 1) 1)
          (native_zneg (w - 1)) =
        1 := by
    change (w - 1) + 1 + -(w - 1) = 1
    calc
      (w - 1) + 1 + -(w - 1) = w + -(w - 1) := by
        have hSub : (w - 1) + 1 = w := by
          rw [Int.sub_eq_add_neg]
          rw [Int.add_assoc]
          have hConst : (-1 : Int) + 1 = 0 := by native_decide
          rw [hConst, Int.add_zero]
        rw [hSub]
      _ = 1 := by
        rw [Int.sub_eq_add_neg]
        change w + -(w + -1) = 1
        rw [Int.neg_add, Int.neg_neg]
        rw [← Int.add_assoc]
        rw [Int.add_right_neg, Int.zero_add]
  have hPow1 : native_int_pow2 1 = 2 := by
    native_decide
  have hMsbOne :=
    EvaluateProofInternal.native_veq_bvashr_msb_zero_of_true w n hSign
  simp [__smtx_model_eval_bvashr, __smtx_model_eval__,
    __smtx_model_eval_extract, __smtx_model_eval_eq,
    __smtx_model_eval_ite, __smtx_model_eval_bvlshr,
    __smtx_model_eval_bvnot, __smtx_bv_sizeof_value,
    native_binary_extract, hArg, hWidth, hPow1, hMsbOne]

theorem EvaluateProofInternal.native_binary_uts_eq_self_of_msb_false
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true)
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = false) :
    native_binary_uts w n = n := by
  by_cases hwpos : 0 < w
  · let p := native_int_pow2 (w - 1)
    have hN : n = native_mod_total n p := by
      simpa [EvaluateProofInternal.smt_bv_msb_set, p, Int.sub_eq_add_neg] using
        EvaluateProofInternal.smt_bv_msb_false_eq_mod_of_pos
          (w := w) (n := n) hwpos hw0 hCanon hSign
    rw [native_binary_uts]
    change native_zplus
        (native_zmult 2
          (native_mod_total n
            (native_int_pow2 (native_zplus w (native_zneg 1)))))
        (native_zneg n) = n
    have hpEq :
        native_int_pow2 (native_zplus w (native_zneg 1)) = p := by
      simp [p, native_zplus, SmtEval.native_zplus, native_zneg,
        SmtEval.native_zneg, Int.sub_eq_add_neg]
    rw [hpEq]
    rw [← hN]
    simp [native_zplus, native_zmult, native_zneg]
    rw [Int.two_mul, Int.add_assoc, Int.add_right_neg, Int.add_zero]
  · have hw : 0 <= w := by
      simpa [native_zleq, SmtEval.native_zleq] using hw0
    have hwEq : w = 0 :=
      Int.le_antisymm (Int.le_of_not_gt hwpos) hw
    subst w
    have hRange := bitvec_payload_range_of_canonical hw0 hCanon
    have hPow0 : native_int_pow2 0 = 1 := by
      native_decide
    have hnEq : n = 0 := by
      have hlt : n < 1 := by
        simpa [hPow0] using hRange.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange.1
    subst n
    native_decide

theorem EvaluateProofInternal.native_binary_not_eq_pow_sub_succ
    (w n : native_Int) :
    native_binary_not w n =
      native_int_pow2 w - (n + 1) := by
  simp [native_binary_not, native_zplus, native_zneg,
    Int.sub_eq_add_neg]

theorem EvaluateProofInternal.native_binary_not_range_of_canonical
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true) :
    0 <= native_binary_not w n ∧
      native_binary_not w n < native_int_pow2 w := by
  have hRange := bitvec_payload_range_of_canonical hw0 hCanon
  have hRaw := EvaluateProofInternal.native_binary_not_eq_pow_sub_succ w n
  constructor
  · rw [hRaw]
    exact Int.sub_nonneg.mpr (Int.add_one_le_of_lt hRange.2)
  · rw [hRaw]
    exact Int.sub_lt_self _ (Int.lt_add_one_of_le hRange.1)

theorem EvaluateProofInternal.native_binary_not_mod_self_of_canonical
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true) :
    native_mod_total (native_binary_not w n) (native_int_pow2 w) =
      native_binary_not w n := by
  have hRange := EvaluateProofInternal.native_binary_not_range_of_canonical
    (w := w) (n := n) hw0 hCanon
  simpa [native_mod_total] using
    Int.emod_eq_of_lt hRange.1 hRange.2

theorem EvaluateProofInternal.smt_bv_msb_true_width_pos
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true)
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = true) :
    0 < w := by
  by_cases hwpos : 0 < w
  · exact hwpos
  · have hw : 0 <= w := by
      simpa [native_zleq, SmtEval.native_zleq] using hw0
    have hwEq : w = 0 :=
      Int.le_antisymm (Int.le_of_not_gt hwpos) hw
    subst w
    have hRange := bitvec_payload_range_of_canonical hw0 hCanon
    have hPow0 : native_int_pow2 0 = 1 := by
      native_decide
    have hnEq : n = 0 := by
      have hlt : n < 1 := by
        simpa [hPow0] using hRange.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange.1
    subst n
    have hSignFalse : EvaluateProofInternal.smt_bv_msb_set 0 0 = false := by
      native_decide
    rw [hSignFalse] at hSign
    cases hSign

theorem EvaluateProofInternal.native_binary_uts_eq_sub_pow_of_msb_true
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true)
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = true) :
    native_binary_uts w n = n - native_int_pow2 w := by
  have hwpos :=
    EvaluateProofInternal.smt_bv_msb_true_width_pos
      (w := w) (n := n) hw0 hCanon hSign
  let p := native_int_pow2 (w - 1)
  let r := native_mod_total n p
  have hN : n = p + r := by
    simpa [EvaluateProofInternal.smt_bv_msb_set, p, r, Int.sub_eq_add_neg] using
      EvaluateProofInternal.smt_bv_msb_true_eq_pow_add_mod_of_pos
        (w := w) (n := n) hwpos hw0 hCanon hSign
  have hPow : native_int_pow2 w = 2 * p := by
    simpa [p] using EvaluateProofInternal.native_int_pow2_succ_pred (w := w) hwpos
  have hpEq :
      native_int_pow2 (native_zplus w (native_zneg 1)) = p := by
    simp [p, native_zplus, SmtEval.native_zplus, native_zneg,
      SmtEval.native_zneg, Int.sub_eq_add_neg]
  rw [native_binary_uts]
  change
    native_zplus
        (native_zmult 2
          (native_mod_total n
            (native_int_pow2 (native_zplus w (native_zneg 1)))))
        (native_zneg n) =
      n - native_int_pow2 w
  rw [hpEq]
  change 2 * r + -n = n - native_int_pow2 w
  rw [hN, hPow]
  change 2 * r + -(p + r) = p + r - 2 * p
  calc
    2 * r + -(p + r) = r + -p := by
      rw [Int.two_mul, Int.neg_add]
      calc
        r + r + (-p + -r) = r + r + (-r + -p) := by
          rw [Int.add_comm (-p) (-r)]
        _ = r + r + -r + -p := by
          rw [← Int.add_assoc]
        _ = r + -p := by
          rw [show r + r + -r = r by
            rw [Int.add_assoc, Int.add_right_neg, Int.add_zero]]
    _ = p + r - 2 * p := by
      rw [Int.two_mul]
      change r + -p = p + r - (p + p)
      rw [Int.sub_eq_add_neg, Int.neg_add]
      symm
      calc
        p + r + (-p + -p) = p + r + -p + -p := by
          rw [← Int.add_assoc]
        _ = r + -p := by
          rw [show p + r + -p = r by
            calc
              p + r + -p = p + (r + -p) := by rw [Int.add_assoc]
              _ = p + (-p + r) := by rw [Int.add_comm r (-p)]
              _ = p + -p + r := by rw [← Int.add_assoc]
              _ = r := by rw [Int.add_right_neg, Int.zero_add]]
        _ = r + -p := rfl

theorem EvaluateProofInternal.native_int_pow2_ge_one_of_nonneg
    {s : native_Int} (hs0 : 0 <= s) :
    1 <= native_int_pow2 s := by
  have hpos := EvaluateProofInternal.native_int_pow2_pos_of_nonneg hs0
  exact (Int.add_one_le_iff).mpr hpos

theorem EvaluateProofInternal.native_neg_succ_div_pow2_eq_neg_div_succ
    {m s : native_Int}
    (hm0 : 0 <= m)
    (hs0 : 0 <= s) :
    native_div_total (-(m + 1)) (native_int_pow2 s) =
      -(native_div_total m (native_int_pow2 s) + 1) := by
  let d := native_int_pow2 s
  let q := native_div_total m d
  let r := native_mod_total m d
  have hdPos : 0 < d := by
    dsimp [d]
    exact EvaluateProofInternal.native_int_pow2_pos_of_nonneg hs0
  have hdNe : d ≠ 0 := Int.ne_of_gt hdPos
  have hDivMod : d * q + r = m := by
    simpa [q, r, d, native_div_total, native_mod_total] using
      Int.mul_ediv_add_emod m d
  have hr0 : 0 <= r := by
    simpa [r, native_mod_total] using
      Int.emod_nonneg m hdNe
  have hrlt : r < d := by
    simpa [r, native_mod_total] using
      Int.emod_lt_of_pos m hdPos
  have hUpper :
      native_div_total (-(m + 1)) d <= -(q + 1) := by
    rw [native_div_total]
    rw [(Int.ediv_le_iff_le_mul (k := d)
      (x := -(m + 1)) (y := -(q + 1)) hdPos)]
    have hEq : m + 1 = d * q + (r + 1) := by
      rw [← hDivMod]
      rw [← Int.add_assoc]
    calc
      -(m + 1) = -(d * q + (r + 1)) := by rw [hEq]
      _ = -(d * q) + -(r + 1) := by rw [Int.neg_add]
      _ < -(d * q) := by
        have hr1pos : 0 < r + 1 := Int.lt_add_one_of_le hr0
        have hneg : -(r + 1) < 0 := by
          have h := Int.neg_lt_neg hr1pos
          simpa using h
        have h := Int.add_lt_add_left hneg (-(d * q))
        simpa using h
      _ = -(q + 1) * d + d := by
        calc
          -(d * q) = -(q * d) := by rw [Int.mul_comm d q]
          _ = -q * d := by rw [Int.neg_mul_eq_neg_mul]
          _ = (-(q + 1) + 1) * d := by
            have hCoeff : -(q + 1) + 1 = -q := by
              rw [Int.neg_add]
              change -q + -1 + 1 = -q
              rw [Int.add_assoc]
              have hConst : (-1 : Int) + 1 = 0 := by native_decide
              rw [hConst, Int.add_zero]
            rw [hCoeff]
          _ = -(q + 1) * d + 1 * d := by rw [Int.add_mul]
          _ = -(q + 1) * d + d := by rw [Int.one_mul]
  have hLower :
      -(q + 1) <= native_div_total (-(m + 1)) d := by
    rw [native_div_total]
    apply Int.le_of_not_gt
    intro hLt
    have hLtMul :=
      (Int.ediv_lt_iff_lt_mul (a := -(m + 1))
        (b := -(q + 1)) (c := d) hdPos).mp hLt
    have hNot : ¬ -(m + 1) < -(q + 1) * d := by
      intro h
      have hLe : m + 1 <= (q + 1) * d := by
        have hEq : m + 1 = d * q + (r + 1) := by
          rw [← hDivMod]
          rw [← Int.add_assoc]
        have hr1le : r + 1 <= d := (Int.add_one_le_iff).mpr hrlt
        have hStep : d * q + (r + 1) <= d * q + d :=
          Int.add_le_add_left hr1le (d * q)
        have hRight : d * q + d = (q + 1) * d := by
          calc
            d * q + d = q * d + d := by rw [Int.mul_comm d q]
            _ = q * d + 1 * d := by rw [Int.one_mul]
            _ = (q + 1) * d := by rw [Int.add_mul]
        rw [hEq]
        rw [← hRight]
        exact hStep
      have hNegLe : -((q + 1) * d) <= -(m + 1) :=
        Int.neg_le_neg hLe
      have hNegMul : -((q + 1) * d) = -(q + 1) * d := by
        rw [Int.neg_mul_eq_neg_mul]
      rw [hNegMul] at hNegLe
      exact (Int.not_lt_of_ge hNegLe) h
    exact hNot hLtMul
  change native_div_total (-(m + 1)) d = -(native_div_total m d + 1)
  exact Int.le_antisymm hUpper hLower

theorem EvaluateProofInternal.int_sub_eq_neg_sub_succ_add_one
    (n p : native_Int) :
    n - p = -(p - (n + 1) + 1) := by
  grind

theorem EvaluateProofInternal.int_sub_sub_neg_succ_eq
    (p q : native_Int) :
    p - (q + 1) - (-(q + 1)) = p := by
  grind

theorem EvaluateProofInternal.native_bvashr_negative_payload_eq_signed_div
    {w n s : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true)
    (hShiftCanon :
      native_zeq s
          (native_mod_total s (native_int_pow2 w)) =
        true)
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = true) :
    native_mod_total
        (native_binary_not w
          (native_mod_total
            (native_div_total
              (native_mod_total (native_binary_not w n)
                (native_int_pow2 w))
              (native_int_pow2 s))
            (native_int_pow2 w)))
        (native_int_pow2 w) =
      native_mod_total
        (native_div_total (native_binary_uts w n)
          (native_int_pow2 s))
        (native_int_pow2 w) := by
  have hWNonneg : 0 <= w := by
    simpa [native_zleq, SmtEval.native_zleq] using hw0
  have hShiftRange :=
    bitvec_payload_range_of_canonical hw0 hShiftCanon
  have hs0 : 0 <= s := hShiftRange.1
  let P := native_int_pow2 w
  let d := native_int_pow2 s
  let m := native_binary_not w n
  have hPPos : 0 < P := by
    dsimp [P]
    exact EvaluateProofInternal.native_int_pow2_pos_of_nonneg hWNonneg
  have hdPos : 0 < d := by
    dsimp [d]
    exact EvaluateProofInternal.native_int_pow2_pos_of_nonneg hs0
  have hdGeOne : 1 <= d := (Int.add_one_le_iff).mpr hdPos
  have hMRange :
      0 <= m ∧ m < P := by
    simpa [m, P] using
      EvaluateProofInternal.native_binary_not_range_of_canonical
        (w := w) (n := n) hw0 hCanon
  have hNotMod :
      native_mod_total (native_binary_not w n) P =
        native_binary_not w n := by
    simpa [P] using
      EvaluateProofInternal.native_binary_not_mod_self_of_canonical
        (w := w) (n := n) hw0 hCanon
  let q := native_div_total m d
  have hQRange : 0 <= q ∧ q < P := by
    constructor
    · dsimp [q, native_div_total]
      exact Int.ediv_nonneg hMRange.1 (Int.le_of_lt hdPos)
    · have hPLePD : P <= P * d := by
        have hMul := Int.mul_le_mul_of_nonneg_left hdGeOne
          (Int.le_of_lt hPPos)
        simpa [Int.mul_one] using hMul
      have hMLtPD : m < P * d :=
        Int.lt_of_lt_of_le hMRange.2 hPLePD
      dsimp [q, native_div_total]
      exact Int.ediv_lt_of_lt_mul hdPos hMLtPD
  have hQMod :
      native_mod_total q P = q := by
    simpa [native_mod_total] using
      Int.emod_eq_of_lt hQRange.1 hQRange.2
  have hSignedArg :
      native_binary_uts w n = -(m + 1) := by
    have hUts :=
      EvaluateProofInternal.native_binary_uts_eq_sub_pow_of_msb_true
        (w := w) (n := n) hw0 hCanon hSign
    have hMRaw : m = P - (n + 1) := by
      dsimp [m, P]
      exact EvaluateProofInternal.native_binary_not_eq_pow_sub_succ w n
    rw [hUts, hMRaw]
    dsimp [P]
    exact EvaluateProofInternal.int_sub_eq_neg_sub_succ_add_one n (native_int_pow2 w)
  have hNegDiv :
      native_div_total (-(m + 1)) d = -(q + 1) := by
    dsimp [q, d]
    exact EvaluateProofInternal.native_neg_succ_div_pow2_eq_neg_div_succ
      (m := m) (s := s) hMRange.1 hs0
  rw [hNotMod]
  change
    native_mod_total
        (native_binary_not w
          (native_mod_total (native_div_total m d) P))
        P =
      native_mod_total
        (native_div_total (native_binary_uts w n) d) P
  rw [show native_div_total m d = q by rfl]
  rw [hQMod]
  rw [hSignedArg, hNegDiv]
  rw [EvaluateProofInternal.native_binary_not_eq_pow_sub_succ w q]
  change
    native_mod_total (P - (q + 1)) P =
      native_mod_total (-(q + 1)) P
  rw [native_mod_total, native_mod_total]
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  have hDiff : P - (q + 1) - (-(q + 1)) = P := by
    exact EvaluateProofInternal.int_sub_sub_neg_succ_eq P q
  rw [hDiff]
  simp

theorem EvaluateProofInternal.smtx_model_eval_bvashr_binary_eq_signed_div_of_msb_true
    {w n s : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true)
    (hShiftCanon :
      native_zeq s
          (native_mod_total s (native_int_pow2 w)) =
        true)
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = true) :
    __smtx_model_eval_bvashr (SmtValue.Binary w n) (SmtValue.Binary w s) =
      SmtValue.Binary w
        (native_mod_total
          (native_div_total (native_binary_uts w n)
            (native_int_pow2 s))
          (native_int_pow2 w)) := by
  rw [EvaluateProofInternal.smtx_model_eval_bvashr_binary_eq_not_lshr_not_of_msb_true hSign]
  rw [EvaluateProofInternal.native_bvashr_negative_payload_eq_signed_div
    hw0 hCanon hShiftCanon hSign]

theorem EvaluateProofInternal.smtx_model_eval_bvashr_binary_eq_signed_div
    {w n s : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true)
    (hShiftCanon :
      native_zeq s
          (native_mod_total s (native_int_pow2 w)) =
        true) :
    __smtx_model_eval_bvashr (SmtValue.Binary w n) (SmtValue.Binary w s) =
      SmtValue.Binary w
        (native_mod_total
          (native_div_total (native_binary_uts w n)
            (native_int_pow2 s))
          (native_int_pow2 w)) := by
  by_cases hSignFalse : EvaluateProofInternal.smt_bv_msb_set w n = false
  · rw [EvaluateProofInternal.smtx_model_eval_bvashr_binary_eq_lshr_of_msb_false hSignFalse]
    rw [EvaluateProofInternal.native_binary_uts_eq_self_of_msb_false hw0 hCanon hSignFalse]
  · have hSignTrue : EvaluateProofInternal.smt_bv_msb_set w n = true := by
      cases hSign : EvaluateProofInternal.smt_bv_msb_set w n <;>
        simp [hSign] at hSignFalse ⊢
    exact EvaluateProofInternal.smtx_model_eval_bvashr_binary_eq_signed_div_of_msb_true
      hw0 hCanon hShiftCanon hSignTrue

theorem EvaluateProofInternal.sbv_to_int_payload_eq_uts_core
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true) :
    (if native_zeq
          (native_mod_total
            (native_div_total n (native_int_pow2 (w - 1))) 2)
          0 then
        n
      else
        native_zplus n (native_zneg (native_int_pow2 w))) =
      native_binary_uts w n := by
  by_cases hwpos : 0 < w
  · let p := native_int_pow2 (w - 1)
    let q := native_div_total n p
    let r := native_mod_total n p
    have hpPos : 0 < p := by
      have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
      have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
      have hnot : ¬ w - 1 < 0 := Int.not_lt_of_ge hwp0
      simp [p, native_int_pow2, native_zexp_total, hnot]
      exact Int.pow_pos (by decide)
    have hRange := bitvec_payload_range_of_canonical hw0 hCanon
    have hPow : native_int_pow2 w = 2 * p := by
      simpa [p] using EvaluateProofInternal.native_int_pow2_succ_pred (w := w) hwpos
    have hqNonneg : 0 <= q :=
      Int.ediv_nonneg hRange.1 (Int.le_of_lt hpPos)
    have hqLt2 : q < 2 := by
      have hlt : n < 2 * p := by
        simpa [hPow] using hRange.2
      exact Int.ediv_lt_of_lt_mul hpPos hlt
    have hqCases : q = 0 ∨ q = 1 := by
      by_cases hq0 : q = 0
      · exact Or.inl hq0
      · have hqPos : 0 < q := by
          rcases Int.lt_or_eq_of_le hqNonneg with hlt | heq
          · exact hlt
          · exact False.elim (hq0 heq.symm)
        have hqGe1 : 1 <= q := (Int.add_one_le_iff).mpr hqPos
        have hqLe1 : q <= 1 := Int.le_of_lt_add_one hqLt2
        exact Or.inr (Int.le_antisymm hqLe1 hqGe1)
    have hDivMod : p * q + r = n := by
      simpa [q, r, p, native_div_total, native_mod_total] using
        Int.mul_ediv_add_emod n p
    have hNMod : native_mod_total n p = r := by
      rfl
    rcases hqCases with hq | hq
    · have hSignZero : native_zeq (native_mod_total q 2) 0 = true := by
        simp [hq, native_zeq, native_mod_total]
      have hnEq : n = r := by
        rw [hq] at hDivMod
        simp at hDivMod
        exact hDivMod.symm
      have hCond :
          native_zeq
              (native_mod_total
                (native_div_total n (native_int_pow2 (w - 1))) 2)
              0 =
            true := by
        simpa [q, p] using hSignZero
      rw [hCond]
      change n = native_binary_uts w n
      rw [native_binary_uts]
      change n =
        native_zplus (native_zmult 2 (native_mod_total n p))
          (native_zneg n)
      rw [hnEq] at hNMod
      rw [hnEq, hNMod]
      simp [native_zplus, native_zmult, native_zneg]
      rw [Int.two_mul]
      rw [Int.add_assoc]
      rw [Int.add_right_neg]
      rw [Int.add_zero]
    · have hSignZero : native_zeq (native_mod_total q 2) 0 = false := by
        simp [hq, native_zeq, native_mod_total]
      have hnEq : n = p + r := by
        rw [hq] at hDivMod
        simp at hDivMod
        exact hDivMod.symm
      have hCond :
          native_zeq
              (native_mod_total
                (native_div_total n (native_int_pow2 (w - 1))) 2)
              0 =
            false := by
        simpa [q, p] using hSignZero
      rw [hCond]
      change
        native_zplus n (native_zneg (native_int_pow2 w)) =
          native_binary_uts w n
      rw [native_binary_uts, hPow]
      change
        native_zplus n (native_zneg (2 * p)) =
          native_zplus (native_zmult 2 (native_mod_total n p))
            (native_zneg n)
      rw [hnEq] at hNMod
      rw [hnEq, hNMod]
      simp [native_zplus, native_zmult, native_zneg]
      have hLeftCancel :
          p + r + (-p + -p) = r + -p := by
        have hCancel : p + r + -p = r := by
          calc
            p + r + -p = p + (r + -p) := by rw [Int.add_assoc]
            _ = p + (-p + r) := by rw [Int.add_comm r (-p)]
            _ = p + -p + r := by rw [← Int.add_assoc]
            _ = r := by rw [Int.add_right_neg, Int.zero_add]
        calc
          p + r + (-p + -p) = p + r + -p + -p := by
            rw [← Int.add_assoc]
          _ = r + -p := by rw [hCancel]
      have hRightCancel :
          r + r + (-p + -r) = r + -p := by
        have hCancel : r + r + -r = r := by
          calc
            r + r + -r = r + (r + -r) := by rw [Int.add_assoc]
            _ = r := by rw [Int.add_right_neg, Int.add_zero]
        calc
          r + r + (-p + -r) = r + r + (-r + -p) := by
            rw [Int.add_comm (-p) (-r)]
          _ = r + r + -r + -p := by
            rw [← Int.add_assoc]
          _ = r + -p := by rw [hCancel]
      calc
        p + r + -(2 * p) = p + r + -(p + p) := by
          rw [Int.two_mul]
        _ = p + r + (-p + -p) := by
          rw [Int.neg_add]
        _ = r + -p := hLeftCancel
        _ = r + r + (-p + -r) := hRightCancel.symm
        _ = 2 * r + -(p + r) := by
          rw [Int.two_mul, Int.neg_add]
  · have hw : 0 <= w := by
      simpa [native_zleq, SmtEval.native_zleq] using hw0
    have hwEq : w = 0 :=
      Int.le_antisymm (Int.le_of_not_gt hwpos) hw
    subst w
    have hRange := bitvec_payload_range_of_canonical hw0 hCanon
    have hPow0 : native_int_pow2 0 = 1 := by
      native_decide
    have hnEq : n = 0 := by
      have hlt : n < 1 := by
        simpa [hPow0] using hRange.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange.1
    subst n
    native_decide

def EvaluateProofInternal.eo_eval_sbv_to_int_rhs (x : Term) : Term :=
  let _v0 := __run_evaluate x
  let _v1 := __bv_bitwidth (__eo_typeof _v0)
  let _v2 := __eo_to_z _v0
  let _v3 :=
    __eo_add (__bv_bitwidth (__eo_typeof x))
      (Term.Numeral (-1 : native_Int))
  __eo_ite (__eo_eq _v1 (Term.Numeral 0)) (Term.Numeral 0)
    (__eo_ite
      (__eo_eq (__eo_extract x _v3 _v3) (Term.Binary 1 0))
      _v2
      (__eo_add _v2
        (__eo_neg
          (__eo_ite (__eo_is_z _v1)
            (__eo_ite (__eo_is_neg _v1) (Term.Numeral 0)
              (__eo_pow (Term.Numeral 2) _v1))
            (__eo_mk_apply (Term.UOp UserOp.int_pow2) _v1)))))

theorem EvaluateProofInternal.eo_eval_sbv_to_int_rhs_binary_eq_uts
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n (native_mod_total n (native_int_pow2 w)) = true) :
    EvaluateProofInternal.eo_eval_sbv_to_int_rhs (Term.Binary w n) =
      Term.Numeral (native_binary_uts w n) := by
  by_cases hwz : w = 0
  · subst w
    have hRange := bitvec_payload_range_of_canonical hw0 hCanon
    have hPow0 : native_int_pow2 0 = 1 := by
      native_decide
    have hnEq : n = 0 := by
      have hlt : n < 1 := by
        simpa [hPow0] using hRange.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange.1
    subst n
    native_decide
  · have hw0Int : 0 <= w := by
      simpa [native_zleq, SmtEval.native_zleq] using hw0
    have hwpos : 0 < w := by
      rcases Int.lt_or_eq_of_le hw0Int with hlt | heq
      · exact hlt
      · exact False.elim (hwz heq.symm)
    have hEqW0 :
        __eo_eq (Term.Numeral w) (Term.Numeral 0) =
          Term.Boolean false := by
      have h0w : ¬ (0 : native_Int) = w := by
        intro h
        exact hwz h.symm
      simp [__eo_eq, native_teq, h0w]
    have hPowExpr :
        __eo_ite (__eo_is_z (Term.Numeral w))
          (__eo_ite (__eo_is_neg (Term.Numeral w)) (Term.Numeral 0)
            (__eo_pow (Term.Numeral 2) (Term.Numeral w)))
          (__eo_mk_apply (Term.UOp UserOp.int_pow2) (Term.Numeral w)) =
        Term.Numeral (native_int_pow2 w) :=
      EvaluateProofInternal.eo_int_pow2_literal_eq w
    dsimp [EvaluateProofInternal.eo_eval_sbv_to_int_rhs]
    change
      __eo_ite (__eo_eq (Term.Numeral w) (Term.Numeral 0))
          (Term.Numeral 0)
          (__eo_ite
            (__eo_eq
              (__eo_extract (Term.Binary w n)
                (Term.Numeral (native_zplus w (native_zneg 1)))
                (Term.Numeral (native_zplus w (native_zneg 1))))
              (Term.Binary 1 0))
            (Term.Numeral n)
            (__eo_add (Term.Numeral n)
              (__eo_neg
                (__eo_ite (__eo_is_z (Term.Numeral w))
                  (__eo_ite (__eo_is_neg (Term.Numeral w))
                    (Term.Numeral 0)
                    (__eo_pow (Term.Numeral 2) (Term.Numeral w)))
                  (__eo_mk_apply (Term.UOp UserOp.int_pow2)
                    (Term.Numeral w)))))) =
        Term.Numeral (native_binary_uts w n)
    rw [hEqW0, eo_ite_false,
      EvaluateProofInternal.eo_sbv_to_int_msb_zero_eq_of_pos (w := w) (n := n) hwpos]
    cases hSignZero :
        native_zeq
          (native_mod_total
            (native_div_total n (native_int_pow2 (w - 1))) 2)
          0
    · rw [eo_ite_false, hPowExpr]
      simp [__eo_add, __eo_neg]
      simpa [hSignZero] using
        EvaluateProofInternal.sbv_to_int_payload_eq_uts_core
          (w := w) (n := n) hw0 hCanon
    · rw [eo_ite_true]
      exact congrArg Term.Numeral
        (by
          simpa [hSignZero] using
            EvaluateProofInternal.sbv_to_int_payload_eq_uts_core
              (w := w) (n := n) hw0 hCanon)

theorem EvaluateProofInternal.eo_eval_sbv_to_int_rhs_arg_binary_of_pos_typeof_int
    (x : Term) {w n : native_Int}
    (hRun : __run_evaluate x = Term.Binary w n)
    (hwpos : 0 < w)
    (hTy : __eo_typeof (EvaluateProofInternal.eo_eval_sbv_to_int_rhs x) =
      Term.UOp UserOp.Int) :
    x = Term.Binary w n := by
  have hEqW0 :
      __eo_eq (Term.Numeral w) (Term.Numeral 0) =
        Term.Boolean false := by
    have hwz : ¬ w = 0 := by
      intro h
      subst w
      exact (by native_decide : ¬ (0 : native_Int) < 0) hwpos
    have h0w : ¬ (0 : native_Int) = w := by
      intro h
      exact hwz h.symm
    simp [__eo_eq, native_teq, h0w]
  have hRunGuard :
      __eo_eq (__bv_bitwidth (__eo_typeof (Term.Binary w n)))
          (Term.Numeral 0) =
        Term.Boolean false := by
    change __eo_eq (Term.Numeral w) (Term.Numeral 0) =
      Term.Boolean false
    exact hEqW0
  cases x
  case Binary wx nx =>
    change Term.Binary wx nx = Term.Binary w n
    change Term.Binary wx nx = Term.Binary w n at hRun
    exact hRun
  case String s =>
    change Term.String s = Term.Binary w n at hRun
    cases hRun
  all_goals
    exfalso
    dsimp [EvaluateProofInternal.eo_eval_sbv_to_int_rhs] at hTy
    rw [hRun, hRunGuard, eo_ite_false] at hTy
    simp [__eo_extract, __eo_eq, __eo_ite, native_ite, native_teq] at hTy
    change Term.Stuck = Term.UOp UserOp.Int at hTy
    cases hTy

theorem EvaluateProofInternal.eo_eval_sbv_to_int_rhs_eq_zero_of_run_typeof_zero
    (x : Term)
    (hRunTy :
      __eo_typeof (__run_evaluate x) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 0)) :
    EvaluateProofInternal.eo_eval_sbv_to_int_rhs x = Term.Numeral 0 := by
  dsimp [EvaluateProofInternal.eo_eval_sbv_to_int_rhs]
  rw [hRunTy]
  rfl

theorem EvaluateProofInternal.eo_eval_sbv_to_int_rhs_arg_binary_of_pos_run_typeof_int
    (x : Term) {k : native_Int}
    (hRunTy :
      __eo_typeof (__run_evaluate x) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral k))
    (hkpos : 0 < k)
    (hTy : __eo_typeof (EvaluateProofInternal.eo_eval_sbv_to_int_rhs x) =
      Term.UOp UserOp.Int) :
    ∃ w n : native_Int, x = Term.Binary w n := by
  have hGuard :
      __eo_eq (__bv_bitwidth (__eo_typeof (__run_evaluate x)))
          (Term.Numeral 0) =
        Term.Boolean false := by
    rw [hRunTy]
    have hkz : ¬ k = 0 := by
      intro h
      subst k
      exact (by native_decide : ¬ (0 : native_Int) < 0) hkpos
    have h0k : ¬ (0 : native_Int) = k := by
      intro h
      exact hkz h.symm
    simp [__bv_bitwidth, __eo_eq, native_teq, h0k]
  cases x
  case Binary w n =>
    exact ⟨w, n, rfl⟩
  case String s =>
    exfalso
    dsimp [EvaluateProofInternal.eo_eval_sbv_to_int_rhs] at hTy
    rw [hGuard, eo_ite_false] at hTy
    have hIdx :
        __eo_add (__bv_bitwidth (__eo_typeof (Term.String s)))
            (Term.Numeral (-1 : native_Int)) =
          Term.Stuck := by
      rfl
    rw [hIdx] at hTy
    simp [__eo_extract, __eo_eq, __eo_ite, native_ite, native_teq] at hTy
    change Term.Stuck = Term.UOp UserOp.Int at hTy
    cases hTy
  all_goals
    exfalso
    dsimp [EvaluateProofInternal.eo_eval_sbv_to_int_rhs] at hTy
    rw [hGuard, eo_ite_false] at hTy
    simp [__eo_extract, __eo_eq, __eo_ite, native_ite, native_teq] at hTy
    change Term.Stuck = Term.UOp UserOp.Int at hTy
    cases hTy

theorem EvaluateProofInternal.eo_eval_sbv_to_int_rhs_typeof_int_of_pos_run_typeof
    (x : Term) {k : native_Int}
    (hRunTy :
      __eo_typeof (__run_evaluate x) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral k))
    (hkpos : 0 < k)
    (hNe : EvaluateProofInternal.eo_eval_sbv_to_int_rhs x ≠ Term.Stuck) :
    __eo_typeof (EvaluateProofInternal.eo_eval_sbv_to_int_rhs x) =
      Term.UOp UserOp.Int := by
  have hGuard :
      __eo_eq (__bv_bitwidth (__eo_typeof (__run_evaluate x)))
          (Term.Numeral 0) =
        Term.Boolean false := by
    rw [hRunTy]
    have hkz : ¬ k = 0 := by
      intro h
      subst k
      exact (by native_decide : ¬ (0 : native_Int) < 0) hkpos
    have h0k : ¬ (0 : native_Int) = k := by
      intro h
      exact hkz h.symm
    simp [__bv_bitwidth, __eo_eq, native_teq, h0k]
  cases x
  case Binary w n =>
    have hwpos : 0 < w := by
      change
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral k) at hRunTy
      cases hRunTy
      exact hkpos
    have hNeg : native_zlt w 0 = false := by
      rw [show native_zlt w 0 = decide (w < 0) by rfl]
      exact decide_eq_false (Int.not_lt.mpr (Int.le_of_lt hwpos))
    dsimp [EvaluateProofInternal.eo_eval_sbv_to_int_rhs]
    rw [hGuard, eo_ite_false]
    cases hSign :
        __eo_eq
            (__eo_extract (Term.Binary w n)
              (__eo_add (__bv_bitwidth (__eo_typeof (Term.Binary w n)))
                (Term.Numeral (-1 : native_Int)))
              (__eo_add (__bv_bitwidth (__eo_typeof (Term.Binary w n)))
                (Term.Numeral (-1 : native_Int))))
            (Term.Binary 1 0)
    case Boolean b =>
      cases b
      · change
          __eo_typeof
              (__eo_add (Term.Numeral n)
                (__eo_neg
                  (__eo_ite (__eo_is_z (Term.Numeral w))
                    (__eo_ite (__eo_is_neg (Term.Numeral w))
                      (Term.Numeral 0)
                      (__eo_pow (Term.Numeral 2) (Term.Numeral w)))
                    (__eo_mk_apply (Term.UOp UserOp.int_pow2)
                      (Term.Numeral w))))) =
            Term.UOp UserOp.Int
        simp [__eo_ite, native_ite, native_teq, __eo_is_z,
          __eo_is_z_internal, __eo_is_neg, __eo_neg, __eo_add,
          __eo_pow, __eo_mk_apply, native_and, native_not, hNeg]
        change __eo_lit_type_Numeral (Term.Numeral _) =
          Term.UOp UserOp.Int
        rfl
      · change __eo_typeof (Term.Numeral n) = Term.UOp UserOp.Int
        rfl
    all_goals
      exfalso
      apply hNe
      dsimp [EvaluateProofInternal.eo_eval_sbv_to_int_rhs]
      rw [hGuard, eo_ite_false]
      simp [__eo_ite, hSign, native_ite, native_teq]
  case String s =>
    change
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral k) at hRunTy
    cases hRunTy
  all_goals
    exfalso
    apply hNe
    dsimp [EvaluateProofInternal.eo_eval_sbv_to_int_rhs]
    rw [hGuard, eo_ite_false]
    simp [__eo_extract, __eo_eq, __eo_ite, native_ite, native_teq]

theorem EvaluateProofInternal.term_apply_ne_stuck (f x : Term) :
    Term.Apply f x ≠ Term.Stuck := by
  intro h
  cases h

theorem EvaluateProofInternal.bv_list_repeat_rec_binary_ne_stuck
    (w n : native_Int) :
    ∀ k : native_Nat,
      __eo_list_repeat_rec (Term.UOp UserOp.concat) (Term.Binary w n) k ≠
        Term.Stuck := by
  intro k
  induction k with
  | zero =>
      change Term.Binary 0 0 ≠ Term.Stuck
      intro h
      cases h
  | succ k ih =>
      change
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp.concat) (Term.Binary w n))
            (__eo_list_repeat_rec (Term.UOp UserOp.concat)
              (Term.Binary w n) k) ≠
          Term.Stuck
      rw [EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck _ _
        (EvaluateProofInternal.term_apply_ne_stuck _ _) ih]
      exact EvaluateProofInternal.term_apply_ne_stuck _ _

theorem EvaluateProofInternal.bv_list_repeat_rec_binary_succ_eq
    (w n : native_Int) (k : native_Nat) :
    __eo_list_repeat_rec (Term.UOp UserOp.concat) (Term.Binary w n)
        (Nat.succ k) =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.concat) (Term.Binary w n))
        (__eo_list_repeat_rec (Term.UOp UserOp.concat) (Term.Binary w n)
          k) := by
  change
    __eo_mk_apply
        (Term.Apply (Term.UOp UserOp.concat) (Term.Binary w n))
        (__eo_list_repeat_rec (Term.UOp UserOp.concat) (Term.Binary w n)
          k) =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.concat) (Term.Binary w n))
        (__eo_list_repeat_rec (Term.UOp UserOp.concat) (Term.Binary w n)
          k)
  exact EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck _ _
    (EvaluateProofInternal.term_apply_ne_stuck _ _)
    (EvaluateProofInternal.bv_list_repeat_rec_binary_ne_stuck w n k)

theorem EvaluateProofInternal.bv_eval_concat_list_repeat_rec_binary
    (w n : native_Int)
    (hWNonneg : native_zleq 0 w = true) :
    ∀ k : native_Nat,
      ∃ m : native_Int,
        __bv_eval_concat
            (__eo_list_repeat_rec (Term.UOp UserOp.concat)
              (Term.Binary w n) k) =
          Term.Binary (native_zmult (native_nat_to_int k) w) m ∧
        __smtx_repeat_rec k (SmtValue.Binary w n) =
          SmtValue.Binary (native_zmult (native_nat_to_int k) w) m ∧
        native_zeq m
          (native_mod_total m
            (native_int_pow2
              (native_zmult (native_nat_to_int k) w))) =
          true
  | Nat.zero => by
      refine ⟨0, ?_, ?_, ?_⟩
      · change Term.Binary 0 0 =
          Term.Binary (native_zmult (native_nat_to_int 0) w) 0
        simp [SmtEval.native_zmult, Smtm.native_nat_to_int]
      · simp [__smtx_repeat_rec, SmtEval.native_zmult,
          Smtm.native_nat_to_int]
      · simp [SmtEval.native_zeq, SmtEval.native_mod_total,
          SmtEval.native_zmult, Smtm.native_nat_to_int]
  | Nat.succ k => by
      rcases EvaluateProofInternal.bv_eval_concat_list_repeat_rec_binary w n hWNonneg k with
        ⟨m, hTerm, hEval, _hCanon⟩
      let recW := native_zmult (native_nat_to_int k) w
      let newW := native_zmult (native_nat_to_int (Nat.succ k)) w
      let newM :=
        native_mod_total (native_binary_concat w n recW m)
          (native_int_pow2 newW)
      have hWidthEq :
          native_zplus w recW = newW := by
        have hWidthEqInt : w + ↑k * w = (↑k + 1) * w := by
          calc
            w + ↑k * w = 1 * w + ↑k * w := by simp
            _ = (1 + ↑k) * w := by rw [Int.add_mul]
            _ = (↑k + 1) * w := by simp [Int.add_comm]
        simpa [recW, newW, SmtEval.native_zplus, SmtEval.native_zmult,
          Smtm.native_nat_to_int] using hWidthEqInt
      have hWidthNonneg :
          native_zleq 0 (native_zplus w recW) = true := by
        have hw : 0 <= w := by
          simpa [SmtEval.native_zleq] using hWNonneg
        have hk : 0 <= native_nat_to_int k := by
          simp [Smtm.native_nat_to_int]
        have hRecW : 0 <= recW := by
          simpa [recW, SmtEval.native_zmult] using Int.mul_nonneg hk hw
        have hAdd : 0 <= w + recW := Int.add_nonneg hw hRecW
        have hsimpa := hAdd
        try simp [SmtEval.native_zleq, SmtEval.native_zplus] at hsimpa ⊢
        exact decide_eq_true hsimpa
      refine ⟨newM, ?_, ?_, ?_⟩
      · rw [EvaluateProofInternal.bv_list_repeat_rec_binary_succ_eq]
        change
          __eo_concat (Term.Binary w n)
              (__bv_eval_concat
                (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                  (Term.Binary w n) k)) =
            Term.Binary newW newM
        rw [hTerm]
        change
          __eo_mk_binary (native_zplus w recW)
              (native_binary_concat w n recW m) =
            Term.Binary newW newM
        have hMk :
            __eo_mk_binary (native_zplus w recW)
                (native_binary_concat w n recW m) =
              Term.Binary (native_zplus w recW)
                (native_mod_total (native_binary_concat w n recW m)
                  (native_int_pow2 (native_zplus w recW))) := by
          simp [__eo_mk_binary, hWidthNonneg, native_ite]
        rw [hMk]
        exact congrArg
          (fun z =>
            Term.Binary z
              (native_mod_total (native_binary_concat w n recW m)
                (native_int_pow2 z)))
          hWidthEq
      · rw [__smtx_repeat_rec, hEval, __smtx_model_eval_concat]
        exact congrArg
          (fun z =>
            SmtValue.Binary z
              (native_mod_total (native_binary_concat w n recW m)
                (native_int_pow2 z)))
          hWidthEq
      · exact native_mod_total_canonical newW
          (native_binary_concat w n recW m)

theorem EvaluateProofInternal.bv_eval_concat_list_repeat_binary_eval
    (M : SmtModel) (i w n : native_Int)
    (hi0 : native_zleq 0 i = true)
    (hWNonneg : native_zleq 0 w = true) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_eval_concat
            (__eo_list_repeat (Term.UOp UserOp.concat)
              (Term.Binary w n) (Term.Numeral i)))) =
      __smtx_repeat_rec (native_int_to_nat i)
        (SmtValue.Binary w n) := by
  have hiNonneg : 0 <= i := by
    simpa [SmtEval.native_zleq] using hi0
  have hiNotNeg : native_zlt i 0 = false := by
    simp [SmtEval.native_zlt]
    omega
  have hList :
      __eo_list_repeat (Term.UOp UserOp.concat) (Term.Binary w n)
          (Term.Numeral i) =
        __eo_list_repeat_rec (Term.UOp UserOp.concat) (Term.Binary w n)
          (native_int_to_nat i) := by
    simp [__eo_list_repeat, native_ite, hiNotNeg]
  rcases EvaluateProofInternal.bv_eval_concat_list_repeat_rec_binary w n hWNonneg
      (native_int_to_nat i) with
    ⟨m, hTerm, hEval, _hCanon⟩
  rw [hList, hTerm, hEval]
  change
    __smtx_model_eval M
        (SmtTerm.Binary
          (native_zmult (native_nat_to_int (native_int_to_nat i)) w) m) =
      SmtValue.Binary
        (native_zmult (native_nat_to_int (native_int_to_nat i)) w) m
  rw [__smtx_model_eval.eq_5]

theorem EvaluateProofInternal.bv_eval_concat_list_repeat_rec_binary_stuck_of_neg
    (w n : native_Int)
    (hWNeg : native_zleq 0 w = false) :
    ∀ k : native_Nat,
      k ≠ 0 ->
        __bv_eval_concat
            (__eo_list_repeat_rec (Term.UOp UserOp.concat)
              (Term.Binary w n) k) =
          Term.Stuck := by
  intro k hk
  induction k with
  | zero =>
      exact False.elim (hk rfl)
  | succ k ih =>
      rw [EvaluateProofInternal.bv_list_repeat_rec_binary_succ_eq]
      change
        __eo_concat (Term.Binary w n)
          (__bv_eval_concat
            (__eo_list_repeat_rec (Term.UOp UserOp.concat)
              (Term.Binary w n) k)) =
          Term.Stuck
      cases k with
      | zero =>
          change __eo_concat (Term.Binary w n) (Term.Binary 0 0) =
            Term.Stuck
          change
            __eo_mk_binary (native_zplus w 0)
                (native_binary_concat w n 0 0) =
              Term.Stuck
          have hWidth :
              native_zleq 0 (native_zplus w 0) = false := by
            simpa [SmtEval.native_zleq, SmtEval.native_zplus]
              using hWNeg
          simp [__eo_mk_binary, hWidth, native_ite]
      | succ k' =>
          have hTail :
              __bv_eval_concat
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.Binary w n) (Nat.succ k')) =
                Term.Stuck := by
            exact ih (by intro h; cases h)
          rw [hTail]
          rfl

theorem EvaluateProofInternal.bv_eval_concat_list_repeat_rec_not_binary_stuck
    (x : Term)
    (hNotBinary : ¬ ∃ w : native_Int, ∃ n : native_Int,
      x = Term.Binary w n) :
    ∀ k : native_Nat,
      k ≠ 0 ->
        __bv_eval_concat
            (__eo_list_repeat_rec (Term.UOp UserOp.concat) x k) =
          Term.Stuck := by
  intro k hk
  induction k with
  | zero =>
      exact False.elim (hk rfl)
  | succ k ih =>
      cases x with
      | Stuck =>
          rfl
      | String s =>
          cases k with
          | zero =>
              change
                __bv_eval_concat
                    (__eo_mk_apply
                      (Term.Apply (Term.UOp UserOp.concat) (Term.String s))
                      (Term.Binary 0 0)) =
                  Term.Stuck
              rw [EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck _ _
                (EvaluateProofInternal.term_apply_ne_stuck _ _)
                (by intro h; cases h)]
              rfl
          | succ k' =>
              change
                __bv_eval_concat
                    (__eo_mk_apply
                      (Term.Apply (Term.UOp UserOp.concat) (Term.String s))
                      (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                        (Term.String s) (Nat.succ k'))) =
                  Term.Stuck
              by_cases hTailStuck :
                  __eo_list_repeat_rec (Term.UOp UserOp.concat)
                      (Term.String s) (Nat.succ k') =
                    Term.Stuck
              · rw [hTailStuck]
                rfl
              · rw [EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck _ _
                  (EvaluateProofInternal.term_apply_ne_stuck _ _) hTailStuck]
                change
                  __eo_concat (Term.String s)
                    (__bv_eval_concat
                      (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                        (Term.String s) (Nat.succ k'))) =
                    Term.Stuck
                have hTailEval :
                    __bv_eval_concat
                        (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                          (Term.String s) (Nat.succ k')) =
                      Term.Stuck :=
                  ih (by intro h; cases h)
                rw [hTailEval]
                rfl
      | Binary w n =>
          exfalso
          exact hNotBinary ⟨w, n, rfl⟩
      | __eo_List =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) Term.__eo_List)
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    Term.__eo_List k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                Term.__eo_List k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | __eo_List_nil =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) Term.__eo_List_nil)
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    Term.__eo_List_nil k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                Term.__eo_List_nil k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | Bool =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) Term.Bool)
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    Term.Bool k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                Term.Bool k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | Boolean b =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.Boolean b))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.Boolean b) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.Boolean b) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | Numeral n =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.Numeral n))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.Numeral n) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.Numeral n) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | Rational q =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.Rational q))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.Rational q) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.Rational q) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | «Type» =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) Term.Type)
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    Term.Type k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                Term.Type k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | DatatypeTypeRef s =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.DatatypeTypeRef s))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.DatatypeTypeRef s) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.DatatypeTypeRef s) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | UOp op =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.UOp op))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.UOp op) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.UOp op) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | UOp1 op a =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.UOp1 op a))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.UOp1 op a) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.UOp1 op a) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | UOp2 op a b =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.UOp2 op a b))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.UOp2 op a b) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.UOp2 op a b) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | UOp3 op a b c =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.UOp3 op a b c))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.UOp3 op a b c) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.UOp3 op a b c) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | Apply f a =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.Apply f a))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.Apply f a) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.Apply f a) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | Var s T =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.Var s T))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.Var s T) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.Var s T) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | DtcAppType a b =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.DtcAppType a b))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.DtcAppType a b) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.DtcAppType a b) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | DtCons s d i =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.DtCons s d i))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.DtCons s d i) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.DtCons s d i) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | UConst i T =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.UConst i T))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.UConst i T) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.UConst i T) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | FunType =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) Term.FunType)
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    Term.FunType k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                Term.FunType k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | __eo_List_cons =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) Term.__eo_List_cons)
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    Term.__eo_List_cons k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                Term.__eo_List_cons k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | DatatypeType s d =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.DatatypeType s d))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.DatatypeType s d) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.DatatypeType s d) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | DtSel s d i j =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat)
                    (Term.DtSel s d i j))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.DtSel s d i j) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.DtSel s d i j) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      | USort i =>
          change
            __bv_eval_concat
                (__eo_mk_apply
                  (Term.Apply (Term.UOp UserOp.concat) (Term.USort i))
                  (__eo_list_repeat_rec (Term.UOp UserOp.concat)
                    (Term.USort i) k)) =
              Term.Stuck
          cases hTail :
              __eo_list_repeat_rec (Term.UOp UserOp.concat)
                (Term.USort i) k <;>
            simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]
      all_goals
        change
          __bv_eval_concat
              (__eo_mk_apply
                (Term.Apply (Term.UOp UserOp.concat) _)
                (__eo_list_repeat_rec (Term.UOp UserOp.concat) _ k)) =
            Term.Stuck
        cases hTail :
            __eo_list_repeat_rec (Term.UOp UserOp.concat) _ k <;>
          simp [__eo_mk_apply, __bv_eval_concat, __eo_concat]

theorem EvaluateProofInternal.eo_repeat_literal_arg_binary_of_typeof_bitvec
    (x : Term) (i w : native_Int)
    (hi1 : native_zleq 1 i = true) :
    __eo_typeof
        (__bv_eval_concat
          (__eo_list_repeat (Term.UOp UserOp.concat) x
            (Term.Numeral i))) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ wx : native_Int, ∃ nx : native_Int, ∃ m : native_Int,
      x = Term.Binary wx nx ∧
        native_zleq 0 wx = true ∧
        w = native_zmult i wx ∧
        __bv_eval_concat
            (__eo_list_repeat (Term.UOp UserOp.concat) x
              (Term.Numeral i)) =
          Term.Binary (native_zmult i wx) m ∧
        native_zeq m
          (native_mod_total m
            (native_int_pow2 (native_zmult i wx))) =
          true := by
  intro h
  have hi : (1 : Int) <= i := by
    simpa [native_zleq, SmtEval.native_zleq] using hi1
  have hi0Int : (0 : Int) <= i := by
    omega
  have hi0 : native_zleq 0 i = true := by
    simpa [native_zleq, SmtEval.native_zleq] using hi0Int
  have hiPos : (0 : Int) < i := by
    omega
  have hiNotNeg : native_zlt i 0 = false := by
    simp [native_zlt, SmtEval.native_zlt]
    omega
  have hIntNat :
      native_nat_to_int (native_int_to_nat i) = i := by
    simpa [native_nat_to_int, native_int_to_nat,
      Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
      Int.toNat_of_nonneg hi0Int]
  have hNatNeZero : native_int_to_nat i ≠ 0 := by
    intro hZero
    have hIeq0 : i = 0 := by
      calc
        i = native_nat_to_int (native_int_to_nat i) := hIntNat.symm
        _ = native_nat_to_int 0 := by rw [hZero]
        _ = 0 := by simp [native_nat_to_int, Smtm.native_nat_to_int]
    have hBad : (0 : Int) < 0 := by
      simpa [hIeq0] using hiPos
    exact (by decide : ¬ (0 : Int) < 0) hBad
  have hList (hxNe : x ≠ Term.Stuck) :
      __eo_list_repeat (Term.UOp UserOp.concat) x (Term.Numeral i) =
        __eo_list_repeat_rec (Term.UOp UserOp.concat) x
          (native_int_to_nat i) := by
    cases x <;> simp [__eo_list_repeat, native_ite, hiNotNeg] at hxNe ⊢
  by_cases hBinary :
      ∃ wx : native_Int, ∃ nx : native_Int, x = Term.Binary wx nx
  · rcases hBinary with ⟨wx, nx, rfl⟩
    cases hWxNonneg : native_zleq 0 wx
    · have hStuck :=
        EvaluateProofInternal.bv_eval_concat_list_repeat_rec_binary_stuck_of_neg wx nx
          hWxNonneg (native_int_to_nat i) hNatNeZero
      rw [hList (by intro h; cases h), hStuck] at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    · rcases EvaluateProofInternal.bv_eval_concat_list_repeat_rec_binary wx nx hWxNonneg
          (native_int_to_nat i) with
        ⟨m, hTerm, _hEval, hCanon⟩
      have hWidth : w = native_zmult i wx := by
        rw [hList (by intro h; cases h), hTerm] at h
        change
          Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral
                (native_zmult
                  (native_nat_to_int (native_int_to_nat i)) wx)) =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
        simp [hIntNat]
      have hRepeatTerm :
          __bv_eval_concat
              (__eo_list_repeat (Term.UOp UserOp.concat)
                (Term.Binary wx nx) (Term.Numeral i)) =
            Term.Binary (native_zmult i wx) m := by
        rw [hList (by intro h; cases h)]
        simpa [hIntNat] using hTerm
      have hCanon' :
          native_zeq m
            (native_mod_total m
              (native_int_pow2 (native_zmult i wx))) =
            true := by
        simpa [hIntNat] using hCanon
      exact ⟨wx, nx, m, rfl, hWxNonneg, hWidth, hRepeatTerm, hCanon'⟩
  · by_cases hxStuck : x = Term.Stuck
    · subst x
      simp [__eo_list_repeat, __bv_eval_concat] at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    · have hStuck :=
        EvaluateProofInternal.bv_eval_concat_list_repeat_rec_not_binary_stuck x hBinary
          (native_int_to_nat i) hNatNeZero
      rw [hList hxStuck, hStuck] at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h

theorem EvaluateProofInternal.eo_concat_args_string_of_typeof_seq
    (x y T : Term) :
    __eo_typeof (__eo_concat x y) =
      Term.Apply (Term.UOp UserOp.Seq) T ->
    ∃ sx : native_String, ∃ sy : native_String,
      x = Term.String sx ∧ y = Term.String sy ∧
        T = Term.UOp UserOp.Char := by
  cases x <;> intro h
  case String sx =>
    cases y <;> simp only [__eo_concat] at h
    case String sy =>
      change
        __eo_typeof (Term.String (native_str_concat sx sy)) =
          Term.Apply (Term.UOp UserOp.Seq) T at h
      change
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) =
          Term.Apply (Term.UOp UserOp.Seq) T at h
      cases h
      exact ⟨sx, sy, rfl, rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.Seq) T at h
      change Term.Stuck = Term.Apply (Term.UOp UserOp.Seq) T at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_concat] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_mk_binary (native_zplus wx wy)
              (native_binary_concat wx nx wy ny)) =
          Term.Apply (Term.UOp UserOp.Seq) T at h
      cases hWidth : native_zleq 0 (native_zplus wx wy)
      · simp [__eo_mk_binary, hWidth, native_ite] at h
        change Term.Stuck = Term.Apply (Term.UOp UserOp.Seq) T at h
        cases h
      · simp [__eo_mk_binary, hWidth, native_ite] at h
        change
          Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_zplus wx wy)) =
            Term.Apply (Term.UOp UserOp.Seq) T at h
        cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.Seq) T at h
      change Term.Stuck = Term.Apply (Term.UOp UserOp.Seq) T at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.Seq) T at h
    change Term.Stuck = Term.Apply (Term.UOp UserOp.Seq) T at h
    cases h

theorem EvaluateProofInternal.eo_concat_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_concat x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ wx nx wy ny : native_Int,
      x = Term.Binary wx nx ∧ y = Term.Binary wy ny ∧
        w = native_zplus wx wy ∧
          native_zleq 0 (native_zplus wx wy) = true := by
  cases x <;> intro h
  case String sx =>
    cases y <;> simp only [__eo_concat] at h
    case String sy =>
      change
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_concat] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_mk_binary (native_zplus wx wy)
              (native_binary_concat wx nx wy ny)) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases hWidth : native_zleq 0 (native_zplus wx wy)
      · simp [__eo_mk_binary, hWidth, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [__eo_mk_binary, hWidth, native_ite] at h
        cases h
        exact ⟨wx, nx, wy, ny, rfl, rfl, rfl, hWidth⟩
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

theorem EvaluateProofInternal.native_string_valid_of_string_type
    {str : native_String}
    (hTy : __smtx_typeof (__eo_to_smt (Term.String str)) =
      SmtType.Seq SmtType.Char) :
    native_string_valid str = true := by
  change __smtx_typeof (SmtTerm.String str) =
    SmtType.Seq SmtType.Char at hTy
  cases hValid : native_string_valid str <;>
    simp [__smtx_typeof, native_ite, hValid] at hTy ⊢

theorem EvaluateProofInternal.smt_string_seq_type_inv
    {str : native_String} {T : SmtType}
    (hTy : __smtx_typeof (__eo_to_smt (Term.String str)) =
      SmtType.Seq T) :
    native_string_valid str = true ∧ T = SmtType.Char := by
  change __smtx_typeof (SmtTerm.String str) = SmtType.Seq T at hTy
  rw [__smtx_typeof.eq_4] at hTy
  cases hValid : native_string_valid str
  · simp [native_ite, hValid] at hTy
  · simp [native_ite, hValid] at hTy
    constructor
    · rfl
    · cases hTy
      rfl

theorem EvaluateProofInternal.eo_len_seq_arg_of_nonstuck
    (x : Term) {T : SmtType}
    (hTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hLen : __eo_len x ≠ Term.Stuck) :
    ∃ str : native_String,
      x = Term.String str ∧ native_string_valid str = true ∧
        T = SmtType.Char := by
  cases x <;> simp [__eo_len] at hLen
  case String str =>
    rcases EvaluateProofInternal.smt_string_seq_type_inv hTy with ⟨hValid, hT⟩
    exact ⟨str, rfl, hValid, hT⟩
  case Binary w n =>
    change __smtx_typeof (SmtTerm.Binary w n) = SmtType.Seq T at hTy
    rw [__smtx_typeof.eq_5] at hTy
    cases hValid :
        native_and (native_zleq 0 w)
          (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
      simp [native_ite, hValid] at hTy

theorem EvaluateProofInternal.eo_extract_same_seq_int_args_of_nonstuck
    (x n : Term) {T : SmtType}
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (_hnTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hExt : __eo_extract x n n ≠ Term.Stuck) :
    ∃ str : native_String, ∃ i : native_Int,
      x = Term.String str ∧ n = Term.Numeral i ∧
        native_string_valid str = true ∧ T = SmtType.Char := by
  cases x <;> simp [__eo_extract] at hExt
  case String str =>
    cases n <;> simp at hExt
    case Numeral i =>
      rcases EvaluateProofInternal.smt_string_seq_type_inv hxTy with ⟨hValid, hT⟩
      exact ⟨str, i, rfl, rfl, hValid, hT⟩
  case Binary w nval =>
    change __smtx_typeof (SmtTerm.Binary w nval) = SmtType.Seq T at hxTy
    rw [__smtx_typeof.eq_5] at hxTy
    cases hValid :
        native_and (native_zleq 0 w)
          (native_zeq nval (native_mod_total nval (native_int_pow2 w))) <;>
      simp [native_ite, hValid] at hxTy

theorem EvaluateProofInternal.eo_extract_seq_args_of_nonstuck
    (x i j : Term) {T : SmtType}
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hExt : __eo_extract x i j ≠ Term.Stuck) :
    ∃ str : native_String, ∃ start stop : native_Int,
      x = Term.String str ∧ i = Term.Numeral start ∧
        j = Term.Numeral stop ∧ native_string_valid str = true ∧
          T = SmtType.Char := by
  cases x <;> simp [__eo_extract] at hExt
  case String str =>
    cases i <;> try
      exact False.elim (hExt rfl)
    case Numeral start =>
      cases j <;> try
        exact False.elim (hExt rfl)
      case Numeral stop =>
        rcases EvaluateProofInternal.smt_string_seq_type_inv hxTy with ⟨hValid, hT⟩
        exact ⟨str, start, stop, rfl, rfl, rfl, hValid, hT⟩
  case Binary w nval =>
    change __smtx_typeof (SmtTerm.Binary w nval) = SmtType.Seq T at hxTy
    rw [__smtx_typeof.eq_5] at hxTy
    cases hValid :
        native_and (native_zleq 0 w)
          (native_zeq nval (native_mod_total nval (native_int_pow2 w))) <;>
      simp [native_ite, hValid] at hxTy

theorem EvaluateProofInternal.eo_extract_seq_char_numeral_args_of_nonstuck
    (x : Term) (i j : native_Int)
    (hxTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char)
    (hExt : __eo_extract x (Term.Numeral i) (Term.Numeral j) ≠
      Term.Stuck) :
    ∃ str : native_String,
      x = Term.String str ∧ native_string_valid str = true := by
  cases x <;> simp [__eo_extract] at hExt
  case String str =>
    exact ⟨str, rfl, EvaluateProofInternal.native_string_valid_of_string_type hxTy⟩
  case Binary w nval =>
    change __smtx_typeof (SmtTerm.Binary w nval) =
      SmtType.Seq SmtType.Char at hxTy
    rw [__smtx_typeof.eq_5] at hxTy
    cases hValid :
        native_and (native_zleq 0 w)
          (native_zeq nval (native_mod_total nval (native_int_pow2 w))) <;>
      simp [native_ite, hValid] at hxTy

theorem EvaluateProofInternal.eo_find_seq_args_of_nonstuck
    (x y : Term) {T : SmtType}
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hFind : __eo_find x y ≠ Term.Stuck) :
    ∃ sx sy : native_String,
      x = Term.String sx ∧ y = Term.String sy ∧
          native_string_valid sx = true ∧
          native_string_valid sy = true ∧ T = SmtType.Char := by
  cases x <;> simp [__eo_find] at hFind
  case String sx =>
    cases y <;> simp at hFind
    case String sy =>
      rcases EvaluateProofInternal.smt_string_seq_type_inv hxTy with ⟨hSxValid, hT⟩
      subst T
      exact ⟨sx, sy, rfl, rfl, hSxValid,
        EvaluateProofInternal.native_string_valid_of_string_type hyTy, rfl⟩

theorem EvaluateProofInternal.eo_find_to_str_seq_args_of_nonstuck
    (x y : Term) {T : SmtType}
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hFind : __eo_find (__eo_to_str x) (__eo_to_str y) ≠ Term.Stuck) :
    ∃ sx sy : native_String,
      x = Term.String sx ∧ y = Term.String sy ∧
          native_string_valid sx = true ∧
          native_string_valid sy = true ∧ T = SmtType.Char := by
  cases x <;> simp [__eo_to_str, __eo_find] at hFind hxTy
  case String sx =>
    cases y <;> simp at hFind hyTy
    case String sy =>
      rcases EvaluateProofInternal.smt_string_seq_type_inv hxTy with ⟨hSxValid, hT⟩
      subst T
      exact ⟨sx, sy, rfl, rfl, hSxValid,
        EvaluateProofInternal.native_string_valid_of_string_type hyTy, rfl⟩
    case Numeral n =>
      change __smtx_typeof (SmtTerm.Numeral n) = SmtType.Seq T at hyTy
      rw [__smtx_typeof.eq_2] at hyTy
      cases hyTy
  case Numeral n =>
    change __smtx_typeof (SmtTerm.Numeral n) = SmtType.Seq T at hxTy
    rw [__smtx_typeof.eq_2] at hxTy
    cases hxTy

theorem EvaluateProofInternal.str_replace_run_repl_string_of_nonneg
    (s pat : native_String) (z : Term)
    (hZTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq SmtType.Char)
    (hNonneg : ¬ native_str_indexof s pat 0 < 0)
    (hRun :
      __eo_ite (__eo_is_neg
            (__eo_find (__eo_to_str (Term.String s))
              (__eo_to_str (Term.String pat))))
          (Term.String s)
          (__eo_concat
            (__eo_concat
              (__eo_extract (Term.String s) (Term.Numeral 0)
                (__eo_add
                  (__eo_find (__eo_to_str (Term.String s))
                    (__eo_to_str (Term.String pat)))
                  (Term.Numeral (-1 : native_Int)))) z)
            (__eo_extract (Term.String s)
              (__eo_add
                (__eo_find (__eo_to_str (Term.String s))
                  (__eo_to_str (Term.String pat)))
                (__eo_len (Term.String pat)))
              (__eo_len (Term.String s)))) ≠ Term.Stuck) :
    ∃ repl : native_String,
      z = Term.String repl ∧ native_string_valid repl = true := by
  have hLt : native_zlt (native_str_indexof s pat 0) 0 = false := by
    rw [show native_zlt (native_str_indexof s pat 0) 0 =
      decide (native_str_indexof s pat 0 < 0) by rfl]
    exact decide_eq_false hNonneg
  cases z <;>
    simp [__eo_find, __eo_to_str, __eo_is_neg, __eo_ite, native_ite,
      native_teq, hLt, __eo_extract, __eo_add, __eo_len, __eo_concat,
      native_zplus, native_zneg, native_str_len] at hRun hZTy
  case String repl =>
    exact ⟨repl, rfl, EvaluateProofInternal.native_string_valid_of_string_type hZTy⟩

theorem EvaluateProofInternal.smt_model_eval_seq_of_type_local
    (M : SmtModel) (hM : model_wf M)
    (t : SmtTerm) (T : SmtType)
    (hTy : __smtx_typeof t = SmtType.Seq T) :
    ∃ seq : SmtSeq, __smtx_model_eval M t = SmtValue.Seq seq := by
  have hNN : __smtx_typeof t ≠ SmtType.None := by
    rw [hTy]
    simp
  have hValTy :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM t hNN
  exact seq_value_canonical (by simpa [hTy] using hValTy)

theorem EvaluateProofInternal.str_to_code_result_string
    {str : native_String}
    (hValid : native_string_valid str = true) :
    __eo_ite (__eo_eq (__eo_len (Term.String str)) (Term.Numeral 1))
        (__eo_to_z (Term.String str))
        (__eo_ite (__eo_is_z (__eo_len (Term.String str)))
          (Term.Numeral (-1 : native_Int))
          (__eo_mk_apply (Term.UOp UserOp.str_to_code) (Term.String str))) =
      Term.Numeral (native_str_to_code str) := by
  cases str with
  | nil =>
      simp [__eo_len, __eo_eq, __eo_ite, __eo_is_z, __eo_is_z_internal,
        native_str_len, native_str_to_code, native_ite, native_teq,
        native_and, native_not]
  | cons c cs =>
      cases cs with
      | nil =>
          have hc : native_char_valid c = true := by
            simpa [native_string_valid] using hValid
          rw [EvaluateProofInternal.eo_to_z_singleton hc]
          simp [__eo_len, __eo_eq, __eo_ite, native_str_len,
            native_str_to_code, native_ite, native_teq, hc]
      | cons d ds =>
          have hNonneg : 0 ≤ (Int.ofNat ds.length) := Int.natCast_nonneg _
          have hLenNe : ¬(1 : Int) = Int.ofNat ds.length + 1 + 1 := by
            omega
          simp [__eo_len, __eo_eq, __eo_ite, __eo_is_z,
            __eo_is_z_internal, native_str_len, native_str_to_code,
            native_ite, native_teq, native_and, native_not]
          by_cases hLen : (1 : Int) = Int.ofNat ds.length + 1 + 1
          · exact False.elim (hLenNe hLen)
          · rfl

def EvaluateProofInternal.native_str_to_int_rev_acc :
    native_String -> native_Int -> native_Int -> native_Int
  | [], _e, n => n
  | c :: cs, e, n =>
      let d := native_zplus (c : native_Int) (-48 : native_Int)
      match native_and (native_zlt d 10) (native_not (native_zlt d 0)) with
      | true =>
          EvaluateProofInternal.native_str_to_int_rev_acc cs (native_zmult e 10)
            (native_zplus (native_zmult d e) n)
      | false => -1

def EvaluateProofInternal.native_decimal_digits_lsb : native_String -> native_Nat
  | [] => 0
  | c :: cs => (c - 48) + 10 * EvaluateProofInternal.native_decimal_digits_lsb cs

theorem EvaluateProofInternal.str_to_int_guard_eq_digit (c : native_Char) :
    native_and
        (native_zlt (native_zplus (c : native_Int) (-48 : native_Int)) 10)
        (native_not
          (native_zlt (native_zplus (c : native_Int) (-48 : native_Int)) 0)) =
      impl_native_char_is_digit c := by
  unfold impl_native_char_is_digit native_zplus native_zlt native_not native_and
  by_cases h48 : 48 ≤ c
  · by_cases h57 : c ≤ 57
    · have h48i : (48 : Int) ≤ (c : Int) := Int.ofNat_le.mpr h48
      have h57i : (c : Int) ≤ (57 : Int) := Int.ofNat_le.mpr h57
      have hLt : (c : Int) + (-48 : Int) < 10 := by omega
      have hNotNeg : ¬(c : Int) + (-48 : Int) < 0 := by omega
      simp [h48, h57, hLt, hNotNeg]
    · have h57lt : 57 < c := Nat.lt_of_not_ge h57
      have h57lti : (57 : Int) < (c : Int) := Int.ofNat_lt.mpr h57lt
      have hNotLt : ¬(c : Int) + (-48 : Int) < 10 := by omega
      simp [h48, h57, hNotLt]
  · have h48lt : c < 48 := Nat.lt_of_not_ge h48
    have h48lti : (c : Int) < (48 : Int) := Int.ofNat_lt.mpr h48lt
    have hNeg : (c : Int) + (-48 : Int) < 0 := by omega
    simp [h48, hNeg]

theorem EvaluateProofInternal.str_to_int_eval_rec_strCharChain :
    ∀ (xs : native_String) (e n : native_Int),
      native_string_valid xs = true ->
        __str_to_int_eval_rec (EvaluateProofInternal.strCharChain xs)
            (Term.Numeral e) (Term.Numeral n) =
          Term.Numeral (EvaluateProofInternal.native_str_to_int_rev_acc xs e n)
  | [], _e, _n, _hValid => by
      rfl
  | c :: cs, e, n, hValid => by
      rcases EvaluateProofInternal.native_string_valid_cons_parts_local hValid with
        ⟨hcValid, hcsValid⟩
      unfold EvaluateProofInternal.strCharChain
      unfold __str_to_int_eval_rec
      rw [EvaluateProofInternal.eo_to_z_singleton hcValid]
      dsimp [__eo_add, __eo_mul]
      let d := native_zplus (c : native_Int) (-48 : native_Int)
      have hGuardTerm :
          __eo_and (__eo_gt (Term.Numeral 10) (Term.Numeral d))
              (__eo_not (__eo_is_neg (Term.Numeral d))) =
            Term.Boolean
              (native_and (native_zlt d 10) (native_not (native_zlt d 0))) := by
        simp [__eo_gt, __eo_is_neg, __eo_not, __eo_and, d]
      rw [hGuardTerm]
      cases hGuard :
          native_and (native_zlt d 10) (native_not (native_zlt d 0))
      · simp [eo_ite_false, EvaluateProofInternal.native_str_to_int_rev_acc, d, hGuard]
      · rw [eo_ite_true]
        simp [EvaluateProofInternal.native_str_to_int_rev_acc, d, hGuard]
        exact EvaluateProofInternal.str_to_int_eval_rec_strCharChain cs
          (native_zmult e 10)
          (native_zplus (native_zmult d e) n) hcsValid

theorem EvaluateProofInternal.native_str_to_int_rev_acc_all_digits :
    ∀ (xs : native_String) (e n : native_Int),
      xs.all impl_native_char_is_digit = true ->
        EvaluateProofInternal.native_str_to_int_rev_acc xs e n =
          native_zplus n
            (native_zmult e (Int.ofNat (EvaluateProofInternal.native_decimal_digits_lsb xs)))
  | [], e, n, _hDigits => by
      simp [EvaluateProofInternal.native_str_to_int_rev_acc, EvaluateProofInternal.native_decimal_digits_lsb,
        native_zplus, native_zmult]
  | c :: cs, e, n, hDigits => by
      have hDigitParts :
          impl_native_char_is_digit c = true ∧
            cs.all impl_native_char_is_digit = true := by
        simpa using hDigits
      have hDigit : impl_native_char_is_digit c = true := hDigitParts.1
      have hTailDigits : cs.all impl_native_char_is_digit = true := hDigitParts.2
      have hGuard :
          native_and
              (native_zlt
                (native_zplus (c : native_Int) (-48 : native_Int)) 10)
              (native_not
                (native_zlt
                  (native_zplus (c : native_Int) (-48 : native_Int)) 0)) =
            true :=
        (EvaluateProofInternal.str_to_int_guard_eq_digit c).trans hDigit
      simp [EvaluateProofInternal.native_str_to_int_rev_acc, hGuard]
      have hTail :=
        EvaluateProofInternal.native_str_to_int_rev_acc_all_digits cs
          (native_zmult e 10)
          (native_zplus
            (native_zmult
              (native_zplus (c : native_Int) (-48 : native_Int)) e) n)
          hTailDigits
      rw [hTail]
      unfold EvaluateProofInternal.native_decimal_digits_lsb native_zplus native_zmult
      have hRange : 48 ≤ c ∧ c ≤ 57 := by
        unfold impl_native_char_is_digit at hDigit
        simpa using hDigit
      have hCast :
          ((c - 48 : Nat) : Int) = (c : Int) + (-48 : Int) := by
        rw [Int.ofNat_sub hRange.1]
        rfl
      rw [Int.natCast_add, Int.natCast_mul]
      rw [hCast]
      cases cs <;>
        simp [EvaluateProofInternal.native_decimal_digits_lsb, Int.mul_add,
          Int.add_assoc, Int.add_comm, Int.add_left_comm, Int.mul_assoc,
          Int.mul_comm, Int.mul_left_comm]

theorem EvaluateProofInternal.native_str_to_int_rev_acc_not_all_digits :
    ∀ (xs : native_String) (e n : native_Int),
      xs.all impl_native_char_is_digit ≠ true ->
        EvaluateProofInternal.native_str_to_int_rev_acc xs e n = (-1 : native_Int)
  | [], _e, _n, hDigits => by
      simp at hDigits
  | c :: cs, e, n, hDigits => by
      by_cases hDigit : impl_native_char_is_digit c = true
      · have hTailNot : cs.all impl_native_char_is_digit ≠ true := by
          intro hTail
          apply hDigits
          simp [hDigit, hTail]
        have hGuard :
            native_and
                (native_zlt
                  (native_zplus (c : native_Int) (-48 : native_Int)) 10)
                (native_not
                  (native_zlt
                    (native_zplus (c : native_Int) (-48 : native_Int)) 0)) =
              true :=
          (EvaluateProofInternal.str_to_int_guard_eq_digit c).trans hDigit
        simp [EvaluateProofInternal.native_str_to_int_rev_acc, hGuard]
        exact EvaluateProofInternal.native_str_to_int_rev_acc_not_all_digits cs
          (native_zmult e 10)
          (native_zplus
            (native_zmult
              (native_zplus (c : native_Int) (-48 : native_Int)) e) n)
          hTailNot
      · have hGuard := EvaluateProofInternal.str_to_int_guard_eq_digit c
        have hGuardFalse :
            native_and
                (native_zlt
                  (native_zplus (c : native_Int) (-48 : native_Int)) 10)
                (native_not
                  (native_zlt
                    (native_zplus (c : native_Int) (-48 : native_Int)) 0)) =
              false := by
          rw [hGuard]
          cases h : impl_native_char_is_digit c <;> simp [h] at hDigit ⊢
        simp [EvaluateProofInternal.native_str_to_int_rev_acc, hGuardFalse]

theorem EvaluateProofInternal.native_decimal_digits_lsb_append_singleton :
    ∀ (xs : native_String) (c : native_Char),
      EvaluateProofInternal.native_decimal_digits_lsb (xs ++ [c]) =
        EvaluateProofInternal.native_decimal_digits_lsb xs + (c - 48) * 10 ^ xs.length
  | [], c => by
      simp [EvaluateProofInternal.native_decimal_digits_lsb]
  | x :: xs, c => by
      rw [show (x :: xs) ++ [c] = x :: (xs ++ [c]) by rfl]
      change
        (x - 48) + 10 * EvaluateProofInternal.native_decimal_digits_lsb (xs ++ [c]) =
          (x - 48) + 10 * EvaluateProofInternal.native_decimal_digits_lsb xs +
            (c - 48) * 10 ^ (xs.length + 1)
      rw [EvaluateProofInternal.native_decimal_digits_lsb_append_singleton xs c]
      simp [Nat.pow_succ, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_assoc,
        Nat.mul_comm]

theorem EvaluateProofInternal.native_decimal_digits_to_nat_foldl_acc :
    ∀ (xs : native_String) (acc : native_Nat),
      xs.foldl (fun acc c => 10 * acc + (c - 48)) acc =
        acc * 10 ^ xs.length + impl_native_decimal_digits_to_nat xs
  | [], acc => by
      simp [impl_native_decimal_digits_to_nat]
  | c :: cs, acc => by
      rw [show
          (c :: cs).foldl (fun acc c => 10 * acc + (c - 48)) acc =
            cs.foldl (fun acc c => 10 * acc + (c - 48))
              (10 * acc + (c - 48)) by
        rfl]
      rw [EvaluateProofInternal.native_decimal_digits_to_nat_foldl_acc cs
        (10 * acc + (c - 48))]
      rw [show impl_native_decimal_digits_to_nat (c :: cs) =
          (c :: cs).foldl (fun acc c => 10 * acc + (c - 48)) 0 by
        rfl]
      rw [show
          (c :: cs).foldl (fun acc c => 10 * acc + (c - 48)) 0 =
            cs.foldl (fun acc c => 10 * acc + (c - 48)) (c - 48) by
        simp]
      rw [EvaluateProofInternal.native_decimal_digits_to_nat_foldl_acc cs (c - 48)]
      simp [Nat.pow_succ, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc,
        Nat.mul_comm]

theorem EvaluateProofInternal.native_decimal_digits_to_nat_cons
    (c : native_Char) (cs : native_String) :
    impl_native_decimal_digits_to_nat (c :: cs) =
      (c - 48) * 10 ^ cs.length + impl_native_decimal_digits_to_nat cs := by
  rw [show impl_native_decimal_digits_to_nat (c :: cs) =
      (c :: cs).foldl (fun acc c => 10 * acc + (c - 48)) 0 by
    rfl]
  rw [show
      (c :: cs).foldl (fun acc c => 10 * acc + (c - 48)) 0 =
        cs.foldl (fun acc c => 10 * acc + (c - 48)) (c - 48) by
    simp]
  exact EvaluateProofInternal.native_decimal_digits_to_nat_foldl_acc cs (c - 48)

theorem EvaluateProofInternal.native_decimal_digits_lsb_reverse_eq :
    ∀ s : native_String,
      EvaluateProofInternal.native_decimal_digits_lsb s.reverse = impl_native_decimal_digits_to_nat s
  | [] => by
      rfl
  | c :: cs => by
      rw [List.reverse_cons]
      rw [EvaluateProofInternal.native_decimal_digits_lsb_append_singleton cs.reverse c]
      rw [EvaluateProofInternal.native_decimal_digits_lsb_reverse_eq cs]
      rw [EvaluateProofInternal.native_decimal_digits_to_nat_cons c cs]
      simp [List.length_reverse, Nat.add_comm]

theorem EvaluateProofInternal.list_all_reverse_eq {α : Type} (p : α -> Bool) :
    ∀ xs : List α, xs.reverse.all p = xs.all p
  | [] => by
      rfl
  | x :: xs => by
      rw [List.reverse_cons, List.all_append]
      rw [EvaluateProofInternal.list_all_reverse_eq p xs]
      cases hp : p x <;> cases hx : xs.all p <;> simp [hp, hx]

theorem EvaluateProofInternal.str_to_int_result_string
    {str : native_String}
    (hValid : native_string_valid str = true) :
    __eo_ite (__eo_is_str (Term.String str))
        (__eo_ite (__eo_eq (Term.String str) (Term.String []))
          (Term.Numeral (-1 : native_Int))
          (__str_to_int_eval_rec
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__str_nary_intro (Term.String str))))
            (Term.Numeral 1) (Term.Numeral 0)))
        (__eo_mk_apply (Term.UOp UserOp.str_to_int) (Term.String str)) =
      Term.Numeral (native_str_to_int str) := by
  have hIsStr :
      __eo_is_str (Term.String str) = Term.Boolean true := by
    simp [__eo_is_str, __eo_is_str_internal, native_teq, native_and,
      native_not]
  rw [hIsStr, eo_ite_true]
  cases str with
  | nil =>
      simp [__eo_eq, __eo_ite, native_teq, native_ite, native_str_to_int]
  | cons c cs =>
      rw [show __eo_eq (Term.String (c :: cs)) (Term.String []) =
          Term.Boolean false by
        simp [__eo_eq, native_teq]]
      rw [eo_ite_false]
      rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain]
      rw [EvaluateProofInternal.eo_list_rev_strCharChain]
      have hRevValid :
          native_string_valid (c :: cs).reverse = true := by
        unfold native_string_valid at hValid ⊢
        rw [EvaluateProofInternal.list_all_reverse_eq native_char_valid, hValid]
      rw [EvaluateProofInternal.str_to_int_eval_rec_strCharChain (c :: cs).reverse 1 0
        hRevValid]
      by_cases hDigits : (c :: cs).all impl_native_char_is_digit = true
      · have hRevDigits :
            (c :: cs).reverse.all impl_native_char_is_digit = true := by
          rw [EvaluateProofInternal.list_all_reverse_eq impl_native_char_is_digit, hDigits]
        rw [EvaluateProofInternal.native_str_to_int_rev_acc_all_digits (c :: cs).reverse 1 0
          hRevDigits]
        rw [EvaluateProofInternal.native_decimal_digits_lsb_reverse_eq (c :: cs)]
        simp [native_str_to_int, hDigits, native_zplus, native_zmult]
      · have hRevDigits :
            (c :: cs).reverse.all impl_native_char_is_digit ≠ true := by
          intro hRev
          apply hDigits
          rwa [EvaluateProofInternal.list_all_reverse_eq impl_native_char_is_digit] at hRev
        rw [EvaluateProofInternal.native_str_to_int_rev_acc_not_all_digits (c :: cs).reverse 1 0
          hRevDigits]
        simp [native_str_to_int, hDigits]

theorem EvaluateProofInternal.str_to_int_result_non_string
    {t : Term}
    (hNotString : ∀ s : native_String, t ≠ Term.String s)
    (hTNe : t ≠ Term.Stuck) :
    __eo_ite (__eo_is_str t)
        (__eo_ite (__eo_eq t (Term.String []))
          (Term.Numeral (-1 : native_Int))
          (__str_to_int_eval_rec
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__str_nary_intro t)))
            (Term.Numeral 1) (Term.Numeral 0)))
        (__eo_mk_apply (Term.UOp UserOp.str_to_int) t) =
      Term.Apply (Term.UOp UserOp.str_to_int) t := by
  rw [EvaluateProofInternal.eo_is_str_false_of_not_string t hNotString, eo_ite_false]
  exact EvaluateProofInternal.eo_mk_apply_eq_apply_of_args_ne_stuck _ _
    (by intro h; cases h) hTNe

theorem EvaluateProofInternal.native_string_valid_reverse_local
    {str : native_String}
    (hValid : native_string_valid str = true) :
    native_string_valid str.reverse = true := by
  rw [native_string_valid, List.all_eq_true] at hValid ⊢
  intro c hc
  exact hValid c (by simpa using List.mem_reverse.mp hc)

theorem EvaluateProofInternal.native_string_valid_append_local
    {xs ys : native_String}
    (hxs : native_string_valid xs = true)
    (hys : native_string_valid ys = true) :
    native_string_valid (xs ++ ys) = true := by
  rw [native_string_valid, List.all_eq_true] at hxs hys ⊢
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hxs c hc
  · exact hys c hc

theorem EvaluateProofInternal.native_string_valid_substr_local
    {str : native_String} (i n : native_Int)
    (hValid : native_string_valid str = true) :
    native_string_valid (native_str_substr str i n) = true := by
  unfold native_str_substr
  by_cases hGuard :
      (decide (i < 0) || decide (n ≤ 0) ||
          decide (i ≥ native_str_len str)) = true
  · simp [hGuard, native_string_valid]
  ·
    simp [hGuard]
    exact native_string_valid_take _
      (native_string_valid_drop (Int.toNat i) hValid)

theorem EvaluateProofInternal.eo_eq_true_eq_local
    (x y : Term) :
    __eo_eq x y = Term.Boolean true ->
    x = y := by
  intro h
  have hyx : y = x := by
    cases x <;> cases y <;> simp [__eo_eq, native_teq] at h ⊢ <;>
      assumption
  exact hyx.symm

theorem EvaluateProofInternal.eo_requires_arg_eq_of_ne_stuck_local
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
      x = y := by
  intro h
  unfold __eo_requires at h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [hxy, native_ite] at h

theorem EvaluateProofInternal.eo_requires_result_ne_stuck_of_ne_stuck_local
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
      z ≠ Term.Stuck := by
  intro h hz
  have hxy : x = y := EvaluateProofInternal.eo_requires_arg_eq_of_ne_stuck_local h
  subst y
  subst z
  simp [__eo_requires, native_ite, native_not, native_teq] at h

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

theorem EvaluateProofInternal.native_unpack_pack_seq_local (T : SmtType) :
    ∀ xs : List SmtValue, native_unpack_seq (native_pack_seq T xs) = xs
  | [] => rfl
  | _ :: xs => by
      simp [native_pack_seq, native_unpack_seq,
        EvaluateProofInternal.native_unpack_pack_seq_local T xs]

theorem EvaluateProofInternal.elem_typeof_pack_seq_local (T : SmtType) :
    ∀ xs : List SmtValue,
      __smtx_elem_typeof_seq_value (native_pack_seq T xs) = T
  | [] => rfl
  | _ :: xs => by
      simp [native_pack_seq, __smtx_elem_typeof_seq_value,
        EvaluateProofInternal.elem_typeof_pack_seq_local T xs]

theorem EvaluateProofInternal.native_seq_extract_pack_string
    (s : native_String) (i n : native_Int) :
    native_pack_seq SmtType.Char
        (native_seq_extract (native_unpack_seq (native_pack_string s)) i n) =
      native_pack_string (native_str_substr s i n) := by
  simp only [native_pack_string, native_seq_extract, native_str_substr,
    native_str_len, EvaluateProofInternal.native_unpack_pack_seq_local]
  by_cases h : (i < 0 ∨ n ≤ 0) ∨ ↑s.length ≤ i
  · simp [h]
  · simp [h, List.map_take, List.map_drop]

theorem EvaluateProofInternal.native_seq_extract_pack_string_one
    (s : native_String) (i : native_Int) :
    native_pack_seq SmtType.Char
        (native_seq_extract (native_unpack_seq (native_pack_string s)) i 1) =
      native_pack_string (native_str_substr s i 1) :=
  EvaluateProofInternal.native_seq_extract_pack_string s i 1

theorem EvaluateProofInternal.native_pack_string_injective :
    Function.Injective native_pack_string := by
  intro s t h
  have hUnpack := congrArg native_unpack_string h
  simpa [RuleProofs.native_unpack_string_pack_string] using hUnpack

theorem EvaluateProofInternal.smtx_model_eval_str_leq_pack_string
    (s t : native_String) :
    __smtx_model_eval_str_leq
        (SmtValue.Seq (native_pack_string s))
        (SmtValue.Seq (native_pack_string t)) =
      SmtValue.Boolean (native_or (decide (s = t)) (native_str_lt s t)) := by
  unfold __smtx_model_eval_str_leq
  simp only [__smtx_model_eval_str_lt,
    RuleProofs.native_unpack_string_pack_string]
  by_cases hEq : s = t
  · subst t
    simp [__smtx_model_eval_eq, __smtx_model_eval_or, native_veq,
      native_or]
  · have hPackNe : native_pack_string s ≠ native_pack_string t := by
      intro hPack
      exact hEq (EvaluateProofInternal.native_pack_string_injective hPack)
    simp [__smtx_model_eval_eq, __smtx_model_eval_or, native_veq,
      native_or, hEq, hPackNe]

theorem EvaluateProofInternal.native_seq_prefix_eq_map_char
    (a b : native_String) :
    native_seq_prefix_eq (a.map SmtValue.Char) (b.map SmtValue.Char) =
      native_string_prefix_eq a b := by
  induction a generalizing b with
  | nil =>
      simp [native_seq_prefix_eq, native_string_prefix_eq]
  | cons c cs ih =>
      cases b with
      | nil =>
          simp [native_seq_prefix_eq, native_string_prefix_eq]
      | cons d ds =>
          simp [native_seq_prefix_eq, native_string_prefix_eq, native_veq,
            ih]

theorem EvaluateProofInternal.native_string_prefix_eq_length_le
    (pat s : native_String)
    (hPrefix : native_string_prefix_eq pat s = true) :
    pat.length ≤ s.length := by
  induction pat generalizing s with
  | nil =>
      simp
  | cons p ps ih =>
      cases s with
      | nil =>
          simp [native_string_prefix_eq] at hPrefix
      | cons c cs =>
          have hTail :
              native_string_prefix_eq ps cs = true := by
            by_cases hpc : p = c
            · subst c
              simpa [native_string_prefix_eq] using hPrefix
            · have hcp : c ≠ p := by
                intro h
                exact hpc h.symm
              simp [native_string_prefix_eq, hpc] at hPrefix
          have hLe := ih cs hTail
          simp [hLe]

theorem EvaluateProofInternal.native_str_indexof_rec_past_end_nonempty
    (s pat : native_String) (i fuel : Nat)
    (hLen : s.length ≤ i) (hPat : pat ≠ []) :
    impl_native_str_indexof_rec s pat i fuel = -1 := by
  induction fuel generalizing i with
  | zero =>
      simp [impl_native_str_indexof_rec]
  | succ fuel ih =>
      unfold impl_native_str_indexof_rec
      have hDrop : s.drop i = [] := List.drop_eq_nil_of_le hLen
      have hPrefix : native_string_prefix_eq pat (s.drop i) = false := by
        cases pat with
        | nil =>
            contradiction
        | cons p ps =>
            simp [native_string_prefix_eq, hDrop]
      simp [hPrefix, ih (i + 1) (by omega)]

theorem EvaluateProofInternal.native_seq_indexof_rec_map_char_prefix
    (pre cur pat : native_String) (fuel : Nat) :
    native_seq_indexof_rec (cur.map SmtValue.Char)
        (pat.map SmtValue.Char) pre.length fuel =
      impl_native_str_indexof_rec (pre ++ cur) pat pre.length fuel := by
  induction fuel generalizing pre cur with
  | zero =>
      simp [native_seq_indexof_rec, impl_native_str_indexof_rec]
  | succ fuel ih =>
      rw [Smtm.native_seq_indexof_rec.eq_def, impl_native_str_indexof_rec]
      rw [EvaluateProofInternal.native_seq_prefix_eq_map_char]
      rw [show (pre ++ cur).drop pre.length = cur by simp]
      by_cases hPrefix : native_string_prefix_eq pat cur = true
      · simp [hPrefix]
      · simp [hPrefix]
        cases cur with
        | nil =>
            cases pat with
            | nil =>
                simp [native_string_prefix_eq] at hPrefix
            | cons p ps =>
                simpa using (EvaluateProofInternal.native_str_indexof_rec_past_end_nonempty pre
                  (p :: ps) (pre.length + 1) fuel
                  (by simp) (by simp)).symm
        | cons c cs =>
            have hAppend : pre ++ c :: cs = (pre ++ [c]) ++ cs := by
              simp [List.append_assoc]
            rw [hAppend]
            simpa [List.length_append] using ih (pre ++ [c]) cs

theorem EvaluateProofInternal.native_seq_indexof_rec_offset_local
    (xs pat : List SmtValue) :
    ∀ (i off fuel : Nat),
      native_seq_indexof_rec xs pat (i + off) fuel =
        (let r := native_seq_indexof_rec xs pat i fuel
         if r = (-1 : native_Int) then (-1 : native_Int)
         else r + Int.ofNat off)
  | _i, _off, 0 => by
      simp [native_seq_indexof_rec]
  | i, off, fuel + 1 => by
      by_cases hPrefix : native_seq_prefix_eq pat xs = true
      · unfold native_seq_indexof_rec
        rw [if_pos hPrefix, if_pos hPrefix]
        have hne : (Int.ofNat i : native_Int) ≠ -1 := by
          intro h
          have hNonneg : (0 : native_Int) ≤ Int.ofNat i :=
            Int.natCast_nonneg i
          have hNeg : ¬ (0 : native_Int) ≤ -1 := by decide
          have hBad : (0 : native_Int) ≤ -1 := by
            rw [← h]
            exact hNonneg
          exact hNeg hBad
        rw [if_neg hne]
        simp
      · unfold native_seq_indexof_rec
        rw [if_neg hPrefix, if_neg hPrefix]
        cases xs with
        | nil =>
            simp
        | cons _ xs =>
            rw [show i + off + 1 = (i + 1) + off by omega]
            exact EvaluateProofInternal.native_seq_indexof_rec_offset_local xs pat
              (i + 1) off fuel

theorem EvaluateProofInternal.native_str_indexof_rec_cons_offset
    (c : native_Char) (cs pat : native_String) (fuel : Nat) :
    impl_native_str_indexof_rec (c :: cs) pat 1 fuel =
      (let r := impl_native_str_indexof_rec cs pat 0 fuel
       if r = (-1 : native_Int) then (-1 : native_Int) else r + 1) := by
  have hHead :=
    EvaluateProofInternal.native_seq_indexof_rec_map_char_prefix ([c] : native_String) cs pat
      fuel
  have hTail :=
    EvaluateProofInternal.native_seq_indexof_rec_map_char_prefix ([] : native_String) cs pat
      fuel
  have hOffset :=
    EvaluateProofInternal.native_seq_indexof_rec_offset_local
      (cs.map SmtValue.Char) (pat.map SmtValue.Char) 0 1 fuel
  rw [show ([c] : native_String).length = 1 by rfl] at hHead
  rw [show ([] : native_String).length = 0 by rfl] at hTail
  change
    impl_native_str_indexof_rec (([c] : native_String) ++ cs) pat 1 fuel =
      (let r := impl_native_str_indexof_rec (([] : native_String) ++ cs) pat 0 fuel
       if r = (-1 : native_Int) then (-1 : native_Int) else r + 1)
  rw [← hHead, hOffset, hTail]
  simp

theorem EvaluateProofInternal.native_str_indexof_cons_not_prefix
    (c p : native_Char) (cs ps : native_String)
    (hPrefix :
      native_string_prefix_eq (p :: ps) (c :: cs) = false) :
    native_str_indexof (c :: cs) (p :: ps) 0 =
      (let r := native_str_indexof cs (p :: ps) 0
       if r = (-1 : native_Int) then (-1 : native_Int) else r + 1) := by
  unfold native_str_indexof
  by_cases hTail : ps.length + 1 ≤ cs.length
  · have hParent : ps.length + 1 ≤ cs.length + 1 := by omega
    simp [native_str_len, hParent, hTail]
    have hFuel :
        cs.length - ps.length + 1 =
          (cs.length - (ps.length + 1) + 1) + 1 := by
      omega
    rw [hFuel]
    unfold impl_native_str_indexof_rec
    simp [hPrefix]
    exact EvaluateProofInternal.native_str_indexof_rec_cons_offset c cs (p :: ps)
      (cs.length - (ps.length + 1) + 1)
  · by_cases hParent : ps.length + 1 ≤ cs.length + 1
    · simp [native_str_len, hParent, hTail]
      have hFuel :
          cs.length - ps.length + 1 = 1 := by
        omega
      rw [hFuel]
      unfold impl_native_str_indexof_rec
      simp [hPrefix, impl_native_str_indexof_rec]
    · simp [native_str_len, hParent, hTail]

theorem EvaluateProofInternal.native_seq_indexof_le_len_sub_pat_of_pat_le_len_local
    (xs pat : List SmtValue) (i : native_Int) :
    pat.length ≤ xs.length →
      native_seq_indexof xs pat i ≤
        Int.ofNat xs.length - Int.ofNat pat.length := by
  intro hPatLe
  rw [native_seq_indexof_eq_rec]
  split
  · have hNonneg :
        (0 : native_Int) ≤ Int.ofNat xs.length - Int.ofNat pat.length := by
      exact Int.sub_nonneg.mpr (Int.ofNat_le.mpr hPatLe)
    exact Int.le_trans (by decide : (-1 : native_Int) ≤ 0) hNonneg
  · dsimp
    split
    · rename_i _hStart _hBounds
      cases native_seq_indexof_rec_bound (xs.drop (Int.toNat i)) pat
          (Int.toNat i)
          (xs.length - (Int.toNat i + pat.length) + 1) with
      | inl hRec =>
          rw [hRec]
          have hNonneg :
              (0 : native_Int) ≤
                Int.ofNat xs.length - Int.ofNat pat.length := by
            exact Int.sub_nonneg.mpr (Int.ofNat_le.mpr hPatLe)
          exact Int.le_trans (by decide : (-1 : native_Int) ≤ 0) hNonneg
      | inr hRec =>
          rcases hRec with ⟨j, hRec, hjlt⟩
          rw [hRec]
          have hNat :
              Int.toNat i + j ≤ xs.length - pat.length := by
            omega
          calc
            Int.ofNat (Int.toNat i + j) ≤
                Int.ofNat (xs.length - pat.length) :=
              Int.ofNat_le.mpr hNat
            _ = Int.ofNat xs.length - Int.ofNat pat.length :=
              Int.ofNat_sub hPatLe
    · have hNonneg :
          (0 : native_Int) ≤ Int.ofNat xs.length - Int.ofNat pat.length := by
        exact Int.sub_nonneg.mpr (Int.ofNat_le.mpr hPatLe)
      exact Int.le_trans (by decide : (-1 : native_Int) ≤ 0) hNonneg

theorem EvaluateProofInternal.native_seq_indexof_zero_nonneg_pat_le_len_local
    (xs pat : List SmtValue)
    (hIdx : 0 ≤ native_seq_indexof xs pat 0) :
    pat.length ≤ xs.length := by
  rw [native_seq_indexof_eq_rec] at hIdx
  simp only [Int.reduceLT, ↓reduceIte, Int.toNat_zero, Nat.zero_add] at hIdx
  split at hIdx
  · assumption
  · have hContr : ¬ ((0 : native_Int) ≤ -1) := by decide
    exact False.elim (hContr hIdx)

theorem EvaluateProofInternal.native_seq_indexof_zero_nonneg_toNat_add_pat_le_len_local
    (xs pat : List SmtValue)
    (hIdxNonneg : 0 ≤ native_seq_indexof xs pat 0) :
    Int.toNat (native_seq_indexof xs pat 0) + pat.length ≤ xs.length := by
  have hPatLe : pat.length ≤ xs.length :=
    EvaluateProofInternal.native_seq_indexof_zero_nonneg_pat_le_len_local xs pat hIdxNonneg
  have hIdxLe :=
    EvaluateProofInternal.native_seq_indexof_le_len_sub_pat_of_pat_le_len_local xs pat 0 hPatLe
  rw [← Int.ofNat_le]
  have hAdd := Int.add_le_of_le_sub_right hIdxLe
  have hMax :
      max (native_seq_indexof xs pat 0) 0 =
        native_seq_indexof xs pat 0 :=
    Int.max_eq_left hIdxNonneg
  simpa [Int.ofNat_toNat, hMax] using hAdd

theorem EvaluateProofInternal.native_seq_indexof_map_char_zero
    (s t : native_String) :
    native_seq_indexof (s.map SmtValue.Char) (t.map SmtValue.Char) 0 =
      native_str_indexof s t 0 := by
  rw [native_seq_indexof_eq_rec]
  unfold native_str_indexof
  simp [native_str_len]
  by_cases hBound : t.length ≤ s.length
  · simp [hBound]
    have hRec :=
      EvaluateProofInternal.native_seq_indexof_rec_map_char_prefix ([] : native_String) s t
        (s.length - t.length + 1)
    simpa using hRec
  · simp [hBound]

theorem EvaluateProofInternal.native_str_indexof_eq_neg_one_of_neg
    (s pat : native_String)
    (hNeg : native_str_indexof s pat 0 < 0) :
    native_str_indexof s pat 0 = -1 := by
  have hCases :=
    native_seq_indexof_eq_neg_one_or_ge (s.map SmtValue.Char)
      (pat.map SmtValue.Char) (0 : native_Int)
  rw [EvaluateProofInternal.native_seq_indexof_map_char_zero] at hCases
  rcases hCases with hEq | hGe
  · exact hEq
  · have hNot : ¬ native_str_indexof s pat 0 < 0 :=
      Int.not_lt_of_ge hGe
    exact False.elim (hNot hNeg)

theorem EvaluateProofInternal.native_str_indexof_zero_nonneg_toNat_add_pat_le_len
    (s pat : native_String)
    (hIdxNonneg : 0 ≤ native_str_indexof s pat 0) :
    Int.toNat (native_str_indexof s pat 0) + pat.length ≤ s.length := by
  have hSeqNonneg :
      0 ≤ native_seq_indexof (s.map SmtValue.Char)
        (pat.map SmtValue.Char) 0 := by
    simpa [EvaluateProofInternal.native_seq_indexof_map_char_zero] using hIdxNonneg
  have hSeq :=
    EvaluateProofInternal.native_seq_indexof_zero_nonneg_toNat_add_pat_le_len_local
      (s.map SmtValue.Char) (pat.map SmtValue.Char) hSeqNonneg
  simpa [EvaluateProofInternal.native_seq_indexof_map_char_zero] using hSeq

theorem EvaluateProofInternal.native_seq_indexof_map_char
    (s t : native_String) (i : native_Int) :
    native_seq_indexof (s.map SmtValue.Char) (t.map SmtValue.Char) i =
      native_str_indexof s t i := by
  rw [native_seq_indexof_eq_rec]
  unfold native_str_indexof
  by_cases hi : i < 0
  · simp [hi]
  · simp [hi, List.length_map]
    let start := Int.toNat i
    by_cases hBound : start + t.length ≤ s.length
    · have hStartLe : start ≤ s.length := by omega
      have hBoundLeft : Int.toNat i + t.length ≤ s.length := by
        simpa [start] using hBound
      have hBound' :
          Int.toNat i + Int.toNat (native_str_len t) ≤
            Int.toNat (native_str_len s) := by
        simpa [start, native_str_len] using hBound
      rw [if_pos hBoundLeft]
      rw [if_pos hBound']
      have hDropMap :
          (s.map SmtValue.Char).drop start =
            (s.drop start).map SmtValue.Char := by
        simp [List.map_drop]
      rw [hDropMap]
      have hTakeLen : (s.take start).length = start := by
        simp [List.length_take, hStartLe]
      have hAppend : s.take start ++ s.drop start = s :=
        List.take_append_drop start s
      have hRec :=
        EvaluateProofInternal.native_seq_indexof_rec_map_char_prefix (s.take start) (s.drop start)
          t (s.length - (start + t.length) + 1)
      rw [hTakeLen, hAppend] at hRec
      simpa [start, native_str_len] using hRec
    · have hBoundLeft : ¬ Int.toNat i + t.length ≤ s.length := by
        simpa [start] using hBound
      have hBound' :
          ¬ Int.toNat i + Int.toNat (native_str_len t) ≤
            Int.toNat (native_str_len s) := by
        simpa [start, native_str_len] using hBound
      rw [if_neg hBoundLeft]
      rw [if_neg hBound']

theorem EvaluateProofInternal.native_seq_indexof_pack_string
    (s t : native_String) (i : native_Int) :
    native_seq_indexof (native_unpack_seq (native_pack_string s))
        (native_unpack_seq (native_pack_string t)) i =
      native_str_indexof s t i := by
  rw [show native_unpack_seq (native_pack_string s) =
      s.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  rw [show native_unpack_seq (native_pack_string t) =
      t.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  simpa [impl_native_string_to_values] using
    EvaluateProofInternal.native_seq_indexof_map_char s t i

theorem EvaluateProofInternal.smtx_model_eval_str_indexof_pack_string
    (s t : native_String) (i : native_Int) :
    __smtx_model_eval_str_indexof
        (SmtValue.Seq (native_pack_string s))
        (SmtValue.Seq (native_pack_string t))
        (SmtValue.Numeral i) =
      SmtValue.Numeral (native_str_indexof s t i) := by
  simp only [__smtx_model_eval_str_indexof]
  rw [EvaluateProofInternal.native_seq_indexof_pack_string]

theorem EvaluateProofInternal.native_str_indexof_neg
    (s t : native_String) {i : native_Int}
    (hi : i < 0) :
    native_str_indexof s t i = -1 := by
  simp [native_str_indexof, hi]

theorem EvaluateProofInternal.native_str_indexof_gt_len
    (s t : native_String) {i : native_Int}
    (hi : native_str_len s < i) :
    native_str_indexof s t i = -1 := by
  unfold native_str_indexof
  have hLenNonneg : 0 ≤ native_str_len s := by
    simp [native_str_len]
  have hiNonneg : 0 ≤ i := Int.le_trans hLenNonneg (Int.le_of_lt hi)
  have hNotNeg : ¬ i < 0 := Int.not_lt_of_ge hiNonneg
  have hStartGt : s.length < Int.toNat i := by
    apply Int.ofNat_lt.mp
    rw [Int.toNat_of_nonneg hiNonneg]
    simpa [native_str_len] using hi
  have hBound :
      ¬ Int.toNat i + Int.toNat (native_str_len t) ≤
        Int.toNat (native_str_len s) := by
    intro h
    have hLenEq : Int.toNat (native_str_len s) = s.length := by
      simp [native_str_len]
    rw [hLenEq] at h
    omega
  rw [if_neg hNotNeg]
  dsimp
  rw [if_neg hBound]

theorem EvaluateProofInternal.native_seq_indexof_neg_local
    (xs pat : List SmtValue) {i : native_Int}
    (hi : i < 0) :
    native_seq_indexof xs pat i = -1 := by
  simp [native_seq_indexof_eq_rec, hi]

theorem EvaluateProofInternal.native_seq_indexof_gt_len_local
    (xs pat : List SmtValue) {i : native_Int}
    (hi : Int.ofNat xs.length < i) :
    native_seq_indexof xs pat i = -1 := by
  rw [native_seq_indexof_eq_rec]
  have hLenNonneg : 0 ≤ (Int.ofNat xs.length : native_Int) := by
    exact Int.natCast_nonneg xs.length
  have hiNonneg : 0 ≤ i := Int.le_trans hLenNonneg (Int.le_of_lt hi)
  have hNotNeg : ¬ i < 0 := Int.not_lt_of_ge hiNonneg
  have hStartGt : xs.length < Int.toNat i := by
    apply Int.ofNat_lt.mp
    rw [Int.toNat_of_nonneg hiNonneg]
    exact hi
  have hBound : ¬ Int.toNat i + pat.length ≤ xs.length := by
    intro h
    omega
  rw [if_neg hNotNeg]
  dsimp
  rw [if_neg hBound]

theorem EvaluateProofInternal.native_str_indexof_zero_of_prefix
    (s pat : native_String)
    (hPrefix : native_string_prefix_eq pat s = true) :
    native_str_indexof s pat 0 = 0 := by
  cases pat with
  | nil =>
      simp [native_str_indexof, impl_native_str_indexof_rec,
        native_string_prefix_eq, native_str_len]
  | cons p ps =>
      have hPatLe : (p :: ps).length ≤ s.length :=
        EvaluateProofInternal.native_string_prefix_eq_length_le (p :: ps) s hPrefix
      have hPatLe' : ps.length + 1 ≤ s.length := by
        simpa using hPatLe
      unfold native_str_indexof
      simp [native_str_len, hPatLe']
      unfold impl_native_str_indexof_rec
      simp [hPrefix]

theorem EvaluateProofInternal.native_seq_contains_pack_string
    (s t : native_String) :
    native_seq_contains (native_unpack_seq (native_pack_string s))
        (native_unpack_seq (native_pack_string t)) =
      native_not (native_zlt (native_str_indexof s t 0) 0) := by
  rw [show native_unpack_seq (native_pack_string s) =
      s.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  rw [show native_unpack_seq (native_pack_string t) =
      t.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  unfold native_seq_contains
  rw [EvaluateProofInternal.native_seq_indexof_map_char_zero]
  by_cases hNeg : native_str_indexof s t 0 < 0
  · simp [native_zlt, native_not, hNeg]
  · have hNonneg : 0 ≤ native_str_indexof s t 0 :=
      Int.le_of_not_gt hNeg
    simp [native_zlt, native_not, hNeg, hNonneg]

def EvaluateProofInternal.native_str_replace_eval_result
    (s pat repl : native_String) : native_String :=
  let idx := native_str_indexof s pat 0
  if idx < 0 then
    s
  else
    s.take (Int.toNat idx) ++ repl ++ s.drop (Int.toNat idx + pat.length)

theorem EvaluateProofInternal.native_str_substr_prefix_take_local
    (s : native_String) (idx : Nat) :
    native_str_substr s 0 (Int.ofNat idx) = s.take idx := by
  cases s with
  | nil =>
      simp [native_str_substr, native_str_len]
  | cons c cs =>
      cases idx with
      | zero =>
          simp [native_str_substr, native_str_len]
      | succ k =>
          by_cases hk : k ≤ cs.length
          · have hki : (↑k : Int) ≤ (↑cs.length : Int) :=
              Int.ofNat_le.mpr hk
            have hMinInt :
                min (↑k : Int) (↑cs.length : Int) = (↑k : Int) :=
              Int.min_eq_left hki
            simp [native_str_substr, native_str_len]
            rw [hMinInt]
            simp
          · have hkge : cs.length ≤ k := Nat.le_of_not_ge hk
            have hki : (↑cs.length : Int) ≤ (↑k : Int) :=
              Int.ofNat_le.mpr hkge
            have hMinInt :
                min (↑k : Int) (↑cs.length : Int) = (↑cs.length : Int) :=
              Int.min_eq_right hki
            have hTake : cs.take k = cs := List.take_of_length_le hkge
            simp [native_str_substr, native_str_len]
            rw [hMinInt]
            simp [hTake]

theorem EvaluateProofInternal.native_str_substr_suffix_drop_local
    (s : native_String) (start : Nat) :
    native_str_substr s (Int.ofNat start)
        (Int.ofNat s.length - Int.ofNat start + 1) =
      s.drop start := by
  unfold native_str_substr native_str_len
  by_cases hlt : start < s.length
  · have hnot1 : ¬((↑start : Int) < 0) := by omega
    have hnot2 : ¬((↑s.length : Int) - ↑start + 1 <= 0) := by omega
    have hnot3 : ¬((↑start : Int) >= ↑s.length) := by omega
    simp [hnot1, hnot2, hnot3]
    have hMin :
        min ((↑s.length : Int) - ↑start + 1)
            ((↑s.length : Int) - ↑start) =
          (↑s.length : Int) - ↑start := by
      apply Int.min_eq_right
      omega
    rw [hMin]
    have hToNat :
        Int.toNat ((↑s.length : Int) - ↑start) = s.length - start := by
      apply Int.ofNat.inj
      change (↑(((↑s.length : Int) - ↑start).toNat) : Int) =
        ↑(s.length - start)
      rw [Int.toNat_of_nonneg]
      · rw [Int.ofNat_sub (Nat.le_of_lt hlt)]
      · omega
    rw [hToNat]
    exact List.take_of_length_le (by rw [List.length_drop]; omega)
  · have hge : s.length ≤ start := Nat.le_of_not_gt hlt
    have hdrop : s.drop start = [] := List.drop_eq_nil_of_le hge
    simp [hdrop]

theorem EvaluateProofInternal.native_str_indexof_suffix_offset
    (s t : native_String) (i : native_Int)
    (hNonneg : 0 ≤ i) (hLe : i ≤ native_str_len s) :
    native_str_indexof s t i =
      (let r :=
        native_str_indexof
          (native_str_substr s i (native_str_len s - i + 1)) t 0
       if r = (-1 : native_Int) then (-1 : native_Int) else i + r) := by
  let start := Int.toNat i
  have hiEq : i = Int.ofNat start := by
    exact (Int.toNat_of_nonneg hNonneg).symm
  have hStartLe : start ≤ s.length := by
    rw [hiEq] at hLe
    have hLe' : (start : native_Int) ≤ Int.ofNat s.length := by
      simpa [native_str_len] using hLe
    exact Int.ofNat_le.mp hLe'
  rw [hiEq]
  have hSubstr :
      native_str_substr s (Int.ofNat start)
          (native_str_len s - Int.ofNat start + 1) =
        s.drop start := by
    simpa [native_str_len] using
      EvaluateProofInternal.native_str_substr_suffix_drop_local s start
  rw [hSubstr]
  unfold native_str_indexof
  have hStartNotNeg : ¬ ((Int.ofNat start : Int) < 0) := by
    exact Int.not_lt_of_ge (Int.natCast_nonneg start)
  by_cases hBound : start + t.length ≤ s.length
  · have hDropBound : t.length ≤ (s.drop start).length := by
      rw [List.length_drop]
      omega
    have hDropBoundNat : t.length ≤ s.length - start := by
      omega
    simp [hBound, hDropBoundNat, native_str_len]
    have hTakeLen : (s.take start).length = start := by
      simp [List.length_take, hStartLe]
    have hAppend : s.take start ++ s.drop start = s :=
      List.take_append_drop start s
    let fuel := s.length - (start + t.length) + 1
    have hFuelDrop :
        (s.drop start).length - t.length + 1 = fuel := by
      rw [List.length_drop]
      omega
    have hHead :=
      EvaluateProofInternal.native_seq_indexof_rec_map_char_prefix (s.take start) (s.drop start)
        t fuel
    have hTail :=
      EvaluateProofInternal.native_seq_indexof_rec_map_char_prefix ([] : native_String)
        (s.drop start) t fuel
    have hTail' :
        native_seq_indexof_rec ((s.drop start).map SmtValue.Char)
            (t.map SmtValue.Char) 0 fuel =
          impl_native_str_indexof_rec (s.drop start) t 0 fuel := by
      simpa using hTail
    have hOffset :=
      EvaluateProofInternal.native_seq_indexof_rec_offset_local
        ((s.drop start).map SmtValue.Char) (t.map SmtValue.Char)
        0 start fuel
    have hOffset' :
        native_seq_indexof_rec ((s.drop start).map SmtValue.Char)
            (t.map SmtValue.Char) start fuel =
          (let r :=
            native_seq_indexof_rec ((s.drop start).map SmtValue.Char)
              (t.map SmtValue.Char) 0 fuel
           if r = (-1 : native_Int) then (-1 : native_Int)
           else r + Int.ofNat start) := by
      simpa using hOffset
    rw [hTakeLen, hAppend] at hHead
    rw [show ([] : native_String) ++ s.drop start = s.drop start by rfl]
      at hTail
    rw [show s.length - start - t.length + 1 = fuel by omega]
    rw [← hHead, hOffset', hTail']
    simp [Int.add_comm]
    intro hBad _
    exact False.elim (hStartNotNeg hBad)
  · have hDropBound : ¬ t.length ≤ (s.drop start).length := by
      rw [List.length_drop]
      omega
    have hDropBoundNat : ¬ t.length ≤ s.length - start := by
      omega
    simp [hBound, hDropBoundNat, native_str_len]

theorem EvaluateProofInternal.str_indexof_result_strings
    (s pat : native_String) (i : native_Int) :
    let runLen := __eo_len (Term.String s)
    let runFind :=
      __eo_find
        (__eo_to_str (__eo_extract (Term.String s) (Term.Numeral i) runLen))
        (__eo_to_str (Term.String pat))
    __eo_ite (__eo_is_neg (Term.Numeral i))
      (Term.Numeral (-1 : native_Int))
      (__eo_ite (__eo_gt (Term.Numeral i) runLen)
        (Term.Numeral (-1 : native_Int))
        (__eo_ite (__eo_is_neg runFind) runFind
          (__eo_add (Term.Numeral i) runFind))) =
      Term.Numeral (native_str_indexof s pat i) := by
  dsimp
  by_cases hiNeg : i < 0
  · have hLt : native_zlt i 0 = true := by
      rw [show native_zlt i 0 = decide (i < 0) by rfl]
      exact decide_eq_true hiNeg
    rw [show __eo_is_neg (Term.Numeral i) = Term.Boolean true by
      simp [__eo_is_neg, hLt]]
    rw [eo_ite_true]
    rw [EvaluateProofInternal.native_str_indexof_neg s pat hiNeg]
  · have hiNonneg : 0 ≤ i := Int.le_of_not_gt hiNeg
    have hLt : native_zlt i 0 = false := by
      rw [show native_zlt i 0 = decide (i < 0) by rfl]
      exact decide_eq_false hiNeg
    rw [show __eo_is_neg (Term.Numeral i) = Term.Boolean false by
      simp [__eo_is_neg, hLt]]
    rw [eo_ite_false]
    by_cases hGt : native_str_len s < i
    · have hGtBool : native_zlt (native_str_len s) i = true := by
        rw [show native_zlt (native_str_len s) i =
            decide (native_str_len s < i) by rfl]
        exact decide_eq_true hGt
      rw [show
          __eo_gt (Term.Numeral i) (__eo_len (Term.String s)) =
            Term.Boolean true by
        simp [__eo_gt, __eo_len, hGtBool]]
      rw [eo_ite_true]
      rw [EvaluateProofInternal.native_str_indexof_gt_len s pat hGt]
    · have hLe : i ≤ native_str_len s := Int.le_of_not_gt hGt
      have hGtBool : native_zlt (native_str_len s) i = false := by
        rw [show native_zlt (native_str_len s) i =
            decide (native_str_len s < i) by rfl]
        exact decide_eq_false hGt
      rw [show
          __eo_gt (Term.Numeral i) (__eo_len (Term.String s)) =
            Term.Boolean false by
        simp [__eo_gt, __eo_len, hGtBool]]
      rw [eo_ite_false]
      let suffix := native_str_substr s i (native_str_len s - i + 1)
      have hFind :
          __eo_find
              (__eo_to_str
                (__eo_extract (Term.String s) (Term.Numeral i)
                  (__eo_len (Term.String s))))
              (__eo_to_str (Term.String pat)) =
            Term.Numeral (native_str_indexof suffix pat 0) := by
        dsimp [suffix]
        simp [__eo_extract, __eo_len, __eo_to_str, __eo_find,
          native_zplus, native_zneg, native_str_len, Int.sub_eq_add_neg]
      rw [hFind]
      by_cases hFoundNeg : native_str_indexof suffix pat 0 < 0
      · have hFoundLt :
            native_zlt (native_str_indexof suffix pat 0) 0 = true := by
          rw [show native_zlt (native_str_indexof suffix pat 0) 0 =
              decide (native_str_indexof suffix pat 0 < 0) by rfl]
          exact decide_eq_true hFoundNeg
        rw [show
            __eo_is_neg (Term.Numeral (native_str_indexof suffix pat 0)) =
              Term.Boolean true by
          simp [__eo_is_neg, hFoundLt]]
        rw [eo_ite_true]
        have hFoundEq :
            native_str_indexof suffix pat 0 = -1 :=
          EvaluateProofInternal.native_str_indexof_eq_neg_one_of_neg suffix pat hFoundNeg
        have hSuffix :=
          EvaluateProofInternal.native_str_indexof_suffix_offset s pat i hiNonneg hLe
        dsimp [suffix] at hSuffix
        rw [hFoundEq] at hSuffix
        simp at hSuffix
        rw [hFoundEq, hSuffix]
      · have hFoundLt :
            native_zlt (native_str_indexof suffix pat 0) 0 = false := by
          rw [show native_zlt (native_str_indexof suffix pat 0) 0 =
              decide (native_str_indexof suffix pat 0 < 0) by rfl]
          exact decide_eq_false hFoundNeg
        rw [show
            __eo_is_neg (Term.Numeral (native_str_indexof suffix pat 0)) =
              Term.Boolean false by
          simp [__eo_is_neg, hFoundLt]]
        rw [eo_ite_false]
        have hFoundNe :
            native_str_indexof suffix pat 0 ≠ (-1 : native_Int) := by
          intro hEq
          apply hFoundNeg
          rw [hEq]
          decide
        have hSuffix :=
          EvaluateProofInternal.native_str_indexof_suffix_offset s pat i hiNonneg hLe
        dsimp [suffix] at hSuffix
        rw [if_neg hFoundNe] at hSuffix
        change
          Term.Numeral (i + native_str_indexof suffix pat 0) =
            Term.Numeral (native_str_indexof s pat i)
        rw [hSuffix]

theorem EvaluateProofInternal.str_indexof_result_strings_of_index_numeral
    (s pat : native_String) (n : Term) (i : native_Int)
    (hn : n = Term.Numeral i) :
    let runLen := __eo_len (Term.String s)
    let runFind :=
      __eo_find
        (__eo_to_str (__eo_extract (Term.String s) n runLen))
        (__eo_to_str (Term.String pat))
    __eo_ite (__eo_is_neg (Term.Numeral i))
      (Term.Numeral (-1 : native_Int))
      (__eo_ite (__eo_gt (Term.Numeral i) runLen)
        (Term.Numeral (-1 : native_Int))
        (__eo_ite (__eo_is_neg runFind) runFind
          (__eo_add n runFind))) =
      Term.Numeral (native_str_indexof s pat i) := by
  subst n
  exact EvaluateProofInternal.str_indexof_result_strings s pat i

theorem EvaluateProofInternal.native_seq_replace_pack_string
    (s pat repl : native_String) :
    native_pack_seq SmtType.Char
        (native_seq_replace (native_unpack_seq (native_pack_string s))
          (native_unpack_seq (native_pack_string pat))
          (native_unpack_seq (native_pack_string repl))) =
      native_pack_string (EvaluateProofInternal.native_str_replace_eval_result s pat repl) := by
  rw [show native_unpack_seq (native_pack_string s) =
      s.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  rw [show native_unpack_seq (native_pack_string pat) =
      pat.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  rw [show native_unpack_seq (native_pack_string repl) =
      repl.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  rw [StrEqReplSupport.native_seq_replace_eq_indexof]
  rw [EvaluateProofInternal.native_seq_indexof_map_char_zero]
  by_cases hNeg : native_str_indexof s pat 0 < 0
  · simp [EvaluateProofInternal.native_str_replace_eval_result, hNeg,
      native_pack_string]
  · simp [EvaluateProofInternal.native_str_replace_eval_result, hNeg,
      native_pack_string, List.map_append, List.map_take, List.map_drop]

theorem EvaluateProofInternal.str_replace_result_strings
    (s pat repl : native_String) :
    __eo_ite (__eo_is_neg
          (__eo_find (__eo_to_str (Term.String s))
            (__eo_to_str (Term.String pat))))
        (Term.String s)
        (__eo_concat
          (__eo_concat
            (__eo_extract (Term.String s) (Term.Numeral 0)
              (__eo_add
                (__eo_find (__eo_to_str (Term.String s))
                  (__eo_to_str (Term.String pat)))
                (Term.Numeral (-1 : native_Int))))
            (Term.String repl))
          (__eo_extract (Term.String s)
            (__eo_add
              (__eo_find (__eo_to_str (Term.String s))
                (__eo_to_str (Term.String pat)))
              (__eo_len (Term.String pat)))
            (__eo_len (Term.String s)))) =
      Term.String (EvaluateProofInternal.native_str_replace_eval_result s pat repl) := by
  let idx := native_str_indexof s pat 0
  simp only [__eo_find, __eo_to_str]
  unfold EvaluateProofInternal.native_str_replace_eval_result
  by_cases hNeg : idx < 0
  · have hGuard :
        __eo_is_neg (Term.Numeral (native_str_indexof s pat 0)) =
          Term.Boolean true := by
      have hLt : native_zlt (native_str_indexof s pat 0) 0 = true := by
        rw [show native_zlt (native_str_indexof s pat 0) 0 =
          decide (native_str_indexof s pat 0 < 0) by rfl]
        exact decide_eq_true (by simpa [idx] using hNeg)
      simp [__eo_is_neg, hLt]
    rw [hGuard, eo_ite_true]
    simp [idx, hNeg]
  · have hNonneg : 0 ≤ idx := Int.le_of_not_gt hNeg
    let n := Int.toNat idx
    have hIdxNat : Int.ofNat n = idx := Int.toNat_of_nonneg hNonneg
    have hStart :
        idx + native_str_len pat = Int.ofNat (n + pat.length) := by
      rw [← hIdxNat]
      simp [native_str_len]
    have hGuard :
        __eo_is_neg (Term.Numeral (native_str_indexof s pat 0)) =
          Term.Boolean false := by
      have hLt : native_zlt (native_str_indexof s pat 0) 0 = false := by
        rw [show native_zlt (native_str_indexof s pat 0) 0 =
          decide (native_str_indexof s pat 0 < 0) by rfl]
        exact decide_eq_false (by simpa [idx] using hNeg)
      simp [__eo_is_neg, hLt]
    rw [hGuard, eo_ite_false]
    simp [__eo_extract, __eo_add, __eo_len, __eo_concat,
      native_zplus, native_zneg, native_str_len]
    rw [show native_str_indexof s pat 0 + -1 + 1 =
        native_str_indexof s pat 0 by
      rw [Int.add_assoc]
      simp]
    rw [show native_str_substr s 0 (native_str_indexof s pat 0) =
        s.take n by
      change native_str_substr s 0 idx = s.take n
      rw [← hIdxNat]
      exact EvaluateProofInternal.native_str_substr_prefix_take_local s n]
    rw [show
        native_str_substr s
            (native_str_indexof s pat 0 + ↑pat.length)
            (↑s.length + -(native_str_indexof s pat 0 + ↑pat.length) + 1) =
          s.drop (n + pat.length) by
      rw [show native_str_indexof s pat 0 + ↑pat.length =
          Int.ofNat (n + pat.length) by
        simpa [idx, native_str_len] using hStart]
      change
        native_str_substr s (Int.ofNat (n + pat.length))
            (Int.ofNat s.length - Int.ofNat (n + pat.length) + 1) =
          s.drop (n + pat.length)
      exact EvaluateProofInternal.native_str_substr_suffix_drop_local s (n + pat.length)]
    rw [if_neg (by simpa [idx] using hNeg)]
    simp [n, idx, native_str_concat, List.append_assoc]

def EvaluateProofInternal.native_str_replace_all_eval_aux
    (fuel : Nat) (pat repl : native_String) :
    native_String -> native_String
  | xs =>
      match fuel with
      | 0 => xs
      | fuel + 1 =>
          match pat with
          | [] => xs
          | _ =>
              let idx := native_str_indexof xs pat 0
              if idx < 0 then
                xs
              else
                let n := Int.toNat idx
                xs.take n ++ repl ++
                  EvaluateProofInternal.native_str_replace_all_eval_aux fuel pat repl
                    (xs.drop (n + pat.length))

def EvaluateProofInternal.native_str_replace_all_eval_result
    (s pat repl : native_String) : native_String :=
  EvaluateProofInternal.native_str_replace_all_eval_aux (s.length + 1) pat repl s

theorem EvaluateProofInternal.native_str_replace_all_eval_result_nil
    (s repl : native_String) :
    EvaluateProofInternal.native_str_replace_all_eval_result s [] repl = s := by
  unfold EvaluateProofInternal.native_str_replace_all_eval_result
  cases s <;>
    simp [EvaluateProofInternal.native_str_replace_all_eval_aux]

theorem EvaluateProofInternal.native_str_replace_all_eval_aux_prefix_cons
    (fuel : Nat) (s repl : native_String) (p : native_Char)
    (ps : native_String)
    (hPrefix : native_string_prefix_eq (p :: ps) s = true) :
    EvaluateProofInternal.native_str_replace_all_eval_aux (fuel + 1) (p :: ps) repl s =
      repl ++
        EvaluateProofInternal.native_str_replace_all_eval_aux fuel (p :: ps) repl
          (s.drop (ps.length + 1)) := by
  have hIdx : native_str_indexof s (p :: ps) 0 = 0 :=
    EvaluateProofInternal.native_str_indexof_zero_of_prefix s (p :: ps) hPrefix
  simp [EvaluateProofInternal.native_str_replace_all_eval_aux, hIdx]

theorem EvaluateProofInternal.native_str_replace_all_eval_aux_eq_chain_of_fuel
    (pat repl : native_String) :
    ∀ (fuel : Nat) (s : native_String),
      s.length + 1 ≤ fuel ->
      pat ≠ [] ->
      EvaluateProofInternal.native_str_replace_all_eval_aux fuel pat repl s =
        EvaluateProofInternal.native_str_replace_all_chain pat repl 0 s := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      intro s hFuel hPat
      cases fuel with
      | zero =>
          omega
      | succ fuel' =>
          cases pat with
          | nil =>
              contradiction
          | cons p ps =>
              cases s with
              | nil =>
                  have hIdx :
                      native_str_indexof [] (p :: ps) 0 = -1 := by
                    simp [native_str_indexof, native_str_len]
                  simp [EvaluateProofInternal.native_str_replace_all_eval_aux,
                    EvaluateProofInternal.native_str_replace_all_chain, hIdx]
              | cons c cs =>
                  have hCsFuel : cs.length + 1 ≤ fuel' := by
                    simp at hFuel
                    omega
                  by_cases hPref :
                      native_string_prefix_eq (p :: ps) (c :: cs) = true
                  · rw [EvaluateProofInternal.native_str_replace_all_eval_aux_prefix_cons fuel'
                      (c :: cs) repl p ps hPref]
                    have hDropLen :
                        ((c :: cs).drop (ps.length + 1)).length ≤
                          cs.length := by
                      simp [List.length_drop]
                    have hDropFuel :
                        ((c :: cs).drop (ps.length + 1)).length + 1 ≤
                          fuel' := by
                      omega
                    rw [ih fuel' (by omega)
                      ((c :: cs).drop (ps.length + 1)) hDropFuel
                      (by simp)]
                    simp [EvaluateProofInternal.native_str_replace_all_chain, hPref,
                      EvaluateProofInternal.native_str_replace_all_chain_skip_eq_drop]
                  · have hPrefFalse :
                        native_string_prefix_eq (p :: ps) (c :: cs) =
                          false := by
                      cases hp :
                          native_string_prefix_eq (p :: ps) (c :: cs) <;>
                        simp [hp] at hPref ⊢
                    have hConsIdx :=
                      EvaluateProofInternal.native_str_indexof_cons_not_prefix c p cs ps
                        hPrefFalse
                    by_cases hTailNeg :
                        native_str_indexof cs (p :: ps) 0 < 0
                    · have hTailEq :
                          native_str_indexof cs (p :: ps) 0 = -1 :=
                        EvaluateProofInternal.native_str_indexof_eq_neg_one_of_neg cs (p :: ps)
                          hTailNeg
                      have hParentNeg :
                          native_str_indexof (c :: cs) (p :: ps) 0 < 0 := by
                        rw [hConsIdx, hTailEq]
                        decide
                      have hTailEvalSelf :
                          EvaluateProofInternal.native_str_replace_all_eval_aux fuel' (p :: ps)
                              repl cs =
                            cs := by
                        cases fuel' with
                        | zero =>
                            omega
                        | succ fuel'' =>
                            simp [EvaluateProofInternal.native_str_replace_all_eval_aux,
                              hTailNeg]
                      have hTailChain :
                          EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl 0 cs =
                            cs := by
                        rw [← ih fuel' (by omega) cs hCsFuel (by simp)]
                        exact hTailEvalSelf
                      simp [EvaluateProofInternal.native_str_replace_all_eval_aux, hParentNeg,
                        EvaluateProofInternal.native_str_replace_all_chain, hPrefFalse,
                        hTailChain]
                    · have hTailNonneg :
                          0 ≤ native_str_indexof cs (p :: ps) 0 :=
                        Int.le_of_not_gt hTailNeg
                      let r := native_str_indexof cs (p :: ps) 0
                      let n := Int.toNat r
                      have hRcast : Int.ofNat n = r :=
                        Int.toNat_of_nonneg hTailNonneg
                      have hTailFit :
                          n + (p :: ps).length ≤ cs.length := by
                        simpa [r, n] using
                          EvaluateProofInternal.native_str_indexof_zero_nonneg_toNat_add_pat_le_len
                            cs (p :: ps) hTailNonneg
                      have hTailNe : r ≠ -1 := by
                        intro h
                        have hBad : r < 0 := by
                          rw [h]
                          decide
                        exact hTailNeg (by simpa [r] using hBad)
                      have hParentIdx :
                          native_str_indexof (c :: cs) (p :: ps) 0 =
                            r + 1 := by
                        rw [hConsIdx]
                        simp [r, hTailNe]
                      have hParentNotNeg :
                          ¬ native_str_indexof (c :: cs) (p :: ps) 0 < 0 := by
                        have hrNonneg : 0 ≤ r := by
                          rw [← hRcast]
                          exact Int.natCast_nonneg n
                        intro hlt
                        have hR1Nonneg : 0 ≤ r + 1 :=
                          Int.add_nonneg hrNonneg (by decide)
                        exact (Int.not_lt_of_ge hR1Nonneg)
                          (by simpa [hParentIdx] using hlt)
                      have hParentToNat :
                          Int.toNat
                              (native_str_indexof (c :: cs) (p :: ps) 0) =
                            n + 1 := by
                        rw [hParentIdx]
                        have hrNonneg : 0 ≤ r := by
                          rw [← hRcast]
                          exact Int.natCast_nonneg n
                        have hNonneg : 0 ≤ r + 1 :=
                          Int.add_nonneg hrNonneg (by decide)
                        apply Int.ofNat.inj
                        calc
                          Int.ofNat (Int.toNat (r + 1)) = r + 1 :=
                            Int.toNat_of_nonneg hNonneg
                          _ = Int.ofNat (n + 1) := by
                            rw [← hRcast]
                            simp
                      cases fuel' with
                      | zero =>
                          omega
                      | succ fuel'' =>
                          have hPatLenPos : 0 < (p :: ps).length := by
                            simp
                          have hSuffixLen :
                              (cs.drop (n + (p :: ps).length)).length + 1 ≤
                                cs.length := by
                            simp [List.length_drop]
                            omega
                          have hSuffixFuelParent :
                              (cs.drop (n + (p :: ps).length)).length + 1 ≤
                                fuel'' + 1 := by
                            omega
                          have hSuffixFuelTail :
                              (cs.drop (n + (p :: ps).length)).length + 1 ≤
                                fuel'' := by
                            simp at hCsFuel
                            omega
                          have hParentSuffix :
                              EvaluateProofInternal.native_str_replace_all_eval_aux (fuel'' + 1)
                                  (p :: ps) repl
                                  (cs.drop (n + (p :: ps).length)) =
                                EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl 0
                                  (cs.drop (n + (p :: ps).length)) :=
                            ih (fuel'' + 1) (by omega)
                              (cs.drop (n + (p :: ps).length))
                              hSuffixFuelParent (by simp)
                          have hTailSuffix :
                              EvaluateProofInternal.native_str_replace_all_eval_aux fuel''
                                  (p :: ps) repl
                                  (cs.drop (n + (p :: ps).length)) =
                                EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl 0
                                  (cs.drop (n + (p :: ps).length)) :=
                            ih fuel'' (by omega)
                              (cs.drop (n + (p :: ps).length))
                              hSuffixFuelTail (by simp)
                          have hTailChain :
                              EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl 0 cs =
                                cs.take n ++ repl ++
                                  EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl 0
                                    (cs.drop (n + (p :: ps).length)) := by
                            rw [← ih (fuel'' + 1) (by omega) cs hCsFuel
                              (by simp)]
                            simp [EvaluateProofInternal.native_str_replace_all_eval_aux, r, n,
                              hTailNeg]
                            simpa [r, n] using hTailSuffix
                          have hR1NotNeg : ¬ r + 1 < 0 := by
                            have hrNonneg : 0 ≤ r := by
                              rw [← hRcast]
                              exact Int.natCast_nonneg n
                            exact Int.not_lt_of_ge
                              (Int.add_nonneg hrNonneg (by decide))
                          have hToNatR1 : Int.toNat (r + 1) = n + 1 := by
                            simpa [hParentIdx] using hParentToNat
                          have hParentDrop :
                              (c :: cs).drop
                                  (n + 1 + (p :: ps).length) =
                                cs.drop (n + (p :: ps).length) := by
                            rw [show n + 1 + (p :: ps).length =
                                (n + (p :: ps).length) + 1 by omega]
                            simp
                          change
                            (let idx :=
                              native_str_indexof (c :: cs) (p :: ps) 0
                             if idx < 0 then
                               c :: cs
                             else
                               (c :: cs).take (Int.toNat idx) ++ repl ++
                                 EvaluateProofInternal.native_str_replace_all_eval_aux
                                   (fuel'' + 1) (p :: ps) repl
                                   ((c :: cs).drop
                                     (Int.toNat idx + (p :: ps).length))) =
                              EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl 0
                                (c :: cs)
                          rw [hParentIdx]
                          rw [if_neg hR1NotNeg]
                          rw [hToNatR1]
                          rw [hParentDrop]
                          rw [hParentSuffix]
                          simp [EvaluateProofInternal.native_str_replace_all_chain, hPrefFalse,
                            hTailChain, List.append_assoc]

theorem EvaluateProofInternal.native_str_replace_all_eval_result_cons_eq_chain
    (s repl : native_String) (p : native_Char) (ps : native_String) :
    EvaluateProofInternal.native_str_replace_all_eval_result s (p :: ps) repl =
      EvaluateProofInternal.native_str_replace_all_chain (p :: ps) repl 0 s := by
  unfold EvaluateProofInternal.native_str_replace_all_eval_result
  exact EvaluateProofInternal.native_str_replace_all_eval_aux_eq_chain_of_fuel (p :: ps) repl
    (s.length + 1) s (by omega) (by simp)

theorem EvaluateProofInternal.native_re_replace_all_nonempty_list_aux_map_char
    (p : native_Char) (ps repl : native_String) :
    ∀ (fuel : Nat) (s : native_String),
      s.length < fuel →
      impl_native_re_replace_all_nonempty_list_aux fuel
          (native_str_to_re ((p :: ps).map SmtValue.Char))
          (repl.map SmtValue.Char) (s.map SmtValue.Char) =
        (EvaluateProofInternal.native_str_replace_all_chain
          (p :: ps) repl 0 s).map SmtValue.Char := by
  intro fuel
  induction fuel with
  | zero =>
      intro s hFuel
      omega
  | succ fuel ih =>
      intro s hFuel
      cases s with
      | nil =>
          simp [impl_native_re_replace_all_nonempty_list_aux,
            native_re_positive_prefix_match_len?,
            EvaluateProofInternal.native_str_replace_all_chain]
      | cons c cs =>
          simp only [List.map_cons]
          rw [impl_native_re_replace_all_nonempty_list_aux.eq_3]
          rw [StrReplaceAllSupport.positive_prefix_str_to_re_cons]
          rw [show
              native_seq_prefix_eq
                  (SmtValue.Char p :: ps.map SmtValue.Char)
                  (SmtValue.Char c :: cs.map SmtValue.Char) =
                native_string_prefix_eq (p :: ps) (c :: cs) by
            simpa only [List.map_cons] using
              EvaluateProofInternal.native_seq_prefix_eq_map_char
                (p :: ps) (c :: cs)]
          by_cases hPrefix :
              native_string_prefix_eq (p :: ps) (c :: cs) = true
          · rw [if_pos hPrefix]
            simp only [List.length_cons, List.length_map]
            have hPatLe : (p :: ps).length ≤ (c :: cs).length :=
              EvaluateProofInternal.native_string_prefix_eq_length_le
                (p :: ps) (c :: cs) hPrefix
            have hDropFuel :
                ((c :: cs).drop (ps.length + 1)).length < fuel := by
              rw [List.length_drop]
              simp only [List.length_cons] at hFuel hPatLe ⊢
              omega
            rw [show
                (SmtValue.Char c :: cs.map SmtValue.Char).drop (ps.length + 1) =
                  ((c :: cs).drop (ps.length + 1)).map SmtValue.Char by
              simp [List.map_drop]]
            have hRec := ih ((c :: cs).drop (ps.length + 1)) hDropFuel
            simp only [List.map_cons] at hRec
            rw [hRec]
            simp [EvaluateProofInternal.native_str_replace_all_chain, hPrefix,
              EvaluateProofInternal.native_str_replace_all_chain_skip_eq_drop,
              List.map_append]
          · rw [if_neg hPrefix]
            simp only [List.length_cons, List.length_map]
            have hCsFuel : cs.length < fuel := by
              simp only [List.length_cons] at hFuel
              omega
            have hRec := ih cs hCsFuel
            simp only [List.map_cons] at hRec
            rw [hRec]
            simp [EvaluateProofInternal.native_str_replace_all_chain, hPrefix]

theorem EvaluateProofInternal.native_seq_replace_all_pack_string
    (s pat repl : native_String) :
    native_pack_seq SmtType.Char
        (native_seq_replace_all
          (native_unpack_seq (native_pack_string s))
          (native_unpack_seq (native_pack_string pat))
          (native_unpack_seq (native_pack_string repl))) =
      native_pack_string
        (EvaluateProofInternal.native_str_replace_all_eval_result s pat repl) := by
  rw [show native_unpack_seq (native_pack_string s) =
      s.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  rw [show native_unpack_seq (native_pack_string pat) =
      pat.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  rw [show native_unpack_seq (native_pack_string repl) =
      repl.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  cases pat with
  | nil =>
      simp only [List.map_nil]
      rw [StrReplaceAllSupport.replace_all_nil_pat]
      rw [EvaluateProofInternal.native_str_replace_all_eval_result_nil]
      simp [Smtm.native_pack_string]
  | cons p ps =>
      unfold native_seq_replace_all native_str_replace_re_all
        impl_native_re_replace_all_nonempty_list
      change native_pack_seq SmtType.Char
          (impl_native_re_replace_all_nonempty_list_aux
            ((s.map SmtValue.Char).length + 1)
            (native_str_to_re ((p :: ps).map SmtValue.Char))
            (repl.map SmtValue.Char) (s.map SmtValue.Char)) = _
      rw [show (s.map SmtValue.Char).length + 1 = s.length + 1 by simp]
      rw [EvaluateProofInternal.native_re_replace_all_nonempty_list_aux_map_char
        p ps repl (s.length + 1) s (by omega)]
      rw [EvaluateProofInternal.native_str_replace_all_eval_result_cons_eq_chain]
      simp [Smtm.native_pack_string]

theorem EvaluateProofInternal.smtx_model_eval_str_replace_all_pack_string
    (s pat repl : native_String) :
    __smtx_model_eval_str_replace_all
        (SmtValue.Seq (native_pack_string s))
        (SmtValue.Seq (native_pack_string pat))
        (SmtValue.Seq (native_pack_string repl)) =
      SmtValue.Seq
        (native_pack_string
          (EvaluateProofInternal.native_str_replace_all_eval_result s pat repl)) := by
  simp only [__smtx_model_eval_str_replace_all]
  rw [show __smtx_elem_typeof_seq_value (native_pack_string s) =
      SmtType.Char by
    simp [native_pack_string, EvaluateProofInternal.elem_typeof_pack_seq_local]]
  rw [EvaluateProofInternal.native_seq_replace_all_pack_string]

theorem EvaluateProofInternal.smtx_model_eval_str_replace_all_pack_string_nil
    (s repl : native_String) :
    __smtx_model_eval_str_replace_all
        (SmtValue.Seq (native_pack_string s))
        (SmtValue.Seq (native_pack_string []))
        (SmtValue.Seq (native_pack_string repl)) =
      SmtValue.Seq (native_pack_string s) := by
  rw [EvaluateProofInternal.smtx_model_eval_str_replace_all_pack_string]
  rw [EvaluateProofInternal.native_str_replace_all_eval_result_nil]

def EvaluateProofInternal.native_seq_update_string_result
    (s : native_String) (i : native_Int) (repl : native_String) :
    native_String :=
  let len : native_Int := Int.ofNat s.length
  if i < 0 || len <= i then
    s
  else
    let idx := Int.toNat i
    s.take idx ++ repl.take (s.length - idx) ++
      s.drop (idx + repl.length)

theorem EvaluateProofInternal.native_string_valid_seq_update_string_result
    (s repl : native_String) (i : native_Int)
    (hs : native_string_valid s = true)
    (hrepl : native_string_valid repl = true) :
    native_string_valid (EvaluateProofInternal.native_seq_update_string_result s i repl) = true := by
  unfold EvaluateProofInternal.native_seq_update_string_result
  by_cases hGuard :
      (decide (i < 0) || decide (Int.ofNat s.length ≤ i)) = true
  · rw [if_pos hGuard]
    exact hs
  · rw [if_neg hGuard]
    exact native_string_valid_append
      (native_string_valid_append
        (native_string_valid_take (Int.toNat i) hs)
        (native_string_valid_take (s.length - Int.toNat i) hrepl))
      (native_string_valid_drop (Int.toNat i + repl.length) hs)

theorem EvaluateProofInternal.native_seq_update_pack_string
    (s : native_String) (i : native_Int) (repl : native_String) :
    native_pack_seq SmtType.Char
        (native_seq_update
          (native_unpack_seq (native_pack_string s)) i
          (native_unpack_seq (native_pack_string repl))) =
      native_pack_string (EvaluateProofInternal.native_seq_update_string_result s i repl) := by
  rw [show native_unpack_seq (native_pack_string s) =
      s.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  rw [show native_unpack_seq (native_pack_string repl) =
      repl.map SmtValue.Char by
    simp [native_pack_string, EvaluateProofInternal.native_unpack_pack_seq_local]]
  unfold native_seq_update EvaluateProofInternal.native_seq_update_string_result
  simp only [List.length_map]
  by_cases hGuard :
      (decide (i < 0) || decide (Int.ofNat s.length ≤ i)) = true
  · rw [if_pos hGuard, if_pos hGuard]
    simp [native_pack_string]
  · rw [if_neg hGuard, if_neg hGuard]
    simp [native_pack_string, List.map_append]

theorem EvaluateProofInternal.smtx_model_eval_str_update_pack_string
    (s repl : native_String) (i : native_Int) :
    __smtx_model_eval_str_update
        (SmtValue.Seq (native_pack_string s))
        (SmtValue.Numeral i)
        (SmtValue.Seq (native_pack_string repl)) =
      SmtValue.Seq
        (native_pack_string (EvaluateProofInternal.native_seq_update_string_result s i repl)) := by
  simp only [__smtx_model_eval_str_update]
  rw [show __smtx_elem_typeof_seq_value (native_pack_string s) =
      SmtType.Char by
    simp [native_pack_string, EvaluateProofInternal.elem_typeof_pack_seq_local]]
  rw [EvaluateProofInternal.native_seq_update_pack_string]

theorem EvaluateProofInternal.native_seq_update_eq_self_of_neg
    (xs ys : List SmtValue) (i : native_Int)
    (hi : i < 0) :
    native_seq_update xs i ys = xs := by
  unfold native_seq_update
  have hDecNeg : decide (i < 0) = true := decide_eq_true hi
  change
    (if (decide (i < 0) || decide (Int.ofNat xs.length <= i)) = true then
        xs
      else
        List.take (Int.toNat i) xs ++
          List.take (xs.length - Int.toNat i) ys ++
            List.drop (Int.toNat i + ys.length) xs) =
      xs
  rw [if_pos (by rw [hDecNeg]; simp)]

theorem EvaluateProofInternal.native_seq_update_eq_self_of_len_le
    (xs ys : List SmtValue) (i : native_Int)
    (hLen : Int.ofNat xs.length <= i) :
    native_seq_update xs i ys = xs := by
  unfold native_seq_update
  have hDecLen :
      decide (Int.ofNat xs.length <= i) = true := decide_eq_true hLen
  change
    (if (decide (i < 0) || decide (Int.ofNat xs.length <= i)) = true then
        xs
      else
        List.take (Int.toNat i) xs ++
          List.take (xs.length - Int.toNat i) ys ++
            List.drop (Int.toNat i + ys.length) xs) =
      xs
  rw [if_pos (by rw [hDecLen]; simp)]

theorem EvaluateProofInternal.smt_typeof_str_update_eq_typeof_string_of_arg_types
    (s n repl : Term) (result : native_String)
    (hSTySeq : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hNTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int)
    (hReplTySeq : __smtx_typeof (__eo_to_smt repl) = SmtType.Seq SmtType.Char)
    (hResultValid : native_string_valid result = true) :
    __smtx_typeof
        (SmtTerm.str_update (__eo_to_smt s) (__eo_to_smt n)
          (__eo_to_smt repl)) =
      __smtx_typeof (SmtTerm.String result) := by
  rw [typeof_str_update_eq]
  simp [__smtx_typeof_str_update, __smtx_typeof, hSTySeq, hNTy,
    hReplTySeq, native_Teq, native_ite, hResultValid]

theorem EvaluateProofInternal.smt_value_rel_model_eval_str_update_to_string_of_runs
    (M : SmtModel)
    (s n repl runS runN runRepl : Term) (result : native_String) :
    RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt s))
        (__smtx_model_eval M (__eo_to_smt runS)) ->
    RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt n))
        (__smtx_model_eval M (__eo_to_smt runN)) ->
    RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt repl))
        (__smtx_model_eval M (__eo_to_smt runRepl)) ->
    __smtx_model_eval_str_update
        (__smtx_model_eval M (__eo_to_smt runS))
        (__smtx_model_eval M (__eo_to_smt runN))
        (__smtx_model_eval M (__eo_to_smt runRepl)) =
      SmtValue.Seq (native_pack_string result) ->
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.str_update (__eo_to_smt s) (__eo_to_smt n)
            (__eo_to_smt repl)))
        (SmtValue.Seq (native_pack_string result)) := by
  intro hSRel hNRel hReplRel hRunEval
  have hRel :=
    EvaluateProofInternal.smt_value_rel_model_eval_str_update_of_rel
      (__smtx_model_eval M (__eo_to_smt s))
      (__smtx_model_eval M (__eo_to_smt n))
      (__smtx_model_eval M (__eo_to_smt repl))
      (__smtx_model_eval M (__eo_to_smt runS))
      (__smtx_model_eval M (__eo_to_smt runN))
      (__smtx_model_eval M (__eo_to_smt runRepl))
      hSRel hNRel hReplRel
  rw [show
      __smtx_model_eval M
          (SmtTerm.str_update (__eo_to_smt s) (__eo_to_smt n)
            (__eo_to_smt repl)) =
        __smtx_model_eval_str_update
          (__smtx_model_eval M (__eo_to_smt s))
          (__smtx_model_eval M (__eo_to_smt n))
          (__smtx_model_eval M (__eo_to_smt repl)) by
    rw [__smtx_model_eval.eq_90]]
  rw [hRunEval] at hRel
  exact hRel

theorem EvaluateProofInternal.eo_or_bool_args_of_bool
    (x y : Term) (b : Bool) :
    __eo_or x y = Term.Boolean b ->
      ∃ bx, ∃ byv,
        x = Term.Boolean bx ∧ y = Term.Boolean byv ∧
          native_or bx byv = b := by
  cases x <;> cases y <;> intro h <;>
    simp [__eo_or, __eo_requires, native_ite, native_teq] at h
  case Binary.Binary wx nx wy ny =>
    exfalso
    by_cases hEq : wx = wy
    · subst wy
      simp [native_not] at h
    · simp [hEq] at h
  case Boolean.Boolean bx byv =>
    cases h
    exact ⟨bx, byv, rfl, rfl, rfl⟩

theorem EvaluateProofInternal.str_update_result_strings_in_bounds
    (s repl : native_String) (idx : Nat) (hIdxLe : idx ≤ s.length) :
    __eo_concat
        (__eo_concat
          (__eo_extract (Term.String s) (Term.Numeral 0)
            (__eo_add (Term.Numeral (Int.ofNat idx))
              (Term.Numeral (-1 : native_Int))))
          (__eo_extract (Term.String repl) (Term.Numeral 0)
            (__eo_add
              (__eo_add (__eo_neg (Term.Numeral (Int.ofNat idx)))
                (__eo_len (Term.String s)))
              (Term.Numeral (-1 : native_Int)))))
        (__eo_extract (Term.String s)
          (__eo_add (Term.Numeral (Int.ofNat idx))
            (__eo_len (Term.String repl)))
          (__eo_len (Term.String s))) =
      Term.String
        (s.take idx ++ repl.take (s.length - idx) ++
          s.drop (idx + repl.length)) := by
  rw [show
      __eo_extract (Term.String s) (Term.Numeral 0)
          (__eo_add (Term.Numeral (Int.ofNat idx))
            (Term.Numeral (-1 : native_Int))) =
        Term.String (s.take idx) by
    simp [__eo_add, __eo_extract, native_zplus, native_zneg]
    change native_str_substr s 0
        ((Int.ofNat idx : native_Int) + (-1 : native_Int) + 1) =
      s.take idx
    rw [show (Int.ofNat idx + (-1 : native_Int) + 1) =
        Int.ofNat idx by omega]
    exact EvaluateProofInternal.native_str_substr_prefix_take_local s idx]
  rw [show
      __eo_extract (Term.String repl) (Term.Numeral 0)
          (__eo_add
            (__eo_add (__eo_neg (Term.Numeral (Int.ofNat idx)))
              (__eo_len (Term.String s)))
            (Term.Numeral (-1 : native_Int))) =
        Term.String (repl.take (s.length - idx)) by
    simp [__eo_add, __eo_neg, __eo_len, __eo_extract, native_zplus,
      native_zneg, native_str_len]
    change native_str_substr repl 0
        (-(Int.ofNat idx : native_Int) + Int.ofNat s.length +
          (-1 : native_Int) + 1) =
      repl.take (s.length - idx)
    rw [show
        -Int.ofNat idx + Int.ofNat s.length + (-1 : native_Int) + 1 =
          Int.ofNat (s.length - idx) by
      calc
        -Int.ofNat idx + Int.ofNat s.length + (-1 : native_Int) + 1 =
            Int.ofNat s.length - Int.ofNat idx := by omega
        _ = Int.ofNat (s.length - idx) :=
            (Int.ofNat_sub hIdxLe).symm]
    exact EvaluateProofInternal.native_str_substr_prefix_take_local repl (s.length - idx)]
  rw [show
      __eo_extract (Term.String s)
          (__eo_add (Term.Numeral (Int.ofNat idx))
            (__eo_len (Term.String repl)))
          (__eo_len (Term.String s)) =
        Term.String (s.drop (idx + repl.length)) by
    simp [__eo_add, __eo_len, __eo_extract, native_zplus, native_zneg,
      native_str_len]
    change native_str_substr s
        ((Int.ofNat idx : native_Int) + Int.ofNat repl.length)
        (Int.ofNat s.length -
            ((Int.ofNat idx : native_Int) + Int.ofNat repl.length) + 1) =
      s.drop (idx + repl.length)
    rw [show
        Int.ofNat idx + Int.ofNat repl.length =
          Int.ofNat (idx + repl.length) by
      simp]
    exact by
      simpa [native_str_len] using
        EvaluateProofInternal.native_str_substr_suffix_drop_local s (idx + repl.length)]
  simp [__eo_concat, native_str_concat, List.append_assoc]

theorem EvaluateProofInternal.str_update_result_strings
    (s repl : native_String) (i : native_Int) :
    let runLen := __eo_len (Term.String s)
    let runRepl := Term.String repl
    __eo_ite
        (__eo_or (__eo_gt (Term.Numeral 0) (Term.Numeral i))
          (__eo_gt (Term.Numeral i) runLen))
        (Term.String s)
        (__eo_concat
          (__eo_concat
            (__eo_extract (Term.String s) (Term.Numeral 0)
              (__eo_add (Term.Numeral i)
                (Term.Numeral (-1 : native_Int))))
            (__eo_extract runRepl (Term.Numeral 0)
              (__eo_add (__eo_add (__eo_neg (Term.Numeral i)) runLen)
                (Term.Numeral (-1 : native_Int)))))
          (__eo_extract (Term.String s)
            (__eo_add (Term.Numeral i) (__eo_len runRepl)) runLen)) =
      Term.String (EvaluateProofInternal.native_seq_update_string_result s i repl) := by
  dsimp
  by_cases hiNeg : i < 0
  · have hLt : native_zlt i 0 = true := by
      rw [show native_zlt i 0 = decide (i < 0) by rfl]
      exact decide_eq_true hiNeg
    simp [EvaluateProofInternal.native_seq_update_string_result, __eo_gt, __eo_or, __eo_ite,
      __eo_len, native_or, native_ite, native_teq, native_str_len,
      hLt, hiNeg]
  · have hLt : native_zlt i 0 = false := by
      rw [show native_zlt i 0 = decide (i < 0) by rfl]
      exact decide_eq_false hiNeg
    by_cases hLenLe : Int.ofNat s.length ≤ i
    · by_cases hLenLt : Int.ofNat s.length < i
      · have hGt : native_zlt (native_str_len s) i = true := by
          rw [show native_zlt (native_str_len s) i =
              decide (native_str_len s < i) by rfl]
          have hsimpa := decide_eq_true hLenLt
          try simp [native_str_len] at hsimpa ⊢
          exact decide_eq_true hsimpa
        have hResultEq : EvaluateProofInternal.native_seq_update_string_result s i repl = s := by
          unfold EvaluateProofInternal.native_seq_update_string_result
          have hGuard :
              (decide (i < 0) ||
                decide (Int.ofNat s.length ≤ i)) = true := by
            rw [show decide (i < 0) = false by
              exact decide_eq_false hiNeg]
            rw [show decide (Int.ofNat s.length ≤ i) = true by
              exact decide_eq_true hLenLe]
            rfl
          rw [if_pos hGuard]
        simp [hResultEq, __eo_len, __eo_gt, __eo_or, __eo_ite,
          native_or, native_ite, native_teq, hLt, hGt]
      · have hiEq : i = Int.ofNat s.length := by
          exact Int.le_antisymm (Int.le_of_not_gt hLenLt) hLenLe
        subst i
        have hGt : native_zlt (native_str_len s) (Int.ofNat s.length) =
            false := by
          rw [show native_zlt (native_str_len s) (Int.ofNat s.length) =
              decide (native_str_len s < Int.ofNat s.length) by rfl]
          simp [native_str_len]
        rw [EvaluateProofInternal.str_update_result_strings_in_bounds s repl s.length
          (Nat.le_refl _)]
        have hDrop : s.drop (s.length + repl.length) = [] :=
          List.drop_eq_nil_of_le (Nat.le_add_right _ _)
        simp [EvaluateProofInternal.native_seq_update_string_result, __eo_len, __eo_gt,
          __eo_or, __eo_ite, native_or, native_ite, native_teq,
          native_str_len, hDrop]
    · have hiNonneg : 0 ≤ i := Int.le_of_not_gt hiNeg
      let idx := Int.toNat i
      have hiEq : i = Int.ofNat idx :=
        (Int.toNat_of_nonneg hiNonneg).symm
      have hIdxLt : idx < s.length := by
        rw [hiEq] at hLenLe
        by_cases hLt : idx < s.length
        · exact hLt
        · exfalso
          exact hLenLe (Int.ofNat_le.mpr (Nat.le_of_not_gt hLt))
      have hLtIdx : native_zlt (Int.ofNat idx) 0 = false := by
        rw [show native_zlt (Int.ofNat idx) 0 =
            decide ((Int.ofNat idx : native_Int) < 0) by rfl]
        simp
      have hGtIdx :
          native_zlt (native_str_len s) (Int.ofNat idx) = false := by
        rw [show native_zlt (native_str_len s) (Int.ofNat idx) =
            decide (native_str_len s < (Int.ofNat idx : native_Int)) by
          rfl]
        apply decide_eq_false
        rw [native_str_len]
        intro hBad
        have hBadNat : s.length < idx := Int.ofNat_lt.mp hBad
        exact (Nat.lt_irrefl idx) (Nat.lt_trans hIdxLt hBadNat)
      have hIdxNonneg : ¬((Int.ofNat idx : native_Int) < 0) := by
        exact Int.not_lt_of_ge (Int.natCast_nonneg idx)
      have hLenNotLeIdx :
          ¬Int.ofNat s.length ≤ (Int.ofNat idx : native_Int) := by
        intro hLe
        exact (Nat.not_le_of_gt hIdxLt) (Int.ofNat_le.mp hLe)
      have hGuardFalseIdx :
          (decide ((Int.ofNat idx : native_Int) < 0) ||
            decide (Int.ofNat s.length ≤ (Int.ofNat idx : native_Int))) =
              false := by
        rw [show decide ((Int.ofNat idx : native_Int) < 0) = false by
          exact decide_eq_false hIdxNonneg]
        rw [show decide (Int.ofNat s.length ≤
            (Int.ofNat idx : native_Int)) = false by
          exact decide_eq_false hLenNotLeIdx]
        rfl
      rw [hiEq]
      rw [EvaluateProofInternal.str_update_result_strings_in_bounds s repl idx
        (Nat.le_of_lt hIdxLt)]
      have hIdxLe : idx ≤ s.length := Nat.le_of_lt hIdxLt
      have hLenNotLtIdx : ¬s.length < idx := by
        intro hBad
        exact (Nat.lt_irrefl idx) (Nat.lt_trans hIdxLt hBad)
      simp [EvaluateProofInternal.native_seq_update_string_result, __eo_len, __eo_gt,
        __eo_or, __eo_ite, native_zlt, native_or, native_ite, native_teq,
        native_str_len, hLenNotLtIdx]
      let body :=
        s.take idx ++
          (repl.take (s.length - idx) ++ s.drop (idx + repl.length))
      change
        (if (Int.ofNat idx : native_Int) < 0 then Term.String s
          else Term.String body) =
        Term.String
          (if (Int.ofNat idx : native_Int) < 0 ∨ s.length ≤ idx then
            s
          else body)
      by_cases hNegIdx : (Int.ofNat idx : native_Int) < 0
      · exact False.elim (hIdxNonneg hNegIdx)
      · have hLenLeIdxFalse : ¬s.length ≤ idx :=
          Nat.not_le_of_gt hIdxLt
        rw [if_neg hNegIdx]
        rw [show
            (if (Int.ofNat idx : native_Int) < 0 ∨ s.length ≤ idx then
              s
            else body) = body by
          rw [if_neg]
          intro hGuard
          cases hGuard with
          | inl hBad => exact hNegIdx hBad
          | inr hBad => exact hLenLeIdxFalse hBad]

theorem EvaluateProofInternal.str_update_run_repl_string_of_body_nonstuck
    (s : native_String) (runRepl : Term) (i : native_Int)
    (hRunReplTy :
      __smtx_typeof (__eo_to_smt runRepl) =
        SmtType.Seq SmtType.Char)
    (hBody :
      __eo_concat
          (__eo_concat
            (__eo_extract (Term.String s) (Term.Numeral 0)
              (__eo_add (Term.Numeral i)
                (Term.Numeral (-1 : native_Int))))
            (__eo_extract runRepl (Term.Numeral 0)
              (__eo_add
                (__eo_add (__eo_neg (Term.Numeral i))
                  (__eo_len (Term.String s)))
                (Term.Numeral (-1 : native_Int)))))
          (__eo_extract (Term.String s)
            (__eo_add (Term.Numeral i) (__eo_len runRepl))
            (__eo_len (Term.String s))) ≠ Term.Stuck) :
      ∃ repl : native_String,
        runRepl = Term.String repl ∧ native_string_valid repl = true := by
  cases runRepl
  case String repl =>
    exact ⟨repl, rfl, EvaluateProofInternal.native_string_valid_of_string_type hRunReplTy⟩
  case Binary w n =>
    exfalso
    change __smtx_typeof (SmtTerm.Binary w n) =
      SmtType.Seq SmtType.Char at hRunReplTy
    rw [__smtx_typeof.eq_5] at hRunReplTy
    cases hValid :
        native_and (native_zleq 0 w)
          (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
      simp [native_ite, hValid] at hRunReplTy
  all_goals
    exfalso
    apply hBody
    simp [__eo_extract, __eo_concat, __eo_add, __eo_len,
      native_zplus, native_zneg, native_str_len]

theorem EvaluateProofInternal.eo_extract_string_same_index
    (s : native_String) (i : native_Int) :
    __eo_extract (Term.String s) (Term.Numeral i) (Term.Numeral i) =
      Term.String (native_str_substr s i 1) := by
  simp [__eo_extract]
  have h :
      native_zplus (native_zplus i (native_zneg i)) 1 = (1 : native_Int) := by
    change (i + -i) + 1 = (1 : native_Int)
    rw [Int.add_right_neg]
    rfl
  rw [h]

theorem EvaluateProofInternal.eo_extract_string_substr_window
    (s : native_String) (i n : native_Int) :
    __eo_extract (Term.String s) (Term.Numeral i)
        (__eo_add (__eo_add (Term.Numeral i) (Term.Numeral n))
          (Term.Numeral (-1 : native_Int))) =
      Term.String (native_str_substr s i n) := by
  simp [__eo_extract, __eo_add, native_zplus, native_zneg]
  rw [show i + n + -1 + -i + 1 = n by
    simp [Int.add_assoc]
    rw [show -1 + (-i + 1) = -i by
      rw [Int.add_comm (-i) 1]
      rw [← Int.add_assoc]
      simp]
    rw [Int.add_comm n (-i)]
    rw [← Int.add_assoc]
    rw [Int.add_right_neg]
    simp]

theorem EvaluateProofInternal.eo_substr_len_arg_of_end_numeral
    (i j : native_Int) (m : Term)
    (hEnd :
      __eo_add (__eo_add (Term.Numeral i) m)
          (Term.Numeral (-1 : native_Int)) =
        Term.Numeral j) :
    ∃ n : native_Int, m = Term.Numeral n ∧ j = i + n + -1 := by
  cases m <;> simp [__eo_add, native_zplus] at hEnd
  case Numeral n =>
    exact ⟨n, rfl, hEnd.symm⟩

theorem EvaluateProofInternal.eo_extract_string_zero_len_minus_one
    (pfx subject : native_String) :
    __eo_extract (Term.String subject) (Term.Numeral 0)
        (__eo_add (__eo_len (Term.String pfx))
          (Term.Numeral (-1 : native_Int))) =
      Term.String (native_str_substr subject 0 (native_str_len pfx)) := by
  simp [__eo_extract, __eo_len, __eo_add, native_zplus, native_zneg]
  rw [show native_str_len pfx + (-1 : native_Int) + 1 =
      native_str_len pfx by
    rw [Int.add_assoc]
    simp]

theorem EvaluateProofInternal.eo_extract_string_suffix_window
    (suffix subject : native_String) :
    __eo_extract (Term.String subject)
        (__eo_add (__eo_len (Term.String subject))
          (__eo_neg (__eo_len (Term.String suffix))))
        (__eo_add (__eo_len (Term.String subject))
          (Term.Numeral (-1 : native_Int))) =
      Term.String
        (native_str_substr subject
          (native_str_len subject + -native_str_len suffix)
          (native_str_len suffix)) := by
  simp [__eo_extract, __eo_len, __eo_add, __eo_neg, native_zplus,
    native_zneg]
  rw [show
      native_str_len subject + -1 +
          -(native_str_len subject + -native_str_len suffix) + 1 =
        native_str_len suffix by
    simp [Int.neg_add, Int.add_assoc, Int.add_comm, Int.add_left_comm]
    rw [Int.add_right_neg]
    rw [Int.add_zero]]

theorem EvaluateProofInternal.smt_value_rel_seq_right_local
    {v : SmtValue} {s : SmtSeq} :
    RuleProofs.smt_value_rel v (SmtValue.Seq s) ->
    ∃ s', v = SmtValue.Seq s' ∧ RuleProofs.smt_seq_rel s' s := by
  intro hRel
  cases v <;>
    simp [RuleProofs.smt_value_rel, RuleProofs.smt_seq_rel,
      __smtx_model_eval_eq, native_veq] at hRel ⊢
  case Seq s' =>
    exact hRel

theorem EvaluateProofInternal.smtx_model_eval_str_indexof_pack_string_of_rel
    (a b c : SmtValue) (s pat : native_String) (i : native_Int) :
    RuleProofs.smt_value_rel a
        (SmtValue.Seq (native_pack_string s)) ->
    RuleProofs.smt_value_rel b
        (SmtValue.Seq (native_pack_string pat)) ->
    RuleProofs.smt_value_rel c (SmtValue.Numeral i) ->
      __smtx_model_eval_str_indexof a b c =
        SmtValue.Numeral (native_str_indexof s pat i) := by
  intro hA hB hC
  rcases EvaluateProofInternal.smt_value_rel_seq_right_local hA with
    ⟨aSeq, hAEq, hASeqRel⟩
  rcases EvaluateProofInternal.smt_value_rel_seq_right_local hB with
    ⟨bSeq, hBEq, hBSeqRel⟩
  have hASeqEq :
      aSeq = native_pack_string s :=
    (RuleProofs.smt_seq_rel_iff_eq _ _).1 hASeqRel
  have hBSeqEq :
      bSeq = native_pack_string pat :=
    (RuleProofs.smt_seq_rel_iff_eq _ _).1 hBSeqRel
  have hCEq : c = SmtValue.Numeral i :=
    EvaluateProofInternal.smt_value_rel_numeral_eq c i hC
  rw [hAEq, hASeqEq, hBEq, hBSeqEq, hCEq]
  exact EvaluateProofInternal.smtx_model_eval_str_indexof_pack_string s pat i

theorem EvaluateProofInternal.eo_eq_numeral_zero_true_eq
    (x : Term) :
    __eo_eq x (Term.Numeral 0) = Term.Boolean true ->
    x = Term.Numeral 0 := by
  cases x <;> intro h <;> simp [__eo_eq, native_teq] at h ⊢
  exact h.symm

theorem EvaluateProofInternal.eo_eq_rational_zero_true_eq
    (x : Term) :
    __eo_eq x (Term.Rational (native_mk_rational 0 1)) =
        Term.Boolean true ->
    x = Term.Rational (native_mk_rational 0 1) := by
  cases x <;> intro h <;> simp [__eo_eq, native_teq] at h ⊢
  case Rational q =>
    exact h.symm

theorem EvaluateProofInternal.eo_to_q_shape
    (x : Term) :
    __eo_to_q x = Term.Stuck ∨
      ∃ q : native_Rat, __eo_to_q x = Term.Rational q := by
  cases x <;> simp [__eo_to_q]

theorem EvaluateProofInternal.native_to_real_zero_eq
    {n : native_Int} :
    native_to_real n = native_mk_rational 0 1 ->
    n = 0 := by
  intro h
  have h' :
      ((n : Rat) / (1 : Rat)) = ((0 : Rat) / (1 : Rat)) := by
    simpa [native_to_real, native_mk_rational] using h
  rw [rat_div_one_intCast n, rat_zero_div_one] at h'
  exact Rat.intCast_inj.mp h'

theorem EvaluateProofInternal.native_mk_rational_zero_den
    (n : native_Int) :
    native_mk_rational n 0 = native_mk_rational 0 1 := by
  unfold native_mk_rational
  change ((n : Rat) / (0 : Rat)) = ((0 : Rat) / (1 : Rat))
  rw [rat_zero_div_one]
  rw [Rat.div_def, Rat.inv_zero, Rat.mul_zero]

theorem EvaluateProofInternal.native_qdiv_total_zero
    (q : native_Rat) :
    native_qdiv_total q (native_mk_rational 0 1) =
      native_mk_rational 0 1 := by
  unfold native_qdiv_total
  rw [native_mk_rational_zero]
  change q / (0 : Rat) = (0 : Rat)
  rw [Rat.div_def, Rat.inv_zero, Rat.mul_zero]

theorem EvaluateProofInternal.native_qeq_false_ne
    {q1 q2 : native_Rat} :
    native_qeq q1 q2 = false ->
    q1 ≠ q2 := by
  intro h hEq
  unfold native_qeq at h
  simp [hEq] at h

theorem EvaluateProofInternal.native_to_real_qdiv_total_eval
    (n1 n2 : native_Int) :
    native_qdiv_total (native_to_real n1) (native_to_real n2) =
      native_mk_rational n1 n2 := by
  rw [native_qdiv_total, native_to_real, native_to_real, native_mk_rational,
    native_mk_rational, native_mk_rational]
  rw [Rat.div_def]
  have hInv :
      ((↑n2 / ↑(1 : Int) : Rat)⁻¹) =
        ((↑(1 : Int) / ↑n2 : Rat)) := by
    simpa [Rat.divInt_eq_div] using (Rat.inv_divInt n2 1)
  rw [hInv]
  simpa [Rat.divInt_eq_div, Int.mul_one, Int.one_mul] using
    (Rat.divInt_mul_divInt n1 1 (d₁ := 1) (d₂ := n2))

theorem EvaluateProofInternal.eo_ite_guard_cases_of_ne_stuck
    (c x y : Term) :
    __eo_ite c x y ≠ Term.Stuck ->
    c = Term.Boolean true ∨ c = Term.Boolean false := by
  intro h
  by_cases hTrue : native_teq c (Term.Boolean true) = true
  · left
    simpa [native_teq] using hTrue
  · by_cases hFalse : native_teq c (Term.Boolean false) = true
    · right
      simpa [native_teq] using hFalse
    · simp [__eo_ite, hTrue, hFalse, native_ite] at h

theorem EvaluateProofInternal.eo_qdiv_total_to_q_args_shape_of_typeof_real
    (x y : Term) :
    __eo_ite
        (__eo_eq (__eo_to_q y) (Term.Rational (native_mk_rational 0 1)))
        (Term.Rational (native_mk_rational 0 1))
        (__eo_qdiv (__eo_to_q x) (__eo_to_q y)) ≠ Term.Stuck ->
    __eo_typeof
        (__eo_ite
          (__eo_eq (__eo_to_q y) (Term.Rational (native_mk_rational 0 1)))
          (Term.Rational (native_mk_rational 0 1))
          (__eo_qdiv (__eo_to_q x) (__eo_to_q y))) =
      Term.UOp UserOp.Real ->
    ∃ qy : native_Rat, __eo_to_q y = Term.Rational qy ∧
      (qy = native_mk_rational 0 1 ∨
        ∃ qx : native_Rat, __eo_to_q x = Term.Rational qx ∧
          native_qeq (native_mk_rational 0 1) qy = false) := by
  intro hNe hTy
  rcases EvaluateProofInternal.eo_ite_guard_cases_of_ne_stuck
      (__eo_eq (__eo_to_q y) (Term.Rational (native_mk_rational 0 1)))
      (Term.Rational (native_mk_rational 0 1))
      (__eo_qdiv (__eo_to_q x) (__eo_to_q y)) hNe with
    hGuard | hGuard
  · have hY :
        __eo_to_q y = Term.Rational (native_mk_rational 0 1) :=
      EvaluateProofInternal.eo_eq_rational_zero_true_eq (__eo_to_q y) hGuard
    exact ⟨native_mk_rational 0 1, hY, Or.inl rfl⟩
  · have hQDivTy :
        __eo_typeof (__eo_qdiv (__eo_to_q x) (__eo_to_q y)) =
          Term.UOp UserOp.Real := by
      rw [hGuard] at hTy
      have hsimpa := hTy
      try simp [__eo_ite] at hsimpa ⊢
      exact hsimpa
    rcases EvaluateProofInternal.eo_to_q_shape y with hYStuck | ⟨qy, hY⟩
    · rw [hYStuck] at hGuard
      simp [__eo_eq] at hGuard
    · by_cases hQEq :
          native_qeq (native_mk_rational 0 1) qy = true
      · rcases EvaluateProofInternal.eo_to_q_shape x with hXStuck | ⟨qx, hX⟩
        · rw [hXStuck, hY] at hQDivTy
          simp [__eo_qdiv] at hQDivTy
          cases hQDivTy
        · rw [hX, hY] at hQDivTy
          simp [__eo_qdiv, hQEq, native_ite] at hQDivTy
          cases hQDivTy
      · have hQEqFalse :
            native_qeq (native_mk_rational 0 1) qy = false := by
          cases hQ : native_qeq (native_mk_rational 0 1) qy <;>
            simp [hQ] at hQEq ⊢
        rcases EvaluateProofInternal.eo_to_q_shape x with hXStuck | ⟨qx, hX⟩
        · rw [hXStuck, hY] at hQDivTy
          simp [__eo_qdiv] at hQDivTy
          cases hQDivTy
        · exact ⟨qy, hY, Or.inr ⟨qx, hX, hQEqFalse⟩⟩

theorem EvaluateProofInternal.eo_qdiv_to_q_args_shape_of_nonstuck
    (x y : Term) :
    __eo_qdiv (__eo_to_q x) (__eo_to_q y) ≠ Term.Stuck ->
    ∃ qx qy : native_Rat,
      __eo_to_q x = Term.Rational qx ∧
      __eo_to_q y = Term.Rational qy ∧
      native_qeq (native_mk_rational 0 1) qy = false := by
  intro hNe
  rcases EvaluateProofInternal.eo_to_q_shape y with hYStuck | ⟨qy, hY⟩
  · rw [hYStuck] at hNe
    simp [__eo_qdiv] at hNe
  · by_cases hQEq :
        native_qeq (native_mk_rational 0 1) qy = true
    · rcases EvaluateProofInternal.eo_to_q_shape x with hXStuck | ⟨qx, hX⟩
      · rw [hXStuck, hY] at hNe
        simp [__eo_qdiv] at hNe
      · rw [hX, hY] at hNe
        simp [__eo_qdiv, hQEq, native_ite] at hNe
    · have hQEqFalse :
          native_qeq (native_mk_rational 0 1) qy = false := by
        cases hQ : native_qeq (native_mk_rational 0 1) qy <;>
          simp [hQ] at hQEq ⊢
      rcases EvaluateProofInternal.eo_to_q_shape x with hXStuck | ⟨qx, hX⟩
      · rw [hXStuck, hY] at hNe
        simp [__eo_qdiv] at hNe
      · exact ⟨qx, qy, hX, hY, hQEqFalse⟩

theorem EvaluateProofInternal.eo_div_total_args_shape_of_typeof_int
    (x y : Term) :
    __eo_ite (__eo_eq y (Term.Numeral 0))
        (Term.Numeral 0) (__eo_zdiv x y) ≠ Term.Stuck ->
    __eo_typeof
        (__eo_ite (__eo_eq y (Term.Numeral 0))
          (Term.Numeral 0) (__eo_zdiv x y)) =
      Term.UOp UserOp.Int ->
    ∃ ny : native_Int, y = Term.Numeral ny ∧
      (ny = 0 ∨
        ∃ nx : native_Int, x = Term.Numeral nx ∧
          native_zeq 0 ny = false) := by
  intro hNe hTy
  rcases EvaluateProofInternal.eo_ite_guard_cases_of_ne_stuck
      (__eo_eq y (Term.Numeral 0))
      (Term.Numeral 0) (__eo_zdiv x y) hNe with
    hGuard | hGuard
  · have hY : y = Term.Numeral 0 :=
      EvaluateProofInternal.eo_eq_numeral_zero_true_eq y hGuard
    subst y
    exact ⟨0, rfl, Or.inl rfl⟩
  · have hZDivTy :
        __eo_typeof (__eo_zdiv x y) = Term.UOp UserOp.Int := by
      rw [hGuard] at hTy
      have hsimpa := hTy
      try simp [__eo_ite] at hsimpa ⊢
      exact hsimpa
    rcases EvaluateProofInternal.eo_zdiv_args_numeral_of_typeof_int x y hZDivTy with
      ⟨nx, ny, hX, hY, hNZ⟩
    exact ⟨ny, hY, Or.inr ⟨nx, hX, hNZ⟩⟩

theorem EvaluateProofInternal.eo_mod_total_args_shape_of_typeof_int
    (x y : Term) :
    __eo_ite (__eo_eq y (Term.Numeral 0))
        x (__eo_zmod x y) ≠ Term.Stuck ->
    __eo_typeof
        (__eo_ite (__eo_eq y (Term.Numeral 0))
          x (__eo_zmod x y)) =
      Term.UOp UserOp.Int ->
    ∃ ny : native_Int, y = Term.Numeral ny ∧
      (ny = 0 ∨
        ∃ nx : native_Int, x = Term.Numeral nx ∧
          native_zeq 0 ny = false) := by
  intro hNe hTy
  rcases EvaluateProofInternal.eo_ite_guard_cases_of_ne_stuck
      (__eo_eq y (Term.Numeral 0))
      x (__eo_zmod x y) hNe with
    hGuard | hGuard
  · have hY : y = Term.Numeral 0 :=
      EvaluateProofInternal.eo_eq_numeral_zero_true_eq y hGuard
    subst y
    exact ⟨0, rfl, Or.inl rfl⟩
  · have hZModTy :
        __eo_typeof (__eo_zmod x y) = Term.UOp UserOp.Int := by
      rw [hGuard] at hTy
      have hsimpa := hTy
      try simp [__eo_ite] at hsimpa ⊢
      exact hsimpa
    rcases EvaluateProofInternal.eo_zmod_args_numeral_of_typeof_int x y hZModTy with
      ⟨nx, ny, hX, hY, hNZ⟩
    exact ⟨ny, hY, Or.inr ⟨nx, hX, hNZ⟩⟩

theorem EvaluateProofInternal.eo_typeof_int_pow2_eq_int_arg_eq_int
    (T : Term) :
    __eo_typeof_int_pow2 T = Term.UOp UserOp.Int ->
    T = Term.UOp UserOp.Int := by
  cases T <;> intro h <;> simp [__eo_typeof_int_pow2] at h ⊢
  case UOp op =>
    cases op <;> simp at h ⊢

theorem EvaluateProofInternal.eo_int_pow2_result_arg_typeof_int
    (x : Term) :
    __eo_typeof
        (__eo_ite (__eo_is_z x)
          (__eo_ite (__eo_is_neg x) (Term.Numeral 0)
            (__eo_pow (Term.Numeral 2) x))
          (__eo_mk_apply (Term.UOp UserOp.int_pow2) x)) =
      Term.UOp UserOp.Int ->
    __eo_typeof x = Term.UOp UserOp.Int := by
  cases x <;> intro h
  case Numeral n =>
    rfl
  all_goals
    simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_pow, __eo_mk_apply, native_ite, native_teq, native_not] at h
  all_goals
    first
    | cases h
    | exact EvaluateProofInternal.eo_typeof_int_pow2_eq_int_arg_eq_int _ h

theorem EvaluateProofInternal.eo_int_pow2_body_typeof_int
    (x : Term)
    (hTy : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_typeof
        (__eo_ite (__eo_is_z x)
          (__eo_ite (__eo_is_neg x) (Term.Numeral 0)
            (__eo_pow (Term.Numeral 2) x))
          (__eo_mk_apply (Term.UOp UserOp.int_pow2) x)) =
      Term.UOp UserOp.Int := by
  cases x <;>
    simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_pow, __eo_mk_apply, native_ite, native_teq, native_not,
      native_and] at hTy ⊢
  all_goals
    first
    | rename_i n
      cases hNeg : native_zlt n 0 <;>
        simp [hNeg, __eo_lit_type_Numeral, native_ite]
      all_goals
        change Term.UOp UserOp.Int = Term.UOp UserOp.Int
        rfl
    | change __eo_typeof_int_pow2 (__eo_typeof _) = Term.UOp UserOp.Int
      rw [hTy]
      rfl
    | cases hTy
    | rfl

theorem EvaluateProofInternal.eo_int_pow2_eval_numeral_to_smt
    (n : native_Int) :
    __eo_to_smt
        (__eo_ite (__eo_is_z (Term.Numeral n))
          (__eo_ite (__eo_is_neg (Term.Numeral n)) (Term.Numeral 0)
            (__eo_pow (Term.Numeral 2) (Term.Numeral n)))
          (__eo_mk_apply (Term.UOp UserOp.int_pow2) (Term.Numeral n))) =
      SmtTerm.Numeral (native_int_pow2 n) := by
  by_cases hNeg : n < 0
  · simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      native_ite, native_teq, native_int_pow2,
      native_zexp_total, native_zlt, native_and, native_not, hNeg]
    rfl
  · simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_pow, native_ite, native_teq, native_int_pow2,
      native_zexp_total, native_zlt, native_and, native_not, hNeg]
    rfl

theorem EvaluateProofInternal.native_int_log_rec_two_eq_nat_log2_go
    (fuel remaining : Nat) :
    impl_native_int_log_rec 2 fuel remaining =
      Nat.rec (motive := fun _ => Nat -> Nat) (fun _ => 0)
        (fun _ ih n => Bool.rec 0 (ih (n.div 2)).succ (Nat.ble 2 n))
        fuel remaining := by
  induction fuel generalizing remaining with
  | zero =>
      rfl
  | succ fuel ih =>
      simp [impl_native_int_log_rec, ih]
      by_cases h : remaining < 2
      · cases hBle : Nat.ble 2 remaining
        · simp [h]
        · have hLe : 2 <= remaining := by
            exact Eq.mp Nat.ble_eq hBle
          exact False.elim ((Nat.not_le.mpr h) hLe)
      · cases hBle : Nat.ble 2 remaining
        · have hLe : 2 <= remaining := Nat.le_of_not_gt h
          have hBleTrue : Nat.ble 2 remaining = true :=
            Eq.mpr Nat.ble_eq hLe
          rw [hBle] at hBleTrue
          cases hBleTrue
        · simp [h]
          rw [Nat.add_comm]
          have hDiv : remaining / 2 = remaining.div 2 := rfl
          rw [hDiv]

theorem EvaluateProofInternal.native_int_log_rec_two_eq_nat_log2 (n : Nat) :
    impl_native_int_log_rec 2 n n = Nat.log2 n := by
  unfold Nat.log2
  rw [EvaluateProofInternal.native_int_log_rec_two_eq_nat_log2_go]

theorem EvaluateProofInternal.native_int_log_two_eq_log2 (n : native_Int) :
    native_int_log 2 n = native_int_log2 n := by
  unfold native_int_log native_int_log2
  by_cases h : n.toNat = 0
  · simp [h]
  · simp [h, EvaluateProofInternal.native_int_log_rec_two_eq_nat_log2]

theorem EvaluateProofInternal.native_int_log2_of_neg
    (n : native_Int) (hNeg : n < 0) :
    native_int_log2 n = 0 := by
  unfold native_int_log2
  have hLe : n ≤ 0 := Int.le_of_lt hNeg
  have hToNat : n.toNat = 0 := Int.toNat_eq_zero.mpr hLe
  simp [hToNat, Nat.log2_zero]

theorem EvaluateProofInternal.eo_int_log2_result_arg_typeof_int
    (x : Term) :
    __eo_typeof
        (__eo_ite (__eo_is_z x)
          (__eo_ite (__eo_is_neg x) (Term.Numeral 0)
            (__eo_log (Term.Numeral 2) x))
          (__eo_mk_apply (Term.UOp UserOp.int_log2) x)) =
      Term.UOp UserOp.Int ->
    __eo_typeof x = Term.UOp UserOp.Int := by
  cases x <;> intro h
  case Numeral n =>
    rfl
  all_goals
    simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_log, __eo_mk_apply, native_ite, native_teq, native_not] at h
  all_goals
    first
    | cases h
    | exact EvaluateProofInternal.eo_typeof_int_pow2_eq_int_arg_eq_int _ h

theorem EvaluateProofInternal.eo_int_log2_body_typeof_int
    (x : Term)
    (hTy : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_typeof
        (__eo_ite (__eo_is_z x)
          (__eo_ite (__eo_is_neg x) (Term.Numeral 0)
            (__eo_log (Term.Numeral 2) x))
          (__eo_mk_apply (Term.UOp UserOp.int_log2) x)) =
      Term.UOp UserOp.Int := by
  cases x <;>
    simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_log, __eo_mk_apply, native_ite, native_teq, native_not,
      native_and] at hTy ⊢
  all_goals
    first
    | rename_i n
      cases hNeg : native_zlt n 0 <;>
        simp [hNeg, __eo_lit_type_Numeral, native_ite]
      all_goals
        change Term.UOp UserOp.Int = Term.UOp UserOp.Int
        rfl
    | change __eo_typeof_int_pow2 (__eo_typeof _) = Term.UOp UserOp.Int
      rw [hTy]
      rfl
    | cases hTy
    | rfl

theorem EvaluateProofInternal.eo_int_log2_eval_numeral_to_smt
    (n : native_Int) :
    __eo_to_smt
        (__eo_ite (__eo_is_z (Term.Numeral n))
          (__eo_ite (__eo_is_neg (Term.Numeral n)) (Term.Numeral 0)
            (__eo_log (Term.Numeral 2) (Term.Numeral n)))
          (__eo_mk_apply (Term.UOp UserOp.int_log2) (Term.Numeral n))) =
      SmtTerm.Numeral (native_int_log2 n) := by
  by_cases hNeg : n < 0
  · have hLog0 : native_int_log2 n = 0 :=
      EvaluateProofInternal.native_int_log2_of_neg n hNeg
    simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      native_ite, native_teq, native_zlt, native_and, native_not,
      hNeg, hLog0]
    rfl
  · simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_log, native_ite, native_teq, native_zlt, native_and,
      native_not, hNeg, EvaluateProofInternal.native_int_log_two_eq_log2]
    rfl

theorem EvaluateProofInternal.eo_typeof_int_ispow2_eq_bool_arg_eq_int
    (T : Term) :
    __eo_typeof_int_ispow2 T = Term.Bool ->
    T = Term.UOp UserOp.Int := by
  cases T <;> intro h <;> simp [__eo_typeof_int_ispow2] at h ⊢
  case UOp op =>
    cases op <;> simp at h ⊢

theorem EvaluateProofInternal.eo_int_ispow2_result_arg_typeof_int
    (x : Term) :
    __eo_typeof
        (let isNeg := __eo_is_neg x
         let isZ := __eo_is_z x
         __eo_ite isZ
          (__eo_ite isNeg (Term.Boolean false)
            (__eo_eq x
              (__eo_pow (Term.Numeral 2)
                (__eo_ite isZ
                  (__eo_ite isNeg (Term.Numeral 0)
                    (__eo_log (Term.Numeral 2) x))
                  (__eo_mk_apply (Term.UOp UserOp.int_log2) x)))))
          (__eo_mk_apply (Term.UOp UserOp.int_ispow2) x)) =
      Term.Bool ->
    __eo_typeof x = Term.UOp UserOp.Int := by
  cases x <;> intro h
  case Numeral n =>
    rfl
  all_goals
    simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_log, __eo_pow, __eo_eq, __eo_mk_apply, native_ite,
      native_teq, native_not] at h
  all_goals
    first
    | cases h
    | exact EvaluateProofInternal.eo_typeof_int_ispow2_eq_bool_arg_eq_int _ h

theorem EvaluateProofInternal.eo_int_ispow2_body_typeof_bool
    (x : Term)
    (hTy : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_typeof
        (let isNeg := __eo_is_neg x
         let isZ := __eo_is_z x
         __eo_ite isZ
          (__eo_ite isNeg (Term.Boolean false)
            (__eo_eq x
              (__eo_pow (Term.Numeral 2)
                (__eo_ite isZ
                  (__eo_ite isNeg (Term.Numeral 0)
                    (__eo_log (Term.Numeral 2) x))
                  (__eo_mk_apply (Term.UOp UserOp.int_log2) x)))))
          (__eo_mk_apply (Term.UOp UserOp.int_ispow2) x)) =
      Term.Bool := by
  cases x <;>
    simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_log, __eo_pow, __eo_eq, __eo_mk_apply, native_ite,
      native_teq, native_not, native_and] at hTy ⊢
  all_goals
    first
    | rename_i n
      cases hNeg : native_zlt n 0 <;>
        simp [hNeg, __eo_lit_type_Numeral, native_ite]
      all_goals
        change Term.Bool = Term.Bool
        rfl
    | change __eo_typeof_int_ispow2 (__eo_typeof _) = Term.Bool
      rw [hTy]
      rfl
    | cases hTy
    | rfl

theorem EvaluateProofInternal.eo_len_typeof_int_of_ne_stuck
    (x : Term)
    (hNe : __eo_len x ≠ Term.Stuck) :
    __eo_typeof (__eo_len x) = Term.UOp UserOp.Int := by
  cases x <;> simp [__eo_len] at hNe ⊢
  all_goals
    change __eo_lit_type_Numeral (Term.Numeral _) =
      Term.UOp UserOp.Int
    rfl

theorem EvaluateProofInternal.eo_to_z_typeof_int_of_ne_stuck
    (x : Term)
    (hNe : __eo_to_z x ≠ Term.Stuck) :
    __eo_typeof (__eo_to_z x) = Term.UOp UserOp.Int := by
  cases x <;> simp [__eo_to_z] at hNe ⊢
  case String s =>
    cases hLen : native_zeq 1 (native_str_len s) <;>
      simp [hLen, native_ite] at hNe ⊢
    change __eo_lit_type_Numeral
        (Term.Numeral (native_str_to_code s)) =
      Term.UOp UserOp.Int
    rfl
  all_goals
    first
    | change __eo_lit_type_Numeral (Term.Numeral _) =
        Term.UOp UserOp.Int
      rfl

theorem EvaluateProofInternal.eo_str_to_code_body_typeof_int
    (x : Term)
    (hTy :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hNe :
      (let len := __eo_len x
       __eo_ite (__eo_eq len (Term.Numeral 1)) (__eo_to_z x)
        (__eo_ite (__eo_is_z len) (Term.Numeral (-1 : native_Int))
          (__eo_mk_apply (Term.UOp UserOp.str_to_code) x))) ≠
        Term.Stuck) :
    __eo_typeof
        (let len := __eo_len x
         __eo_ite (__eo_eq len (Term.Numeral 1)) (__eo_to_z x)
          (__eo_ite (__eo_is_z len) (Term.Numeral (-1 : native_Int))
            (__eo_mk_apply (Term.UOp UserOp.str_to_code) x))) =
      Term.UOp UserOp.Int := by
  cases x <;>
    simp [__eo_len, __eo_eq, __eo_ite, __eo_is_z,
      __eo_is_z_internal, __eo_to_z, __eo_mk_apply, native_ite,
      native_teq, native_not, native_and] at hTy hNe ⊢
  case String s =>
    by_cases hLen : (1 : native_Int) = native_str_len s
    · simp [hLen, native_zeq] at hNe ⊢
      change __eo_lit_type_Numeral
          (Term.Numeral (native_str_to_code s)) =
        Term.UOp UserOp.Int
      rfl
    · simp [hLen] at hNe ⊢
      change __eo_lit_type_Numeral
          (Term.Numeral (-1 : native_Int)) =
        Term.UOp UserOp.Int
      rfl
  all_goals
    first
    | split <;> simp at hNe ⊢
      change __eo_lit_type_Numeral (Term.Numeral _) =
        Term.UOp UserOp.Int
      rfl
    | change __eo_typeof_str_to_code (__eo_typeof _) =
        Term.UOp UserOp.Int
      rw [hTy]
      rfl
    | change __eo_lit_type_Numeral (Term.Numeral _) =
        Term.UOp UserOp.Int
      rfl
    | cases hTy

theorem EvaluateProofInternal.eo_to_str_typeof_seq_char_of_ne_stuck
    (x : Term)
    (hNe : __eo_to_str x ≠ Term.Stuck) :
    __eo_typeof (__eo_to_str x) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases x <;> simp [__eo_to_str] at hNe ⊢
  case Numeral n =>
    cases hGuard : native_and (native_zleq 0 n) (native_zlt n 196608) <;>
      simp [hGuard, native_ite] at hNe ⊢
    change __eo_lit_type_String
        (Term.String (native_str_from_code n)) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
    rfl
  case String s =>
    rfl

theorem EvaluateProofInternal.eo_concat_typeof_seq_char_of_left_seq_char_and_ne_stuck
    (a b : Term)
    (hA :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hNe : __eo_concat a b ≠ Term.Stuck) :
    __eo_typeof (__eo_concat a b) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases a <;> cases b <;> simp [__eo_concat] at hA hNe ⊢
  case String.String s t =>
    rfl
  all_goals
    cases hA

theorem EvaluateProofInternal.str_case_conv_rec_strCharChain_typeof_seq_char_of_ne_stuck :
    ∀ (s : native_String) (isLower : native_Bool),
      __str_case_conv_rec (EvaluateProofInternal.strCharChain s) (Term.Boolean isLower) ≠
        Term.Stuck ->
      __eo_typeof
          (__str_case_conv_rec (EvaluateProofInternal.strCharChain s)
            (Term.Boolean isLower)) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  | [], _isLower, _hNe => by
      simp [EvaluateProofInternal.strCharChain, __str_case_conv_rec]
      change __eo_lit_type_String (Term.String []) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
      rfl
  | c :: cs, true, hNe => by
      unfold EvaluateProofInternal.strCharChain
      change
        __eo_typeof
            (__eo_concat
              (__eo_to_str
                (__eo_add (__eo_to_z (Term.String [c]))
                  (__eo_ite
                    (__eo_and (__eo_gt (Term.Numeral 91)
                      (__eo_to_z (Term.String [c])))
                      (__eo_gt (__eo_to_z (Term.String [c]))
                        (Term.Numeral 64)))
                    (Term.Numeral 32)
                    (Term.Numeral 0))))
              (__str_case_conv_rec (EvaluateProofInternal.strCharChain cs)
                (Term.Boolean true))) =
          Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
      have hConcatNe :
          __eo_concat
              (__eo_to_str
                (__eo_add (__eo_to_z (Term.String [c]))
                  (__eo_ite
                    (__eo_and (__eo_gt (Term.Numeral 91)
                      (__eo_to_z (Term.String [c])))
                      (__eo_gt (__eo_to_z (Term.String [c]))
                        (Term.Numeral 64)))
                    (Term.Numeral 32)
                    (Term.Numeral 0))))
              (__str_case_conv_rec (EvaluateProofInternal.strCharChain cs)
                (Term.Boolean true)) ≠ Term.Stuck := by
        simpa [EvaluateProofInternal.strCharChain, __str_case_conv_rec] using hNe
      have hHeadNe :
          __eo_to_str
              (__eo_add (__eo_to_z (Term.String [c]))
                (__eo_ite
                  (__eo_and (__eo_gt (Term.Numeral 91)
                    (__eo_to_z (Term.String [c])))
                    (__eo_gt (__eo_to_z (Term.String [c]))
                      (Term.Numeral 64)))
                  (Term.Numeral 32)
                  (Term.Numeral 0))) ≠ Term.Stuck := by
        intro hHead
        apply hConcatNe
        rw [hHead]
        rfl
      have hHeadTy :=
        EvaluateProofInternal.eo_to_str_typeof_seq_char_of_ne_stuck _ hHeadNe
      exact
        EvaluateProofInternal.eo_concat_typeof_seq_char_of_left_seq_char_and_ne_stuck
          _ _ hHeadTy hConcatNe
  | c :: cs, false, hNe => by
      unfold EvaluateProofInternal.strCharChain
      change
        __eo_typeof
            (__eo_concat
              (__eo_to_str
                (__eo_add (__eo_to_z (Term.String [c]))
                  (__eo_ite
                    (__eo_and (__eo_gt (Term.Numeral 123)
                      (__eo_to_z (Term.String [c])))
                      (__eo_gt (__eo_to_z (Term.String [c]))
                        (Term.Numeral 96)))
                    (Term.Numeral (-32 : native_Int))
                    (Term.Numeral 0))))
              (__str_case_conv_rec (EvaluateProofInternal.strCharChain cs)
                (Term.Boolean false))) =
          Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
      have hConcatNe :
          __eo_concat
              (__eo_to_str
                (__eo_add (__eo_to_z (Term.String [c]))
                  (__eo_ite
                    (__eo_and (__eo_gt (Term.Numeral 123)
                      (__eo_to_z (Term.String [c])))
                      (__eo_gt (__eo_to_z (Term.String [c]))
                        (Term.Numeral 96)))
                    (Term.Numeral (-32 : native_Int))
                    (Term.Numeral 0))))
              (__str_case_conv_rec (EvaluateProofInternal.strCharChain cs)
                (Term.Boolean false)) ≠ Term.Stuck := by
        simpa [EvaluateProofInternal.strCharChain, __str_case_conv_rec] using hNe
      have hHeadNe :
          __eo_to_str
              (__eo_add (__eo_to_z (Term.String [c]))
                (__eo_ite
                  (__eo_and (__eo_gt (Term.Numeral 123)
                    (__eo_to_z (Term.String [c])))
                    (__eo_gt (__eo_to_z (Term.String [c]))
                      (Term.Numeral 96)))
                  (Term.Numeral (-32 : native_Int))
                  (Term.Numeral 0))) ≠ Term.Stuck := by
        intro hHead
        apply hConcatNe
        rw [hHead]
        rfl
      have hHeadTy :=
        EvaluateProofInternal.eo_to_str_typeof_seq_char_of_ne_stuck _ hHeadNe
      exact
        EvaluateProofInternal.eo_concat_typeof_seq_char_of_left_seq_char_and_ne_stuck
          _ _ hHeadTy hConcatNe

theorem EvaluateProofInternal.eo_str_to_lower_body_typeof_seq_char
    (x : Term)
    (hTy :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hNe :
      __eo_ite (__eo_is_str x)
        (__str_case_conv_rec (__str_flatten (__str_nary_intro x))
          (Term.Boolean true))
        (__eo_mk_apply (Term.UOp UserOp.str_to_lower) x) ≠
        Term.Stuck) :
    __eo_typeof
        (__eo_ite (__eo_is_str x)
          (__str_case_conv_rec (__str_flatten (__str_nary_intro x))
            (Term.Boolean true))
          (__eo_mk_apply (Term.UOp UserOp.str_to_lower) x)) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases x <;>
    simp [__eo_is_str, __eo_is_str_internal, __eo_ite,
      __eo_mk_apply, native_ite, native_teq, native_and, native_not]
      at hTy hNe ⊢
  case String s =>
    rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain]
    exact EvaluateProofInternal.str_case_conv_rec_strCharChain_typeof_seq_char_of_ne_stuck
      s true (by
        simpa [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain] using hNe)
  all_goals
    first
    | change __eo_typeof_str_to_lower (__eo_typeof _) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
      rw [hTy]
      rfl
    | cases hTy

theorem EvaluateProofInternal.eo_str_to_upper_body_typeof_seq_char
    (x : Term)
    (hTy :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hNe :
      __eo_ite (__eo_is_str x)
        (__str_case_conv_rec (__str_flatten (__str_nary_intro x))
          (Term.Boolean false))
        (__eo_mk_apply (Term.UOp UserOp.str_to_upper) x) ≠
        Term.Stuck) :
    __eo_typeof
        (__eo_ite (__eo_is_str x)
          (__str_case_conv_rec (__str_flatten (__str_nary_intro x))
            (Term.Boolean false))
          (__eo_mk_apply (Term.UOp UserOp.str_to_upper) x)) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases x <;>
    simp [__eo_is_str, __eo_is_str_internal, __eo_ite,
      __eo_mk_apply, native_ite, native_teq, native_and, native_not]
      at hTy hNe ⊢
  case String s =>
    rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain]
    exact EvaluateProofInternal.str_case_conv_rec_strCharChain_typeof_seq_char_of_ne_stuck
      s false (by
        simpa [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain] using hNe)
  all_goals
    first
    | change __eo_typeof_str_to_lower (__eo_typeof _) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
      rw [hTy]
      rfl
    | cases hTy

theorem EvaluateProofInternal.str_to_int_eval_rec_strCharChain_typeof_int_of_ne_stuck :
    ∀ (xs : native_String) (e n : native_Int),
      __str_to_int_eval_rec (EvaluateProofInternal.strCharChain xs)
          (Term.Numeral e) (Term.Numeral n) ≠ Term.Stuck ->
        __eo_typeof
            (__str_to_int_eval_rec (EvaluateProofInternal.strCharChain xs)
              (Term.Numeral e) (Term.Numeral n)) =
          Term.UOp UserOp.Int
  | [], _e, _n, _hNe => by
      change __eo_lit_type_Numeral (Term.Numeral _) =
        Term.UOp UserOp.Int
      rfl
  | c :: cs, e, n, hNe => by
      let d := native_zplus (native_str_to_code [c]) (-48 : native_Int)
      by_cases hGuard :
          native_zlt d 10 = true ∧ native_zlt d 0 = false
      · have hTailNe :
            __str_to_int_eval_rec (EvaluateProofInternal.strCharChain cs)
                (Term.Numeral (native_zmult e 10))
                (Term.Numeral (native_zplus (native_zmult d e) n)) ≠
              Term.Stuck := by
          intro hTail
          apply hNe
          unfold EvaluateProofInternal.strCharChain
          unfold __str_to_int_eval_rec
          simp [__eo_to_z, __eo_add, __eo_gt, __eo_is_neg, __eo_not,
            __eo_and, __eo_mul, __eo_ite, native_ite, native_teq,
            native_and, native_not, native_str_len, native_zeq, d,
            hGuard.1, hGuard.2, hTail]
        unfold EvaluateProofInternal.strCharChain
        unfold __str_to_int_eval_rec
        simp [__eo_to_z, __eo_add, __eo_gt, __eo_is_neg, __eo_not,
          __eo_and, __eo_mul, __eo_ite, native_ite, native_teq,
          native_and, native_not, native_str_len, native_zeq, d,
          hGuard.1, hGuard.2]
        exact EvaluateProofInternal.str_to_int_eval_rec_strCharChain_typeof_int_of_ne_stuck
          cs (native_zmult e 10)
          (native_zplus (native_zmult d e) n) hTailNe
      · have hBad :
            native_zlt d 10 = false ∨ native_zlt d 0 = true := by
          cases h10 : native_zlt d 10 <;>
            cases h0 : native_zlt d 0 <;>
            simp [h10, h0] at hGuard ⊢
        rcases hBad with h10 | h0
        · unfold EvaluateProofInternal.strCharChain
          unfold __str_to_int_eval_rec
          simp [__eo_to_z, __eo_add, __eo_gt, __eo_is_neg, __eo_not,
            __eo_and, __eo_mul, __eo_ite, native_ite, native_teq,
            native_and, native_not, native_str_len, native_zeq, d, h10]
          change __eo_lit_type_Numeral (Term.Numeral _) =
            Term.UOp UserOp.Int
          rfl
        · unfold EvaluateProofInternal.strCharChain
          unfold __str_to_int_eval_rec
          simp [__eo_to_z, __eo_add, __eo_gt, __eo_is_neg, __eo_not,
            __eo_and, __eo_mul, __eo_ite, native_ite, native_teq,
            native_and, native_not, native_str_len, native_zeq, d, h0]
          change __eo_lit_type_Numeral (Term.Numeral _) =
            Term.UOp UserOp.Int
          rfl

theorem EvaluateProofInternal.eo_str_to_int_body_typeof_int
    (x : Term)
    (hTy :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hNe :
      __eo_ite (__eo_is_str x)
        (__eo_ite (__eo_eq x (Term.String []))
          (Term.Numeral (-1 : native_Int))
          (__str_to_int_eval_rec
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__str_nary_intro x)))
            (Term.Numeral 1) (Term.Numeral 0)))
        (__eo_mk_apply (Term.UOp UserOp.str_to_int) x) ≠
        Term.Stuck) :
    __eo_typeof
        (__eo_ite (__eo_is_str x)
          (__eo_ite (__eo_eq x (Term.String []))
            (Term.Numeral (-1 : native_Int))
            (__str_to_int_eval_rec
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_flatten (__str_nary_intro x)))
              (Term.Numeral 1) (Term.Numeral 0)))
          (__eo_mk_apply (Term.UOp UserOp.str_to_int) x)) =
      Term.UOp UserOp.Int := by
  cases x <;>
    simp [__eo_is_str, __eo_is_str_internal, __eo_ite,
      __eo_eq, __eo_mk_apply, native_ite, native_teq, native_and,
      native_not] at hTy hNe ⊢
  case String s =>
    cases s with
    | nil =>
        change __eo_lit_type_Numeral (Term.Numeral _) =
          Term.UOp UserOp.Int
        rfl
    | cons c cs =>
        rw [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain]
        rw [EvaluateProofInternal.eo_list_rev_strCharChain]
        exact EvaluateProofInternal.str_to_int_eval_rec_strCharChain_typeof_int_of_ne_stuck
          (c :: cs).reverse 1 0 (by
            simpa [EvaluateProofInternal.str_flatten_nary_intro_string_char_chain,
              EvaluateProofInternal.eo_list_rev_strCharChain] using hNe)
  all_goals
    first
    | change __eo_typeof_str_to_code (__eo_typeof _) = Term.UOp UserOp.Int
      rw [hTy]
      rfl
    | cases hTy

theorem EvaluateProofInternal.eo_str_rev_body_typeof_seq
    (x U : Term)
    (hTy : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) U)
    (hNe :
      __eo_ite (__eo_is_str x)
        (__str_nary_elim
          (__str_collect
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_flatten (__str_nary_intro x)))))
        (__eo_mk_apply (Term.UOp UserOp.str_rev) x) ≠ Term.Stuck) :
    __eo_typeof
        (__eo_ite (__eo_is_str x)
          (__str_nary_elim
            (__str_collect
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_flatten (__str_nary_intro x)))))
          (__eo_mk_apply (Term.UOp UserOp.str_rev) x)) =
      Term.Apply (Term.UOp UserOp.Seq) U := by
  cases x
  case String s =>
    rw [EvaluateProofInternal.str_rev_result_string]
    cases hTy
    rfl
  all_goals
    simp [__eo_is_str, __eo_is_str_internal, __eo_ite,
      __eo_mk_apply, native_ite, native_teq, native_and, native_not]
      at hTy hNe ⊢
  all_goals
    change __eo_typeof_str_rev (__eo_typeof _) =
      Term.Apply (Term.UOp UserOp.Seq) U
    rw [hTy]
    rfl

theorem EvaluateProofInternal.eo_eval_str_from_int_rhs_typeof_seq_char
    (x : Term)
    (hRunTy : __eo_typeof (__run_evaluate x) = Term.UOp UserOp.Int) :
    __eo_typeof (EvaluateProofInternal.eo_eval_str_from_int_rhs x) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases hRunX : __run_evaluate x
  case Numeral n =>
    rw [EvaluateProofInternal.eo_eval_str_from_int_rhs_run_numeral (x := x) (n := n) hRunX]
    rfl
  all_goals
    have hRunXNe : __run_evaluate x ≠ Term.Stuck := by
      intro hStuck
      rw [hStuck] at hRunTy
      change Term.Stuck = Term.UOp UserOp.Int at hRunTy
      cases hRunTy
    have hNotNumeral :
        ∀ n : native_Int, __run_evaluate x ≠ Term.Numeral n := by
      intro n hNum
      rw [hRunX] at hNum
      cases hNum
    rw [EvaluateProofInternal.eo_eval_str_from_int_rhs_run_non_numeral
      (x := x) (t := __run_evaluate x) rfl hNotNumeral hRunXNe]
    change __eo_typeof_str_from_code (__eo_typeof (__run_evaluate x)) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
    rw [hRunTy]
    rfl

theorem EvaluateProofInternal.eo_eval_str_from_code_rhs_typeof_seq_char
    (x : Term)
    (hXEoInt : __eo_typeof x = Term.UOp UserOp.Int)
    (hRunFromNe : EvaluateProofInternal.eo_eval_str_from_code_rhs x ≠ Term.Stuck)
    (hActive :
      EvaluateProofInternal.eo_eval_str_from_code_rhs x ≠
        Term.Apply (Term.UOp UserOp.str_from_code) x) :
    __eo_typeof (EvaluateProofInternal.eo_eval_str_from_code_rhs x) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases hRunX : __run_evaluate x
  case Numeral n =>
    rw [EvaluateProofInternal.eo_eval_str_from_code_rhs_run_numeral_eq_of_active
      (x := x) (n := n) hRunX hXEoInt hRunFromNe hActive]
    rfl
  all_goals
    exfalso
    apply hActive
    dsimp [EvaluateProofInternal.eo_eval_str_from_code_rhs]
    rw [hRunX]
    simp [__eo_ite, native_ite, native_teq, __eo_is_z,
      __eo_is_z_internal, native_and, native_not]

theorem EvaluateProofInternal.int_ispow2_numeral_to_smt_type_bool
    (n : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (let isNeg := __eo_is_neg (Term.Numeral n)
           let isZ := __eo_is_z (Term.Numeral n)
           __eo_ite isZ
            (__eo_ite isNeg (Term.Boolean false)
              (__eo_eq (Term.Numeral n)
                (__eo_pow (Term.Numeral 2)
                  (__eo_ite isZ
                    (__eo_ite isNeg (Term.Numeral 0)
                      (__eo_log (Term.Numeral 2) (Term.Numeral n)))
                    (__eo_mk_apply (Term.UOp UserOp.int_log2)
                      (Term.Numeral n))))))
            (__eo_mk_apply (Term.UOp UserOp.int_ispow2)
              (Term.Numeral n)))) =
      SmtType.Bool := by
  by_cases hNeg : n < 0
  · simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      native_ite, native_teq, native_and, native_not, native_zlt, hNeg]
    rw [__smtx_typeof.eq_1]
  · simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      __eo_eq, __eo_pow, __eo_log, native_ite, native_teq, native_and,
      native_not, native_zlt, hNeg, EvaluateProofInternal.native_int_log_two_eq_log2,
      eq_comm]
    rw [__smtx_typeof.eq_1]

theorem EvaluateProofInternal.int_ispow2_numeral_eval_rel
    (M : SmtModel) (n : native_Int) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.and
          (SmtTerm.geq (SmtTerm.Numeral n) (SmtTerm.Numeral 0))
          (SmtTerm.eq (SmtTerm.Numeral n)
            (SmtTerm.int_pow2 (SmtTerm.int_log2 (SmtTerm.Numeral n))))))
      (__smtx_model_eval M
        (__eo_to_smt
          (let isNeg := __eo_is_neg (Term.Numeral n)
           let isZ := __eo_is_z (Term.Numeral n)
           __eo_ite isZ
            (__eo_ite isNeg (Term.Boolean false)
              (__eo_eq (Term.Numeral n)
                (__eo_pow (Term.Numeral 2)
                  (__eo_ite isZ
                    (__eo_ite isNeg (Term.Numeral 0)
                      (__eo_log (Term.Numeral 2) (Term.Numeral n)))
                    (__eo_mk_apply (Term.UOp UserOp.int_log2)
                      (Term.Numeral n))))))
            (__eo_mk_apply (Term.UOp UserOp.int_ispow2)
              (Term.Numeral n))))) := by
  by_cases hNeg : n < 0
  · have hGeq : native_zleq 0 n = false := by
      unfold native_zleq
      rw [decide_eq_false_iff_not]
      exact Int.not_le.mpr hNeg
    simp [__smtx_model_eval, __smtx_model_eval_geq, __smtx_model_eval_leq,
      __smtx_model_eval_eq, __smtx_model_eval_and,
      __smtx_model_eval_int_pow2, __smtx_model_eval_int_log2,
      __eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite,
      native_ite, native_teq, native_and, native_not,
      native_veq, native_zlt, hNeg, hGeq, RuleProofs.smt_value_rel]
  · have hGeq : native_zleq 0 n = true := by
      unfold native_zleq
      rw [decide_eq_true_eq]
      exact Int.le_of_not_gt hNeg
    simp [__smtx_model_eval, __smtx_model_eval_geq, __smtx_model_eval_leq,
      __smtx_model_eval_eq, __smtx_model_eval_and,
      __smtx_model_eval_int_pow2, __smtx_model_eval_int_log2,
      __eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_ite, __eo_eq,
      __eo_pow, __eo_log, native_ite, native_teq, native_and, native_not,
      native_veq, native_zlt, hGeq, hNeg, EvaluateProofInternal.native_int_log_two_eq_log2,
      native_int_pow2, RuleProofs.smt_value_rel, eq_comm]

theorem EvaluateProofInternal.eo_abs_arg_numeral_of_typeof_int
    (x : Term) :
    __eo_typeof (__eo_ite (__eo_is_neg x) (__eo_neg x) x) =
      Term.UOp UserOp.Int ->
    ∃ nx : native_Int, x = Term.Numeral nx := by
  cases x <;> intro h
  case Numeral nx =>
    exact ⟨nx, rfl⟩
  case Rational q =>
    cases hNeg : native_qlt q (native_mk_rational 0 1)
    · simp [__eo_is_neg, __eo_ite, hNeg, native_ite,
        native_teq] at h
      change Term.UOp UserOp.Real = Term.UOp UserOp.Int at h
      cases h
    · simp [__eo_is_neg, __eo_neg, __eo_ite, hNeg, native_ite,
        native_teq] at h
      change Term.UOp UserOp.Real = Term.UOp UserOp.Int at h
      cases h
  all_goals
    simp [__eo_is_neg, __eo_ite, native_ite, native_teq] at h
    change Term.Stuck = Term.UOp UserOp.Int at h
    cases h

theorem EvaluateProofInternal.eo_abs_arg_rational_of_typeof_real
    (x : Term) :
    __eo_typeof (__eo_ite (__eo_is_neg x) (__eo_neg x) x) =
      Term.UOp UserOp.Real ->
    ∃ qx : native_Rat, x = Term.Rational qx := by
  cases x <;> intro h
  case Rational qx =>
    exact ⟨qx, rfl⟩
  case Numeral nx =>
    cases hNeg : native_zlt nx 0
    · simp [__eo_is_neg, __eo_neg, __eo_ite, hNeg, native_ite,
        native_teq] at h
      change Term.UOp UserOp.Int = Term.UOp UserOp.Real at h
      cases h
    · simp [__eo_is_neg, __eo_ite, hNeg, native_ite,
        native_teq] at h
      change Term.UOp UserOp.Int = Term.UOp UserOp.Real at h
      cases h
  all_goals
    simp [__eo_is_neg, __eo_ite, native_ite, native_teq] at h
    change Term.Stuck = Term.UOp UserOp.Real at h
    cases h

theorem EvaluateProofInternal.eo_neg_arg_binary_of_typeof_bitvec
    (x : Term) (w : native_Int) :
    __eo_typeof (__eo_neg x) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, x = Term.Binary w nx := by
  cases x <;> intro h
  case Numeral n =>
    simp only [__eo_neg] at h
    change Term.UOp UserOp.Int =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
  case Rational r =>
    simp only [__eo_neg] at h
    change Term.UOp UserOp.Real =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
  case Binary wx nx =>
    simp only [__eo_neg] at h
    change
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
    exact ⟨nx, rfl⟩
  all_goals
    simp only [__eo_neg] at h
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

theorem EvaluateProofInternal.eo_to_q_typeof_real_of_arg_int
    (x : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Int)
    (hNe : __eo_to_q x ≠ Term.Stuck) :
    __eo_typeof (__eo_to_q x) = Term.UOp UserOp.Real := by
  cases x <;> simp [__eo_to_q] at hX hNe ⊢
  all_goals
    first
    | rfl
    | contradiction
    | cases hX

theorem EvaluateProofInternal.eo_to_q_typeof_real_of_arg_real
    (x : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Real)
    (hNe : __eo_to_q x ≠ Term.Stuck) :
    __eo_typeof (__eo_to_q x) = Term.UOp UserOp.Real := by
  cases x <;> simp [__eo_to_q] at hX hNe ⊢
  all_goals
    first
    | rfl
    | contradiction
    | cases hX

theorem EvaluateProofInternal.eo_eq_typeof_bool_of_args_real
    (x y : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Real)
    (hY : __eo_typeof y = Term.UOp UserOp.Real) :
    __eo_typeof (__eo_eq x y) = Term.Bool := by
  cases x <;> cases y <;> simp [__eo_eq] at hX hY ⊢
  all_goals
    first
    | contradiction
    | rfl
    | cases hY
    | cases hX

theorem EvaluateProofInternal.eo_ite_typeof_of_branches_same
    (c t e T : Term)
    (hTNe : T ≠ Term.Stuck)
    (hT : __eo_typeof t = T)
    (hE : __eo_typeof e = T)
    (hNe : __eo_ite c t e ≠ Term.Stuck) :
    __eo_typeof (__eo_ite c t e) = T := by
  cases c <;>
    simp [__eo_ite, native_ite, native_teq] at hNe ⊢
  case Boolean b =>
    cases b <;> simpa [native_ite] using (by
      first
      | exact hT
      | exact hE)
  all_goals
    contradiction

theorem EvaluateProofInternal.eo_zdiv_typeof_int_of_args_int_and_ne_stuck
    (x y : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Int)
    (hY : __eo_typeof y = Term.UOp UserOp.Int)
    (hNe : __eo_zdiv x y ≠ Term.Stuck) :
    __eo_typeof (__eo_zdiv x y) = Term.UOp UserOp.Int := by
  cases x <;> cases y <;> simp [__eo_zdiv] at hX hY hNe ⊢
  case Numeral.Numeral nx ny =>
    cases hZero : native_zeq 0 ny <;>
      simp [hZero, native_ite] at hNe ⊢
    rfl
  all_goals
    first
    | cases hX
    | cases hY
    | contradiction

theorem EvaluateProofInternal.eo_zmod_typeof_int_of_args_int_and_ne_stuck
    (x y : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Int)
    (hY : __eo_typeof y = Term.UOp UserOp.Int)
    (hNe : __eo_zmod x y ≠ Term.Stuck) :
    __eo_typeof (__eo_zmod x y) = Term.UOp UserOp.Int := by
  cases x <;> cases y <;> simp [__eo_zmod] at hX hY hNe ⊢
  case Numeral.Numeral nx ny =>
    cases hZero : native_zeq 0 ny <;>
      simp [hZero, native_ite] at hNe ⊢
    rfl
  all_goals
    first
    | cases hX
    | cases hY
    | contradiction

theorem EvaluateProofInternal.eo_qdiv_typeof_real_of_ne_stuck
    (x y : Term)
    (hNe : __eo_qdiv x y ≠ Term.Stuck) :
    __eo_typeof (__eo_qdiv x y) = Term.UOp UserOp.Real := by
  cases x <;> cases y <;> simp [__eo_qdiv] at hNe ⊢
  case Numeral.Numeral nx ny =>
    cases hZero : native_zeq 0 ny <;>
      simp [hZero, native_ite] at hNe ⊢
    rfl
  case Rational.Rational qx qy =>
    cases hZero : native_qeq (native_mk_rational 0 1) qy <;>
      simp [hZero, native_ite] at hNe ⊢
    rfl
  all_goals
    contradiction

theorem EvaluateProofInternal.eo_zdiv_left_ne_stuck {a b : Term} :
    __eo_zdiv a b ≠ Term.Stuck -> a ≠ Term.Stuck := by
  intro h ha
  rw [ha] at h
  cases b <;> simp [__eo_zdiv] at h

theorem EvaluateProofInternal.eo_zdiv_right_ne_stuck {a b : Term} :
    __eo_zdiv a b ≠ Term.Stuck -> b ≠ Term.Stuck := by
  intro h hb
  rw [hb] at h
  cases a <;> simp [__eo_zdiv] at h

theorem EvaluateProofInternal.eo_zmod_left_ne_stuck {a b : Term} :
    __eo_zmod a b ≠ Term.Stuck -> a ≠ Term.Stuck := by
  intro h ha
  rw [ha] at h
  cases b <;> simp [__eo_zmod] at h

theorem EvaluateProofInternal.eo_zmod_right_ne_stuck {a b : Term} :
    __eo_zmod a b ≠ Term.Stuck -> b ≠ Term.Stuck := by
  intro h hb
  rw [hb] at h
  cases a <;> simp [__eo_zmod] at h

theorem EvaluateProofInternal.eo_qdiv_left_ne_stuck {a b : Term} :
    __eo_qdiv a b ≠ Term.Stuck -> a ≠ Term.Stuck := by
  intro h ha
  rw [ha] at h
  cases b <;> simp [__eo_qdiv] at h

theorem EvaluateProofInternal.eo_qdiv_right_ne_stuck {a b : Term} :
    __eo_qdiv a b ≠ Term.Stuck -> b ≠ Term.Stuck := by
  intro h hb
  rw [hb] at h
  cases a <;> simp [__eo_qdiv] at h

theorem EvaluateProofInternal.eo_leq_body_typeof_bool_of_int_args
    (x y : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Int)
    (hY : __eo_typeof y = Term.UOp UserOp.Int)
    (hNe :
      (let d := __eo_add x (__eo_neg y)
       __eo_or (__eo_is_neg d)
        (__eo_eq (__eo_to_q d)
          (Term.Rational (native_mk_rational 0 1)))) ≠ Term.Stuck) :
    __eo_typeof
        (let d := __eo_add x (__eo_neg y)
         __eo_or (__eo_is_neg d)
          (__eo_eq (__eo_to_q d)
            (Term.Rational (native_mk_rational 0 1)))) =
      Term.Bool := by
  let d := __eo_add x (__eo_neg y)
  have hOrNe :
      __eo_or (__eo_is_neg d)
          (__eo_eq (__eo_to_q d)
            (Term.Rational (native_mk_rational 0 1))) ≠
        Term.Stuck := by
    simpa [d] using hNe
  have hIsNegNe : __eo_is_neg d ≠ Term.Stuck :=
    EvaluateProofInternal.eo_or_left_ne_stuck hOrNe
  have hDNe : d ≠ Term.Stuck :=
    EvaluateProofInternal.eo_is_neg_arg_ne_stuck hIsNegNe
  have hNegYNe : __eo_neg y ≠ Term.Stuck :=
    EvaluateProofInternal.eo_add_right_ne_stuck (by simpa [d] using hDNe)
  have hNegY : __eo_typeof (__eo_neg y) = Term.UOp UserOp.Int :=
    EvaluateProofInternal.eo_neg_typeof_int_of_arg_int y hY hNegYNe
  have hD : __eo_typeof d = Term.UOp UserOp.Int := by
    dsimp [d]
    exact EvaluateProofInternal.eo_add_typeof_int_of_args_int x (__eo_neg y) hX hNegY
      (by simpa [d] using hDNe)
  have hIsNeg : __eo_typeof (__eo_is_neg d) = Term.Bool :=
    EvaluateProofInternal.eo_is_neg_typeof_bool_of_arg_int d hD hIsNegNe
  have hEqNe :
      __eo_eq (__eo_to_q d)
          (Term.Rational (native_mk_rational 0 1)) ≠
        Term.Stuck :=
    EvaluateProofInternal.eo_or_right_ne_stuck hOrNe
  have hToQNe : __eo_to_q d ≠ Term.Stuck :=
    EvaluateProofInternal.eo_eq_left_ne_stuck hEqNe
  have hToQ : __eo_typeof (__eo_to_q d) = Term.UOp UserOp.Real :=
    EvaluateProofInternal.eo_to_q_typeof_real_of_arg_int d hD hToQNe
  have hEq :
      __eo_typeof
          (__eo_eq (__eo_to_q d)
            (Term.Rational (native_mk_rational 0 1))) =
        Term.Bool :=
    EvaluateProofInternal.eo_eq_typeof_bool_of_args_real
      (__eo_to_q d) (Term.Rational (native_mk_rational 0 1))
      hToQ rfl
  simpa [d] using
    EvaluateProofInternal.eo_or_typeof_bool_of_args_bool (__eo_is_neg d)
      (__eo_eq (__eo_to_q d)
        (Term.Rational (native_mk_rational 0 1))) hIsNeg hEq hOrNe

theorem EvaluateProofInternal.eo_leq_body_typeof_bool_of_real_args
    (x y : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Real)
    (hY : __eo_typeof y = Term.UOp UserOp.Real)
    (hNe :
      (let d := __eo_add x (__eo_neg y)
       __eo_or (__eo_is_neg d)
        (__eo_eq (__eo_to_q d)
          (Term.Rational (native_mk_rational 0 1)))) ≠ Term.Stuck) :
    __eo_typeof
        (let d := __eo_add x (__eo_neg y)
         __eo_or (__eo_is_neg d)
          (__eo_eq (__eo_to_q d)
            (Term.Rational (native_mk_rational 0 1)))) =
      Term.Bool := by
  let d := __eo_add x (__eo_neg y)
  have hOrNe :
      __eo_or (__eo_is_neg d)
          (__eo_eq (__eo_to_q d)
            (Term.Rational (native_mk_rational 0 1))) ≠
        Term.Stuck := by
    simpa [d] using hNe
  have hIsNegNe : __eo_is_neg d ≠ Term.Stuck :=
    EvaluateProofInternal.eo_or_left_ne_stuck hOrNe
  have hDNe : d ≠ Term.Stuck :=
    EvaluateProofInternal.eo_is_neg_arg_ne_stuck hIsNegNe
  have hNegYNe : __eo_neg y ≠ Term.Stuck :=
    EvaluateProofInternal.eo_add_right_ne_stuck (by simpa [d] using hDNe)
  have hNegY : __eo_typeof (__eo_neg y) = Term.UOp UserOp.Real :=
    EvaluateProofInternal.eo_neg_typeof_real_of_arg_real y hY hNegYNe
  have hD : __eo_typeof d = Term.UOp UserOp.Real := by
    dsimp [d]
    exact EvaluateProofInternal.eo_add_typeof_real_of_args_real x (__eo_neg y) hX hNegY
      (by simpa [d] using hDNe)
  have hIsNeg : __eo_typeof (__eo_is_neg d) = Term.Bool :=
    EvaluateProofInternal.eo_is_neg_typeof_bool_of_arg_real d hD hIsNegNe
  have hEqNe :
      __eo_eq (__eo_to_q d)
          (Term.Rational (native_mk_rational 0 1)) ≠
        Term.Stuck :=
    EvaluateProofInternal.eo_or_right_ne_stuck hOrNe
  have hToQNe : __eo_to_q d ≠ Term.Stuck :=
    EvaluateProofInternal.eo_eq_left_ne_stuck hEqNe
  have hToQ : __eo_typeof (__eo_to_q d) = Term.UOp UserOp.Real :=
    EvaluateProofInternal.eo_to_q_typeof_real_of_arg_real d hD hToQNe
  have hEq :
      __eo_typeof
          (__eo_eq (__eo_to_q d)
            (Term.Rational (native_mk_rational 0 1))) =
        Term.Bool :=
    EvaluateProofInternal.eo_eq_typeof_bool_of_args_real
      (__eo_to_q d) (Term.Rational (native_mk_rational 0 1))
      hToQ rfl
  simpa [d] using
    EvaluateProofInternal.eo_or_typeof_bool_of_args_bool (__eo_is_neg d)
      (__eo_eq (__eo_to_q d)
        (Term.Rational (native_mk_rational 0 1))) hIsNeg hEq hOrNe

theorem EvaluateProofInternal.eo_zdiv_typeof_int_of_right_int_and_ne_stuck
    (x y : Term)
    (hY : __eo_typeof y = Term.UOp UserOp.Int)
    (hNe : __eo_zdiv x y ≠ Term.Stuck) :
    __eo_typeof (__eo_zdiv x y) = Term.UOp UserOp.Int := by
  cases y <;> simp [__eo_zdiv] at hY hNe ⊢
  case Numeral ny =>
    cases x <;> simp [__eo_zdiv] at hNe ⊢
    case Numeral nx =>
      cases hZero : native_zeq 0 ny <;>
        simp [hZero, native_ite] at hNe ⊢
      rfl
    all_goals
      contradiction
  all_goals
    cases hY

theorem EvaluateProofInternal.eo_zmod_typeof_int_of_right_int_and_ne_stuck
    (x y : Term)
    (hY : __eo_typeof y = Term.UOp UserOp.Int)
    (hNe : __eo_zmod x y ≠ Term.Stuck) :
    __eo_typeof (__eo_zmod x y) = Term.UOp UserOp.Int := by
  cases y <;> simp [__eo_zmod] at hY hNe ⊢
  case Numeral ny =>
    cases x <;> simp [__eo_zmod] at hNe ⊢
    case Numeral nx =>
      cases hZero : native_zeq 0 ny <;>
        simp [hZero, native_ite] at hNe ⊢
      rfl
    all_goals
      contradiction
  all_goals
    cases hY

theorem EvaluateProofInternal.eo_div_total_body_typeof_int_of_right_int
    (x y : Term)
    (hY : __eo_typeof y = Term.UOp UserOp.Int)
    (hNe :
      __eo_ite (__eo_eq y (Term.Numeral 0))
          (Term.Numeral 0) (__eo_zdiv x y) ≠ Term.Stuck) :
    __eo_typeof
        (__eo_ite (__eo_eq y (Term.Numeral 0))
          (Term.Numeral 0) (__eo_zdiv x y)) =
      Term.UOp UserOp.Int := by
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
      (__eo_eq y (Term.Numeral 0))
      (Term.Numeral 0) (__eo_zdiv x y) hNe with
    ⟨b, hCond, hSel⟩
  cases b
  · have hDivTy :
        __eo_typeof (__eo_zdiv x y) = Term.UOp UserOp.Int :=
      EvaluateProofInternal.eo_zdiv_typeof_int_of_right_int_and_ne_stuck x y hY hSel
    rw [hCond]
    simpa [__eo_ite, native_ite, native_teq] using hDivTy
  · rw [hCond]
    rfl

theorem EvaluateProofInternal.eo_mod_total_body_typeof_int_of_args_int
    (x y : Term)
    (hX : __eo_typeof x = Term.UOp UserOp.Int)
    (hY : __eo_typeof y = Term.UOp UserOp.Int)
    (hNe :
      __eo_ite (__eo_eq y (Term.Numeral 0))
          x (__eo_zmod x y) ≠ Term.Stuck) :
    __eo_typeof
        (__eo_ite (__eo_eq y (Term.Numeral 0))
          x (__eo_zmod x y)) =
      Term.UOp UserOp.Int := by
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
      (__eo_eq y (Term.Numeral 0))
      x (__eo_zmod x y) hNe with
    ⟨b, hCond, hSel⟩
  cases b
  · have hModTy :
        __eo_typeof (__eo_zmod x y) = Term.UOp UserOp.Int :=
      EvaluateProofInternal.eo_zmod_typeof_int_of_right_int_and_ne_stuck x y hY hSel
    rw [hCond]
    simpa [__eo_ite, native_ite, native_teq] using hModTy
  · rw [hCond]
    simpa [__eo_ite, native_ite, native_teq] using hX

theorem EvaluateProofInternal.eo_qdiv_total_body_typeof_real_of_ne_stuck
    (x y : Term)
    (hNe :
      __eo_ite
          (__eo_eq y (Term.Rational (native_mk_rational 0 1)))
          (Term.Rational (native_mk_rational 0 1))
          (__eo_qdiv x y) ≠ Term.Stuck) :
    __eo_typeof
        (__eo_ite
          (__eo_eq y (Term.Rational (native_mk_rational 0 1)))
          (Term.Rational (native_mk_rational 0 1))
          (__eo_qdiv x y)) =
      Term.UOp UserOp.Real := by
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
      (__eo_eq y (Term.Rational (native_mk_rational 0 1)))
      (Term.Rational (native_mk_rational 0 1))
      (__eo_qdiv x y) hNe with
    ⟨b, hCond, hSel⟩
  cases b
  · have hQDivTy :
        __eo_typeof (__eo_qdiv x y) = Term.UOp UserOp.Real :=
      EvaluateProofInternal.eo_qdiv_typeof_real_of_ne_stuck x y hSel
    rw [hCond]
    simpa [__eo_ite, native_ite, native_teq] using hQDivTy
  · rw [hCond]
    rfl

theorem EvaluateProofInternal.eo_mod_total_left_ne_stuck {x y : Term} :
    __eo_ite (__eo_eq y (Term.Numeral 0)) x (__eo_zmod x y) ≠
        Term.Stuck ->
      x ≠ Term.Stuck := by
  intro h hx
  rw [hx] at h
  -- every branch of the guard chain is `Term.Stuck`, so the whole chain is
  -- `Term.Stuck` and contradicts `h`; `simp` no longer collapses it itself
  cases y <;> simp [__eo_eq, __eo_ite, __eo_zmod, native_ite] at h
  -- what simp leaves is a guard chain whose every branch is `Term.Stuck`,
  -- so the chain equals `Term.Stuck` and contradicts `h`
  all_goals
    first
      | exact h rfl
      | exact h (by split <;> (try split) <;> rfl)
      | exact h (by simp [native_teq, native_ite, ite_self])
      | exact h (by simp only [native_teq]; split <;> (try split) <;> rfl)

theorem EvaluateProofInternal.eo_and_typeof_bitvec_of_args_bitvec
    (x y : Term) (w : native_Int)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hY :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hNe : __eo_and x y ≠ Term.Stuck) :
    __eo_typeof (__eo_and x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  cases x <;> cases y <;> simp [__eo_and] at hX hY hNe ⊢
  case Binary.Binary wx nx wy ny =>
    cases hX
    cases hY
    simp [__eo_requires, native_ite, native_teq, native_not] at hNe ⊢
    rfl
  all_goals
    contradiction

theorem EvaluateProofInternal.eo_or_typeof_bitvec_of_args_bitvec
    (x y : Term) (w : native_Int)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hY :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hNe : __eo_or x y ≠ Term.Stuck) :
    __eo_typeof (__eo_or x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  cases x <;> cases y <;> simp [__eo_or] at hX hY hNe ⊢
  case Binary.Binary wx nx wy ny =>
    cases hX
    cases hY
    simp [__eo_requires, native_ite, native_teq, native_not] at hNe ⊢
    rfl
  all_goals
    contradiction

theorem EvaluateProofInternal.eo_xor_typeof_bitvec_of_args_bitvec
    (x y : Term) (w : native_Int)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hY :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hNe : __eo_xor x y ≠ Term.Stuck) :
    __eo_typeof (__eo_xor x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  cases x <;> cases y <;> simp [__eo_xor] at hX hY hNe ⊢
  case Binary.Binary wx nx wy ny =>
    cases hX
    cases hY
    simp [__eo_requires, native_ite, native_teq, native_not] at hNe ⊢
    rfl
  all_goals
    contradiction

theorem EvaluateProofInternal.eo_add_typeof_bitvec_of_args_bitvec
    (x y : Term) (w : native_Int)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hY :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hNe : __eo_add x y ≠ Term.Stuck) :
    __eo_typeof (__eo_add x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  cases x <;> cases y <;> simp [__eo_add] at hX hY hNe ⊢
  case Binary.Binary wx nx wy ny =>
    cases hX
    cases hY
    simp [__eo_requires, native_ite, native_teq, native_not] at hNe ⊢
    rfl
  all_goals
    contradiction

theorem EvaluateProofInternal.eo_mul_typeof_bitvec_of_args_bitvec
    (x y : Term) (w : native_Int)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hY :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hNe : __eo_mul x y ≠ Term.Stuck) :
    __eo_typeof (__eo_mul x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  cases x <;> cases y <;> simp [__eo_mul] at hX hY hNe ⊢
  case Binary.Binary wx nx wy ny =>
    cases hX
    cases hY
    simp [__eo_requires, native_ite, native_teq, native_not] at hNe ⊢
    rfl
  all_goals
    contradiction

theorem EvaluateProofInternal.eo_neg_typeof_bitvec_of_arg_bitvec
    (x : Term) (w : native_Int)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hNe : __eo_neg x ≠ Term.Stuck) :
    __eo_typeof (__eo_neg x) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  cases x <;> simp [__eo_neg] at hX hNe ⊢
  case Binary wx nx =>
    cases hX
    rfl
  all_goals
    contradiction

theorem EvaluateProofInternal.eo_zdiv_typeof_bitvec_of_args_bitvec_and_ne_stuck
    (x y : Term) (w : native_Int)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hY :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hNe : __eo_zdiv x y ≠ Term.Stuck) :
    __eo_typeof (__eo_zdiv x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  cases x <;> cases y <;> simp [__eo_zdiv] at hX hY hNe ⊢
  case Binary.Binary wx nx wy ny =>
    cases hX
    cases hY
    cases hZero : native_zeq 0 ny <;>
      simp [__eo_requires, __eo_eq, hZero, native_ite, native_teq,
        native_not] at hNe ⊢
    all_goals
      rfl
  all_goals
    first
    | cases hX
    | cases hY

theorem EvaluateProofInternal.eo_zmod_typeof_bitvec_of_args_bitvec_and_ne_stuck
    (x y : Term) (w : native_Int)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hY :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hNe : __eo_zmod x y ≠ Term.Stuck) :
    __eo_typeof (__eo_zmod x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  cases x <;> cases y <;> simp [__eo_zmod] at hX hY hNe ⊢
  case Binary.Binary wx nx wy ny =>
    cases hX
    cases hY
    cases hZero : native_zeq 0 ny <;>
      simp [__eo_requires, __eo_eq, hZero, native_ite, native_teq,
        native_not] at hNe ⊢
    all_goals
      rfl
  all_goals
    first
    | cases hX
    | cases hY

theorem EvaluateProofInternal.eo_concat_typeof_bitvec_of_args_bitvec_and_ne_stuck
    (x y : Term) (wx wy : native_Int)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx))
    (hY :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wy))
    (hNe : __eo_concat x y ≠ Term.Stuck) :
    __eo_typeof (__eo_concat x y) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_zplus wx wy)) := by
  cases x <;> cases y <;> simp [__eo_concat] at hX hY hNe ⊢
  case Binary.Binary vx nx vy ny =>
    cases hX
    cases hY
    cases hWidth : native_zleq 0 (native_zplus wx wy) <;>
      simp [__eo_mk_binary, hWidth, native_ite] at hNe ⊢
    all_goals
      first
      | rfl
      | contradiction
  all_goals
    first
    | cases hX
    | cases hY

theorem EvaluateProofInternal.eo_eq_typeof_bool_of_ne_stuck
    (x y : Term)
    (hNe : __eo_eq x y ≠ Term.Stuck) :
    __eo_typeof (__eo_eq x y) = Term.Bool := by
  cases x <;> cases y <;> simp [__eo_eq] at hNe ⊢

theorem EvaluateProofInternal.eo_gt_typeof_bool_of_ne_stuck
    (x y : Term)
    (hNe : __eo_gt x y ≠ Term.Stuck) :
    __eo_typeof (__eo_gt x y) = Term.Bool := by
  cases x <;> cases y <;> simp [__eo_gt] at hNe ⊢
  case Binary.Binary wx nx wy ny =>
    by_cases hWidth : wx = wy
    · subst wy
      simp [__eo_requires, native_ite, native_teq, native_not] at hNe ⊢
    · simp [__eo_requires, native_ite, native_teq, native_not, hWidth]
        at hNe

theorem EvaluateProofInternal.eo_to_bin_typeof_bitvec_of_width_numeral_and_ne_stuck
    (w : native_Int) (n : Term)
    (hNe : __eo_to_bin (Term.Numeral w) n ≠ Term.Stuck) :
    __eo_typeof (__eo_to_bin (Term.Numeral w) n) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  cases n <;> simp [__eo_to_bin] at hNe ⊢
  case Numeral n =>
    cases hBound : native_zleq w 4294967296 <;>
      cases hWidth : native_zleq 0 w <;>
      simp [__eo_mk_binary, hBound, hWidth, native_ite] at hNe ⊢
    all_goals
      first
      | rfl
      | contradiction
  case Binary wn n =>
    cases hBound : native_zleq w 4294967296 <;>
      cases hWidth : native_zleq 0 w <;>
      simp [__eo_mk_binary, hBound, hWidth, native_ite] at hNe ⊢
    all_goals
      first
      | rfl
      | contradiction

theorem EvaluateProofInternal.eo_ite_to_bin_typeof_bitvec_of_width_numeral_and_ne_stuck
    (c n m : Term) (w : native_Int)
    (hNe :
      __eo_ite c (__eo_to_bin (Term.Numeral w) n)
          (__eo_to_bin (Term.Numeral w) m) ≠ Term.Stuck) :
    __eo_typeof
        (__eo_ite c (__eo_to_bin (Term.Numeral w) n)
          (__eo_to_bin (Term.Numeral w) m)) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
      c (__eo_to_bin (Term.Numeral w) n)
      (__eo_to_bin (Term.Numeral w) m) hNe with
    ⟨b, hCond, hSel⟩
  cases b
  · rw [hCond]
    have hsimpa :=
      EvaluateProofInternal.eo_to_bin_typeof_bitvec_of_width_numeral_and_ne_stuck w m hSel
    try simp [__eo_ite] at hsimpa ⊢
    exact hsimpa
  · rw [hCond]
    have hsimpa :=
      EvaluateProofInternal.eo_to_bin_typeof_bitvec_of_width_numeral_and_ne_stuck w n hSel
    try simp [__eo_ite] at hsimpa ⊢
    exact hsimpa

theorem EvaluateProofInternal.eo_typeof_bvult_bool_of_smt_bitvec_args
    (x y : Term) (w : native_Nat)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hYTy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w) :
    __eo_typeof_bvult (__eo_typeof x) (__eo_typeof y) = Term.Bool := by
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hXTy]
    simp
  have hYTrans : RuleProofs.eo_has_smt_translation y := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hYTy]
    simp
  have hXMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
  have hYMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation y hYTrans
  have hXEoBv :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec
      (hXMatch.symm.trans hXTy)
  have hYEoBv :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec
      (hYMatch.symm.trans hYTy)
  rw [hXEoBv, hYEoBv]
  simp [__eo_typeof_bvult, __eo_requires, __eo_eq, native_ite,
    native_teq, native_not]

theorem EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec
    (x : Term) (w : native_Nat)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_typeof x =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)) := by
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hXTy]
    simp
  have hXMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans
  exact TranslationProofs.eo_to_smt_type_eq_bitvec
    (hXMatch.symm.trans hXTy)

theorem EvaluateProofInternal.eo_typeof_bvand_bitvec_of_smt_bitvec_args
    (x y : Term) (w : native_Nat)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hYTy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w) :
    __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)) := by
  have hXEoBv := EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec x w hXTy
  have hYEoBv := EvaluateProofInternal.eo_typeof_eq_bitvec_of_smt_bitvec y w hYTy
  rw [hXEoBv, hYEoBv]
  simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
    native_teq, native_not]

theorem EvaluateProofInternal.eo_repeat_typeof_bitvec_of_arg_bitvec_and_ne_stuck
    (x : Term) (i w : native_Int)
    (hi1 : native_zleq 1 i = true)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hNe :
      __bv_eval_concat
          (__eo_list_repeat (Term.UOp UserOp.concat) x
            (Term.Numeral i)) ≠ Term.Stuck) :
    __eo_typeof
        (__bv_eval_concat
          (__eo_list_repeat (Term.UOp UserOp.concat) x
            (Term.Numeral i))) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_zmult i w)) := by
  have hi : (1 : Int) <= i := by
    simpa [native_zleq, SmtEval.native_zleq] using hi1
  have hi0Int : (0 : Int) <= i := by
    omega
  have hiNotNeg : native_zlt i 0 = false := by
    simp [native_zlt, SmtEval.native_zlt]
    omega
  have hIntNat :
      native_nat_to_int (native_int_to_nat i) = i := by
    simpa [native_nat_to_int, native_int_to_nat,
      Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
      Int.toNat_of_nonneg hi0Int]
  have hNatNeZero : native_int_to_nat i ≠ 0 := by
    intro hZero
    have hIeq0 : i = 0 := by
      calc
        i = native_nat_to_int (native_int_to_nat i) := hIntNat.symm
        _ = native_nat_to_int 0 := by rw [hZero]
        _ = 0 := by simp [native_nat_to_int, Smtm.native_nat_to_int]
    have hBad : (1 : Int) <= 0 := by
      simpa [hIeq0] using hi
    exact (by decide : ¬ (1 : Int) <= 0) hBad
  by_cases hBinary :
      ∃ wx : native_Int, ∃ nx : native_Int, x = Term.Binary wx nx
  · rcases hBinary with ⟨wx, nx, rfl⟩
    change
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at hX
    cases hX
    have hList :
        __eo_list_repeat (Term.UOp UserOp.concat)
            (Term.Binary w nx) (Term.Numeral i) =
          __eo_list_repeat_rec (Term.UOp UserOp.concat)
            (Term.Binary w nx) (native_int_to_nat i) := by
      simp [__eo_list_repeat, native_ite, hiNotNeg]
    cases hWxNonneg : native_zleq 0 w
    · have hStuck :=
        EvaluateProofInternal.bv_eval_concat_list_repeat_rec_binary_stuck_of_neg
          w nx hWxNonneg (native_int_to_nat i) hNatNeZero
      exact False.elim (hNe (by rw [hList, hStuck]))
    · rcases EvaluateProofInternal.bv_eval_concat_list_repeat_rec_binary
        w nx hWxNonneg (native_int_to_nat i) with
        ⟨m, hTerm, _hEval, _hCanon⟩
      rw [hList, hTerm]
      change
        __eo_typeof
            (Term.Binary
              (native_zmult (native_nat_to_int (native_int_to_nat i)) w)
              m) =
          Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_zmult i w))
      simp [hIntNat]
      rfl
  · have hList (hxNe : x ≠ Term.Stuck) :
        __eo_list_repeat (Term.UOp UserOp.concat) x
            (Term.Numeral i) =
          __eo_list_repeat_rec (Term.UOp UserOp.concat) x
            (native_int_to_nat i) := by
      cases x <;> simp [__eo_list_repeat, native_ite, hiNotNeg]
        at hxNe ⊢
    by_cases hxStuck : x = Term.Stuck
    · subst x
      simp [__eo_list_repeat, __bv_eval_concat] at hNe
    · have hStuck :=
        EvaluateProofInternal.bv_eval_concat_list_repeat_rec_not_binary_stuck x hBinary
          (native_int_to_nat i) hNatNeZero
      exact False.elim (hNe (by rw [hList hxStuck, hStuck]))

theorem EvaluateProofInternal.eo_extract_typeof_bitvec_of_arg_bitvec_and_ne_stuck
    (x : Term) (i j w : native_Int)
    (hj0 : native_zleq 0 j = true)
    (hWidth : native_zlt 0
      (native_zplus (native_zplus i 1) (native_zneg j)) = true)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (hNe :
      __eo_extract x (Term.Numeral j) (Term.Numeral i) ≠
        Term.Stuck) :
    __eo_typeof (__eo_extract x (Term.Numeral j) (Term.Numeral i)) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral
          (native_zplus (native_zplus i (native_zneg j)) 1)) := by
  cases x <;> simp [__eo_extract] at hX hNe ⊢
  case Binary wx nx =>
    change
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at hX
    cases hX
    have hjNonneg : 0 <= j := by
      simpa [native_zleq, SmtEval.native_zleq] using hj0
    have hjNotNeg : native_zlt j 0 = false := by
      simpa [native_zlt, SmtEval.native_zlt] using
        Int.not_lt_of_ge hjNonneg
    have hWidthAssoc :
        native_zplus (native_zplus i 1) (native_zneg j) =
          native_zplus (native_zplus i (native_zneg j)) 1 := by
      simp [native_zplus, SmtEval.native_zplus, native_zneg,
        SmtEval.native_zneg, Int.add_assoc, Int.add_comm,
        Int.add_left_comm]
    have hWidthPosNative :
        native_zlt 0
            (native_zplus (native_zplus i (native_zneg j)) 1) =
          true := by
      simpa [hWidthAssoc] using hWidth
    have hWidthNonnegNative :
        native_zleq 0
            (native_zplus (native_zplus i (native_zneg j)) 1) =
          true := by
      have hPos :
          (0 : native_Int) <
            native_zplus (native_zplus i (native_zneg j)) 1 := by
        simpa [native_zlt, SmtEval.native_zlt] using hWidthPosNative
      simpa [native_zleq, SmtEval.native_zleq] using Int.le_of_lt hPos
    cases hDeltaNeg :
        native_zlt (native_zplus i (native_zneg j)) 0
    · have hDeltaNotLt : ¬ i + -j < 0 := by
        have hsimpa := hDeltaNeg
        try simp [native_zlt, SmtEval.native_zlt, native_zplus, SmtEval.native_zplus, native_zneg, SmtEval.native_zneg] at hsimpa ⊢
        exact Int.not_lt.mp (of_decide_eq_false hsimpa)
      have hDeltaNonneg : 0 <= i + -j :=
        Int.le_of_not_gt hDeltaNotLt
      have hWidthNonneg :
          native_zleq 0
              (native_zplus (native_zplus i (native_zneg j)) 1) =
            true := by
        have hNonneg : 0 <= i + -j + 1 :=
          Int.add_nonneg hDeltaNonneg (by decide)
        simpa [native_zleq, SmtEval.native_zleq, native_zplus,
          SmtEval.native_zplus, native_zneg, SmtEval.native_zneg,
          Int.add_assoc] using hNonneg
      simp [hjNotNeg, hDeltaNeg, native_or, native_ite, __eo_mk_binary,
        hWidthNonneg]
      rfl
    · have hDeltaLt : i + -j < 0 := by
        have hsimpa := hDeltaNeg
        try simp [native_zlt, SmtEval.native_zlt, native_zplus, SmtEval.native_zplus, native_zneg, SmtEval.native_zneg] at hsimpa ⊢
        exact of_decide_eq_true hsimpa
      have hWidthGe : 0 <= i + -j + 1 := by
        simpa [native_zleq, SmtEval.native_zleq, native_zplus,
          SmtEval.native_zplus, native_zneg, SmtEval.native_zneg,
          Int.add_assoc] using hWidthNonnegNative
      have hWidthZeroInt : i + -j + 1 = 0 :=
        Int.le_antisymm (Int.add_one_le_iff.mpr hDeltaLt) hWidthGe
      have hWidthZero :
          native_zplus (native_zplus i (native_zneg j)) 1 = 0 := by
        simpa [native_zplus, SmtEval.native_zplus, native_zneg,
          SmtEval.native_zneg, Int.add_assoc] using hWidthZeroInt
      simp [hjNotNeg, hDeltaNeg, native_or, native_ite,
        __eo_lit_type_Binary, __eo_len, __eo_mk_apply, hWidthZero]
      rfl
  all_goals
    first
    | contradiction
    | cases hX

theorem EvaluateProofInternal.eo_concat_typeof_seq_of_args_seq_and_ne_stuck
    (x y U : Term)
    (hX :
      __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) U)
    (hY :
      __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) U)
    (hNe : __eo_concat x y ≠ Term.Stuck) :
    __eo_typeof (__eo_concat x y) =
      Term.Apply (Term.UOp UserOp.Seq) U := by
  cases x <;> cases y <;> simp [__eo_concat] at hX hY hNe ⊢
  all_goals
    first
    -- `__eo_typeof (Term.String _)` is `Seq Char` for any string, but the
    -- concatenated literal no longer matches `hX`/`hY` syntactically.  This
    -- must come first: `cases hX` succeeds without closing the goal.
    | rfl
    | simpa using hX
    | cases hX
    | cases hY
    | contradiction
  -- `cases hX` substitutes `U` but does not close the goal; once `U` is
  -- concrete the literal's type is `rfl`
  all_goals rfl

theorem EvaluateProofInternal.eo_extract_typeof_seq_of_target_seq_and_ne_stuck
    (x i j U : Term)
    (hX :
      __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) U)
    (hNe : __eo_extract x i j ≠ Term.Stuck) :
    __eo_typeof (__eo_extract x i j) =
      Term.Apply (Term.UOp UserOp.Seq) U := by
  cases x <;> cases i <;> cases j <;>
    simp [__eo_extract] at hX hNe ⊢
  all_goals
    first
    | rfl
    | simpa using hX
    | cases hX
    | contradiction
  all_goals rfl

theorem EvaluateProofInternal.eo_not_is_neg_find_typeof_bool_of_ne_stuck
    (x y : Term)
    (hNe : __eo_not (__eo_is_neg (__eo_find x y)) ≠ Term.Stuck) :
    __eo_typeof (__eo_not (__eo_is_neg (__eo_find x y))) =
      Term.Bool := by
  cases x <;> cases y <;>
    simp [__eo_find, __eo_is_neg, __eo_not] at hNe ⊢

theorem EvaluateProofInternal.eo_find_typeof_int_of_ne_stuck
    (x y : Term)
    (hNe : __eo_find x y ≠ Term.Stuck) :
    __eo_typeof (__eo_find x y) = Term.UOp UserOp.Int := by
  cases x <;> cases y <;>
    simp [__eo_find] at hNe ⊢
  case String.String =>
    rfl

theorem EvaluateProofInternal.eo_seq_type_eq_of_same_smt_elem
    {U V : Term} {T : SmtType}
    (hValid :
      TranslationProofs.eo_type_valid (Term.Apply (Term.UOp UserOp.Seq) U))
    (hU : __eo_to_smt_type U = T)
    (hV : __eo_to_smt_type V = T) :
    Term.Apply (Term.UOp UserOp.Seq) U =
      Term.Apply (Term.UOp UserOp.Seq) V := by
  apply EvaluateProofInternal.eo_to_smt_type_eq_of_top_valid hValid
  simp [__eo_to_smt_type, hU, hV]

theorem EvaluateProofInternal.eo_str_replace_body_source_ne_stuck_of_ne_stuck
    (s pat repl : Term)
    (hNe :
      (let idx := __eo_find (__eo_to_str s) (__eo_to_str pat)
       __eo_ite (__eo_is_neg idx) s
        (__eo_concat
          (__eo_concat
            (__eo_extract s (Term.Numeral 0)
              (__eo_add idx (Term.Numeral (-1 : native_Int))))
            repl)
          (__eo_extract s (__eo_add idx (__eo_len pat)) (__eo_len s)))) ≠
        Term.Stuck) :
    s ≠ Term.Stuck := by
  let idx := __eo_find (__eo_to_str s) (__eo_to_str pat)
  let left :=
    __eo_extract s (Term.Numeral 0)
      (__eo_add idx (Term.Numeral (-1 : native_Int)))
  let inner := __eo_concat left repl
  let right := __eo_extract s (__eo_add idx (__eo_len pat)) (__eo_len s)
  let body := __eo_ite (__eo_is_neg idx) s (__eo_concat inner right)
  change body ≠ Term.Stuck at hNe
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
      (__eo_is_neg idx) s (__eo_concat inner right) hNe with
    ⟨selected, _hCond, hSelectedNe⟩
  cases selected
  · have hTailNe : __eo_concat inner right ≠ Term.Stuck := by
      simpa using hSelectedNe
    have hInnerNe : inner ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_left_ne_stuck (by simpa [inner, right] using hTailNe)
    have hLeftNe : left ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_left_ne_stuck (by simpa [left, inner] using hInnerNe)
    exact EvaluateProofInternal.eo_extract_target_ne_stuck (by simpa [left] using hLeftNe)
  · simpa using hSelectedNe

theorem EvaluateProofInternal.eo_str_replace_body_typeof_seq_of_args_seq_and_ne_stuck
    (s pat repl U : Term)
    (hS : __eo_typeof s = Term.Apply (Term.UOp UserOp.Seq) U)
    (hRepl :
      repl ≠ Term.Stuck ->
        __eo_typeof repl = Term.Apply (Term.UOp UserOp.Seq) U)
    (hNe :
      (let idx := __eo_find (__eo_to_str s) (__eo_to_str pat)
       __eo_ite (__eo_is_neg idx) s
        (__eo_concat
          (__eo_concat
            (__eo_extract s (Term.Numeral 0)
              (__eo_add idx (Term.Numeral (-1 : native_Int))))
            repl)
          (__eo_extract s (__eo_add idx (__eo_len pat)) (__eo_len s)))) ≠
        Term.Stuck) :
    __eo_typeof
      (let idx := __eo_find (__eo_to_str s) (__eo_to_str pat)
       __eo_ite (__eo_is_neg idx) s
        (__eo_concat
          (__eo_concat
            (__eo_extract s (Term.Numeral 0)
              (__eo_add idx (Term.Numeral (-1 : native_Int))))
            repl)
          (__eo_extract s (__eo_add idx (__eo_len pat)) (__eo_len s)))) =
      Term.Apply (Term.UOp UserOp.Seq) U := by
  let idx := __eo_find (__eo_to_str s) (__eo_to_str pat)
  let left :=
    __eo_extract s (Term.Numeral 0)
      (__eo_add idx (Term.Numeral (-1 : native_Int)))
  let inner := __eo_concat left repl
  let right := __eo_extract s (__eo_add idx (__eo_len pat)) (__eo_len s)
  let body := __eo_ite (__eo_is_neg idx) s (__eo_concat inner right)
  have hSeqNe :
      Term.Apply (Term.UOp UserOp.Seq) U ≠ Term.Stuck := by
    intro h
    cases h
  change __eo_typeof body = Term.Apply (Term.UOp UserOp.Seq) U
  change body ≠ Term.Stuck at hNe
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
      (__eo_is_neg idx) s (__eo_concat inner right) hNe with
    ⟨selected, hCond, hSelectedNe⟩
  cases selected
  · dsimp [body]
    rw [hCond]
    change __eo_typeof (__eo_concat inner right) =
      Term.Apply (Term.UOp UserOp.Seq) U
    have hTailNe : __eo_concat inner right ≠ Term.Stuck := by
      simpa using hSelectedNe
    have hInnerNe : inner ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_left_ne_stuck (by simpa [inner, right] using hTailNe)
    have hLeftNe : left ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_left_ne_stuck (by simpa [left, inner] using hInnerNe)
    have hReplNe : repl ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_right_ne_stuck (by simpa [left, inner] using hInnerNe)
    have hRightNe : right ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_right_ne_stuck (by simpa [inner, right] using hTailNe)
    have hLeftTy :
        __eo_typeof left = Term.Apply (Term.UOp UserOp.Seq) U :=
      EvaluateProofInternal.eo_extract_typeof_seq_of_target_seq_and_ne_stuck
        s (Term.Numeral 0)
        (__eo_add idx (Term.Numeral (-1 : native_Int))) U hS
        (by simpa [left] using hLeftNe)
    have hInnerTy :
        __eo_typeof inner = Term.Apply (Term.UOp UserOp.Seq) U :=
      EvaluateProofInternal.eo_concat_typeof_seq_of_args_seq_and_ne_stuck
        left repl U hLeftTy (hRepl hReplNe) hInnerNe
    have hRightTy :
        __eo_typeof right = Term.Apply (Term.UOp UserOp.Seq) U :=
      EvaluateProofInternal.eo_extract_typeof_seq_of_target_seq_and_ne_stuck
        s (__eo_add idx (__eo_len pat)) (__eo_len s) U hS
        (by simpa [right] using hRightNe)
    exact
      EvaluateProofInternal.eo_concat_typeof_seq_of_args_seq_and_ne_stuck
        inner right U hInnerTy hRightTy hTailNe
  · dsimp [body]
    rw [hCond]
    change __eo_typeof s = Term.Apply (Term.UOp UserOp.Seq) U
    exact hS

theorem EvaluateProofInternal.eo_str_indexof_body_typeof_int_of_start_int_and_ne_stuck
    (s pat start runStart : Term)
    (hStart : __eo_typeof start = Term.UOp UserOp.Int)
    (hNe :
      (let lenS := __eo_len s
       let find :=
        __eo_find (__eo_to_str (__eo_extract s start lenS))
          (__eo_to_str pat)
       __eo_ite (__eo_is_neg runStart) (Term.Numeral (-1 : native_Int))
        (__eo_ite (__eo_gt runStart lenS) (Term.Numeral (-1 : native_Int))
          (__eo_ite (__eo_is_neg find) find (__eo_add start find)))) ≠
        Term.Stuck) :
    __eo_typeof
      (let lenS := __eo_len s
       let find :=
        __eo_find (__eo_to_str (__eo_extract s start lenS))
          (__eo_to_str pat)
       __eo_ite (__eo_is_neg runStart) (Term.Numeral (-1 : native_Int))
        (__eo_ite (__eo_gt runStart lenS) (Term.Numeral (-1 : native_Int))
          (__eo_ite (__eo_is_neg find) find (__eo_add start find)))) =
      Term.UOp UserOp.Int := by
  let lenS := __eo_len s
  let find :=
    __eo_find (__eo_to_str (__eo_extract s start lenS)) (__eo_to_str pat)
  let inner := __eo_ite (__eo_is_neg find) find (__eo_add start find)
  let rest :=
    __eo_ite (__eo_gt runStart lenS) (Term.Numeral (-1 : native_Int))
      inner
  let body :=
    __eo_ite (__eo_is_neg runStart) (Term.Numeral (-1 : native_Int))
      rest
  change __eo_typeof body = Term.UOp UserOp.Int
  change body ≠ Term.Stuck at hNe
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
      (__eo_is_neg runStart) (Term.Numeral (-1 : native_Int)) rest hNe with
    ⟨topSelected, hTopCond, hTopSelectedNe⟩
  cases topSelected
  · dsimp [body]
    rw [hTopCond]
    change __eo_typeof rest = Term.UOp UserOp.Int
    have hRestNe : rest ≠ Term.Stuck := by
      simpa using hTopSelectedNe
    change
      __eo_ite (__eo_gt runStart lenS) (Term.Numeral (-1 : native_Int))
        inner ≠ Term.Stuck at hRestNe
    rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
        (__eo_gt runStart lenS) (Term.Numeral (-1 : native_Int)) inner
        hRestNe with
      ⟨gtSelected, hGtCond, hGtSelectedNe⟩
    cases gtSelected
    · dsimp [rest]
      rw [hGtCond]
      change __eo_typeof inner = Term.UOp UserOp.Int
      have hInnerNe : inner ≠ Term.Stuck := by
        simpa using hGtSelectedNe
      change __eo_ite (__eo_is_neg find) find (__eo_add start find) ≠
        Term.Stuck at hInnerNe
      rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
          (__eo_is_neg find) find (__eo_add start find) hInnerNe with
        ⟨findSelected, hFindCond, hFindSelectedNe⟩
      cases findSelected
      · dsimp [inner]
        rw [hFindCond]
        change __eo_typeof (__eo_add start find) = Term.UOp UserOp.Int
        have hAddNe : __eo_add start find ≠ Term.Stuck := by
          simpa using hFindSelectedNe
        have hFindNegNe : __eo_is_neg find ≠ Term.Stuck := by
          rw [hFindCond]
          simp
        have hFindNe : find ≠ Term.Stuck :=
          EvaluateProofInternal.eo_is_neg_arg_ne_stuck hFindNegNe
        have hFindTy : __eo_typeof find = Term.UOp UserOp.Int :=
          EvaluateProofInternal.eo_find_typeof_int_of_ne_stuck
            (__eo_to_str (__eo_extract s start lenS)) (__eo_to_str pat)
            (by simpa [find] using hFindNe)
        exact EvaluateProofInternal.eo_add_typeof_int_of_args_int start find hStart hFindTy hAddNe
      · dsimp [inner]
        rw [hFindCond]
        change __eo_typeof find = Term.UOp UserOp.Int
        have hFindNe : find ≠ Term.Stuck := by
          simpa using hFindSelectedNe
        exact
          EvaluateProofInternal.eo_find_typeof_int_of_ne_stuck
            (__eo_to_str (__eo_extract s start lenS)) (__eo_to_str pat)
            (by simpa [find] using hFindNe)
    · dsimp [rest]
      rw [hGtCond]
      change __eo_typeof (Term.Numeral (-1 : native_Int)) =
        Term.UOp UserOp.Int
      rfl
  · dsimp [body]
    rw [hTopCond]
    change __eo_typeof (Term.Numeral (-1 : native_Int)) =
      Term.UOp UserOp.Int
    rfl

theorem EvaluateProofInternal.eo_str_update_body_source_ne_stuck_of_ne_stuck
    (s n repl : Term)
    (hNe :
      (let lenS := __eo_len s
       __eo_ite (__eo_or (__eo_gt (Term.Numeral 0) n) (__eo_gt n lenS)) s
        (__eo_concat
          (__eo_concat
            (__eo_extract s (Term.Numeral 0)
              (__eo_add n (Term.Numeral (-1 : native_Int))))
            (__eo_extract repl (Term.Numeral 0)
              (__eo_add (__eo_add (__eo_neg n) lenS)
                (Term.Numeral (-1 : native_Int)))))
          (__eo_extract s (__eo_add n (__eo_len repl)) lenS))) ≠
        Term.Stuck) :
    s ≠ Term.Stuck := by
  let lenS := __eo_len s
  let left :=
    __eo_extract s (Term.Numeral 0)
      (__eo_add n (Term.Numeral (-1 : native_Int)))
  let middle :=
    __eo_extract repl (Term.Numeral 0)
      (__eo_add (__eo_add (__eo_neg n) lenS)
        (Term.Numeral (-1 : native_Int)))
  let inner := __eo_concat left middle
  let right := __eo_extract s (__eo_add n (__eo_len repl)) lenS
  let body :=
    __eo_ite (__eo_or (__eo_gt (Term.Numeral 0) n) (__eo_gt n lenS)) s
      (__eo_concat inner right)
  change body ≠ Term.Stuck at hNe
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
      (__eo_or (__eo_gt (Term.Numeral 0) n) (__eo_gt n lenS)) s
      (__eo_concat inner right) hNe with
    ⟨selected, _hCond, hSelectedNe⟩
  cases selected
  · have hTailNe : __eo_concat inner right ≠ Term.Stuck := by
      simpa using hSelectedNe
    have hInnerNe : inner ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_left_ne_stuck (by simpa [inner, right] using hTailNe)
    have hLeftNe : left ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_left_ne_stuck (by simpa [left, inner] using hInnerNe)
    exact EvaluateProofInternal.eo_extract_target_ne_stuck (by simpa [left] using hLeftNe)
  · simpa using hSelectedNe

theorem EvaluateProofInternal.eo_str_update_body_typeof_seq_of_args_seq_and_ne_stuck
    (s n repl U : Term)
    (hS : __eo_typeof s = Term.Apply (Term.UOp UserOp.Seq) U)
    (hRepl :
      repl ≠ Term.Stuck ->
        __eo_typeof repl = Term.Apply (Term.UOp UserOp.Seq) U)
    (hNe :
      (let lenS := __eo_len s
       __eo_ite (__eo_or (__eo_gt (Term.Numeral 0) n) (__eo_gt n lenS)) s
        (__eo_concat
          (__eo_concat
            (__eo_extract s (Term.Numeral 0)
              (__eo_add n (Term.Numeral (-1 : native_Int))))
            (__eo_extract repl (Term.Numeral 0)
              (__eo_add (__eo_add (__eo_neg n) lenS)
                (Term.Numeral (-1 : native_Int)))))
          (__eo_extract s (__eo_add n (__eo_len repl)) lenS))) ≠
        Term.Stuck) :
    __eo_typeof
      (let lenS := __eo_len s
       __eo_ite (__eo_or (__eo_gt (Term.Numeral 0) n) (__eo_gt n lenS)) s
        (__eo_concat
          (__eo_concat
            (__eo_extract s (Term.Numeral 0)
              (__eo_add n (Term.Numeral (-1 : native_Int))))
            (__eo_extract repl (Term.Numeral 0)
              (__eo_add (__eo_add (__eo_neg n) lenS)
                (Term.Numeral (-1 : native_Int)))))
          (__eo_extract s (__eo_add n (__eo_len repl)) lenS))) =
      Term.Apply (Term.UOp UserOp.Seq) U := by
  let lenS := __eo_len s
  let left :=
    __eo_extract s (Term.Numeral 0)
      (__eo_add n (Term.Numeral (-1 : native_Int)))
  let middle :=
    __eo_extract repl (Term.Numeral 0)
      (__eo_add (__eo_add (__eo_neg n) lenS)
        (Term.Numeral (-1 : native_Int)))
  let inner := __eo_concat left middle
  let right := __eo_extract s (__eo_add n (__eo_len repl)) lenS
  let body :=
    __eo_ite (__eo_or (__eo_gt (Term.Numeral 0) n) (__eo_gt n lenS)) s
      (__eo_concat inner right)
  change __eo_typeof body = Term.Apply (Term.UOp UserOp.Seq) U
  change body ≠ Term.Stuck at hNe
  rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
      (__eo_or (__eo_gt (Term.Numeral 0) n) (__eo_gt n lenS)) s
      (__eo_concat inner right) hNe with
    ⟨selected, hCond, hSelectedNe⟩
  cases selected
  · dsimp [body]
    rw [hCond]
    change __eo_typeof (__eo_concat inner right) =
      Term.Apply (Term.UOp UserOp.Seq) U
    have hTailNe : __eo_concat inner right ≠ Term.Stuck := by
      simpa using hSelectedNe
    have hInnerNe : inner ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_left_ne_stuck (by simpa [inner, right] using hTailNe)
    have hLeftNe : left ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_left_ne_stuck (by simpa [left, inner] using hInnerNe)
    have hMiddleNe : middle ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_right_ne_stuck (by simpa [left, inner] using hInnerNe)
    have hReplNe : repl ≠ Term.Stuck :=
      EvaluateProofInternal.eo_extract_target_ne_stuck (by simpa [middle] using hMiddleNe)
    have hRightNe : right ≠ Term.Stuck :=
      EvaluateProofInternal.eo_concat_right_ne_stuck (by simpa [inner, right] using hTailNe)
    have hLeftTy :
        __eo_typeof left = Term.Apply (Term.UOp UserOp.Seq) U :=
      EvaluateProofInternal.eo_extract_typeof_seq_of_target_seq_and_ne_stuck
        s (Term.Numeral 0) (__eo_add n (Term.Numeral (-1 : native_Int)))
        U hS (by simpa [left] using hLeftNe)
    have hMiddleTy :
        __eo_typeof middle = Term.Apply (Term.UOp UserOp.Seq) U :=
      EvaluateProofInternal.eo_extract_typeof_seq_of_target_seq_and_ne_stuck
        repl (Term.Numeral 0)
        (__eo_add (__eo_add (__eo_neg n) lenS)
          (Term.Numeral (-1 : native_Int)))
        U (hRepl hReplNe) (by simpa [middle] using hMiddleNe)
    have hInnerTy :
        __eo_typeof inner = Term.Apply (Term.UOp UserOp.Seq) U :=
      EvaluateProofInternal.eo_concat_typeof_seq_of_args_seq_and_ne_stuck
        left middle U hLeftTy hMiddleTy hInnerNe
    have hRightTy :
        __eo_typeof right = Term.Apply (Term.UOp UserOp.Seq) U :=
      EvaluateProofInternal.eo_extract_typeof_seq_of_target_seq_and_ne_stuck
        s (__eo_add n (__eo_len repl)) lenS U hS
        (by simpa [right] using hRightNe)
    exact
      EvaluateProofInternal.eo_concat_typeof_seq_of_args_seq_and_ne_stuck
        inner right U hInnerTy hRightTy hTailNe
  · dsimp [body]
    rw [hCond]
    change __eo_typeof s = Term.Apply (Term.UOp UserOp.Seq) U
    exact hS

theorem EvaluateProofInternal.str_leq_eval_rec_typeof_bool_of_ne_stuck :
    ∀ x y : Term,
      __str_leq_eval_rec x y ≠ Term.Stuck ->
        __eo_typeof (__str_leq_eval_rec x y) = Term.Bool
  | Term.Stuck, _, hNe => by
      exact False.elim (hNe rfl)
  | x, Term.Stuck, hNe => by
      cases x <;> simp [__str_leq_eval_rec] at hNe
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2,
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t1) t2,
      hNe => by
      change
        __eo_typeof
            (__eo_ite (__eo_eq s1 t1)
              (__str_leq_eval_rec s2 t2)
              (__eo_gt (__eo_to_z t1) (__eo_to_z s1))) =
          Term.Bool
      rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
          (__eo_eq s1 t1) (__str_leq_eval_rec s2 t2)
          (__eo_gt (__eo_to_z t1) (__eo_to_z s1)) hNe with
        ⟨b, hCond, hSel⟩
      cases b
      · rw [hCond]
        change __eo_gt (__eo_to_z t1) (__eo_to_z s1) ≠ Term.Stuck
          at hSel
        have hsimpa :=
          EvaluateProofInternal.eo_gt_typeof_bool_of_ne_stuck
            (__eo_to_z t1) (__eo_to_z s1) hSel
        try simp [__eo_ite] at hsimpa ⊢
        exact hsimpa
      · rw [hCond]
        change __str_leq_eval_rec s2 t2 ≠ Term.Stuck at hSel
        have hsimpa :=
          EvaluateProofInternal.str_leq_eval_rec_typeof_bool_of_ne_stuck s2 t2 hSel
        try simp [__eo_ite] at hsimpa ⊢
        exact hsimpa
  | Term.String s, y, hNe => by
      cases s <;> cases y <;>
        simp [__str_leq_eval_rec] at hNe ⊢ <;> rfl
  | x, y, hNe => by
      cases x
      case String s =>
        cases s <;> cases y <;>
          simp [__str_leq_eval_rec] at hNe ⊢ <;> rfl
      case Apply f a =>
        cases y <;> simp [__str_leq_eval_rec] at hNe ⊢ <;> try rfl
        rename_i g b
        cases f <;> cases g <;>
          try (simp [__str_leq_eval_rec] at hNe ⊢ <;> rfl)
        rename_i f1 s1 g1 t1
        cases f1 <;> cases g1 <;>
          try (simp [__str_leq_eval_rec] at hNe ⊢ <;> rfl)
        rename_i op1 op2
        by_cases hOp1 : op1 = UserOp.str_concat
        · subst op1
          by_cases hOp2 : op2 = UserOp.str_concat
          · subst op2
            change
              __eo_typeof
                  (__eo_ite (__eo_eq s1 t1)
                    (__str_leq_eval_rec a b)
                    (__eo_gt (__eo_to_z t1) (__eo_to_z s1))) =
                Term.Bool
            rcases EvaluateProofInternal.eo_ite_selected_nonstuck_of_nonstuck
                (__eo_eq s1 t1) (__str_leq_eval_rec a b)
                (__eo_gt (__eo_to_z t1) (__eo_to_z s1)) hNe with
              ⟨b', hCond, hSel⟩
            cases b'
            · rw [hCond]
              change __eo_gt (__eo_to_z t1) (__eo_to_z s1) ≠ Term.Stuck
                at hSel
              have hsimpa :=
                EvaluateProofInternal.eo_gt_typeof_bool_of_ne_stuck
                  (__eo_to_z t1) (__eo_to_z s1) hSel
              try simp [__eo_ite] at hsimpa ⊢
              exact hsimpa
            · rw [hCond]
              change __str_leq_eval_rec a b ≠ Term.Stuck at hSel
              have hsimpa :=
                EvaluateProofInternal.str_leq_eval_rec_typeof_bool_of_ne_stuck a b hSel
              try simp [__eo_ite] at hsimpa ⊢
              exact hsimpa
          · simp [__str_leq_eval_rec, hOp2] at hNe ⊢ <;> try rfl
        · simp [__str_leq_eval_rec, hOp1] at hNe ⊢ <;> try rfl
      all_goals
        cases y <;> simp [__str_leq_eval_rec] at hNe ⊢ <;> try rfl

theorem EvaluateProofInternal.eo_str_leq_body_typeof_bool_of_seq_char_args_and_ne_stuck
    (x y : Term)
    (hX :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hY :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hNe :
      __eo_ite (__eo_and (__eo_is_str x) (__eo_is_str y))
          (__str_leq_eval_rec (__str_flatten (__str_nary_intro x))
            (__str_flatten (__str_nary_intro y)))
          (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_leq) x)
            y) ≠ Term.Stuck) :
    __eo_typeof
        (__eo_ite (__eo_and (__eo_is_str x) (__eo_is_str y))
          (__str_leq_eval_rec (__str_flatten (__str_nary_intro x))
            (__str_flatten (__str_nary_intro y)))
          (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_leq) x)
            y)) = Term.Bool := by
  have hFallback :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) x) y) =
        Term.Bool := by
    change __eo_typeof_str_lt (__eo_typeof x) (__eo_typeof y) = Term.Bool
    rw [hX, hY]
    rfl
  cases x <;> cases y <;>
    simp [__eo_is_str, __eo_is_str_internal, __eo_and, __eo_ite,
      __eo_mk_apply, __eo_typeof_str_lt, native_and, native_not,
      native_ite, native_teq] at hX hY hNe hFallback ⊢
  case String.String sx sy =>
    exact EvaluateProofInternal.str_leq_eval_rec_typeof_bool_of_ne_stuck
      (__str_flatten (__str_nary_intro (Term.String sx)))
      (__str_flatten (__str_nary_intro (Term.String sy))) hNe
  all_goals
    first
    | exact hFallback
    | rfl
    | contradiction
    | cases hX
    | cases hY
