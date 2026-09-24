module

public import Cpc.Proofs.RuleSupport.StrConcatClashSupport
import all Cpc.Proofs.RuleSupport.StrConcatClashSupport

public section

open Eo
open SmtEval
open Smtm
open StrConcatClashSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StrConcatUnifySupport

abbrev strConcatUnifyTail (x y : Term) : Term :=
  mkConcat x y

abbrev strConcatUnifyLeftEq
    (pfx s2 s3 t1 t2 : Term) : Term :=
  mkEq (mkConcat pfx (strConcatUnifyTail s2 s3))
    (mkConcat pfx (strConcatUnifyTail t1 t2))

abbrev strConcatUnifyRightEq (s2 s3 t1 t2 : Term) : Term :=
  mkEq (__str_nary_elim (strConcatUnifyTail s2 s3))
    (__str_nary_elim (strConcatUnifyTail t1 t2))

abbrev strConcatUnifyConclusion
    (pfx s2 s3 t1 t2 : Term) : Term :=
  mkEq (strConcatUnifyLeftEq pfx s2 s3 t1 t2)
    (strConcatUnifyRightEq s2 s3 t1 t2)

theorem eo_typeof_eq_bool_of_ne_stuck (A B : Term)
    (h : __eo_typeof_eq A B ≠ Term.Stuck) :
    __eo_typeof_eq A B = Term.Bool := by
  cases A <;> cases B <;>
    simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
      native_not] at h ⊢
  all_goals assumption

theorem eo_typeof_str_concat_result_of_args
    (a b U : Term)
    (haTy : __eo_typeof a = Term.Apply Term.Seq U)
    (hbTy : __eo_typeof b = Term.Apply Term.Seq U)
    (hUNe : U ≠ Term.Stuck) :
    __eo_typeof (mkConcat a b) = Term.Apply Term.Seq U := by
  change __eo_typeof_str_concat (__eo_typeof a) (__eo_typeof b) = _
  simp [haTy, hbTy, __eo_typeof_str_concat, __eo_requires, __eo_eq,
    native_ite, native_teq, SmtEval.native_not, hUNe]

theorem eo_typeof_str_concat_args_of_result_seq
    (a b U : Term)
    (hTy : __eo_typeof (mkConcat a b) = Term.Apply Term.Seq U) :
    __eo_typeof a = Term.Apply Term.Seq U ∧
      __eo_typeof b = Term.Apply Term.Seq U := by
  have hNe :
      __eo_typeof_str_concat (__eo_typeof a) (__eo_typeof b) ≠
        Term.Stuck := by
    change __eo_typeof (mkConcat a b) ≠ Term.Stuck
    rw [hTy]
    intro h
    cases h
  rcases eo_typeof_str_concat_args_of_ne_stuck _ _ hNe with
    ⟨V, haTyV, hbTyV⟩
  have hVNe : V ≠ Term.Stuck := by
    intro hV
    subst V
    simp [haTyV, hbTyV, __eo_typeof_str_concat, __eo_requires, __eo_eq,
      native_ite, native_teq, SmtEval.native_not] at hNe
  have hOutV :
      __eo_typeof (mkConcat a b) = Term.Apply Term.Seq V :=
    eo_typeof_str_concat_result_of_args a b V haTyV hbTyV hVNe
  have hVU : V = U := by
    have hSeq : Term.Apply Term.Seq V = Term.Apply Term.Seq U := by
      rw [← hOutV, hTy]
    injection hSeq
  subst V
  exact ⟨haTyV, hbTyV⟩

theorem str_concat_unify_smt_types_of_eo_type
    (pfx s2 s3 t1 t2 : Term)
    (hPrefixTrans : RuleProofs.eo_has_smt_translation pfx)
    (hS2Trans : RuleProofs.eo_has_smt_translation s2)
    (hS3Trans : RuleProofs.eo_has_smt_translation s3)
    (hT1Trans : RuleProofs.eo_has_smt_translation t1)
    (hT2Trans : RuleProofs.eo_has_smt_translation t2)
    (hTy :
      __eo_typeof (strConcatUnifyConclusion pfx s2 s3 t1 t2) =
        Term.Bool) :
    ∃ T,
      __smtx_typeof (__eo_to_smt pfx) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt s2) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt s3) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt t1) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt t2) = SmtType.Seq T ∧
      __str_nary_elim (strConcatUnifyTail s2 s3) ≠ Term.Stuck ∧
      __str_nary_elim (strConcatUnifyTail t1 t2) ≠ Term.Stuck := by
  let sTail := strConcatUnifyTail s2 s3
  let tTail := strConcatUnifyTail t1 t2
  let leftFull := mkConcat pfx sTail
  let rightFull := mkConcat pfx tTail
  let leftEq := mkEq leftFull rightFull
  let rightEq := mkEq (__str_nary_elim sTail) (__str_nary_elim tTail)
  change __eo_typeof_eq (__eo_typeof leftEq) (__eo_typeof rightEq) =
    Term.Bool at hTy
  have hOuterNe :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy
  have hLeftEqTy : __eo_typeof leftEq = Term.Bool := by
    change __eo_typeof_eq (__eo_typeof leftFull) (__eo_typeof rightFull) =
      Term.Bool
    apply eo_typeof_eq_bool_of_ne_stuck
    exact hOuterNe.1
  have hRightEqTy : __eo_typeof rightEq = Term.Bool := by
    change __eo_typeof_eq
        (__eo_typeof (__str_nary_elim sTail))
        (__eo_typeof (__str_nary_elim tTail)) = Term.Bool
    apply eo_typeof_eq_bool_of_ne_stuck
    exact hOuterNe.2
  change __eo_typeof_eq (__eo_typeof leftFull) (__eo_typeof rightFull) =
    Term.Bool at hLeftEqTy
  have hFullSame :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hLeftEqTy
  have hFullNe :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hLeftEqTy
  have hLeftFullNe := hFullNe.1
  change __eo_typeof_str_concat (__eo_typeof pfx)
      (__eo_typeof sTail) ≠ Term.Stuck at hLeftFullNe
  rcases eo_typeof_str_concat_args_of_ne_stuck _ _ hLeftFullNe with
    ⟨U, hPrefixEoTy, hSTailEoTy⟩
  have hUNe : U ≠ Term.Stuck := by
    intro hU
    subst U
    simp [hPrefixEoTy, hSTailEoTy, __eo_typeof_str_concat,
      __eo_requires, __eo_eq, native_ite, native_teq,
      SmtEval.native_not] at hLeftFullNe
  have hLeftFullTy : __eo_typeof leftFull = Term.Apply Term.Seq U := by
    exact eo_typeof_str_concat_result_of_args pfx sTail U
      hPrefixEoTy hSTailEoTy hUNe
  have hRightFullTy : __eo_typeof rightFull = Term.Apply Term.Seq U := by
    exact hFullSame.symm.trans hLeftFullTy
  have hSArgs := eo_typeof_str_concat_args_of_result_seq s2 s3 U
    (by simpa [sTail] using hSTailEoTy)
  have hRightArgs := eo_typeof_str_concat_args_of_result_seq
    pfx tTail U (by simpa [rightFull] using hRightFullTy)
  have hTArgs := eo_typeof_str_concat_args_of_result_seq t1 t2 U
    (by simpa [tTail] using hRightArgs.2)
  have hPrefixTy := smtx_typeof_seq_of_eo_typeof pfx U
    hPrefixTrans hPrefixEoTy
  have hS2Ty := smtx_typeof_seq_of_eo_typeof s2 U hS2Trans hSArgs.1
  have hS3Ty := smtx_typeof_seq_of_eo_typeof s3 U hS3Trans hSArgs.2
  have hT1Ty := smtx_typeof_seq_of_eo_typeof t1 U hT1Trans hTArgs.1
  have hT2Ty := smtx_typeof_seq_of_eo_typeof t2 U hT2Trans hTArgs.2
  change __eo_typeof_eq
      (__eo_typeof (__str_nary_elim sTail))
      (__eo_typeof (__str_nary_elim tTail)) = Term.Bool at hRightEqTy
  have hElimTyNe :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hRightEqTy
  have hElimSNe : __str_nary_elim sTail ≠ Term.Stuck := by
    intro h
    rw [h] at hElimTyNe
    exact hElimTyNe.1 rfl
  have hElimTNe : __str_nary_elim tTail ≠ Term.Stuck := by
    intro h
    rw [h] at hElimTyNe
    exact hElimTyNe.2 rfl
  exact ⟨__eo_to_smt_type U, hPrefixTy, hS2Ty, hS3Ty,
    hT1Ty, hT2Ty, hElimSNe, hElimTNe⟩

theorem smtx_model_eval_eq_eq_of_rel_iff
    (v1 v2 w1 w2 : SmtValue)
    (hIff : RuleProofs.smt_value_rel v1 v2 ↔
      RuleProofs.smt_value_rel w1 w2) :
    __smtx_model_eval_eq v1 v2 = __smtx_model_eval_eq w1 w2 := by
  by_cases hV : RuleProofs.smt_value_rel v1 v2
  · have hW := hIff.mp hV
    unfold RuleProofs.smt_value_rel at hV hW
    rw [hV, hW]
  · have hW : ¬ RuleProofs.smt_value_rel w1 w2 := by
      intro h
      exact hV (hIff.mpr h)
    rw [smtx_model_eval_eq_false_of_not_rel v1 v2 hV,
      smtx_model_eval_eq_false_of_not_rel w1 w2 hW]

theorem eo_has_bool_type_str_concat_unify
    (pfx s2 s3 t1 t2 : Term) (T : SmtType)
    (hPrefixTy : __smtx_typeof (__eo_to_smt pfx) = SmtType.Seq T)
    (hS2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq T)
    (hS3Ty : __smtx_typeof (__eo_to_smt s3) = SmtType.Seq T)
    (hT1Ty : __smtx_typeof (__eo_to_smt t1) = SmtType.Seq T)
    (hT2Ty : __smtx_typeof (__eo_to_smt t2) = SmtType.Seq T)
    (hElimSNe : __str_nary_elim (strConcatUnifyTail s2 s3) ≠ Term.Stuck)
    (hElimTNe : __str_nary_elim (strConcatUnifyTail t1 t2) ≠ Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (strConcatUnifyConclusion pfx s2 s3 t1 t2) := by
  have hSTailTy :
      __smtx_typeof (__eo_to_smt (strConcatUnifyTail s2 s3)) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq s2 s3 T hS2Ty hS3Ty
  have hTTailTy :
      __smtx_typeof (__eo_to_smt (strConcatUnifyTail t1 t2)) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq t1 t2 T hT1Ty hT2Ty
  have hLeftFullTy :
      __smtx_typeof
          (__eo_to_smt (mkConcat pfx (strConcatUnifyTail s2 s3))) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq pfx (strConcatUnifyTail s2 s3) T
      hPrefixTy hSTailTy
  have hRightFullTy :
      __smtx_typeof
          (__eo_to_smt (mkConcat pfx (strConcatUnifyTail t1 t2))) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq pfx (strConcatUnifyTail t1 t2) T
      hPrefixTy hTTailTy
  have hElimSTy :
      __smtx_typeof
          (__eo_to_smt (__str_nary_elim (strConcatUnifyTail s2 s3))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck
      (strConcatUnifyTail s2 s3) T hSTailTy hElimSNe
  have hElimTTy :
      __smtx_typeof
          (__eo_to_smt (__str_nary_elim (strConcatUnifyTail t1 t2))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck
      (strConcatUnifyTail t1 t2) T hTTailTy hElimTNe
  have hLeftBool : RuleProofs.eo_has_bool_type
      (strConcatUnifyLeftEq pfx s2 s3 t1 t2) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (by rw [hLeftFullTy, hRightFullTy])
      (by rw [hLeftFullTy]; exact seq_ne_none T)
  have hRightBool : RuleProofs.eo_has_bool_type
      (strConcatUnifyRightEq s2 s3 t1 t2) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (by rw [hElimSTy, hElimTTy])
      (by rw [hElimSTy]; exact seq_ne_none T)
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLeftBool.trans hRightBool.symm)
    (by rw [hLeftBool]; decide)

theorem eo_interprets_str_concat_unify
    (M : SmtModel) (hM : model_wf M)
    (pfx s2 s3 t1 t2 : Term) (T : SmtType)
    (hPrefixTy : __smtx_typeof (__eo_to_smt pfx) = SmtType.Seq T)
    (hS2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq T)
    (hS3Ty : __smtx_typeof (__eo_to_smt s3) = SmtType.Seq T)
    (hT1Ty : __smtx_typeof (__eo_to_smt t1) = SmtType.Seq T)
    (hT2Ty : __smtx_typeof (__eo_to_smt t2) = SmtType.Seq T)
    (hElimSNe : __str_nary_elim (strConcatUnifyTail s2 s3) ≠ Term.Stuck)
    (hElimTNe : __str_nary_elim (strConcatUnifyTail t1 t2) ≠ Term.Stuck) :
    eo_interprets M (strConcatUnifyConclusion pfx s2 s3 t1 t2) true := by
  let sTail := strConcatUnifyTail s2 s3
  let tTail := strConcatUnifyTail t1 t2
  have hSTailTy : __smtx_typeof (__eo_to_smt sTail) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq s2 s3 T hS2Ty hS3Ty
  have hTTailTy : __smtx_typeof (__eo_to_smt tTail) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq t1 t2 T hT1Ty hT2Ty
  have hElimSRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim sTail)))
      (__smtx_model_eval M (__eo_to_smt sTail)) :=
    smt_value_rel_str_nary_elim M hM sTail T hSTailTy hElimSNe
  have hElimTRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim tTail)))
      (__smtx_model_eval M (__eo_to_smt tTail)) :=
    smt_value_rel_str_nary_elim M hM tTail T hTTailTy hElimTNe
  have hLeftIff :
      RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt (mkConcat pfx sTail)))
          (__smtx_model_eval M (__eo_to_smt (mkConcat pfx tTail))) ↔
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt sTail))
          (__smtx_model_eval M (__eo_to_smt tTail)) := by
    constructor
    · exact smt_value_rel_str_concat_left_cancel M hM pfx sTail tTail T
        hPrefixTy hSTailTy hTTailTy
    · exact smt_value_rel_str_concat_right_congr M hM pfx sTail tTail T
        hPrefixTy hSTailTy hTTailTy
  have hRightIff :
      RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt (__str_nary_elim sTail)))
          (__smtx_model_eval M (__eo_to_smt (__str_nary_elim tTail))) ↔
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt sTail))
          (__smtx_model_eval M (__eo_to_smt tTail)) := by
    constructor
    · intro h
      exact RuleProofs.smt_value_rel_trans
        (__smtx_model_eval M (__eo_to_smt sTail))
        (__smtx_model_eval M (__eo_to_smt (__str_nary_elim sTail)))
        (__smtx_model_eval M (__eo_to_smt tTail))
        (RuleProofs.smt_value_rel_symm _ _ hElimSRel)
        (RuleProofs.smt_value_rel_trans _ _ _ h hElimTRel)
    · intro h
      exact RuleProofs.smt_value_rel_trans
        (__smtx_model_eval M (__eo_to_smt (__str_nary_elim sTail)))
        (__smtx_model_eval M (__eo_to_smt sTail))
        (__smtx_model_eval M (__eo_to_smt (__str_nary_elim tTail)))
        hElimSRel
        (RuleProofs.smt_value_rel_trans _ _ _ h
          (RuleProofs.smt_value_rel_symm _ _ hElimTRel))
  have hEvalEq :
      __smtx_model_eval M
          (__eo_to_smt (strConcatUnifyLeftEq pfx s2 s3 t1 t2)) =
        __smtx_model_eval M
          (__eo_to_smt (strConcatUnifyRightEq s2 s3 t1 t2)) := by
    change __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt (mkConcat pfx sTail))
          (__eo_to_smt (mkConcat pfx tTail))) =
      __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt (__str_nary_elim sTail))
          (__eo_to_smt (__str_nary_elim tTail)))
    rw [smtx_eval_eq_term_eq, smtx_eval_eq_term_eq]
    exact smtx_model_eval_eq_eq_of_rel_iff _ _ _ _
      (hLeftIff.trans hRightIff.symm)
  have hBool := eo_has_bool_type_str_concat_unify pfx s2 s3 t1 t2 T
    hPrefixTy hS2Ty hS3Ty hT1Ty hT2Ty hElimSNe hElimTNe
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M
        (__eo_to_smt (strConcatUnifyRightEq s2 s3 t1 t2)))

abbrev strConcatUnifyBaseEmpty (A : Term) : Term :=
  __seq_empty (Term.Apply Term.Seq A)

abbrev strConcatUnifyBaseTail (t1 t2 : Term) : Term :=
  mkConcat t1 t2

abbrev strConcatUnifyBaseLeftEq (x t1 t2 : Term) : Term :=
  mkEq x (mkConcat x (strConcatUnifyBaseTail t1 t2))

abbrev strConcatUnifyBaseRightEq
    (t1 t2 A : Term) : Term :=
  mkEq (strConcatUnifyBaseEmpty A)
    (__str_nary_elim (strConcatUnifyBaseTail t1 t2))

abbrev strConcatUnifyBaseConclusion
    (x t1 t2 A : Term) : Term :=
  mkEq (strConcatUnifyBaseLeftEq x t1 t2)
    (strConcatUnifyBaseRightEq t1 t2 A)

theorem eo_typeof_seq_empty_seq_of_ne_stuck
    (A : Term)
    (h : __eo_typeof (strConcatUnifyBaseEmpty A) ≠ Term.Stuck) :
    __eo_typeof (strConcatUnifyBaseEmpty A) = Term.Apply Term.Seq A := by
  by_cases hChar : A = Term.Char
  · subst A
    rfl
  · have hDefault :
        strConcatUnifyBaseEmpty A =
          Term.seq_empty (Term.Apply Term.Seq A) := by
      cases A <;> simp [strConcatUnifyBaseEmpty, __seq_empty] at hChar ⊢
      case UOp op =>
        cases op <;>
          simp [strConcatUnifyBaseEmpty, __seq_empty] at hChar ⊢
    rw [hDefault] at h
    rw [hDefault]
    change
      __eo_typeof_seq_empty
          (__eo_typeof_Seq (__eo_typeof A))
          (Term.Apply Term.Seq A) =
        Term.Apply Term.Seq A
    change
      __eo_typeof_seq_empty
          (__eo_typeof_Seq (__eo_typeof A))
          (Term.Apply Term.Seq A) ≠ Term.Stuck at h
    cases hTy : __eo_typeof A <;>
      simp [__eo_typeof_Seq, __eo_typeof_seq_empty,
        __eo_disamb_type_seq_empty, hTy] at h ⊢

theorem smt_typeof_seq_empty_of_eo_type_wf
    (A : Term) (T : SmtType)
    (hA : __eo_to_smt_type (Term.Apply Term.Seq A) = SmtType.Seq T)
    (hSeqWF : __smtx_type_wf (SmtType.Seq T) = true) :
    __smtx_typeof (__eo_to_smt (strConcatUnifyBaseEmpty A)) =
      SmtType.Seq T := by
  by_cases hSpecial : A = Term.Char
  · subst A
    simp [strConcatUnifyBaseEmpty, __seq_empty,
      __eo_to_smt_type, __smtx_typeof_guard] at hA
    cases hA
    change __smtx_typeof (SmtTerm.String (native_string_lit "")) =
      SmtType.Seq SmtType.Char
    rw [__smtx_typeof.eq_4]
    simp [native_string_lit, native_string_valid, native_ite]
  · have hDefault :
        strConcatUnifyBaseEmpty A =
          Term.seq_empty (Term.Apply Term.Seq A) := by
      cases A <;> simp [strConcatUnifyBaseEmpty, __seq_empty] at hSpecial ⊢
      case UOp op =>
        cases op <;>
          simp [strConcatUnifyBaseEmpty, __seq_empty] at hSpecial ⊢
    rw [hDefault]
    change __smtx_typeof
        (__eo_to_smt_seq_empty
          (__eo_to_smt_type (Term.Apply Term.Seq A))) = SmtType.Seq T
    rw [hA]
    change __smtx_typeof (SmtTerm.seq_empty T) = SmtType.Seq T
    simp [__smtx_typeof, __smtx_typeof_guard_wf, native_ite, hSeqWF]

theorem str_concat_unify_base_smt_types_of_eo_type
    (x t1 t2 A : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hT1Trans : RuleProofs.eo_has_smt_translation t1)
    (hT2Trans : RuleProofs.eo_has_smt_translation t2)
    (hTy : __eo_typeof (strConcatUnifyBaseConclusion x t1 t2 A) =
      Term.Bool) :
    ∃ T,
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt t1) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt t2) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (strConcatUnifyBaseEmpty A)) =
        SmtType.Seq T ∧
      __str_nary_elim (strConcatUnifyBaseTail t1 t2) ≠ Term.Stuck := by
  let tail := strConcatUnifyBaseTail t1 t2
  let empty := strConcatUnifyBaseEmpty A
  let leftEq := strConcatUnifyBaseLeftEq x t1 t2
  let rightEq := strConcatUnifyBaseRightEq t1 t2 A
  change __eo_typeof_eq (__eo_typeof leftEq) (__eo_typeof rightEq) =
    Term.Bool at hTy
  have hOuterNe :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy
  have hLeftEqTy : __eo_typeof leftEq = Term.Bool := by
    change __eo_typeof_eq (__eo_typeof x)
        (__eo_typeof (mkConcat x tail)) = Term.Bool
    apply eo_typeof_eq_bool_of_ne_stuck
    exact hOuterNe.1
  have hRightEqTy : __eo_typeof rightEq = Term.Bool := by
    change __eo_typeof_eq (__eo_typeof empty)
        (__eo_typeof (__str_nary_elim tail)) = Term.Bool
    apply eo_typeof_eq_bool_of_ne_stuck
    exact hOuterNe.2
  change __eo_typeof_eq (__eo_typeof x)
      (__eo_typeof (mkConcat x tail)) = Term.Bool at hLeftEqTy
  have hLeftSame :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hLeftEqTy
  have hLeftNe :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hLeftEqTy
  have hConcatNe := hLeftNe.2
  change __eo_typeof_str_concat (__eo_typeof x) (__eo_typeof tail) ≠
    Term.Stuck at hConcatNe
  rcases eo_typeof_str_concat_args_of_ne_stuck _ _ hConcatNe with
    ⟨U, hXEoTy, hTailEoTy⟩
  have hUNe : U ≠ Term.Stuck := by
    intro hU
    subst U
    simp [hXEoTy, hTailEoTy, __eo_typeof_str_concat, __eo_requires,
      __eo_eq, native_ite, native_teq, SmtEval.native_not] at hConcatNe
  have hTailArgs := eo_typeof_str_concat_args_of_result_seq t1 t2 U
    (by simpa [tail] using hTailEoTy)
  have hXTy := smtx_typeof_seq_of_eo_typeof x U hXTrans hXEoTy
  have hT1Ty := smtx_typeof_seq_of_eo_typeof t1 U hT1Trans hTailArgs.1
  have hT2Ty := smtx_typeof_seq_of_eo_typeof t2 U hT2Trans hTailArgs.2
  let T := __eo_to_smt_type U
  have hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq t1 t2 T hT1Ty hT2Ty
  change __eo_typeof_eq (__eo_typeof empty)
      (__eo_typeof (__str_nary_elim tail)) = Term.Bool at hRightEqTy
  have hRightSame :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hRightEqTy
  have hRightNe :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hRightEqTy
  have hElimNe : __str_nary_elim tail ≠ Term.Stuck := by
    intro h
    rw [h] at hRightNe
    exact hRightNe.2 rfl
  have hEmptyEoTy : __eo_typeof empty = Term.Apply Term.Seq A := by
    apply eo_typeof_seq_empty_seq_of_ne_stuck A
    simpa [empty] using hRightNe.1
  have hElimTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim tail)) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck tail T hTailTy hElimNe
  have hElimTrans :
      RuleProofs.eo_has_smt_translation (__str_nary_elim tail) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hElimTy]
    exact seq_ne_none T
  have hElimMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation
      (__str_nary_elim tail) hElimTrans
  have hAType :
      __eo_to_smt_type (Term.Apply Term.Seq A) = SmtType.Seq T := by
    rw [← hEmptyEoTy, hRightSame, ← hElimMatch, hElimTy]
  have hTailNN : term_has_non_none_type (__eo_to_smt tail) := by
    unfold term_has_non_none_type
    rw [hTailTy]
    exact seq_ne_none T
  have hSeqWF : __smtx_type_wf (SmtType.Seq T) = true :=
    smt_term_seq_type_wf_of_non_none (__eo_to_smt tail) hTailNN hTailTy
  have hEmptyTy : __smtx_typeof (__eo_to_smt empty) = SmtType.Seq T := by
    simpa [empty] using
      smt_typeof_seq_empty_of_eo_type_wf A T hAType hSeqWF
  exact ⟨T, hXTy, hT1Ty, hT2Ty, hEmptyTy, hElimNe⟩

theorem eo_has_bool_type_str_concat_unify_base
    (x t1 t2 A : Term) (T : SmtType)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hT1Ty : __smtx_typeof (__eo_to_smt t1) = SmtType.Seq T)
    (hT2Ty : __smtx_typeof (__eo_to_smt t2) = SmtType.Seq T)
    (hEmptyTy :
      __smtx_typeof (__eo_to_smt (strConcatUnifyBaseEmpty A)) =
        SmtType.Seq T)
    (hElimNe : __str_nary_elim (strConcatUnifyBaseTail t1 t2) ≠
      Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (strConcatUnifyBaseConclusion x t1 t2 A) := by
  have hTailTy :
      __smtx_typeof (__eo_to_smt (strConcatUnifyBaseTail t1 t2)) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq t1 t2 T hT1Ty hT2Ty
  have hXConcatTy :
      __smtx_typeof
          (__eo_to_smt (mkConcat x (strConcatUnifyBaseTail t1 t2))) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x (strConcatUnifyBaseTail t1 t2) T
      hXTy hTailTy
  have hElimTy :
      __smtx_typeof
          (__eo_to_smt
            (__str_nary_elim (strConcatUnifyBaseTail t1 t2))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck
      (strConcatUnifyBaseTail t1 t2) T hTailTy hElimNe
  have hLeftBool : RuleProofs.eo_has_bool_type
      (strConcatUnifyBaseLeftEq x t1 t2) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (by rw [hXTy, hXConcatTy]) (by rw [hXTy]; exact seq_ne_none T)
  have hRightBool : RuleProofs.eo_has_bool_type
      (strConcatUnifyBaseRightEq t1 t2 A) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (by rw [hEmptyTy, hElimTy])
      (by rw [hEmptyTy]; exact seq_ne_none T)
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLeftBool.trans hRightBool.symm)
    (by rw [hLeftBool]; decide)

theorem eo_interprets_str_concat_unify_base
    (M : SmtModel) (hM : model_wf M)
    (x t1 t2 A : Term) (T : SmtType)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hT1Ty : __smtx_typeof (__eo_to_smt t1) = SmtType.Seq T)
    (hT2Ty : __smtx_typeof (__eo_to_smt t2) = SmtType.Seq T)
    (hEmptyTy :
      __smtx_typeof (__eo_to_smt (strConcatUnifyBaseEmpty A)) =
        SmtType.Seq T)
    (hElimNe : __str_nary_elim (strConcatUnifyBaseTail t1 t2) ≠
      Term.Stuck) :
    eo_interprets M (strConcatUnifyBaseConclusion x t1 t2 A) true := by
  let tail := strConcatUnifyBaseTail t1 t2
  let empty := strConcatUnifyBaseEmpty A
  have hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq t1 t2 T hT1Ty hT2Ty
  have hEmptyNe : empty ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_seq empty T hEmptyTy
  have hEmptyNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) empty =
        Term.Boolean true := by
    simpa [empty, strConcatUnifyBaseEmpty] using
      eo_is_list_nil_str_concat_seq_empty_of_ne_stuck
        (Term.Apply Term.Seq A) hEmptyNe
  have hXEmptyRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x empty)))
      (__smtx_model_eval M (__eo_to_smt x)) :=
    smt_value_rel_str_concat_list_nil_right_empty M hM x empty T
      hXTy hEmptyNil hEmptyTy
  have hElimRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim tail)))
      (__smtx_model_eval M (__eo_to_smt tail)) :=
    smt_value_rel_str_nary_elim M hM tail T hTailTy hElimNe
  have hLeftIff :
      RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt (mkConcat x tail))) ↔
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt empty))
          (__smtx_model_eval M (__eo_to_smt tail)) := by
    constructor
    · intro h
      have hConcatRel : RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt (mkConcat x empty)))
          (__smtx_model_eval M (__eo_to_smt (mkConcat x tail))) :=
        RuleProofs.smt_value_rel_trans _ _ _ hXEmptyRel h
      exact smt_value_rel_str_concat_left_cancel M hM x empty tail T
        hXTy hEmptyTy hTailTy hConcatRel
    · intro h
      have hConcatRel := smt_value_rel_str_concat_right_congr M hM
        x empty tail T hXTy hEmptyTy hTailTy h
      exact RuleProofs.smt_value_rel_trans _ _ _
        (RuleProofs.smt_value_rel_symm _ _ hXEmptyRel) hConcatRel
  have hRightIff :
      RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt empty))
          (__smtx_model_eval M (__eo_to_smt (__str_nary_elim tail))) ↔
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt empty))
          (__smtx_model_eval M (__eo_to_smt tail)) := by
    constructor
    · intro h
      exact RuleProofs.smt_value_rel_trans _ _ _ h hElimRel
    · intro h
      exact RuleProofs.smt_value_rel_trans _ _ _ h
        (RuleProofs.smt_value_rel_symm _ _ hElimRel)
  have hEvalEq :
      __smtx_model_eval M
          (__eo_to_smt (strConcatUnifyBaseLeftEq x t1 t2)) =
        __smtx_model_eval M
          (__eo_to_smt (strConcatUnifyBaseRightEq t1 t2 A)) := by
    change __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt x)
          (__eo_to_smt (mkConcat x tail))) =
      __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt empty)
          (__eo_to_smt (__str_nary_elim tail)))
    rw [smtx_eval_eq_term_eq, smtx_eval_eq_term_eq]
    exact smtx_model_eval_eq_eq_of_rel_iff _ _ _ _
      (hLeftIff.trans hRightIff.symm)
  have hBool := eo_has_bool_type_str_concat_unify_base x t1 t2 A T
    hXTy hT1Ty hT2Ty hEmptyTy hElimNe
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M
      (__eo_to_smt (strConcatUnifyBaseRightEq t1 t2 A)))

/-!
The reverse variants append the distinguished string through CPC's n-ary
list representation.  In particular, the middle argument may be an empty
list whose element type differs from the surrounding strings: both list
concatenation and singleton elimination erase that empty argument.  The
helpers below therefore split on list emptiness instead of assuming that the
un-normalized `mkConcat head middle` is SMT-typed.
-/

abbrev strConcatUnifyRevNil (head : Term) : Term :=
  __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof head)

abbrev strConcatUnifyRevSingleton (head suffix : Term) : Term :=
  mkConcat suffix (strConcatUnifyRevNil head)

abbrev strConcatUnifyRevAppend
    (head middle suffix : Term) : Term :=
  mkConcat head
    (__eo_list_concat (Term.UOp UserOp.str_concat) middle
      (strConcatUnifyRevSingleton head suffix))

abbrev strConcatUnifyBaseRevLeftEq
    (suffix head middle : Term) : Term :=
  mkEq suffix (strConcatUnifyRevAppend head middle suffix)

abbrev strConcatUnifyBaseRevConclusion
    (suffix head middle A : Term) : Term :=
  mkEq (strConcatUnifyBaseRevLeftEq suffix head middle)
    (strConcatUnifyBaseRightEq head middle A)

abbrev strConcatUnifyRevLeftEq
    (suffix sHead sMiddle tHead tMiddle : Term) : Term :=
  mkEq (strConcatUnifyRevAppend sHead sMiddle suffix)
    (strConcatUnifyRevAppend tHead tMiddle suffix)

abbrev strConcatUnifyRevRightEq
    (sHead sMiddle tHead tMiddle : Term) : Term :=
  mkEq (__str_nary_elim (mkConcat sHead sMiddle))
    (__str_nary_elim (mkConcat tHead tMiddle))

abbrev strConcatUnifyRevConclusion
    (suffix sHead sMiddle tHead tMiddle : Term) : Term :=
  mkEq (strConcatUnifyRevLeftEq suffix sHead sMiddle tHead tMiddle)
    (strConcatUnifyRevRightEq sHead sMiddle tHead tMiddle)

theorem str_nary_elim_concat_eq_head_of_nil
    (head middle : Term)
    (hMiddleList :
      __eo_is_list (Term.UOp UserOp.str_concat) middle =
        Term.Boolean true)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) middle =
        Term.Boolean true) :
    __str_nary_elim (mkConcat head middle) = head := by
  have hList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat head middle) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.str_concat) head middle (by decide) hMiddleList
  simp [__str_nary_elim, __eo_list_singleton_elim, hList,
    __eo_list_singleton_elim_2, hNil, eo_ite_true, __eo_requires,
    native_teq, native_ite, SmtEval.native_ite, SmtEval.native_not]

theorem str_nary_elim_concat_eq_self_of_not_nil
    (head middle : Term)
    (hMiddleList :
      __eo_is_list (Term.UOp UserOp.str_concat) middle =
        Term.Boolean true)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) middle =
        Term.Boolean false) :
    __str_nary_elim (mkConcat head middle) = mkConcat head middle := by
  have hList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat head middle) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.str_concat) head middle (by decide) hMiddleList
  simp [__str_nary_elim, __eo_list_singleton_elim, hList,
    __eo_list_singleton_elim_2, hNil, eo_ite_false, __eo_requires,
    native_teq, native_ite, SmtEval.native_ite, SmtEval.native_not]

theorem str_concat_unify_base_rev_smt_types_of_eo_type
    (suffix head middle A : Term)
    (hSuffixTrans : RuleProofs.eo_has_smt_translation suffix)
    (hHeadTrans : RuleProofs.eo_has_smt_translation head)
    (hMiddleTrans : RuleProofs.eo_has_smt_translation middle)
    (hTy :
      __eo_typeof
          (strConcatUnifyBaseRevConclusion suffix head middle A) =
        Term.Bool) :
    ∃ T,
      __smtx_typeof (__eo_to_smt suffix) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt head) = SmtType.Seq T ∧
      __smtx_typeof
          (__eo_to_smt (strConcatUnifyBaseEmpty A)) = SmtType.Seq T ∧
      __smtx_typeof
          (__eo_to_smt (__str_nary_elim (mkConcat head middle))) =
        SmtType.Seq T ∧
      __smtx_typeof
          (__eo_to_smt
            (strConcatUnifyRevAppend head middle suffix)) =
        SmtType.Seq T ∧
      __str_nary_elim (mkConcat head middle) ≠ Term.Stuck ∧
      __eo_is_list (Term.UOp UserOp.str_concat) middle =
        Term.Boolean true ∧
      ((__eo_is_list_nil (Term.UOp UserOp.str_concat) middle =
          Term.Boolean true) ∨
        (__eo_is_list_nil (Term.UOp UserOp.str_concat) middle =
            Term.Boolean false ∧
          __smtx_typeof (__eo_to_smt middle) = SmtType.Seq T)) := by
  let nil := strConcatUnifyRevNil head
  let z := strConcatUnifyRevSingleton head suffix
  let lc := __eo_list_concat (Term.UOp UserOp.str_concat) middle z
  let appended := strConcatUnifyRevAppend head middle suffix
  let empty := strConcatUnifyBaseEmpty A
  let elim := __str_nary_elim (mkConcat head middle)
  let leftEq := strConcatUnifyBaseRevLeftEq suffix head middle
  let rightEq := strConcatUnifyBaseRightEq head middle A
  change __eo_typeof_eq (__eo_typeof leftEq) (__eo_typeof rightEq) =
    Term.Bool at hTy
  have hOuterNe :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy
  have hLeftEqTy : __eo_typeof leftEq = Term.Bool := by
    change __eo_typeof_eq (__eo_typeof suffix) (__eo_typeof appended) =
      Term.Bool
    apply eo_typeof_eq_bool_of_ne_stuck
    exact hOuterNe.1
  have hRightEqTy : __eo_typeof rightEq = Term.Bool := by
    change __eo_typeof_eq (__eo_typeof empty) (__eo_typeof elim) =
      Term.Bool
    apply eo_typeof_eq_bool_of_ne_stuck
    exact hOuterNe.2
  change __eo_typeof_eq (__eo_typeof suffix) (__eo_typeof appended) =
    Term.Bool at hLeftEqTy
  have hLeftSame :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hLeftEqTy
  have hLeftNe :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hLeftEqTy
  have hAppendConcatNe :
      __eo_typeof_str_concat (__eo_typeof head) (__eo_typeof lc) ≠
        Term.Stuck := by
    exact hLeftNe.2
  rcases eo_typeof_str_concat_args_of_ne_stuck _ _ hAppendConcatNe with
    ⟨U, hHeadEoTy, hLcEoTy⟩
  have hUNe : U ≠ Term.Stuck := by
    intro hU
    subst U
    simp [hHeadEoTy, hLcEoTy, __eo_typeof_str_concat, __eo_requires,
      __eo_eq, native_ite, native_teq, SmtEval.native_not] at hAppendConcatNe
  have hAppendEoTy : __eo_typeof appended = Term.Apply Term.Seq U := by
    simpa [appended, strConcatUnifyRevAppend, lc, z, nil,
      strConcatUnifyRevSingleton, strConcatUnifyRevNil] using
      eo_typeof_str_concat_result_of_args head lc U hHeadEoTy hLcEoTy hUNe
  have hSuffixEoTy : __eo_typeof suffix = Term.Apply Term.Seq U := by
    rw [hLeftSame, hAppendEoTy]
  have hLcNe : lc ≠ Term.Stuck := by
    intro h
    rw [h] at hLcEoTy
    cases hLcEoTy
  have hLists := concat_clash_rev_list_concat_facts middle z
    (by simpa [lc] using hLcNe)
  have hMiddleList := hLists.1
  have hMiddleNe : middle ≠ Term.Stuck := by
    intro h
    subst middle
    simp [__eo_is_list] at hMiddleList
  rcases eo_is_list_nil_str_concat_boolean_of_ne_stuck middle hMiddleNe with
    ⟨isNil, hNilBool⟩
  change __eo_typeof_eq (__eo_typeof empty) (__eo_typeof elim) =
    Term.Bool at hRightEqTy
  have hRightSame :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hRightEqTy
  have hRightNe :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hRightEqTy
  have hEmptyEoTy : __eo_typeof empty = Term.Apply Term.Seq A := by
    apply eo_typeof_seq_empty_seq_of_ne_stuck A
    simpa [empty] using hRightNe.1
  have hElimEoTy : __eo_typeof elim = Term.Apply Term.Seq A := by
    rw [← hRightSame, hEmptyEoTy]
  have hElimNe : elim ≠ Term.Stuck := by
    intro h
    rw [h] at hElimEoTy
    cases hElimEoTy
  cases isNil with
  | false =>
      have hNil :
          __eo_is_list_nil (Term.UOp UserOp.str_concat) middle =
            Term.Boolean false := by
        simpa using hNilBool
      have hElimEq : elim = mkConcat head middle := by
        simpa [elim] using
          str_nary_elim_concat_eq_self_of_not_nil head middle
            hMiddleList hNil
      have hRawEoTy :
          __eo_typeof (mkConcat head middle) = Term.Apply Term.Seq A := by
        simpa [hElimEq] using hElimEoTy
      have hRawArgs :=
        eo_typeof_str_concat_args_of_result_seq head middle A hRawEoTy
      have hUA : U = A := by
        have hSeq : Term.Apply Term.Seq U = Term.Apply Term.Seq A := by
          rw [← hHeadEoTy, hRawArgs.1]
        injection hSeq
      subst U
      let T := __eo_to_smt_type A
      have hSuffixTy := smtx_typeof_seq_of_eo_typeof suffix A
        hSuffixTrans hSuffixEoTy
      have hHeadTy := smtx_typeof_seq_of_eo_typeof head A
        hHeadTrans hHeadEoTy
      have hMiddleTy := smtx_typeof_seq_of_eo_typeof middle A
        hMiddleTrans hRawArgs.2
      have hRawTy :
          __smtx_typeof (__eo_to_smt (mkConcat head middle)) =
            SmtType.Seq T :=
        smt_typeof_str_concat_of_seq head middle T hHeadTy hMiddleTy
      have hElimTy : __smtx_typeof (__eo_to_smt elim) = SmtType.Seq T := by
        rw [hElimEq]
        exact hRawTy
      have hHeadNN : term_has_non_none_type (__eo_to_smt head) := by
        unfold term_has_non_none_type
        rw [hHeadTy]
        exact seq_ne_none T
      have hHeadMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation head
          hHeadTrans
      have hAType :
          __eo_to_smt_type (Term.Apply Term.Seq A) = SmtType.Seq T := by
        rw [← hHeadEoTy, ← hHeadMatch, hHeadTy]
      have hSeqWF : __smtx_type_wf (SmtType.Seq T) = true :=
        smt_term_seq_type_wf_of_non_none (__eo_to_smt head) hHeadNN
          hHeadTy
      have hEmptyTy : __smtx_typeof (__eo_to_smt empty) =
          SmtType.Seq T := by
        simpa [empty] using
          smt_typeof_seq_empty_of_eo_type_wf A T hAType hSeqWF
      have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
        simpa [nil] using concat_clash_rev_smt_typeof_nil head T hHeadTy
      have hZTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T := by
        simpa [z, strConcatUnifyRevSingleton] using
          smt_typeof_str_concat_of_seq suffix nil T hSuffixTy hNilTy
      have hLcEq : lc = __eo_list_concat_rec middle z :=
        concat_clash_rev_list_concat_eq_rec middle z
          (by simpa [lc] using hLcNe)
      have hLcTy : __smtx_typeof (__eo_to_smt lc) = SmtType.Seq T := by
        rw [hLcEq]
        exact smt_typeof_list_concat_rec_str_concat_of_seq middle z T
          hMiddleList hMiddleTy hZTy
      have hAppendTy : __smtx_typeof (__eo_to_smt appended) =
          SmtType.Seq T := by
        simpa [appended, strConcatUnifyRevAppend, lc, z, nil,
          strConcatUnifyRevSingleton, strConcatUnifyRevNil] using
          smt_typeof_str_concat_of_seq head lc T hHeadTy hLcTy
      exact ⟨T, hSuffixTy, hHeadTy, hEmptyTy,
        by simpa [elim] using hElimTy,
        by simpa [appended] using hAppendTy,
        by simpa [elim] using hElimNe, hMiddleList,
        Or.inr ⟨hNil, hMiddleTy⟩⟩
  | true =>
      have hNil :
          __eo_is_list_nil (Term.UOp UserOp.str_concat) middle =
            Term.Boolean true := by
        simpa using hNilBool
      have hElimEq : elim = head := by
        simpa [elim] using
          str_nary_elim_concat_eq_head_of_nil head middle hMiddleList hNil
      have hHeadEoTyA : __eo_typeof head = Term.Apply Term.Seq A := by
        simpa [hElimEq] using hElimEoTy
      have hUA : U = A := by
        have hSeq : Term.Apply Term.Seq U = Term.Apply Term.Seq A := by
          rw [← hHeadEoTy, hHeadEoTyA]
        injection hSeq
      subst U
      let T := __eo_to_smt_type A
      have hSuffixTy := smtx_typeof_seq_of_eo_typeof suffix A
        hSuffixTrans hSuffixEoTy
      have hHeadTy := smtx_typeof_seq_of_eo_typeof head A
        hHeadTrans hHeadEoTy
      have hElimTy : __smtx_typeof (__eo_to_smt elim) = SmtType.Seq T := by
        rw [hElimEq]
        exact hHeadTy
      have hHeadNN : term_has_non_none_type (__eo_to_smt head) := by
        unfold term_has_non_none_type
        rw [hHeadTy]
        exact seq_ne_none T
      have hHeadMatch :=
        TranslationProofs.eo_to_smt_typeof_matches_translation head
          hHeadTrans
      have hAType :
          __eo_to_smt_type (Term.Apply Term.Seq A) = SmtType.Seq T := by
        rw [← hHeadEoTy, ← hHeadMatch, hHeadTy]
      have hSeqWF : __smtx_type_wf (SmtType.Seq T) = true :=
        smt_term_seq_type_wf_of_non_none (__eo_to_smt head) hHeadNN
          hHeadTy
      have hEmptyTy : __smtx_typeof (__eo_to_smt empty) =
          SmtType.Seq T := by
        simpa [empty] using
          smt_typeof_seq_empty_of_eo_type_wf A T hAType hSeqWF
      have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
        simpa [nil] using concat_clash_rev_smt_typeof_nil head T hHeadTy
      have hZTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T := by
        simpa [z, strConcatUnifyRevSingleton] using
          smt_typeof_str_concat_of_seq suffix nil T hSuffixTy hNilTy
      have hLcEqRec : lc = __eo_list_concat_rec middle z :=
        concat_clash_rev_list_concat_eq_rec middle z
          (by simpa [lc] using hLcNe)
      have hRecEq : __eo_list_concat_rec middle z = z :=
        eo_list_concat_rec_str_concat_nil_eq_of_nil_true middle z hNil
      have hLcEq : lc = z := hLcEqRec.trans hRecEq
      have hLcTy : __smtx_typeof (__eo_to_smt lc) = SmtType.Seq T := by
        rw [hLcEq]
        exact hZTy
      have hAppendTy : __smtx_typeof (__eo_to_smt appended) =
          SmtType.Seq T := by
        simpa [appended, strConcatUnifyRevAppend, lc, z, nil,
          strConcatUnifyRevSingleton, strConcatUnifyRevNil] using
          smt_typeof_str_concat_of_seq head lc T hHeadTy hLcTy
      exact ⟨T, hSuffixTy, hHeadTy, hEmptyTy,
        by simpa [elim] using hElimTy,
        by simpa [appended] using hAppendTy,
        by simpa [elim] using hElimNe, hMiddleList, Or.inl hNil⟩

theorem eo_has_bool_type_str_concat_unify_base_rev
    (suffix head middle A : Term) (T : SmtType)
    (hSuffixTy :
      __smtx_typeof (__eo_to_smt suffix) = SmtType.Seq T)
    (hEmptyTy :
      __smtx_typeof (__eo_to_smt (strConcatUnifyBaseEmpty A)) =
        SmtType.Seq T)
    (hElimTy :
      __smtx_typeof
          (__eo_to_smt (__str_nary_elim (mkConcat head middle))) =
        SmtType.Seq T)
    (hAppendTy :
      __smtx_typeof
          (__eo_to_smt
            (strConcatUnifyRevAppend head middle suffix)) =
        SmtType.Seq T) :
    RuleProofs.eo_has_bool_type
      (strConcatUnifyBaseRevConclusion suffix head middle A) := by
  have hLeftBool : RuleProofs.eo_has_bool_type
      (strConcatUnifyBaseRevLeftEq suffix head middle) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (by rw [hSuffixTy, hAppendTy])
      (by rw [hSuffixTy]; exact seq_ne_none T)
  have hRightBool : RuleProofs.eo_has_bool_type
      (strConcatUnifyBaseRightEq head middle A) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (by rw [hEmptyTy, hElimTy])
      (by rw [hEmptyTy]; exact seq_ne_none T)
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLeftBool.trans hRightBool.symm)
    (by rw [hLeftBool]; decide)

theorem eo_typeof_list_concat_rec_right_type_eq_seq
    (a z U : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true) :
    __eo_typeof (__eo_list_concat_rec a z) = Term.Apply Term.Seq U ->
      __eo_typeof z = Term.Apply Term.Seq U := by
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      intro hTy
      simp [__eo_is_list] at hList
  | case2 a hA =>
      intro hTy
      have hRec : __eo_list_concat_rec a Term.Stuck = Term.Stuck := by
        cases a <;> rfl
      rw [hRec] at hTy
      cases hTy
  | case3 g x y z hZ ih =>
      intro hTy
      have hg : g = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.str_concat)
          g x y hList
      subst g
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self
          (Term.UOp UserOp.str_concat) x y hList
      have hZNe : z ≠ Term.Stuck := hZ
      have hTailRecNe : __eo_list_concat_rec y z ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.str_concat) y z hTailList hZNe
      rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
        x y z hTailRecNe] at hTy
      have hArgs := eo_typeof_str_concat_args_of_result_seq
        x (__eo_list_concat_rec y z) U hTy
      exact ih hTailList hArgs.2
  | case4 nil z hNil hZ hNot =>
      intro hTy
      simpa [__eo_list_concat_rec] using hTy

theorem str_concat_unify_rev_side_smt_types
    (suffix head middle U : Term)
    (hSuffixTrans : RuleProofs.eo_has_smt_translation suffix)
    (hHeadTrans : RuleProofs.eo_has_smt_translation head)
    (hMiddleTrans : RuleProofs.eo_has_smt_translation middle)
    (hAppendEoTy :
      __eo_typeof (strConcatUnifyRevAppend head middle suffix) =
        Term.Apply Term.Seq U)
    (hNormEoNe :
      __eo_typeof (__str_nary_elim (mkConcat head middle)) ≠
        Term.Stuck) :
    let T := __eo_to_smt_type U
    __smtx_typeof (__eo_to_smt suffix) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt head) = SmtType.Seq T ∧
      __smtx_typeof
          (__eo_to_smt (__str_nary_elim (mkConcat head middle))) =
        SmtType.Seq T ∧
      __smtx_typeof
          (__eo_to_smt
            (strConcatUnifyRevAppend head middle suffix)) =
        SmtType.Seq T ∧
      __eo_is_list (Term.UOp UserOp.str_concat) middle =
        Term.Boolean true ∧
      ((__eo_is_list_nil (Term.UOp UserOp.str_concat) middle =
          Term.Boolean true) ∨
        (__eo_is_list_nil (Term.UOp UserOp.str_concat) middle =
            Term.Boolean false ∧
          __smtx_typeof (__eo_to_smt middle) = SmtType.Seq T)) := by
  let T := __eo_to_smt_type U
  let nil := strConcatUnifyRevNil head
  let z := strConcatUnifyRevSingleton head suffix
  let lc := __eo_list_concat (Term.UOp UserOp.str_concat) middle z
  have hAppendRawEoTy :
      __eo_typeof (mkConcat head lc) = Term.Apply Term.Seq U := by
    simpa [strConcatUnifyRevAppend, lc, z, nil,
      strConcatUnifyRevSingleton, strConcatUnifyRevNil] using hAppendEoTy
  have hAppendArgs :=
    eo_typeof_str_concat_args_of_result_seq head lc U hAppendRawEoTy
  have hHeadEoTy := hAppendArgs.1
  have hLcEoTy := hAppendArgs.2
  have hLcNe : lc ≠ Term.Stuck := by
    intro h
    rw [h] at hLcEoTy
    cases hLcEoTy
  have hLists := concat_clash_rev_list_concat_facts middle z
    (by simpa [lc] using hLcNe)
  have hMiddleList := hLists.1
  have hLcEqRec : lc = __eo_list_concat_rec middle z :=
    concat_clash_rev_list_concat_eq_rec middle z
      (by simpa [lc] using hLcNe)
  have hRecEoTy :
      __eo_typeof (__eo_list_concat_rec middle z) =
        Term.Apply Term.Seq U := by
    rw [← hLcEqRec]
    exact hLcEoTy
  have hZEoTy : __eo_typeof z = Term.Apply Term.Seq U :=
    eo_typeof_list_concat_rec_right_type_eq_seq middle z U
      hMiddleList hRecEoTy
  have hZArgs := eo_typeof_str_concat_args_of_result_seq suffix nil U
    (by simpa [z, strConcatUnifyRevSingleton] using hZEoTy)
  have hSuffixEoTy := hZArgs.1
  have hSuffixTy := smtx_typeof_seq_of_eo_typeof suffix U
    hSuffixTrans hSuffixEoTy
  have hHeadTy := smtx_typeof_seq_of_eo_typeof head U
    hHeadTrans hHeadEoTy
  have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    simpa [nil] using concat_clash_rev_smt_typeof_nil head T hHeadTy
  have hZTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T := by
    simpa [z, strConcatUnifyRevSingleton] using
      smt_typeof_str_concat_of_seq suffix nil T hSuffixTy hNilTy
  have hMiddleNe : middle ≠ Term.Stuck := by
    intro h
    subst middle
    simp [__eo_is_list] at hMiddleList
  rcases eo_is_list_nil_str_concat_boolean_of_ne_stuck middle hMiddleNe with
    ⟨isNil, hNilBool⟩
  cases isNil with
  | false =>
      have hNil :
          __eo_is_list_nil (Term.UOp UserOp.str_concat) middle =
            Term.Boolean false := by
        simpa using hNilBool
      have hNormEq :
          __str_nary_elim (mkConcat head middle) =
            mkConcat head middle :=
        str_nary_elim_concat_eq_self_of_not_nil head middle hMiddleList
          hNil
      have hRawEoNe : __eo_typeof (mkConcat head middle) ≠
          Term.Stuck := by
        simpa [hNormEq] using hNormEoNe
      change __eo_typeof_str_concat (__eo_typeof head)
          (__eo_typeof middle) ≠ Term.Stuck at hRawEoNe
      rcases eo_typeof_str_concat_args_of_ne_stuck _ _ hRawEoNe with
        ⟨V, hHeadEoTyV, hMiddleEoTyV⟩
      have hVU : V = U := by
        have hSeq : Term.Apply Term.Seq V = Term.Apply Term.Seq U := by
          rw [← hHeadEoTyV, hHeadEoTy]
        injection hSeq
      subst V
      have hMiddleTy := smtx_typeof_seq_of_eo_typeof middle U
        hMiddleTrans hMiddleEoTyV
      have hNormTy :
          __smtx_typeof
              (__eo_to_smt (__str_nary_elim (mkConcat head middle))) =
            SmtType.Seq T := by
        rw [hNormEq]
        exact smt_typeof_str_concat_of_seq head middle T
          hHeadTy hMiddleTy
      have hLcTy : __smtx_typeof (__eo_to_smt lc) = SmtType.Seq T := by
        rw [hLcEqRec]
        exact smt_typeof_list_concat_rec_str_concat_of_seq middle z T
          hMiddleList hMiddleTy hZTy
      have hAppendTy :
          __smtx_typeof
              (__eo_to_smt
                (strConcatUnifyRevAppend head middle suffix)) =
            SmtType.Seq T := by
        simpa [strConcatUnifyRevAppend, lc, z, nil,
          strConcatUnifyRevSingleton, strConcatUnifyRevNil] using
          smt_typeof_str_concat_of_seq head lc T hHeadTy hLcTy
      exact ⟨hSuffixTy, hHeadTy, hNormTy, hAppendTy, hMiddleList,
        Or.inr ⟨hNil, hMiddleTy⟩⟩
  | true =>
      have hNil :
          __eo_is_list_nil (Term.UOp UserOp.str_concat) middle =
            Term.Boolean true := by
        simpa using hNilBool
      have hNormEq :
          __str_nary_elim (mkConcat head middle) = head :=
        str_nary_elim_concat_eq_head_of_nil head middle hMiddleList hNil
      have hNormTy :
          __smtx_typeof
              (__eo_to_smt (__str_nary_elim (mkConcat head middle))) =
            SmtType.Seq T := by
        rw [hNormEq]
        exact hHeadTy
      have hRecEq : __eo_list_concat_rec middle z = z :=
        eo_list_concat_rec_str_concat_nil_eq_of_nil_true middle z hNil
      have hLcEq : lc = z := hLcEqRec.trans hRecEq
      have hLcTy : __smtx_typeof (__eo_to_smt lc) = SmtType.Seq T := by
        rw [hLcEq]
        exact hZTy
      have hAppendTy :
          __smtx_typeof
              (__eo_to_smt
                (strConcatUnifyRevAppend head middle suffix)) =
            SmtType.Seq T := by
        simpa [strConcatUnifyRevAppend, lc, z, nil,
          strConcatUnifyRevSingleton, strConcatUnifyRevNil] using
          smt_typeof_str_concat_of_seq head lc T hHeadTy hLcTy
      exact ⟨hSuffixTy, hHeadTy, hNormTy, hAppendTy, hMiddleList,
        Or.inl hNil⟩

theorem str_concat_unify_rev_smt_types_of_eo_type
    (suffix sHead sMiddle tHead tMiddle : Term)
    (hSuffixTrans : RuleProofs.eo_has_smt_translation suffix)
    (hSHeadTrans : RuleProofs.eo_has_smt_translation sHead)
    (hSMiddleTrans : RuleProofs.eo_has_smt_translation sMiddle)
    (hTHeadTrans : RuleProofs.eo_has_smt_translation tHead)
    (hTMiddleTrans : RuleProofs.eo_has_smt_translation tMiddle)
    (hTy :
      __eo_typeof
          (strConcatUnifyRevConclusion
            suffix sHead sMiddle tHead tMiddle) = Term.Bool) :
    ∃ T,
      __smtx_typeof (__eo_to_smt suffix) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt sHead) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt tHead) = SmtType.Seq T ∧
      __smtx_typeof
          (__eo_to_smt (__str_nary_elim (mkConcat sHead sMiddle))) =
        SmtType.Seq T ∧
      __smtx_typeof
          (__eo_to_smt (__str_nary_elim (mkConcat tHead tMiddle))) =
        SmtType.Seq T ∧
      __smtx_typeof
          (__eo_to_smt
            (strConcatUnifyRevAppend sHead sMiddle suffix)) =
        SmtType.Seq T ∧
      __smtx_typeof
          (__eo_to_smt
            (strConcatUnifyRevAppend tHead tMiddle suffix)) =
        SmtType.Seq T ∧
      __eo_is_list (Term.UOp UserOp.str_concat) sMiddle =
        Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.str_concat) tMiddle =
        Term.Boolean true ∧
      ((__eo_is_list_nil (Term.UOp UserOp.str_concat) sMiddle =
          Term.Boolean true) ∨
        (__eo_is_list_nil (Term.UOp UserOp.str_concat) sMiddle =
            Term.Boolean false ∧
          __smtx_typeof (__eo_to_smt sMiddle) = SmtType.Seq T)) ∧
      ((__eo_is_list_nil (Term.UOp UserOp.str_concat) tMiddle =
          Term.Boolean true) ∨
        (__eo_is_list_nil (Term.UOp UserOp.str_concat) tMiddle =
            Term.Boolean false ∧
          __smtx_typeof (__eo_to_smt tMiddle) = SmtType.Seq T)) := by
  let sAppend := strConcatUnifyRevAppend sHead sMiddle suffix
  let tAppend := strConcatUnifyRevAppend tHead tMiddle suffix
  let sNorm := __str_nary_elim (mkConcat sHead sMiddle)
  let tNorm := __str_nary_elim (mkConcat tHead tMiddle)
  let leftEq :=
    strConcatUnifyRevLeftEq suffix sHead sMiddle tHead tMiddle
  let rightEq := strConcatUnifyRevRightEq sHead sMiddle tHead tMiddle
  change __eo_typeof_eq (__eo_typeof leftEq) (__eo_typeof rightEq) =
    Term.Bool at hTy
  have hOuterNe :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy
  have hLeftEqTy : __eo_typeof leftEq = Term.Bool := by
    change __eo_typeof_eq (__eo_typeof sAppend) (__eo_typeof tAppend) =
      Term.Bool
    apply eo_typeof_eq_bool_of_ne_stuck
    exact hOuterNe.1
  have hRightEqTy : __eo_typeof rightEq = Term.Bool := by
    change __eo_typeof_eq (__eo_typeof sNorm) (__eo_typeof tNorm) =
      Term.Bool
    apply eo_typeof_eq_bool_of_ne_stuck
    exact hOuterNe.2
  change __eo_typeof_eq (__eo_typeof sAppend) (__eo_typeof tAppend) =
    Term.Bool at hLeftEqTy
  have hAppendSame :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hLeftEqTy
  have hAppendNe :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hLeftEqTy
  let sLc := __eo_list_concat (Term.UOp UserOp.str_concat) sMiddle
    (strConcatUnifyRevSingleton sHead suffix)
  have hSAppendConcatNe :
      __eo_typeof_str_concat (__eo_typeof sHead) (__eo_typeof sLc) ≠
        Term.Stuck := by
    exact hAppendNe.1
  rcases eo_typeof_str_concat_args_of_ne_stuck _ _ hSAppendConcatNe with
    ⟨U, hSHeadEoTy, hSLcEoTy⟩
  have hUNe : U ≠ Term.Stuck := by
    intro h
    subst U
    simp [hSHeadEoTy, hSLcEoTy, __eo_typeof_str_concat,
      __eo_requires, __eo_eq, native_ite, native_teq,
      SmtEval.native_not] at hSAppendConcatNe
  have hSAppendEoTy : __eo_typeof sAppend = Term.Apply Term.Seq U := by
    simpa [sAppend, strConcatUnifyRevAppend, sLc,
      strConcatUnifyRevSingleton, strConcatUnifyRevNil] using
      eo_typeof_str_concat_result_of_args sHead sLc U
        hSHeadEoTy hSLcEoTy hUNe
  have hTAppendEoTy : __eo_typeof tAppend = Term.Apply Term.Seq U := by
    rw [← hAppendSame, hSAppendEoTy]
  change __eo_typeof_eq (__eo_typeof sNorm) (__eo_typeof tNorm) =
    Term.Bool at hRightEqTy
  have hNormNe :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hRightEqTy
  have hSSide := str_concat_unify_rev_side_smt_types
    suffix sHead sMiddle U hSuffixTrans hSHeadTrans hSMiddleTrans
    (by simpa [sAppend] using hSAppendEoTy)
    (by simpa [sNorm] using hNormNe.1)
  have hTSide := str_concat_unify_rev_side_smt_types
    suffix tHead tMiddle U hSuffixTrans hTHeadTrans hTMiddleTrans
    (by simpa [tAppend] using hTAppendEoTy)
    (by simpa [tNorm] using hNormNe.2)
  rcases hSSide with
    ⟨hSuffixTy, hSHeadTy, hSNormTy, hSAppendTy,
      hSMiddleList, hSMiddleCases⟩
  rcases hTSide with
    ⟨_hSuffixTy, hTHeadTy, hTNormTy, hTAppendTy,
      hTMiddleList, hTMiddleCases⟩
  exact ⟨__eo_to_smt_type U, hSuffixTy, hSHeadTy, hTHeadTy,
    hSNormTy, hTNormTy, hSAppendTy, hTAppendTy, hSMiddleList,
    hTMiddleList, hSMiddleCases, hTMiddleCases⟩

theorem smt_value_rel_str_concat_unify_rev_append
    (M : SmtModel) (hM : model_wf M)
    (head middle suffix : Term) (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hSuffixTy : __smtx_typeof (__eo_to_smt suffix) = SmtType.Seq T)
    (hAppendTy :
      __smtx_typeof
          (__eo_to_smt
            (strConcatUnifyRevAppend head middle suffix)) =
        SmtType.Seq T)
    (hMiddleList :
      __eo_is_list (Term.UOp UserOp.str_concat) middle =
        Term.Boolean true)
    (hMiddleCases :
      (__eo_is_list_nil (Term.UOp UserOp.str_concat) middle =
          Term.Boolean true) ∨
        (__eo_is_list_nil (Term.UOp UserOp.str_concat) middle =
            Term.Boolean false ∧
          __smtx_typeof (__eo_to_smt middle) = SmtType.Seq T)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (strConcatUnifyRevAppend head middle suffix)))
      (__smtx_model_eval M
        (__eo_to_smt
          (mkConcat (__str_nary_elim (mkConcat head middle)) suffix))) := by
  let nil := strConcatUnifyRevNil head
  let z := strConcatUnifyRevSingleton head suffix
  let lc := __eo_list_concat (Term.UOp UserOp.str_concat) middle z
  have hAppendRawTy :
      __smtx_typeof (__eo_to_smt (mkConcat head lc)) = SmtType.Seq T := by
    simpa [strConcatUnifyRevAppend, lc, z, nil,
      strConcatUnifyRevSingleton, strConcatUnifyRevNil] using hAppendTy
  have hAppendArgs :=
    str_concat_args_of_seq_type head lc T hAppendRawTy
  have hLcTy : __smtx_typeof (__eo_to_smt lc) = SmtType.Seq T :=
    hAppendArgs.2
  have hLcNe : lc ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_seq lc T hLcTy
  have hLcEqRec : lc = __eo_list_concat_rec middle z :=
    concat_clash_rev_list_concat_eq_rec middle z
      (by simpa [lc] using hLcNe)
  have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    simpa [nil] using concat_clash_rev_smt_typeof_nil head T hHeadTy
  have hNilNe : nil ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_seq nil T hNilTy
  have hNilNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
        Term.Boolean true := by
    simpa [nil, strConcatUnifyRevNil] using
      strConcat_nil_is_list_nil_of_ne_stuck (__eo_typeof head)
        (by simpa [nil, strConcatUnifyRevNil] using hNilNe)
  have hZTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T := by
    simpa [z, strConcatUnifyRevSingleton] using
      smt_typeof_str_concat_of_seq suffix nil T hSuffixTy hNilTy
  have hZRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt z))
      (__smtx_model_eval M (__eo_to_smt suffix)) := by
    simpa [z, strConcatUnifyRevSingleton] using
      smt_value_rel_str_concat_list_nil_right_empty M hM suffix nil T
        hSuffixTy hNilNil hNilTy
  rcases hMiddleCases with hMiddleNil | hMiddleNonNil
  · have hRecEq : __eo_list_concat_rec middle z = z :=
      eo_list_concat_rec_str_concat_nil_eq_of_nil_true middle z hMiddleNil
    have hLcEq : lc = z := hLcEqRec.trans hRecEq
    have hElimEq : __str_nary_elim (mkConcat head middle) = head :=
      str_nary_elim_concat_eq_head_of_nil head middle hMiddleList
        hMiddleNil
    rw [hElimEq]
    simpa [strConcatUnifyRevAppend, lc, z, nil,
      strConcatUnifyRevSingleton, strConcatUnifyRevNil, hLcEq] using
      smt_value_rel_str_concat_right_congr M hM head z suffix T
        hHeadTy hZTy hSuffixTy hZRel
  · rcases hMiddleNonNil with ⟨hMiddleNil, hMiddleTy⟩
    have hRecTy :
        __smtx_typeof
            (__eo_to_smt (__eo_list_concat_rec middle z)) =
          SmtType.Seq T :=
      smt_typeof_list_concat_rec_str_concat_of_seq middle z T
        hMiddleList hMiddleTy hZTy
    have hRecRel : RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (__eo_list_concat_rec middle z)))
        (__smtx_model_eval M (__eo_to_smt (mkConcat middle z))) :=
      smt_value_rel_list_concat_rec_str_concat M hM middle z T
        hMiddleList hMiddleTy hZTy
    have hMiddleSuffixTy :
        __smtx_typeof (__eo_to_smt (mkConcat middle suffix)) =
          SmtType.Seq T :=
      smt_typeof_str_concat_of_seq middle suffix T hMiddleTy hSuffixTy
    have hMiddleCongr : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (mkConcat middle z)))
        (__smtx_model_eval M (__eo_to_smt (mkConcat middle suffix))) :=
      smt_value_rel_str_concat_right_congr M hM middle z suffix T
        hMiddleTy hZTy hSuffixTy hZRel
    have hLcRel : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt lc))
        (__smtx_model_eval M (__eo_to_smt (mkConcat middle suffix))) := by
      rw [hLcEqRec]
      exact RuleProofs.smt_value_rel_trans _ _ _ hRecRel hMiddleCongr
    have hOuterCongr : RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (mkConcat head lc)))
        (__smtx_model_eval M
          (__eo_to_smt (mkConcat head (mkConcat middle suffix)))) :=
      smt_value_rel_str_concat_right_congr M hM head lc
        (mkConcat middle suffix) T hHeadTy hLcTy hMiddleSuffixTy hLcRel
    have hAssoc := smt_value_rel_str_concat_assoc M hM
      head middle suffix T hHeadTy hMiddleTy hSuffixTy
    have hElimEq :
        __str_nary_elim (mkConcat head middle) =
          mkConcat head middle :=
      str_nary_elim_concat_eq_self_of_not_nil head middle hMiddleList
        hMiddleNil
    rw [hElimEq]
    exact RuleProofs.smt_value_rel_trans _ _ _
      (by simpa [strConcatUnifyRevAppend, lc, z, nil,
        strConcatUnifyRevSingleton, strConcatUnifyRevNil] using hOuterCongr)
      (RuleProofs.smt_value_rel_symm _ _ hAssoc)

theorem eo_has_bool_type_str_concat_unify_rev
    (suffix sHead sMiddle tHead tMiddle : Term) (T : SmtType)
    (hSNormTy :
      __smtx_typeof
          (__eo_to_smt (__str_nary_elim (mkConcat sHead sMiddle))) =
        SmtType.Seq T)
    (hTNormTy :
      __smtx_typeof
          (__eo_to_smt (__str_nary_elim (mkConcat tHead tMiddle))) =
        SmtType.Seq T)
    (hSAppendTy :
      __smtx_typeof
          (__eo_to_smt
            (strConcatUnifyRevAppend sHead sMiddle suffix)) =
        SmtType.Seq T)
    (hTAppendTy :
      __smtx_typeof
          (__eo_to_smt
            (strConcatUnifyRevAppend tHead tMiddle suffix)) =
        SmtType.Seq T) :
    RuleProofs.eo_has_bool_type
      (strConcatUnifyRevConclusion
        suffix sHead sMiddle tHead tMiddle) := by
  have hLeftBool : RuleProofs.eo_has_bool_type
      (strConcatUnifyRevLeftEq suffix sHead sMiddle tHead tMiddle) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (by rw [hSAppendTy, hTAppendTy])
      (by rw [hSAppendTy]; exact seq_ne_none T)
  have hRightBool : RuleProofs.eo_has_bool_type
      (strConcatUnifyRevRightEq sHead sMiddle tHead tMiddle) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (by rw [hSNormTy, hTNormTy])
      (by rw [hSNormTy]; exact seq_ne_none T)
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLeftBool.trans hRightBool.symm)
    (by rw [hLeftBool]; decide)

theorem eo_interprets_str_concat_unify_rev
    (M : SmtModel) (hM : model_wf M)
    (suffix sHead sMiddle tHead tMiddle : Term) (T : SmtType)
    (hSuffixTy :
      __smtx_typeof (__eo_to_smt suffix) = SmtType.Seq T)
    (hSHeadTy :
      __smtx_typeof (__eo_to_smt sHead) = SmtType.Seq T)
    (hTHeadTy :
      __smtx_typeof (__eo_to_smt tHead) = SmtType.Seq T)
    (hSNormTy :
      __smtx_typeof
          (__eo_to_smt (__str_nary_elim (mkConcat sHead sMiddle))) =
        SmtType.Seq T)
    (hTNormTy :
      __smtx_typeof
          (__eo_to_smt (__str_nary_elim (mkConcat tHead tMiddle))) =
        SmtType.Seq T)
    (hSAppendTy :
      __smtx_typeof
          (__eo_to_smt
            (strConcatUnifyRevAppend sHead sMiddle suffix)) =
        SmtType.Seq T)
    (hTAppendTy :
      __smtx_typeof
          (__eo_to_smt
            (strConcatUnifyRevAppend tHead tMiddle suffix)) =
        SmtType.Seq T)
    (hSMiddleList :
      __eo_is_list (Term.UOp UserOp.str_concat) sMiddle =
        Term.Boolean true)
    (hTMiddleList :
      __eo_is_list (Term.UOp UserOp.str_concat) tMiddle =
        Term.Boolean true)
    (hSMiddleCases :
      (__eo_is_list_nil (Term.UOp UserOp.str_concat) sMiddle =
          Term.Boolean true) ∨
        (__eo_is_list_nil (Term.UOp UserOp.str_concat) sMiddle =
            Term.Boolean false ∧
          __smtx_typeof (__eo_to_smt sMiddle) = SmtType.Seq T))
    (hTMiddleCases :
      (__eo_is_list_nil (Term.UOp UserOp.str_concat) tMiddle =
          Term.Boolean true) ∨
        (__eo_is_list_nil (Term.UOp UserOp.str_concat) tMiddle =
            Term.Boolean false ∧
          __smtx_typeof (__eo_to_smt tMiddle) = SmtType.Seq T)) :
    eo_interprets M
      (strConcatUnifyRevConclusion
        suffix sHead sMiddle tHead tMiddle) true := by
  let sNorm := __str_nary_elim (mkConcat sHead sMiddle)
  let tNorm := __str_nary_elim (mkConcat tHead tMiddle)
  let sAppend := strConcatUnifyRevAppend sHead sMiddle suffix
  let tAppend := strConcatUnifyRevAppend tHead tMiddle suffix
  have hSAppendRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt sAppend))
      (__smtx_model_eval M (__eo_to_smt (mkConcat sNorm suffix))) := by
    simpa [sAppend, sNorm] using
      smt_value_rel_str_concat_unify_rev_append M hM
        sHead sMiddle suffix T hSHeadTy hSuffixTy hSAppendTy
        hSMiddleList hSMiddleCases
  have hTAppendRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt tAppend))
      (__smtx_model_eval M (__eo_to_smt (mkConcat tNorm suffix))) := by
    simpa [tAppend, tNorm] using
      smt_value_rel_str_concat_unify_rev_append M hM
        tHead tMiddle suffix T hTHeadTy hSuffixTy hTAppendTy
        hTMiddleList hTMiddleCases
  have hConcatIff :
      RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt (mkConcat sNorm suffix)))
          (__smtx_model_eval M (__eo_to_smt (mkConcat tNorm suffix))) ↔
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt sNorm))
          (__smtx_model_eval M (__eo_to_smt tNorm)) := by
    constructor
    · exact smt_value_rel_str_concat_right_cancel M hM
        suffix sNorm tNorm T hSuffixTy hSNormTy hTNormTy
    · exact smt_value_rel_str_concat_left_congr M hM
        sNorm tNorm suffix T hSNormTy hTNormTy hSuffixTy
  have hLeftIff :
      RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt sAppend))
          (__smtx_model_eval M (__eo_to_smt tAppend)) ↔
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt sNorm))
          (__smtx_model_eval M (__eo_to_smt tNorm)) := by
    constructor
    · intro h
      apply hConcatIff.mp
      exact RuleProofs.smt_value_rel_trans _ _ _
        (RuleProofs.smt_value_rel_symm _ _ hSAppendRel)
        (RuleProofs.smt_value_rel_trans _ _ _ h hTAppendRel)
    · intro h
      have hConcat := hConcatIff.mpr h
      exact RuleProofs.smt_value_rel_trans _ _ _ hSAppendRel
        (RuleProofs.smt_value_rel_trans _ _ _ hConcat
          (RuleProofs.smt_value_rel_symm _ _ hTAppendRel))
  have hEvalEq :
      __smtx_model_eval M
          (__eo_to_smt
            (strConcatUnifyRevLeftEq
              suffix sHead sMiddle tHead tMiddle)) =
        __smtx_model_eval M
          (__eo_to_smt
            (strConcatUnifyRevRightEq
              sHead sMiddle tHead tMiddle)) := by
    change __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt sAppend) (__eo_to_smt tAppend)) =
      __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt sNorm) (__eo_to_smt tNorm))
    rw [smtx_eval_eq_term_eq, smtx_eval_eq_term_eq]
    exact smtx_model_eval_eq_eq_of_rel_iff _ _ _ _ hLeftIff
  have hBool := eo_has_bool_type_str_concat_unify_rev
    suffix sHead sMiddle tHead tMiddle T
      hSNormTy hTNormTy hSAppendTy hTAppendTy
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M
        (__eo_to_smt
          (strConcatUnifyRevRightEq sHead sMiddle tHead tMiddle)))

theorem eo_interprets_str_concat_unify_base_rev
    (M : SmtModel) (hM : model_wf M)
    (suffix head middle A : Term) (T : SmtType)
    (hSuffixTy :
      __smtx_typeof (__eo_to_smt suffix) = SmtType.Seq T)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hEmptyTy :
      __smtx_typeof (__eo_to_smt (strConcatUnifyBaseEmpty A)) =
        SmtType.Seq T)
    (hElimTy :
      __smtx_typeof
          (__eo_to_smt (__str_nary_elim (mkConcat head middle))) =
        SmtType.Seq T)
    (hAppendTy :
      __smtx_typeof
          (__eo_to_smt
            (strConcatUnifyRevAppend head middle suffix)) =
        SmtType.Seq T)
    (hMiddleList :
      __eo_is_list (Term.UOp UserOp.str_concat) middle =
        Term.Boolean true)
    (hMiddleCases :
      (__eo_is_list_nil (Term.UOp UserOp.str_concat) middle =
          Term.Boolean true) ∨
        (__eo_is_list_nil (Term.UOp UserOp.str_concat) middle =
            Term.Boolean false ∧
          __smtx_typeof (__eo_to_smt middle) = SmtType.Seq T)) :
    eo_interprets M
      (strConcatUnifyBaseRevConclusion suffix head middle A) true := by
  let empty := strConcatUnifyBaseEmpty A
  let norm := __str_nary_elim (mkConcat head middle)
  let appended := strConcatUnifyRevAppend head middle suffix
  have hEmptyNe : empty ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_seq empty T hEmptyTy
  have hEmptyNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) empty =
        Term.Boolean true := by
    simpa [empty, strConcatUnifyBaseEmpty] using
      eo_is_list_nil_str_concat_seq_empty_of_ne_stuck
        (Term.Apply Term.Seq A) hEmptyNe
  have hNormTy : __smtx_typeof (__eo_to_smt norm) = SmtType.Seq T := by
    simpa [norm] using hElimTy
  have hAppendRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt appended))
      (__smtx_model_eval M (__eo_to_smt (mkConcat norm suffix))) := by
    simpa [appended, norm] using
      smt_value_rel_str_concat_unify_rev_append M hM head middle suffix T
        hHeadTy hSuffixTy hAppendTy hMiddleList hMiddleCases
  have hEmptySuffixRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat empty suffix)))
      (__smtx_model_eval M (__eo_to_smt suffix)) :=
    smt_value_rel_str_concat_list_nil_left_empty M hM empty suffix T
      hEmptyNil hEmptyTy hSuffixTy
  have hCoreIff :
      RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt suffix))
          (__smtx_model_eval M (__eo_to_smt (mkConcat norm suffix))) ↔
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt empty))
          (__smtx_model_eval M (__eo_to_smt norm)) := by
    constructor
    · intro h
      have hConcatRel : RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt (mkConcat empty suffix)))
          (__smtx_model_eval M (__eo_to_smt (mkConcat norm suffix))) :=
        RuleProofs.smt_value_rel_trans _ _ _ hEmptySuffixRel h
      exact smt_value_rel_str_concat_right_cancel M hM suffix empty norm T
        hSuffixTy hEmptyTy hNormTy hConcatRel
    · intro h
      have hConcatRel := smt_value_rel_str_concat_left_congr M hM
        empty norm suffix T hEmptyTy hNormTy hSuffixTy h
      exact RuleProofs.smt_value_rel_trans _ _ _
        (RuleProofs.smt_value_rel_symm _ _ hEmptySuffixRel) hConcatRel
  have hLeftIff :
      RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt suffix))
          (__smtx_model_eval M (__eo_to_smt appended)) ↔
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt empty))
          (__smtx_model_eval M (__eo_to_smt norm)) := by
    constructor
    · intro h
      apply hCoreIff.mp
      exact RuleProofs.smt_value_rel_trans _ _ _ h hAppendRel
    · intro h
      have hCore := hCoreIff.mpr h
      exact RuleProofs.smt_value_rel_trans _ _ _ hCore
        (RuleProofs.smt_value_rel_symm _ _ hAppendRel)
  have hEvalEq :
      __smtx_model_eval M
          (__eo_to_smt
            (strConcatUnifyBaseRevLeftEq suffix head middle)) =
        __smtx_model_eval M
          (__eo_to_smt (strConcatUnifyBaseRightEq head middle A)) := by
    change __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt suffix) (__eo_to_smt appended)) =
      __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt empty) (__eo_to_smt norm))
    rw [smtx_eval_eq_term_eq, smtx_eval_eq_term_eq]
    exact smtx_model_eval_eq_eq_of_rel_iff _ _ _ _ hLeftIff
  have hBool := eo_has_bool_type_str_concat_unify_base_rev
    suffix head middle A T hSuffixTy hEmptyTy hElimTy hAppendTy
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M
        (__eo_to_smt (strConcatUnifyBaseRightEq head middle A)))

end StrConcatUnifySupport
