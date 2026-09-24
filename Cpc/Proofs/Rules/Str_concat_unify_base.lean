module

public import Cpc.Proofs.RuleSupport.StrConcatUnifySupport
import all Cpc.Proofs.RuleSupport.StrConcatUnifySupport

open Eo
open SmtEval
open Smtm
open StrConcatUnifySupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev rawStrConcatUnifyBaseConclusion
    (x t1 t2 A : Term) : Term :=
  __eo_mk_apply
    (Term.Apply (Term.UOp UserOp.eq)
      (strConcatUnifyBaseLeftEq x t1 t2))
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.eq)
        (strConcatUnifyBaseEmpty A))
      (__str_nary_elim (strConcatUnifyBaseTail t1 t2)))

private theorem raw_str_concat_unify_base_eq
    (x t1 t2 A : Term)
    (h : rawStrConcatUnifyBaseConclusion x t1 t2 A ≠ Term.Stuck) :
    rawStrConcatUnifyBaseConclusion x t1 t2 A =
      strConcatUnifyBaseConclusion x t1 t2 A := by
  let empty := strConcatUnifyBaseEmpty A
  let elim := __str_nary_elim (strConcatUnifyBaseTail t1 t2)
  let f := __eo_mk_apply (Term.UOp UserOp.eq) empty
  let rhs := __eo_mk_apply f elim
  have hRhs : rhs ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq)
        (strConcatUnifyBaseLeftEq x t1 t2)) rhs
      (by simpa [rawStrConcatUnifyBaseConclusion, empty, elim, f, rhs]
        using h)
  have hF : f ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck f elim hRhs
  have eF : f = Term.Apply (Term.UOp UserOp.eq) empty :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.eq) empty hF
  have eRhs : rhs = Term.Apply f elim :=
    eo_mk_apply_eq_apply_of_ne_stuck f elim hRhs
  have eOuter :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (strConcatUnifyBaseLeftEq x t1 t2)) rhs =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (strConcatUnifyBaseLeftEq x t1 t2)) rhs :=
    eo_mk_apply_eq_apply_of_ne_stuck _ _
      (by simpa [rawStrConcatUnifyBaseConclusion, empty, elim, f, rhs]
        using h)
  change __eo_mk_apply
      (Term.Apply (Term.UOp UserOp.eq)
        (strConcatUnifyBaseLeftEq x t1 t2)) rhs =
    strConcatUnifyBaseConclusion x t1 t2 A
  rw [eOuter, eRhs, eF]

private theorem str_concat_unify_base_type_shape
    (x t1 t2 ty : Term)
    (h : __eo_prog_str_concat_unify_base x t1 t2 ty ≠ Term.Stuck) :
    ∃ A, ty = Term.Apply Term.Seq A := by
  have hx : x ≠ Term.Stuck := by
    intro hx
    subst x
    simp [__eo_prog_str_concat_unify_base] at h
  have ht1 : t1 ≠ Term.Stuck := by
    intro ht1
    subst t1
    cases x <;> simp [__eo_prog_str_concat_unify_base] at h
  have ht2 : t2 ≠ Term.Stuck := by
    intro ht2
    subst t2
    cases x <;> cases t1 <;> simp [__eo_prog_str_concat_unify_base] at h
  cases ty <;>
    simp [__eo_prog_str_concat_unify_base, hx, ht1, ht2] at h ⊢
  case Apply f A =>
    cases f <;>
      simp [__eo_prog_str_concat_unify_base, hx, ht1, ht2] at h ⊢
    case UOp op =>
      cases op <;>
        simp [__eo_prog_str_concat_unify_base, hx, ht1, ht2] at h ⊢

public theorem cmd_step_str_concat_unify_base_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_concat_unify_base args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_concat_unify_base args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_concat_unify_base args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_concat_unify_base args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons a1 args =>
      cases args with
      | nil => exact absurd rfl hProg
      | cons a2 args =>
          cases args with
          | nil => exact absurd rfl hProg
          | cons a3 args =>
              cases args with
              | nil => exact absurd rfl hProg
              | cons a4 args =>
                  cases args with
                  | cons _ _ => exact absurd rfl hProg
                  | nil =>
                      cases premises with
                      | cons _ _ => exact absurd rfl hProg
                      | nil =>
                          change __eo_typeof
                              (__eo_prog_str_concat_unify_base a1 a2 a3 a4) =
                            Term.Bool at hResultTy
                          have hRuleProg :
                              __eo_prog_str_concat_unify_base a1 a2 a3 a4 ≠
                                Term.Stuck :=
                            term_ne_stuck_of_typeof_bool hResultTy
                          rcases str_concat_unify_base_type_shape
                              a1 a2 a3 a4 hRuleProg with ⟨A, hA4⟩
                          subst a4
                          have hA1Trans :
                              RuleProofs.eo_has_smt_translation a1 := by
                            exact hCmdTrans.1
                          have hA2Trans :
                              RuleProofs.eo_has_smt_translation a2 := by
                            exact hCmdTrans.2.1
                          have hA3Trans :
                              RuleProofs.eo_has_smt_translation a3 := by
                            exact hCmdTrans.2.2.1
                          have hA1Ne :=
                            RuleProofs.term_ne_stuck_of_has_smt_translation
                              a1 hA1Trans
                          have hA2Ne :=
                            RuleProofs.term_ne_stuck_of_has_smt_translation
                              a2 hA2Trans
                          have hA3Ne :=
                            RuleProofs.term_ne_stuck_of_has_smt_translation
                              a3 hA3Trans
                          have hRawBody :
                              __eo_prog_str_concat_unify_base a1 a2 a3
                                  (Term.Apply Term.Seq A) =
                                rawStrConcatUnifyBaseConclusion
                                  a1 a2 a3 A := by
                            simp [__eo_prog_str_concat_unify_base,
                              rawStrConcatUnifyBaseConclusion,
                              strConcatUnifyBaseLeftEq,
                              strConcatUnifyBaseTail,
                              strConcatUnifyBaseEmpty, hA1Ne, hA2Ne, hA3Ne,
                              mkEq, mkConcat]
                          have hRawNe :
                              rawStrConcatUnifyBaseConclusion a1 a2 a3 A ≠
                                Term.Stuck := by
                            rw [← hRawBody]
                            exact term_ne_stuck_of_typeof_bool hResultTy
                          have hProgEq :
                              __eo_prog_str_concat_unify_base a1 a2 a3
                                  (Term.Apply Term.Seq A) =
                                strConcatUnifyBaseConclusion a1 a2 a3 A :=
                            hRawBody.trans
                              (raw_str_concat_unify_base_eq a1 a2 a3 A hRawNe)
                          have hConclusionTy :
                              __eo_typeof
                                  (strConcatUnifyBaseConclusion a1 a2 a3 A) =
                                Term.Bool := by
                            simpa [hProgEq] using hResultTy
                          rcases str_concat_unify_base_smt_types_of_eo_type
                              a1 a2 a3 A hA1Trans hA2Trans hA3Trans
                              hConclusionTy with
                            ⟨T, hA1Ty, hA2Ty, hA3Ty, hEmptyTy, hElimNe⟩
                          have hBool := eo_has_bool_type_str_concat_unify_base
                            a1 a2 a3 A T hA1Ty hA2Ty hA3Ty hEmptyTy hElimNe
                          refine ⟨?_, ?_⟩
                          · intro _hTrue
                            change eo_interprets M
                              (__eo_prog_str_concat_unify_base a1 a2 a3
                                (Term.Apply Term.Seq A)) true
                            rw [hProgEq]
                            exact eo_interprets_str_concat_unify_base M hM
                              a1 a2 a3 A T hA1Ty hA2Ty hA3Ty hEmptyTy
                              hElimNe
                          · change RuleProofs.eo_has_smt_translation
                              (__eo_prog_str_concat_unify_base a1 a2 a3
                                (Term.Apply Term.Seq A))
                            rw [hProgEq]
                            exact
                              RuleProofs.eo_has_smt_translation_of_has_bool_type
                                _ hBool
