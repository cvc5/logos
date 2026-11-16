module

public import Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
import all Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
public import Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
import all Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
public import Cpc.Proofs.RuleSupport.StrConcatUnifySupport
import all Cpc.Proofs.RuleSupport.StrConcatUnifySupport
public import Cpc.Proofs.RuleSupport.StrIndexofStripSupport
import all Cpc.Proofs.RuleSupport.StrIndexofStripSupport

open Eo
open SmtEval
open Smtm
open StrEqReplSupport
open StrContainsReplCharSupport
open StrIndexofStripSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev stripPrefixLenPremise (s n : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len s)) n

private abbrev stripPrefixContainsPremise (s t : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains s) t))
    (Term.Boolean true)

private abbrev stripPrefixGenTail (s₁ s₂ : Term) : Term :=
  __eo_mk_apply (Term.Apply Term.str_concat s₂)
    (__eo_nil Term.str_concat (__eo_typeof s₁))

private abbrev stripPrefixRhs (s₁ s₂ t : Term) : Term :=
  Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len s₁))
    (Term.Apply
      (Term.Apply Term.plus
        (Term.Apply (Term.Apply (Term.Apply Term.str_indexof s₂) t)
          (Term.Numeral 0)))
      (Term.Numeral 0))

private abbrev stripPrefixGenConclusion (s₁ s₂ t n : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply Term.eq
      (__eo_mk_apply
        (__eo_mk_apply
          (__eo_mk_apply Term.str_indexof
            (__eo_mk_apply (Term.Apply Term.str_concat s₁)
              (stripPrefixGenTail s₁ s₂))) t) n))
    (stripPrefixRhs s₁ s₂ t)

private abbrev stripPrefixLhs (s₁ s₂ t n : Term) : Term :=
  Term.Apply
    (Term.Apply
      (Term.Apply Term.str_indexof
        (Term.Apply (Term.Apply Term.str_concat s₁)
          (Term.Apply (Term.Apply Term.str_concat s₂)
            (__seq_empty (__eo_typeof s₁))))) t) n

private abbrev stripPrefixConclusion (s₁ s₂ t n : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (stripPrefixLhs s₁ s₂ t n))
    (stripPrefixRhs s₁ s₂ t)

private theorem eqs4_of_requires_nested_and_eq_true_not_stuck
    (x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ B : Term)
    (h :
      __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and (__eo_eq x₁ y₁) (__eo_eq x₂ y₂))
            (__eo_eq x₃ y₃))
          (__eo_eq x₄ y₄))
        (Term.Boolean true) B ≠ Term.Stuck) :
    y₁ = x₁ ∧ y₂ = x₂ ∧ y₃ = x₃ ∧ y₄ = x₄ := by
  have hGuard := support_eo_requires_cond_eq_of_non_stuck h
  have h₃₄ := eo_and_eq_true_parts _ _ hGuard
  have h₁₂₃ := eo_and_eq_true_parts _ _ h₃₄.1
  have h₁₂ := eo_and_eq_true_parts _ _ h₁₂₃.1
  exact ⟨RuleProofs.eq_of_eo_eq_true x₁ y₁ h₁₂.1,
    RuleProofs.eq_of_eo_eq_true x₂ y₂ h₁₂.2,
    RuleProofs.eq_of_eo_eq_true x₃ y₃ h₁₂₃.2,
    RuleProofs.eq_of_eo_eq_true x₄ y₄ h₃₄.2⟩

private theorem prog_str_indexof_strip_prefix_len_info
    (s₁ s₂ t n P₁ P₂ : Term)
    (hProg :
      __eo_prog_str_indexof_strip_prefix_len s₁ s₂ t n
          (Proof.pf P₁) (Proof.pf P₂) ≠ Term.Stuck) :
    P₁ = stripPrefixLenPremise s₁ n ∧
      P₂ = stripPrefixContainsPremise s₂ t ∧
      __eo_prog_str_indexof_strip_prefix_len s₁ s₂ t n
          (Proof.pf P₁) (Proof.pf P₂) =
        stripPrefixGenConclusion s₁ s₂ t n := by
  unfold __eo_prog_str_indexof_strip_prefix_len at hProg
  split at hProg <;> try contradiction
  next heq₁ heq₂ =>
    cases heq₁
    cases heq₂
    rcases eqs4_of_requires_nested_and_eq_true_not_stuck
        _ _ _ _ _ _ _ _ _ hProg with
      ⟨hS₁, hN, hS₂, hT⟩
    subst_vars
    refine ⟨rfl, rfl, ?_⟩
    simp [__eo_prog_str_indexof_strip_prefix_len, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, stripPrefixGenConclusion, stripPrefixGenTail,
      stripPrefixRhs]

/-- From a well-typed generated conclusion, recover the argument types and the
reduced conclusion shape. -/
private theorem gen_conclusion_info
    (s₁ s₂ t n : Term)
    (hTy : __eo_typeof (stripPrefixGenConclusion s₁ s₂ t n) = Term.Bool) :
    ∃ T, __eo_typeof s₁ = Term.Apply Term.Seq T ∧
      __eo_typeof s₂ = Term.Apply Term.Seq T ∧
      __eo_typeof t = Term.Apply Term.Seq T ∧
      __eo_typeof n = Term.Int ∧
      stripPrefixGenConclusion s₁ s₂ t n =
        stripPrefixConclusion s₁ s₂ t n := by
  have hNS := term_ne_stuck_of_typeof_bool hTy
  rcases mk_apply_info _ _ hNS with ⟨hE₁, hEqL, _⟩
  rcases mk_apply_info _ _ hEqL with ⟨hE₂, _, hL⟩
  rcases mk_apply_info _ _ hL with ⟨hE₃, hL₂, _⟩
  rcases mk_apply_info _ _ hL₂ with ⟨hE₄, hL₃, _⟩
  rcases mk_apply_info _ _ hL₃ with ⟨hE₅, _, hC⟩
  rcases mk_apply_info _ _ hC with ⟨hE₆, _, hZ⟩
  have hGen :
      stripPrefixGenConclusion s₁ s₂ t n =
        Term.Apply
          (Term.Apply Term.eq
            (Term.Apply
              (Term.Apply
                (Term.Apply Term.str_indexof
                  (Term.Apply (Term.Apply Term.str_concat s₁)
                    (stripPrefixGenTail s₁ s₂))) t) n))
          (stripPrefixRhs s₁ s₂ t) := by
    simp only [stripPrefixGenConclusion] at hE₁ hE₂ hE₃ hE₄ hE₅ hE₆ ⊢
    rw [hE₁, hE₂, hE₃, hE₄, hE₅, hE₆]
  rw [hGen] at hTy
  have hOps :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy
  have hLeftNN := hOps.1
  change __eo_typeof_str_indexof
      (__eo_typeof
        (Term.Apply (Term.Apply Term.str_concat s₁)
          (stripPrefixGenTail s₁ s₂)))
      (__eo_typeof t) (__eo_typeof n) ≠ Term.Stuck at hLeftNN
  rcases eo_typeof_str_indexof_args_of_ne_stuck _ _ _ hLeftNN with
    ⟨T, hConcatTy, hTTy, hNTy⟩
  have hArgs :=
    StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
      s₁ (stripPrefixGenTail s₁ s₂) T hConcatTy
  have hNil :
      __eo_nil Term.str_concat (__eo_typeof s₁) =
        __seq_empty (__eo_typeof s₁) := by
    rw [hArgs.1]
    rfl
  have hEmptyNS : __seq_empty (__eo_typeof s₁) ≠ Term.Stuck := by
    rw [hArgs.1]
    exact seq_empty_seq_ne_stuck T
  have hTail :
      stripPrefixGenTail s₁ s₂ =
        Term.Apply (Term.Apply Term.str_concat s₂)
          (__seq_empty (__eo_typeof s₁)) := by
    simp only [stripPrefixGenTail]
    rw [hNil]
    exact (mk_apply_info _ _ (by
      rw [← hNil]
      exact hZ)).1
  have hTailTy := hArgs.2
  rw [hTail] at hTailTy
  have hArgs₂ :=
    StrConcatUnifySupport.eo_typeof_str_concat_args_of_result_seq
      s₂ (__seq_empty (__eo_typeof s₁)) T hTailTy
  refine ⟨T, hArgs.1, hArgs₂.1, hTTy, hNTy, ?_⟩
  rw [hGen, hTail]

private theorem smtx_typeof_conclusion_sides
    (s₁ s₂ t n T : Term)
    (hS₁Trans : RuleProofs.eo_has_smt_translation s₁)
    (hS₂Trans : RuleProofs.eo_has_smt_translation s₂)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hS₁Ty : __eo_typeof s₁ = Term.Apply Term.Seq T)
    (hS₂Ty : __eo_typeof s₂ = Term.Apply Term.Seq T)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int) :
    RuleProofs.eo_has_bool_type (stripPrefixConclusion s₁ s₂ t n) := by
  have hS₁SmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq s₁ T hS₁Trans hS₁Ty
  have hS₂SmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq s₂ T hS₂Trans hS₂Ty
  have hTSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hEmptyTy :=
    smtx_typeof_seq_empty_typeof_of_smt_type_seq s₁ (__eo_to_smt_type T)
      hS₁SmtTy
  have hInnerTy :
      __smtx_typeof
          (SmtTerm.str_concat (__eo_to_smt s₂)
            (__eo_to_smt (__seq_empty (__eo_typeof s₁)))) =
        SmtType.Seq (__eo_to_smt_type T) := by
    rw [typeof_str_concat_eq]
    simp [hS₂SmtTy, hEmptyTy, __smtx_typeof_seq_op_2, native_ite,
      native_Teq]
  have hConcatTy :
      __smtx_typeof
          (SmtTerm.str_concat (__eo_to_smt s₁)
            (SmtTerm.str_concat (__eo_to_smt s₂)
              (__eo_to_smt (__seq_empty (__eo_typeof s₁))))) =
        SmtType.Seq (__eo_to_smt_type T) := by
    rw [typeof_str_concat_eq]
    simp [hS₁SmtTy, hInnerTy, __smtx_typeof_seq_op_2, native_ite,
      native_Teq]
  have hLeftTy :
      __smtx_typeof (__eo_to_smt (stripPrefixLhs s₁ s₂ t n)) =
        SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.str_indexof
          (SmtTerm.str_concat (__eo_to_smt s₁)
            (SmtTerm.str_concat (__eo_to_smt s₂)
              (__eo_to_smt (__seq_empty (__eo_typeof s₁)))))
          (__eo_to_smt t) (__eo_to_smt n)) = SmtType.Int
    rw [typeof_str_indexof_eq]
    simp [hConcatTy, hTSmtTy, hNSmtTy, __smtx_typeof_str_indexof,
      native_ite, native_Teq]
  have hIdxTy :
      __smtx_typeof
          (SmtTerm.str_indexof (__eo_to_smt s₂) (__eo_to_smt t)
            (SmtTerm.Numeral 0)) = SmtType.Int := by
    rw [typeof_str_indexof_eq]
    simp [hS₂SmtTy, hTSmtTy, __smtx_typeof_str_indexof,
      native_ite, native_Teq, __smtx_typeof.eq_def]
  have hRightTy :
      __smtx_typeof (__eo_to_smt (stripPrefixRhs s₁ s₂ t)) =
        SmtType.Int := by
    change __smtx_typeof
        (SmtTerm.plus (SmtTerm.str_len (__eo_to_smt s₁))
          (SmtTerm.plus
            (SmtTerm.str_indexof (__eo_to_smt s₂) (__eo_to_smt t)
              (SmtTerm.Numeral 0))
            (SmtTerm.Numeral 0))) = SmtType.Int
    rw [typeof_plus_eq, typeof_plus_eq, typeof_str_len_eq, hIdxTy]
    simp [hS₁SmtTy, __smtx_typeof_seq_op_1_ret,
      __smtx_typeof_arith_overload_op_2, native_ite, native_Teq,
      __smtx_typeof.eq_def]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by rw [hLeftTy, hRightTy]) (by rw [hLeftTy]; simp)

private theorem facts_strip_prefix_len
    (M : SmtModel) (hM : model_wf M)
    (s₁ s₂ t n T : Term)
    (hS₁Trans : RuleProofs.eo_has_smt_translation s₁)
    (hS₂Trans : RuleProofs.eo_has_smt_translation s₂)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hS₁Ty : __eo_typeof s₁ = Term.Apply Term.Seq T)
    (hS₂Ty : __eo_typeof s₂ = Term.Apply Term.Seq T)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hPremLen : eo_interprets M (stripPrefixLenPremise s₁ n) true)
    (hPremContains :
      eo_interprets M (stripPrefixContainsPremise s₂ t) true) :
    eo_interprets M (stripPrefixConclusion s₁ s₂ t n) true := by
  have hBool :=
    smtx_typeof_conclusion_sides s₁ s₂ t n T hS₁Trans hS₂Trans hTTrans
      hNTrans hS₁Ty hS₂Ty hTTy hNTy
  have hS₁SmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq s₁ T hS₁Trans hS₁Ty
  have hS₂SmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq s₂ T hS₂Trans hS₂Ty
  have hTSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hEvalTy : ∀ (x : Term) (U : SmtType),
      __smtx_typeof (__eo_to_smt x) = U → U ≠ SmtType.None →
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) = U := by
    intro x U hx hU
    have := smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x)
      (by unfold term_has_non_none_type; rw [hx]; exact hU)
    rw [hx] at this
    exact this
  rcases seq_value_canonical
      (hEvalTy s₁ _ hS₁SmtTy (by simp)) with ⟨ss₁, hS₁Eval⟩
  rcases seq_value_canonical
      (hEvalTy s₂ _ hS₂SmtTy (by simp)) with ⟨ss₂, hS₂Eval⟩
  rcases seq_value_canonical
      (hEvalTy t _ hTSmtTy (by simp)) with ⟨st, hTEval⟩
  rcases int_value_canonical
      (hEvalTy n _ hNSmtTy (by simp)) with ⟨ni, hNEval⟩
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt (__seq_empty (__eo_typeof s₁))) =
        SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type T)) :=
    eval_seq_empty_typeof M s₁ (__eo_to_smt_type T) hS₁SmtTy
  have hNLen : ni = ((native_unpack_seq ss₁).length : Int) := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremLen
    cases hPremLen with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt s₁)) (__eo_to_smt n)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hS₁Eval,
          hNEval] at hEval
        have h := by
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_veq, native_seq_len] using hEval
        exact h.symm
  have hContains :
      native_seq_contains (native_unpack_seq ss₂) (native_unpack_seq st) =
        true := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremContains
    cases hPremContains with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.str_contains (__eo_to_smt s₂) (__eo_to_smt t))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq,
          StrContainsReplCharSupport.smtx_eval_str_contains_term_eq,
          hS₂Eval, hTEval, StrEqReplSupport.smtx_eval_boolean_term_eq]
          at hEval
        simpa [__smtx_model_eval_str_contains, __smtx_model_eval_eq,
          native_veq] using hEval
  have hCore :=
    native_seq_indexof_append_prefix_shift (native_unpack_seq ss₁)
      (native_unpack_seq ss₂) (native_unpack_seq st) 0 (by decide) (by simp)
      (by simpa using hContains)
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt (stripPrefixLhs s₁ s₂ t n)) =
        __smtx_model_eval M (__eo_to_smt (stripPrefixRhs s₁ s₂ t)) := by
    change __smtx_model_eval M
        (SmtTerm.str_indexof
          (SmtTerm.str_concat (__eo_to_smt s₁)
            (SmtTerm.str_concat (__eo_to_smt s₂)
              (__eo_to_smt (__seq_empty (__eo_typeof s₁)))))
          (__eo_to_smt t) (__eo_to_smt n)) =
      __smtx_model_eval M
        (SmtTerm.plus (SmtTerm.str_len (__eo_to_smt s₁))
          (SmtTerm.plus
            (SmtTerm.str_indexof (__eo_to_smt s₂) (__eo_to_smt t)
              (SmtTerm.Numeral 0))
            (SmtTerm.Numeral 0)))
    rw [smtx_eval_str_indexof_term_eq,
      StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      StrSubstrContainsSupport.smtx_eval_plus_term_eq,
      StrSubstrContainsSupport.smtx_eval_plus_term_eq,
      smtx_eval_str_indexof_term_eq, smtx_eval_str_len_term_eq,
      StrEqReplSupport.smtx_eval_numeral_term_eq,
      hS₁Eval, hS₂Eval, hTEval, hNEval, hEmptyEval]
    simp only [__smtx_model_eval_str_indexof, __smtx_model_eval_str_concat,
      __smtx_model_eval_plus, __smtx_model_eval_str_len, native_seq_concat,
      Smtm.native_unpack_pack_seq, native_seq_len, native_zplus]
    simp only [native_unpack_seq, List.append_nil, hNLen]
    simpa using congrArg SmtValue.Numeral hCore
  exact RuleProofs.eo_interprets_eq_of_rel M _ _ hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_str_indexof_strip_prefix_len_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_strip_prefix_len args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_indexof_strip_prefix_len args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_strip_prefix_len args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_indexof_strip_prefix_len args
          premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons s₁ args =>
  cases args with
  | nil => exact absurd rfl hProg
  | cons s₂ args =>
  cases args with
  | nil => exact absurd rfl hProg
  | cons t args =>
  cases args with
  | nil => exact absurd rfl hProg
  | cons n args =>
  cases args with
  | cons _ _ => exact absurd rfl hProg
  | nil =>
  cases premises with
  | nil => exact absurd rfl hProg
  | cons i₁ premises =>
  cases premises with
  | nil => exact absurd rfl hProg
  | cons i₂ premises =>
  cases premises with
  | cons _ _ => exact absurd rfl hProg
  | nil =>
  let P₁ := __eo_state_proven_nth s i₁
  let P₂ := __eo_state_proven_nth s i₂
  have hS₁Trans : RuleProofs.eo_has_smt_translation s₁ := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
  have hS₂Trans : RuleProofs.eo_has_smt_translation s₂ := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.1
  have hTTrans : RuleProofs.eo_has_smt_translation t := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.2.1
  have hNTrans : RuleProofs.eo_has_smt_translation n := by
    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.2.2.1
  change __eo_typeof
      (__eo_prog_str_indexof_strip_prefix_len s₁ s₂ t n (Proof.pf P₁)
        (Proof.pf P₂)) = Term.Bool at hResultTy
  have hRuleProg :
      __eo_prog_str_indexof_strip_prefix_len s₁ s₂ t n (Proof.pf P₁)
          (Proof.pf P₂) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rcases prog_str_indexof_strip_prefix_len_info s₁ s₂ t n P₁ P₂
      hRuleProg with ⟨hP₁, hP₂, hProgGen⟩
  rw [hProgGen] at hResultTy
  rcases gen_conclusion_info s₁ s₂ t n hResultTy with
    ⟨T, hS₁Ty, hS₂Ty, hTTy, hNTy, hGenEq⟩
  have hProgEq :
      __eo_prog_str_indexof_strip_prefix_len s₁ s₂ t n (Proof.pf P₁)
          (Proof.pf P₂) = stripPrefixConclusion s₁ s₂ t n := by
    rw [hProgGen, hGenEq]
  have hBool :=
    smtx_typeof_conclusion_sides s₁ s₂ t n T hS₁Trans hS₂Trans hTTrans
      hNTrans hS₁Ty hS₂Ty hTTy hNTy
  change StepRuleProperties M (premiseTermList s _)
    (__eo_prog_str_indexof_strip_prefix_len s₁ s₂ t n (Proof.pf P₁)
      (Proof.pf P₂))
  refine ⟨?_, ?_⟩
  · intro hTrue
    have hPrem₁ : eo_interprets M (stripPrefixLenPremise s₁ n) true := by
      simpa [hP₁] using hTrue P₁ (by simp [P₁, premiseTermList])
    have hPrem₂ :
        eo_interprets M (stripPrefixContainsPremise s₂ t) true := by
      simpa [hP₂] using hTrue P₂ (by simp [P₂, premiseTermList])
    rw [hProgEq]
    exact facts_strip_prefix_len M hM s₁ s₂ t n T hS₁Trans hS₂Trans
      hTTrans hNTrans hS₁Ty hS₂Ty hTTy hNTy hPrem₁ hPrem₂
  · rw [hProgEq]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hBool
