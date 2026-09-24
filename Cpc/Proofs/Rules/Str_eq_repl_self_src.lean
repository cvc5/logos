module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
public import Cpc.Proofs.RuleSupport.StrEqReplSupport
import all Cpc.Proofs.RuleSupport.StrEqReplSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev replaceSelfSrcValue (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace x) y) x

private abbrev replaceSelfSrcLhs (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (replaceSelfSrcValue x y)) y

private abbrev replaceSelfSrcRhs (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.eq x) y

private abbrev replaceSelfSrcConclusion (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (replaceSelfSrcLhs x y))
    (replaceSelfSrcRhs x y)

private theorem eo_typeof_eq_nonstuck_bool (A B : Term)
    (h : __eo_typeof_eq A B ≠ Term.Stuck) :
    __eo_typeof_eq A B = Term.Bool := by
  cases A <;> cases B <;>
    simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
      native_not] at h ⊢
  all_goals assumption

private theorem eo_typeof_str_replace_args_of_ne_stuck
    (A B C : Term)
    (h : __eo_typeof_str_replace A B C ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U ∧
      C = Term.Apply Term.Seq U := by
  cases A <;> simp [__eo_typeof_str_replace] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_replace] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_replace] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_replace] at h ⊢
        case Apply g y =>
          cases g <;> simp [__eo_typeof_str_replace] at h ⊢
          case UOp opg =>
            cases opg <;> simp [__eo_typeof_str_replace] at h ⊢
            case Seq =>
              cases C <;> simp [__eo_typeof_str_replace] at h ⊢
              case Apply k z =>
                cases k <;> simp [__eo_typeof_str_replace] at h ⊢
                case UOp opk =>
                  cases opk <;> simp [__eo_typeof_str_replace] at h ⊢
                  case Seq =>
                    have hEq :=
                      RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                        x x y z (Term.Apply Term.Seq x) h
                    rcases hEq with ⟨hy, hz⟩
                    subst y
                    subst z
                    simp

private theorem smtx_typeof_of_eo_seq
    (a T : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Apply Term.Seq T) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type T) := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  have hComponentNN : __eo_to_smt_type T ≠ SmtType.None := by
    intro hNone
    unfold RuleProofs.eo_has_smt_translation at hTrans
    apply hTrans
    rw [hTyRaw, hTy]
    simp [TranslationProofs.eo_to_smt_type_seq,
      __smtx_typeof_guard, hNone, native_ite, native_Teq]
  rw [hTy] at hTyRaw
  rw [TranslationProofs.eo_to_smt_type_seq] at hTyRaw
  simpa using hTyRaw.trans
    (TranslationProofs.smtx_typeof_guard_of_non_none
      (__eo_to_smt_type T) (SmtType.Seq (__eo_to_smt_type T)) hComponentNN)

private theorem smtx_eval_str_replace_term_eq
    (M : SmtModel) (x y z : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_replace x y z) =
      __smtx_model_eval_str_replace
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M z) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem native_seq_replace_self
    (xs repl : List SmtValue) :
    native_seq_replace xs xs repl = repl := by
  cases xs with
  | nil => simp [native_seq_replace]
  | cons x xs =>
      simp [native_seq_replace, native_seq_indexof_self_zero]

private theorem native_seq_indexof_zero_decomp_take_drop
    (xs pat : List SmtValue)
    (hIdxNonneg : 0 ≤ native_seq_indexof xs pat 0) :
    xs.take (Int.toNat (native_seq_indexof xs pat 0)) ++ pat ++
        xs.drop (Int.toNat (native_seq_indexof xs pat 0) + pat.length) =
      xs := by
  let idx := native_seq_indexof xs pat 0
  let j := Int.toNat idx
  have hCast : Int.ofNat j = idx := Int.toNat_of_nonneg hIdxNonneg
  have hIdx : native_seq_indexof xs pat 0 = Int.ofNat j := by
    rw [hCast]
  unfold native_seq_indexof at hIdx
  by_cases hBounds : pat.length ≤ xs.length
  · simp [hBounds] at hIdx
    rcases native_seq_indexof_rec_decomp xs pat 0
        (xs.length - pat.length + 1) j hIdx with
      ⟨_hLe, before, after, hXs, hBeforeLen⟩
    have hBeforeLen' : before.length = j := by
      simpa using hBeforeLen
    change xs.take j ++ pat ++ xs.drop (j + pat.length) = xs
    rw [hXs, ← hBeforeLen']
    simp
  · simp [hBounds] at hIdx

private theorem native_seq_replace_self_src_eq_iff
    (xs pat : List SmtValue) :
    native_seq_replace xs pat xs = pat ↔ xs = pat := by
  constructor
  · intro hReplace
    cases pat with
    | nil =>
        simp [native_seq_replace] at hReplace
        exact hReplace
    | cons p ps =>
        by_cases hNeg : native_seq_indexof xs (p :: ps) 0 < 0
        · simpa [native_seq_replace, hNeg] using hReplace
        · have hNonneg : 0 ≤ native_seq_indexof xs (p :: ps) 0 :=
            int_nonneg_of_not_neg hNeg
          let n := Int.toNat (native_seq_indexof xs (p :: ps) 0)
          have hDecomp :
              xs.take n ++ (p :: ps) ++ xs.drop (n + (p :: ps).length) = xs := by
            simpa [n] using
              native_seq_indexof_zero_decomp_take_drop xs (p :: ps) hNonneg
          have hReplace' :
              xs.take n ++ xs ++ xs.drop (n + (p :: ps).length) =
                p :: ps := by
            simpa [native_seq_replace, hNeg, n] using hReplace
          have hLenReplace := congrArg List.length hReplace'
          have hLenDecomp := congrArg List.length hDecomp
          have hTakeNil : xs.take n = [] := by
            apply List.eq_nil_of_length_eq_zero
            simp only [List.length_append, List.length_cons] at hLenReplace hLenDecomp
            omega
          have hDropNil : xs.drop (n + (p :: ps).length) = [] := by
            apply List.eq_nil_of_length_eq_zero
            change (xs.drop (n + (ps.length + 1))).length = 0
            simp only [List.length_append, List.length_cons] at hLenReplace hLenDecomp
            omega
          have hDropNil' : xs.drop (n + (ps.length + 1)) = [] := by
            simpa using hDropNil
          simpa [hTakeNil, hDropNil'] using hDecomp.symm
  · intro hEq
    subst pat
    exact native_seq_replace_self xs xs

private theorem prog_str_eq_repl_self_src_eq
    (x y : Term) (hX : x ≠ Term.Stuck) (hY : y ≠ Term.Stuck) :
    __eo_prog_str_eq_repl_self_src x y =
      replaceSelfSrcConclusion x y := by
  have hRaw :
      __eo_prog_str_eq_repl_self_src x y =
        Term.Apply
          (Term.Apply Term.eq
            (Term.Apply
              (Term.Apply Term.eq
                (Term.Apply (Term.Apply (Term.Apply Term.str_replace x) y) x))
              y))
          (Term.Apply (Term.Apply Term.eq x) y) := by
    unfold __eo_prog_str_eq_repl_self_src
    split
    · exact False.elim (hX rfl)
    · exact False.elim (hY rfl)
    · rfl
  simpa [replaceSelfSrcConclusion, replaceSelfSrcLhs, replaceSelfSrcRhs,
    replaceSelfSrcValue] using hRaw

private theorem typed___eo_prog_str_eq_repl_self_src_impl
    (x y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_eq_repl_self_src x y) := by
  let repl := replaceSelfSrcValue x y
  let lhs := replaceSelfSrcLhs x y
  let rhs := replaceSelfSrcRhs x y
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hReplTy :
      __smtx_typeof (__eo_to_smt repl) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt x)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq]
    simp [hXSmtTy, hYSmtTy, __smtx_typeof_seq_op_3, native_ite, native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool := by
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type repl y
      (by rw [hReplTy, hYSmtTy]) (by rw [hReplTy]; simp)
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool := by
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type x y
      (by rw [hXSmtTy, hYSmtTy]) (by rw [hXSmtTy]; simp)
  have hConclusionTy : RuleProofs.eo_has_bool_type
      (replaceSelfSrcConclusion x y) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hXNotStuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNotStuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  rw [prog_str_eq_repl_self_src_eq x y hXNotStuck hYNotStuck]
  exact hConclusionTy

private theorem facts___eo_prog_str_eq_repl_self_src_impl
    (M : SmtModel) (hM : model_wf M) (x y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T) :
    eo_interprets M (__eo_prog_str_eq_repl_self_src x y) true := by
  let lhs := replaceSelfSrcLhs x y
  let rhs := replaceSelfSrcRhs x y
  have hXNotStuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNotStuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hProg :
      __eo_prog_str_eq_repl_self_src x y =
        replaceSelfSrcConclusion x y :=
    prog_str_eq_repl_self_src_eq x y hXNotStuck hYNotStuck
  have hBoolEq : RuleProofs.eo_has_bool_type
      (replaceSelfSrcConclusion x y) := by
    simpa [hProg] using
      typed___eo_prog_str_eq_repl_self_src_impl x y hXTrans hYTrans hXTy hYTy
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hXEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        rw [hXSmtTy]
        simp)
  have hYEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hYSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt y) (by
        unfold term_has_non_none_type
        rw [hYSmtTy]
        simp)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  rcases seq_value_canonical hYEvalTy with ⟨sy, hYEval⟩
  have hSxTy :
      __smtx_typeof_seq_value sx = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hXEval] using hXEvalTy
  have hSyTy :
      __smtx_typeof_seq_value sy = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hYEval] using hYEvalTy
  have hSxElem : __smtx_elem_typeof_seq_value sx = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSxTy
  have hSyElem : __smtx_elem_typeof_seq_value sy = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSyTy
  have hSeqEqIff :
      native_pack_seq (__smtx_elem_typeof_seq_value sx)
          (native_seq_replace (native_unpack_seq sx) (native_unpack_seq sy)
            (native_unpack_seq sx)) = sy ↔
        sx = sy := by
    constructor
    · intro hEq
      have hLists :
          native_seq_replace (native_unpack_seq sx) (native_unpack_seq sy)
              (native_unpack_seq sx) =
            native_unpack_seq sy := by
        have := congrArg native_unpack_seq hEq
        simpa [Smtm.native_unpack_pack_seq] using this
      have hUnpack : native_unpack_seq sx = native_unpack_seq sy :=
        (native_seq_replace_self_src_eq_iff _ _).mp hLists
      calc
        sx = native_pack_seq (__smtx_elem_typeof_seq_value sx)
            (native_unpack_seq sx) := (native_pack_unpack_seq sx).symm
        _ = native_pack_seq (__smtx_elem_typeof_seq_value sy)
            (native_unpack_seq sy) := by rw [hSxElem, hSyElem, hUnpack]
        _ = sy := native_pack_unpack_seq sy
    · intro hEq
      subst sy
      simp [native_seq_replace_self, native_pack_unpack_seq]
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.eq
          (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
            (__eo_to_smt x))
          (__eo_to_smt y)) =
      __smtx_model_eval M (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y))
    rw [smtx_eval_eq_term_eq, smtx_eval_str_replace_term_eq,
      smtx_eval_eq_term_eq, hXEval, hYEval]
    simp [__smtx_model_eval_str_replace, __smtx_model_eval_eq, native_veq,
      hSeqEqIff]
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_eq_repl_self_src_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_eq_repl_self_src args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_eq_repl_self_src args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_eq_repl_self_src args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_eq_repl_self_src args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons a1 args =>
      cases args with
      | nil => exact absurd rfl hProg
      | cons a2 args =>
          cases args with
          | cons _ _ => exact absurd rfl hProg
          | nil =>
              cases premises with
              | cons _ _ => exact absurd rfl hProg
              | nil =>
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using
                      hCmdTrans.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using
                      hCmdTrans.2.1
                  have hA1NotStuck :=
                    RuleProofs.term_ne_stuck_of_has_smt_translation a1 hA1Trans
                  have hA2NotStuck :=
                    RuleProofs.term_ne_stuck_of_has_smt_translation a2 hA2Trans
                  have hProgEq :
                      __eo_cmd_step_proven s CRule.str_eq_repl_self_src
                          (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                          CIndexList.nil =
                        replaceSelfSrcConclusion a1 a2 := by
                    change __eo_prog_str_eq_repl_self_src a1 a2 =
                      replaceSelfSrcConclusion a1 a2
                    exact prog_str_eq_repl_self_src_eq a1 a2 hA1NotStuck
                      hA2NotStuck
                  rw [hProgEq] at hResultTy
                  have hOuterLeftTy :
                      __eo_typeof (replaceSelfSrcLhs a1 a2) ≠ Term.Stuck := by
                    change __eo_typeof_eq
                        (__eo_typeof (replaceSelfSrcLhs a1 a2))
                        (__eo_typeof (replaceSelfSrcRhs a1 a2)) =
                      Term.Bool at hResultTy
                    exact (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                      (__eo_typeof (replaceSelfSrcLhs a1 a2))
                      (__eo_typeof (replaceSelfSrcRhs a1 a2)) hResultTy).1
                  have hInnerLeftBool :
                      __eo_typeof (replaceSelfSrcLhs a1 a2) = Term.Bool := by
                    change __eo_typeof_eq
                        (__eo_typeof (replaceSelfSrcValue a1 a2))
                        (__eo_typeof a2) = Term.Bool
                    exact eo_typeof_eq_nonstuck_bool _ _ hOuterLeftTy
                  have hReplaceTy :
                      __eo_typeof (replaceSelfSrcValue a1 a2) ≠ Term.Stuck := by
                    change __eo_typeof_eq
                        (__eo_typeof (replaceSelfSrcValue a1 a2))
                        (__eo_typeof a2) = Term.Bool at hInnerLeftBool
                    exact (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                      (__eo_typeof (replaceSelfSrcValue a1 a2))
                      (__eo_typeof a2) hInnerLeftBool).1
                  have hArgTypes :
                      ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                        __eo_typeof a2 = Term.Apply Term.Seq T := by
                    change __eo_typeof_str_replace (__eo_typeof a1)
                        (__eo_typeof a2) (__eo_typeof a1) ≠
                      Term.Stuck at hReplaceTy
                    rcases eo_typeof_str_replace_args_of_ne_stuck
                        (__eo_typeof a1) (__eo_typeof a2) (__eo_typeof a1)
                        hReplaceTy with
                      ⟨T, hA1Ty, hA2Ty, _hA1Ty'⟩
                    exact ⟨T, hA1Ty, hA2Ty⟩
                  rcases hArgTypes with ⟨T, hA1Ty, hA2Ty⟩
                  have hProps :
                      StepRuleProperties M []
                        (__eo_prog_str_eq_repl_self_src a1 a2) := by
                    refine ⟨?_,
                      RuleProofs.eo_has_smt_translation_of_has_bool_type _
                        (typed___eo_prog_str_eq_repl_self_src_impl a1 a2
                          hA1Trans hA2Trans hA1Ty hA2Ty)⟩
                    intro _hTrue
                    exact facts___eo_prog_str_eq_repl_self_src_impl M hM a1 a2
                      hA1Trans hA2Trans hA1Ty hA2Ty
                  change StepRuleProperties M []
                    (__eo_prog_str_eq_repl_self_src a1 a2)
                  simpa [premiseTermList] using hProps
