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

private abbrev noChangePremise (pat repl : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq pat) repl))
    (Term.Boolean false)

private abbrev noChangeValue (x pat repl : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace x) pat) repl

private abbrev noChangeLhs (x pat repl : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (noChangeValue x pat repl)) x

private abbrev noChangeRhs (x pat : Term) : Term :=
  Term.Apply Term.not (Term.Apply (Term.Apply Term.str_contains x) pat)

private abbrev noChangeConclusion (x pat repl : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (noChangeLhs x pat repl))
    (noChangeRhs x pat)

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

private theorem smtx_eval_str_contains_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_contains x y) =
      __smtx_model_eval_str_contains
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_boolean_term_eq (M : SmtModel) (b : native_Bool) :
    __smtx_model_eval M (SmtTerm.Boolean b) = SmtValue.Boolean b := by
  rw [__smtx_model_eval.eq_def]

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

private theorem native_seq_prefix_eq_nil_left (xs : List SmtValue) :
    native_seq_prefix_eq [] xs = true := by
  cases xs <;> rfl

private theorem native_seq_indexof_rec_empty_succ
    (xs : List SmtValue) (i fuel : Nat) :
    native_seq_indexof_rec xs [] i (fuel + 1) = Int.ofNat i := by
  unfold native_seq_indexof_rec
  rw [if_pos (native_seq_prefix_eq_nil_left xs)]

private theorem native_seq_indexof_empty_zero (xs : List SmtValue) :
    native_seq_indexof xs [] 0 = 0 := by
  unfold native_seq_indexof
  simp
  exact native_seq_indexof_rec_empty_succ xs 0 xs.length

private theorem native_seq_replace_eq_self_of_contains_false
    (xs pat repl : List SmtValue)
    (hContains : native_seq_contains xs pat = false) :
    native_seq_replace xs pat repl = xs := by
  have hNot : ¬ 0 ≤ native_seq_indexof xs pat 0 := by
    unfold native_seq_contains at hContains
    simpa using hContains
  have hNeg := Int.lt_of_not_ge hNot
  cases pat with
  | nil =>
      rw [native_seq_indexof_empty_zero xs] at hNeg
      exact False.elim (Int.lt_irrefl 0 hNeg)
  | cons p ps =>
      simp [native_seq_replace, hNeg]

private theorem native_seq_replace_eq_self_iff_contains_false
    (xs pat repl : List SmtValue) (hPatRepl : pat ≠ repl) :
    native_seq_replace xs pat repl = xs ↔
      native_seq_contains xs pat = false := by
  constructor
  · intro hReplace
    cases hContains : native_seq_contains xs pat with
    | false => rfl
    | true =>
        exfalso
        have hNonneg : 0 ≤ native_seq_indexof xs pat 0 := by
          unfold native_seq_contains at hContains
          exact of_decide_eq_true hContains
        cases pat with
        | nil =>
            have hExpanded : repl ++ xs = xs := by
              simpa [native_seq_replace] using hReplace
            have hLen := congrArg List.length hExpanded
            have hReplNil : repl = [] := by
              apply List.eq_nil_of_length_eq_zero
              simp only [List.length_append] at hLen
              omega
            exact hPatRepl hReplNil.symm
        | cons p ps =>
            let n := Int.toNat (native_seq_indexof xs (p :: ps) 0)
            have hNotNeg : ¬ native_seq_indexof xs (p :: ps) 0 < 0 :=
              Int.not_lt_of_ge hNonneg
            have hExpanded :
                xs.take n ++ repl ++ xs.drop (n + (p :: ps).length) =
                  xs := by
              simpa [native_seq_replace, hNotNeg, n] using hReplace
            have hDecomp :
                xs.take n ++ (p :: ps) ++
                    xs.drop (n + (p :: ps).length) =
                  xs := by
              simpa [n] using
                native_seq_indexof_zero_decomp_take_drop xs (p :: ps)
                  hNonneg
            have hBoth := hExpanded.trans hDecomp.symm
            have hBoth' :
                xs.take n ++
                    (repl ++ xs.drop (n + (p :: ps).length)) =
                  xs.take n ++
                    ((p :: ps) ++ xs.drop (n + (p :: ps).length)) := by
              simpa [List.append_assoc] using hBoth
            have hTail :
                repl ++ xs.drop (n + (p :: ps).length) =
                  (p :: ps) ++ xs.drop (n + (p :: ps).length) := by
              exact List.append_cancel_left hBoth'
            have hEq : repl = p :: ps := List.append_cancel_right hTail
            exact hPatRepl hEq.symm
  · exact native_seq_replace_eq_self_of_contains_false xs pat repl

private theorem prog_str_eq_repl_no_change_info
    (x pat repl P : Term)
    (hProg : __eo_prog_str_eq_repl_no_change x pat repl (Proof.pf P) ≠
      Term.Stuck) :
    ∃ pat0 repl0,
      P = noChangePremise pat0 repl0 ∧
      pat0 = pat ∧ repl0 = repl ∧
      __eo_prog_str_eq_repl_no_change x pat repl (Proof.pf P) =
        noChangeConclusion x pat repl := by
  unfold __eo_prog_str_eq_repl_no_change at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    have hEq :=
      RuleProofs.eqs_of_requires_and_eq_true_not_stuck _ _ _ _ _ hProg
    rcases hEq with ⟨hPat, hRepl⟩
    subst_vars
    refine ⟨_, _, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_eq_repl_no_change, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, noChangeConclusion, noChangeLhs, noChangeRhs,
      noChangeValue]

private theorem typed___eo_prog_str_eq_repl_no_change_impl
    (x pat repl P : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hPatTrans : RuleProofs.eo_has_smt_translation pat)
    (hReplTrans : RuleProofs.eo_has_smt_translation repl)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hPatTy : __eo_typeof pat = Term.Apply Term.Seq T)
    (hReplTy : __eo_typeof repl = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_eq_repl_no_change x pat repl (Proof.pf P) =
        noChangeConclusion x pat repl) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_eq_repl_no_change x pat repl (Proof.pf P)) := by
  let value := noChangeValue x pat repl
  let lhs := noChangeLhs x pat repl
  let contains := Term.Apply (Term.Apply Term.str_contains x) pat
  let rhs := noChangeRhs x pat
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hPatSmtTy := smtx_typeof_of_eo_seq pat T hPatTrans hPatTy
  have hReplSmtTy := smtx_typeof_of_eo_seq repl T hReplTrans hReplTy
  have hValueTy :
      __smtx_typeof (__eo_to_smt value) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt pat)
          (__eo_to_smt repl)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq]
    simp [hXSmtTy, hPatSmtTy, hReplSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type value x
      (by rw [hValueTy, hXSmtTy]) (by rw [hValueTy]; simp)
  have hContainsTy : __smtx_typeof (__eo_to_smt contains) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt pat)) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hXSmtTy, hPatSmtTy, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.not (__eo_to_smt contains)) = SmtType.Bool
    rw [typeof_not_eq, hContainsTy]
    simp [native_ite, native_Teq]
  have hBool : RuleProofs.eo_has_bool_type (noChangeConclusion x pat repl) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem facts___eo_prog_str_eq_repl_no_change_impl
    (M : SmtModel) (hM : model_wf M) (x pat repl P : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hPatTrans : RuleProofs.eo_has_smt_translation pat)
    (hReplTrans : RuleProofs.eo_has_smt_translation repl)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hPatTy : __eo_typeof pat = Term.Apply Term.Seq T)
    (hReplTy : __eo_typeof repl = Term.Apply Term.Seq T)
    (hPrem : eo_interprets M (noChangePremise pat repl) true)
    (hProgEq :
      __eo_prog_str_eq_repl_no_change x pat repl (Proof.pf P) =
        noChangeConclusion x pat repl) :
    eo_interprets M
      (__eo_prog_str_eq_repl_no_change x pat repl (Proof.pf P)) true := by
  let lhs := noChangeLhs x pat repl
  let rhs := noChangeRhs x pat
  have hBool : RuleProofs.eo_has_bool_type
      (noChangeConclusion x pat repl) := by
    simpa [hProgEq] using
      typed___eo_prog_str_eq_repl_no_change_impl x pat repl P
        hXTrans hPatTrans hReplTrans hXTy hPatTy hReplTy hProgEq
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hPatSmtTy := smtx_typeof_of_eo_seq pat T hPatTrans hPatTy
  have hReplSmtTy := smtx_typeof_of_eo_seq repl T hReplTrans hReplTy
  have hXEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        rw [hXSmtTy]
        simp)
  have hPatEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt pat)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hPatSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt pat) (by
        unfold term_has_non_none_type
        rw [hPatSmtTy]
        simp)
  have hReplEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt repl)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hReplSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt repl) (by
        unfold term_has_non_none_type
        rw [hReplSmtTy]
        simp)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  rcases seq_value_canonical hPatEvalTy with ⟨spat, hPatEval⟩
  rcases seq_value_canonical hReplEvalTy with ⟨srepl, hReplEval⟩
  have hSpatTy :
      __smtx_typeof_seq_value spat = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hPatEval] using hPatEvalTy
  have hSreplTy :
      __smtx_typeof_seq_value srepl = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hReplEval] using hReplEvalTy
  have hSpatElem : __smtx_elem_typeof_seq_value spat = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSpatTy
  have hSreplElem : __smtx_elem_typeof_seq_value srepl = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSreplTy
  have hSeqNe : spat ≠ srepl := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.eq (__eo_to_smt pat) (__eo_to_smt repl))
              (SmtTerm.Boolean false)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_eq_term_eq, hPatEval,
          hReplEval, smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_eq, native_veq] using hEval
  have hListsNe : native_unpack_seq spat ≠ native_unpack_seq srepl := by
    intro hLists
    apply hSeqNe
    calc
      spat = native_pack_seq (__smtx_elem_typeof_seq_value spat)
          (native_unpack_seq spat) := (native_pack_unpack_seq spat).symm
      _ = native_pack_seq (__smtx_elem_typeof_seq_value srepl)
          (native_unpack_seq srepl) := by rw [hSpatElem, hSreplElem, hLists]
      _ = srepl := native_pack_unpack_seq srepl
  have hSxTy :
      __smtx_typeof_seq_value sx = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hXEval] using hXEvalTy
  have hSxElem : __smtx_elem_typeof_seq_value sx = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSxTy
  have hPackedEqIff :
      native_pack_seq (__smtx_elem_typeof_seq_value sx)
          (native_seq_replace (native_unpack_seq sx) (native_unpack_seq spat)
            (native_unpack_seq srepl)) = sx ↔
        native_seq_replace (native_unpack_seq sx) (native_unpack_seq spat)
            (native_unpack_seq srepl) = native_unpack_seq sx := by
    constructor
    · intro hEq
      have := congrArg native_unpack_seq hEq
      simpa [Smtm.native_unpack_pack_seq] using this
    · intro hEq
      rw [hEq]
      exact native_pack_unpack_seq sx
  have hReplaceIff :
      native_seq_replace (native_unpack_seq sx) (native_unpack_seq spat)
          (native_unpack_seq srepl) = native_unpack_seq sx ↔
        native_seq_contains (native_unpack_seq sx) (native_unpack_seq spat) =
          false :=
    native_seq_replace_eq_self_iff_contains_false _ _ _ hListsNe
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.eq
          (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt pat)
            (__eo_to_smt repl))
          (__eo_to_smt x)) =
      __smtx_model_eval M
        (SmtTerm.not
          (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt pat)))
    rw [smtx_eval_eq_term_eq, smtx_eval_str_replace_term_eq,
      smtx_eval_not_term_eq, smtx_eval_str_contains_term_eq,
      hXEval, hPatEval, hReplEval]
    simp [__smtx_model_eval_str_replace, __smtx_model_eval_str_contains,
      __smtx_model_eval_eq, __smtx_model_eval_not, native_veq,
      SmtEval.native_not, hPackedEqIff, hReplaceIff]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_eq_repl_no_change_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_eq_repl_no_change args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_eq_repl_no_change args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_eq_repl_no_change args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_eq_repl_no_change args premises ≠
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
              | cons _ _ => exact absurd rfl hProg
              | nil =>
                  cases premises with
                  | nil => exact absurd rfl hProg
                  | cons n premises =>
                      cases premises with
                      | cons _ _ => exact absurd rfl hProg
                      | nil =>
                          let P := __eo_state_proven_nth s n
                          have hA1Trans :
                              RuleProofs.eo_has_smt_translation a1 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk]
                              using hCmdTrans.1
                          have hA2Trans :
                              RuleProofs.eo_has_smt_translation a2 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk]
                              using hCmdTrans.2.1
                          have hA3Trans :
                              RuleProofs.eo_has_smt_translation a3 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk]
                              using hCmdTrans.2.2.1
                          change __eo_typeof
                              (__eo_prog_str_eq_repl_no_change a1 a2 a3
                                (Proof.pf P)) = Term.Bool at hResultTy
                          have hRuleProg :
                              __eo_prog_str_eq_repl_no_change a1 a2 a3
                                  (Proof.pf P) ≠ Term.Stuck :=
                            term_ne_stuck_of_typeof_bool hResultTy
                          rcases prog_str_eq_repl_no_change_info
                              a1 a2 a3 P hRuleProg with
                            ⟨pat0, repl0, hPremShape, hPat0, hRepl0, hProgEq⟩
                          subst pat0
                          subst repl0
                          rw [hProgEq] at hResultTy
                          have hOuterLeftTy :
                              __eo_typeof (noChangeLhs a1 a2 a3) ≠
                                Term.Stuck := by
                            change __eo_typeof_eq
                                (__eo_typeof (noChangeLhs a1 a2 a3))
                                (__eo_typeof (noChangeRhs a1 a2)) =
                              Term.Bool at hResultTy
                            exact
                              (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                (__eo_typeof (noChangeLhs a1 a2 a3))
                                (__eo_typeof (noChangeRhs a1 a2))
                                hResultTy).1
                          have hInnerLeftBool :
                              __eo_typeof (noChangeLhs a1 a2 a3) =
                                Term.Bool := by
                            change __eo_typeof_eq
                                (__eo_typeof (noChangeValue a1 a2 a3))
                                (__eo_typeof a1) = Term.Bool
                            exact eo_typeof_eq_nonstuck_bool _ _ hOuterLeftTy
                          have hValueTy :
                              __eo_typeof (noChangeValue a1 a2 a3) ≠
                                Term.Stuck := by
                            change __eo_typeof_eq
                                (__eo_typeof (noChangeValue a1 a2 a3))
                                (__eo_typeof a1) = Term.Bool at hInnerLeftBool
                            exact
                              (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                (__eo_typeof (noChangeValue a1 a2 a3))
                                (__eo_typeof a1) hInnerLeftBool).1
                          rcases eo_typeof_str_replace_args_of_ne_stuck
                              (__eo_typeof a1) (__eo_typeof a2)
                              (__eo_typeof a3) hValueTy with
                            ⟨T, hA1Ty, hA2Ty, hA3Ty⟩
                          refine ⟨?_, ?_⟩
                          · intro hTrue
                            have hPremRaw : eo_interprets M P true :=
                              hTrue P (by simp [P, premiseTermList])
                            have hPrem :
                                eo_interprets M
                                  (noChangePremise a2 a3) true := by
                              simpa [hPremShape] using hPremRaw
                            exact facts___eo_prog_str_eq_repl_no_change_impl
                              M hM a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                              hA1Ty hA2Ty hA3Ty hPrem hProgEq
                          · exact
                              RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                (typed___eo_prog_str_eq_repl_no_change_impl
                                  a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                                  hA1Ty hA2Ty hA3Ty hProgEq)
