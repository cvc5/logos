module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
public import Cpc.Proofs.RuleSupport.StrEqReplSupport
import all Cpc.Proofs.RuleSupport.StrEqReplSupport
public import Cpc.Proofs.RuleSupport.StringSupport
import all Cpc.Proofs.RuleSupport.StringSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev containsReplTgtRepl (x y z : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace x) y) z

private abbrev containsReplTgtLhs (x y z : Term) : Term :=
  Term.Apply (Term.Apply Term.str_contains (containsReplTgtRepl x y z)) z

private abbrev containsReplTgtContains (x y : Term) : Term :=
  Term.Apply (Term.Apply Term.str_contains x) y

private abbrev containsReplTgtRhs (x y z : Term) : Term :=
  Term.Apply (Term.Apply Term.or (containsReplTgtContains x y))
    (Term.Apply (Term.Apply Term.or (containsReplTgtContains x z))
      (Term.Boolean false))

private abbrev containsReplTgtConclusion (x y z : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (containsReplTgtLhs x y z))
    (containsReplTgtRhs x y z)

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

private theorem eo_typeof_str_contains_args_of_ne_stuck
    (A B : Term)
    (h : __eo_typeof_str_contains A B ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U := by
  cases A <;> simp [__eo_typeof_str_contains] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_contains] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_contains] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_contains] at h ⊢
        case Apply g y =>
          cases g <;> simp [__eo_typeof_str_contains] at h ⊢
          case UOp opg =>
            cases opg <;> simp [__eo_typeof_str_contains] at h ⊢
            case Seq =>
              have hyx : y = x :=
                RuleProofs.eq_of_requires_eq_true_not_stuck x y Term.Bool h
              exact hyx

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

private theorem native_seq_prefix_eq_append (pat rest : List SmtValue) :
    native_seq_prefix_eq pat (pat ++ rest) = true := by
  induction pat with
  | nil => rfl
  | cons p ps ih =>
      have hp : native_veq p p = true := by simp [native_veq]
      simp [native_seq_prefix_eq, hp, ih]

private theorem native_seq_indexof_rec_append_ne_neg
    (pat after : List SmtValue) :
    ∀ (before : List SmtValue) (i fuel : Nat),
      before.length < fuel →
      native_seq_indexof_rec (before ++ pat ++ after) pat i fuel ≠ -1 := by
  intro before
  induction before with
  | nil =>
      intro i fuel hFuel
      cases fuel with
      | zero => simp at hFuel
      | succ f =>
          simp only [List.nil_append]
          unfold native_seq_indexof_rec
          rw [if_pos (native_seq_prefix_eq_append pat after)]
          simp
  | cons b bs ih =>
      intro i fuel hFuel
      cases fuel with
      | zero => simp at hFuel
      | succ f =>
          have hbs : bs.length < f := by
            simp only [List.length_cons] at hFuel
            omega
          unfold native_seq_indexof_rec
          by_cases hPre :
              native_seq_prefix_eq pat ((b :: bs) ++ pat ++ after) = true
          · rw [if_pos hPre]
            simp
          · rw [if_neg hPre]
            have hxs : (b :: bs) ++ pat ++ after =
                b :: (bs ++ pat ++ after) := by
              simp
            rw [hxs]
            simpa using ih (i + 1) f hbs

private theorem native_seq_contains_of_decomp
    (before pat after : List SmtValue) :
    native_seq_contains (before ++ pat ++ after) pat = true := by
  have hLen : pat.length ≤ (before ++ pat ++ after).length := by
    simp [List.length_append]
    omega
  have hNe :
      native_seq_indexof (before ++ pat ++ after) pat 0 ≠ -1 := by
    rw [native_seq_indexof_eq_rec]
    simp only [Int.reduceLT, ↓reduceIte, Int.toNat_zero, Nat.zero_add]
    rw [dif_pos hLen]
    have hFuel :
        before.length <
          (before ++ pat ++ after).length - pat.length + 1 := by
      simp [List.length_append]
      omega
    simpa using
      native_seq_indexof_rec_append_ne_neg pat after before 0
        ((before ++ pat ++ after).length - pat.length + 1) hFuel
  have hGe :
      0 ≤ native_seq_indexof (before ++ pat ++ after) pat 0 := by
    rcases native_seq_indexof_eq_neg_one_or_ge
        (before ++ pat ++ after) pat 0 with h | h
    · exact absurd h hNe
    · exact h
  unfold native_seq_contains
  exact decide_eq_true hGe

private theorem native_seq_indexof_rec_nil
    (xs : List SmtValue) (i fuel : Nat)
    (hFuel : fuel ≠ 0) :
    native_seq_indexof_rec xs [] i fuel = Int.ofNat i := by
  cases fuel with
  | zero => exact False.elim (hFuel rfl)
  | succ fuel =>
      rw [Smtm.native_seq_indexof_rec.eq_def]
      simp [native_seq_prefix_eq]

private theorem native_seq_indexof_nil_zero (xs : List SmtValue) :
    native_seq_indexof xs [] 0 = 0 := by
  unfold native_seq_indexof
  simp [native_seq_indexof_rec_nil]

private theorem native_seq_replace_eq_self_of_indexof_neg
    (xs pat repl : List SmtValue)
    (hIdxNeg : native_seq_indexof xs pat 0 < 0) :
    native_seq_replace xs pat repl = xs := by
  cases pat with
  | nil =>
      have hIdx := native_seq_indexof_nil_zero xs
      rw [hIdx] at hIdxNeg
      exact False.elim (Int.lt_irrefl 0 hIdxNeg)
  | cons p ps =>
      simp [native_seq_replace, hIdxNeg]

private theorem native_seq_replace_eq_self_of_contains_false
    (xs pat repl : List SmtValue)
    (hContains : native_seq_contains xs pat = false) :
    native_seq_replace xs pat repl = xs := by
  have hNot : ¬ 0 ≤ native_seq_indexof xs pat 0 := by
    unfold native_seq_contains at hContains
    simpa using hContains
  exact native_seq_replace_eq_self_of_indexof_neg xs pat repl
    (Int.lt_of_not_ge hNot)

private theorem native_seq_contains_replace_tgt
    (xs pat repl : List SmtValue) :
    native_seq_contains (native_seq_replace xs pat repl) repl =
      SmtEval.native_or (native_seq_contains xs pat)
        (SmtEval.native_or (native_seq_contains xs repl) false) := by
  by_cases hPat : native_seq_contains xs pat = true
  · have hLeftTrue :
        native_seq_contains (native_seq_replace xs pat repl) repl = true := by
      cases pat with
      | nil =>
          simpa [native_seq_replace, List.append_assoc] using
            native_seq_contains_of_decomp [] repl xs
      | cons p ps =>
          have hNonneg : 0 ≤ native_seq_indexof xs (p :: ps) 0 := by
            unfold native_seq_contains at hPat
            exact of_decide_eq_true hPat
          have hNotNeg : ¬ native_seq_indexof xs (p :: ps) 0 < 0 :=
            Int.not_lt_of_ge hNonneg
          rw [StrEqReplSupport.native_seq_replace_eq_indexof]
          rw [if_neg hNotNeg]
          exact native_seq_contains_of_decomp
            (xs.take (Int.toNat (native_seq_indexof xs (p :: ps) 0)))
            repl
            (xs.drop (Int.toNat (native_seq_indexof xs (p :: ps) 0) +
              (p :: ps).length))
    rw [hLeftTrue, hPat]
    cases native_seq_contains xs repl <;> simp [SmtEval.native_or]
  · have hPatFalse : native_seq_contains xs pat = false := by
      cases h : native_seq_contains xs pat
      · rfl
      · exact False.elim (hPat h)
    rw [native_seq_replace_eq_self_of_contains_false xs pat repl hPatFalse,
      hPatFalse]
    cases native_seq_contains xs repl <;> simp [SmtEval.native_or]

private theorem prog_str_contains_repl_tgt_eq
    (x y z : Term)
    (hX : x ≠ Term.Stuck) (hY : y ≠ Term.Stuck) (hZ : z ≠ Term.Stuck) :
    __eo_prog_str_contains_repl_tgt x y z =
      containsReplTgtConclusion x y z := by
  have hRaw :
      __eo_prog_str_contains_repl_tgt x y z =
        Term.Apply
          (Term.Apply Term.eq
            (Term.Apply
              (Term.Apply Term.str_contains
                (Term.Apply (Term.Apply (Term.Apply Term.str_replace x) y) z))
              z))
          (Term.Apply
            (Term.Apply Term.or
              (Term.Apply (Term.Apply Term.str_contains x) y))
            (Term.Apply
              (Term.Apply Term.or
                (Term.Apply (Term.Apply Term.str_contains x) z))
              (Term.Boolean false))) := by
    unfold __eo_prog_str_contains_repl_tgt
    split
    · exact False.elim (hX rfl)
    · exact False.elim (hY rfl)
    · exact False.elim (hZ rfl)
    · rfl
  simpa [containsReplTgtConclusion, containsReplTgtLhs,
    containsReplTgtRhs, containsReplTgtContains, containsReplTgtRepl]
    using hRaw

private theorem typed___eo_prog_str_contains_repl_tgt_impl
    (x y z : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hZTrans : RuleProofs.eo_has_smt_translation z)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hZTy : __eo_typeof z = Term.Apply Term.Seq T) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_contains_repl_tgt x y z) := by
  let repl := containsReplTgtRepl x y z
  let lhs := containsReplTgtLhs x y z
  let cxy := containsReplTgtContains x y
  let cxz := containsReplTgtContains x z
  let inner := Term.Apply (Term.Apply Term.or cxz) (Term.Boolean false)
  let rhs := containsReplTgtRhs x y z
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hZSmtTy := smtx_typeof_of_eo_seq z T hZTrans hZTy
  have hReplSmtTy :
      __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt z)) =
      SmtType.Seq (__eo_to_smt_type T) := by
    rw [typeof_str_replace_eq]
    simp [hXSmtTy, hYSmtTy, hZSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hReplTy :
      __smtx_typeof (__eo_to_smt repl) = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [repl, containsReplTgtRepl, __eo_to_smt, __eo_to_smt_type, __smtx_typeof] using hReplSmtTy
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.str_contains
          (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
            (__eo_to_smt z))
          (__eo_to_smt z)) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hReplSmtTy, hZSmtTy, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hCxyTy : RuleProofs.eo_has_bool_type cxy := by
    change __smtx_typeof (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y)) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hXSmtTy, hYSmtTy, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hCxzTy : RuleProofs.eo_has_bool_type cxz := by
    change __smtx_typeof (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt z)) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hXSmtTy, hZSmtTy, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hInnerTy : RuleProofs.eo_has_bool_type inner := by
    exact RuleProofs.eo_has_bool_type_or_of_bool_args cxz (Term.Boolean false)
      hCxzTy RuleProofs.eo_has_bool_type_false
  have hRhsTy : RuleProofs.eo_has_bool_type rhs := by
    exact RuleProofs.eo_has_bool_type_or_of_bool_args cxy inner hCxyTy hInnerTy
  have hBoolEq :
      RuleProofs.eo_has_bool_type (containsReplTgtConclusion x y z) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hXNotStuck : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNotStuck : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hZNotStuck : z ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation z hZTrans
  rw [prog_str_contains_repl_tgt_eq x y z hXNotStuck hYNotStuck hZNotStuck]
  exact hBoolEq

private theorem facts___eo_prog_str_contains_repl_tgt_impl
    (M : SmtModel) (hM : model_wf M) (x y z : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hZTrans : RuleProofs.eo_has_smt_translation z)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hZTy : __eo_typeof z = Term.Apply Term.Seq T) :
    eo_interprets M (__eo_prog_str_contains_repl_tgt x y z) true := by
  let lhs := containsReplTgtLhs x y z
  let rhs := containsReplTgtRhs x y z
  have hXNotStuck : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNotStuck : y ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hZNotStuck : z ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation z hZTrans
  have hProg :
      __eo_prog_str_contains_repl_tgt x y z =
        containsReplTgtConclusion x y z :=
    prog_str_contains_repl_tgt_eq x y z hXNotStuck hYNotStuck hZNotStuck
  have hBoolEq :
      RuleProofs.eo_has_bool_type (containsReplTgtConclusion x y z) := by
    simpa [hProg] using
      typed___eo_prog_str_contains_repl_tgt_impl x y z hXTrans hYTrans
        hZTrans hXTy hYTy hZTy
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hZSmtTy := smtx_typeof_of_eo_seq z T hZTrans hZTy
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
  have hZEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt z)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hZSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt z) (by
        unfold term_has_non_none_type
        rw [hZSmtTy]
        simp)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  rcases seq_value_canonical hYEvalTy with ⟨sy, hYEval⟩
  rcases seq_value_canonical hZEvalTy with ⟨sz, hZEval⟩
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_contains
          (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
            (__eo_to_smt z))
          (__eo_to_smt z)) =
      __smtx_model_eval M
        (SmtTerm.or
          (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y))
          (SmtTerm.or
            (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt z))
            (SmtTerm.Boolean false)))
    rw [smtx_eval_str_contains_term_eq, smtx_eval_str_replace_term_eq,
      smtx_eval_or_term_eq, smtx_eval_or_term_eq,
      smtx_eval_str_contains_term_eq, smtx_eval_str_contains_term_eq]
    rw [hXEval, hYEval, hZEval]
    rw [show __smtx_model_eval M (SmtTerm.Boolean false) =
        SmtValue.Boolean false by
      rw [__smtx_model_eval.eq_def]]
    simp [__smtx_model_eval_str_contains, __smtx_model_eval_str_replace,
      __smtx_model_eval_or, SmtEval.native_or, Smtm.native_unpack_pack_seq,
      native_seq_contains_replace_tgt]
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_contains_repl_tgt_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_repl_tgt args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_contains_repl_tgt args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_repl_tgt args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_contains_repl_tgt args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  cases premises with
                  | nil =>
                      have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using
                          hCmdTrans.1
                      have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using
                          hCmdTrans.2.1
                      have hA3Trans : RuleProofs.eo_has_smt_translation a3 := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using
                          hCmdTrans.2.2.1
                      have hA1NotStuck : a1 ≠ Term.Stuck :=
                        RuleProofs.term_ne_stuck_of_has_smt_translation a1 hA1Trans
                      have hA2NotStuck : a2 ≠ Term.Stuck :=
                        RuleProofs.term_ne_stuck_of_has_smt_translation a2 hA2Trans
                      have hA3NotStuck : a3 ≠ Term.Stuck :=
                        RuleProofs.term_ne_stuck_of_has_smt_translation a3 hA3Trans
                      have hProgEq :
                          __eo_cmd_step_proven s CRule.str_contains_repl_tgt
                            (CArgList.cons a1
                              (CArgList.cons a2
                                (CArgList.cons a3 CArgList.nil)))
                            CIndexList.nil =
                            containsReplTgtConclusion a1 a2 a3 := by
                        change __eo_prog_str_contains_repl_tgt a1 a2 a3 =
                          containsReplTgtConclusion a1 a2 a3
                        exact prog_str_contains_repl_tgt_eq a1 a2 a3
                          hA1NotStuck hA2NotStuck hA3NotStuck
                      let lhs := containsReplTgtLhs a1 a2 a3
                      rw [hProgEq] at hResultTy
                      change __eo_typeof_eq (__eo_typeof lhs)
                          (__eo_typeof (containsReplTgtRhs a1 a2 a3)) =
                        Term.Bool at hResultTy
                      have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                        (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                          (__eo_typeof lhs)
                          (__eo_typeof (containsReplTgtRhs a1 a2 a3))
                          hResultTy).1
                      have hArgTypes :
                          ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                            __eo_typeof a2 = Term.Apply Term.Seq T ∧
                            __eo_typeof a3 = Term.Apply Term.Seq T := by
                        change __eo_typeof_str_contains
                            (__eo_typeof (containsReplTgtRepl a1 a2 a3))
                            (__eo_typeof a3) ≠ Term.Stuck at hLhsNotStuck
                        rcases eo_typeof_str_contains_args_of_ne_stuck
                            (__eo_typeof (containsReplTgtRepl a1 a2 a3))
                            (__eo_typeof a3) hLhsNotStuck with
                          ⟨T, hReplTy, hA3Ty⟩
                        have hReplNotStuck :
                            __eo_typeof (containsReplTgtRepl a1 a2 a3) ≠
                              Term.Stuck := by
                          rw [hReplTy]
                          simp
                        change __eo_typeof_str_replace (__eo_typeof a1)
                            (__eo_typeof a2) (__eo_typeof a3) ≠
                          Term.Stuck at hReplNotStuck
                        rcases eo_typeof_str_replace_args_of_ne_stuck
                            (__eo_typeof a1) (__eo_typeof a2)
                            (__eo_typeof a3) hReplNotStuck with
                          ⟨U, hA1Ty, hA2Ty, hA3Ty'⟩
                        rw [hA3Ty] at hA3Ty'
                        cases hA3Ty'
                        exact ⟨T, hA1Ty, hA2Ty, hA3Ty⟩
                      rcases hArgTypes with ⟨T, hA1Ty, hA2Ty, hA3Ty⟩
                      have hProps :
                          StepRuleProperties M (premiseTermList s CIndexList.nil)
                            (__eo_prog_str_contains_repl_tgt a1 a2 a3) := by
                        refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                          (typed___eo_prog_str_contains_repl_tgt_impl a1 a2 a3
                            hA1Trans hA2Trans hA3Trans hA1Ty hA2Ty hA3Ty)⟩
                        intro _hTrue
                        exact facts___eo_prog_str_contains_repl_tgt_impl M hM
                          a1 a2 a3 hA1Trans hA2Trans hA3Trans hA1Ty hA2Ty hA3Ty
                      change StepRuleProperties M []
                        (__eo_prog_str_contains_repl_tgt a1 a2 a3)
                      simpa [premiseTermList] using hProps
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
