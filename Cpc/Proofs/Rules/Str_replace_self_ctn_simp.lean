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

private abbrev replaceSelfCtnRepl (s t : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace t) s) t

private abbrev replaceSelfCtnLhs (s t : Term) : Term :=
  Term.Apply (Term.Apply Term.str_contains s) (replaceSelfCtnRepl s t)

private abbrev replaceSelfCtnRhs (s t : Term) : Term :=
  Term.Apply (Term.Apply Term.str_contains s) t

private abbrev replaceSelfCtnConclusion (s t : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (replaceSelfCtnLhs s t))
    (replaceSelfCtnRhs s t)

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

private theorem native_seq_contains_decomp_exists
    (xs pat : List SmtValue)
    (h : native_seq_contains xs pat = true) :
    ∃ before after, xs = before ++ pat ++ after := by
  have hGe : 0 ≤ native_seq_indexof xs pat 0 := by
    unfold native_seq_contains at h
    exact of_decide_eq_true h
  exact ⟨_, _, (native_seq_indexof_zero_decomp xs pat hGe).symm⟩

private theorem native_seq_contains_trans
    (xs mid pat : List SmtValue)
    (h1 : native_seq_contains xs mid = true)
    (h2 : native_seq_contains mid pat = true) :
    native_seq_contains xs pat = true := by
  rcases native_seq_contains_decomp_exists xs mid h1 with
    ⟨pre₁, post₁, hxs⟩
  rcases native_seq_contains_decomp_exists mid pat h2 with
    ⟨pre₂, post₂, hmid⟩
  subst xs
  subst mid
  simpa [List.append_assoc] using
    native_seq_contains_of_decomp (pre₁ ++ pre₂) pat (post₂ ++ post₁)

private theorem native_seq_contains_antisymm
    (xs ys : List SmtValue)
    (hxy : native_seq_contains xs ys = true)
    (hyx : native_seq_contains ys xs = true) :
    xs = ys := by
  rcases native_seq_contains_decomp_exists xs ys hxy with
    ⟨pre₁, post₁, hxs⟩
  rcases native_seq_contains_decomp_exists ys xs hyx with
    ⟨pre₂, post₂, hys⟩
  have hLen₁ :
      xs.length = pre₁.length + ys.length + post₁.length := by
    simpa [List.length_append, Nat.add_assoc] using congrArg List.length hxs
  have hLen₂ :
      ys.length = pre₂.length + xs.length + post₂.length := by
    simpa [List.length_append, Nat.add_assoc] using congrArg List.length hys
  have hPre₁ : pre₁.length = 0 := by omega
  have hPost₁ : post₁.length = 0 := by omega
  have hPreNil : pre₁ = [] := by
    cases pre₁ <;> simp at hPre₁ ⊢
  have hPostNil : post₁ = [] := by
    cases post₁ <;> simp at hPost₁ ⊢
  simpa [hPreNil, hPostNil] using hxs

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
  rw [native_seq_indexof_eq_rec]
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

private theorem native_seq_replace_id
    (xs pat : List SmtValue) :
    native_seq_replace xs pat pat = xs := by
  cases pat with
  | nil =>
      simp [native_seq_replace]
  | cons p ps =>
      by_cases hNeg : native_seq_indexof xs (p :: ps) 0 < 0
      · simp [native_seq_replace, hNeg]
      · have hNonneg : 0 ≤ native_seq_indexof xs (p :: ps) 0 :=
          int_nonneg_of_not_neg hNeg
        simpa [native_seq_replace, hNeg, List.append_assoc] using
          native_seq_indexof_zero_decomp_take_drop xs (p :: ps) hNonneg

private theorem native_seq_replace_contains_repl_of_contains
    (xs pat repl : List SmtValue)
    (hContains : native_seq_contains xs pat = true) :
    native_seq_contains (native_seq_replace xs pat repl) repl = true := by
  cases pat with
  | nil =>
      simpa [native_seq_replace, List.append_assoc] using
        native_seq_contains_of_decomp [] repl xs
  | cons p ps =>
      have hNonneg : 0 ≤ native_seq_indexof xs (p :: ps) 0 := by
        unfold native_seq_contains at hContains
        exact of_decide_eq_true hContains
      have hNotNeg : ¬ native_seq_indexof xs (p :: ps) 0 < 0 :=
        Int.not_lt_of_ge hNonneg
      rw [StrEqReplSupport.native_seq_replace_eq_indexof]
      rw [if_neg hNotNeg]
      exact native_seq_contains_of_decomp
        (xs.take (Int.toNat (native_seq_indexof xs (p :: ps) 0)))
        repl
        (xs.drop (Int.toNat (native_seq_indexof xs (p :: ps) 0) +
          (p :: ps).length))

private theorem native_seq_contains_replace_self_ctn_simp
    (s t : List SmtValue) :
    native_seq_contains s (native_seq_replace t s t) =
      native_seq_contains s t := by
  by_cases hST : native_seq_contains s t = true
  · by_cases hTS : native_seq_contains t s = true
    · have hEq : s = t := native_seq_contains_antisymm s t hST hTS
      subst s
      simp [native_seq_replace_id]
    · have hTSFalse : native_seq_contains t s = false := by
        cases h : native_seq_contains t s
        · rfl
        · exact False.elim (hTS h)
      rw [native_seq_replace_eq_self_of_contains_false t s t hTSFalse]
  · have hSTFalse : native_seq_contains s t = false := by
      cases h : native_seq_contains s t
      · rfl
      · exact False.elim (hST h)
    have hLhsFalse :
        native_seq_contains s (native_seq_replace t s t) = false := by
      cases hLhs : native_seq_contains s (native_seq_replace t s t)
      · rfl
      · exfalso
        have hLhsTrue :
            native_seq_contains s (native_seq_replace t s t) = true := by
          simpa using hLhs
        by_cases hTS : native_seq_contains t s = true
        · have hReplT :
            native_seq_contains (native_seq_replace t s t) t = true :=
            native_seq_replace_contains_repl_of_contains t s t hTS
          have hSTTrue :=
            native_seq_contains_trans s (native_seq_replace t s t) t
              hLhsTrue hReplT
          rw [hSTFalse] at hSTTrue
          contradiction
        · have hTSFalse : native_seq_contains t s = false := by
            cases h : native_seq_contains t s
            · rfl
            · exact False.elim (hTS h)
          rw [native_seq_replace_eq_self_of_contains_false t s t hTSFalse] at hLhsTrue
          rw [hSTFalse] at hLhsTrue
          contradiction
    rw [hLhsFalse, hSTFalse]

private theorem prog_str_replace_self_ctn_simp_eq
    (s t : Term)
    (hS : s ≠ Term.Stuck) (hT : t ≠ Term.Stuck) :
    __eo_prog_str_replace_self_ctn_simp s t =
      replaceSelfCtnConclusion s t := by
  have hRaw :
      __eo_prog_str_replace_self_ctn_simp s t =
        Term.Apply
          (Term.Apply Term.eq
            (Term.Apply
              (Term.Apply Term.str_contains s)
              (Term.Apply (Term.Apply (Term.Apply Term.str_replace t) s) t)))
          (Term.Apply (Term.Apply Term.str_contains s) t) := by
    unfold __eo_prog_str_replace_self_ctn_simp
    split
    · exact False.elim (hS rfl)
    · exact False.elim (hT rfl)
    · rfl
  simpa [replaceSelfCtnConclusion, replaceSelfCtnLhs,
    replaceSelfCtnRhs, replaceSelfCtnRepl] using hRaw

private theorem typed___eo_prog_str_replace_self_ctn_simp_impl
    (s t : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_replace_self_ctn_simp s t) := by
  let repl := replaceSelfCtnRepl s t
  let lhs := replaceSelfCtnLhs s t
  let rhs := replaceSelfCtnRhs s t
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hReplSmtTy :
      __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt t) (__eo_to_smt s)
          (__eo_to_smt t)) =
      SmtType.Seq (__eo_to_smt_type T) := by
    rw [typeof_str_replace_eq]
    simp [hTSmtTy, hSSmtTy, __smtx_typeof_seq_op_3, native_ite,
      native_Teq]
  have hReplTy :
      __smtx_typeof (__eo_to_smt repl) = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [repl, replaceSelfCtnRepl, __eo_to_smt, __eo_to_smt_type, __smtx_typeof] using hReplSmtTy
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.str_contains (__eo_to_smt s)
          (SmtTerm.str_replace (__eo_to_smt t) (__eo_to_smt s)
            (__eo_to_smt t))) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hSSmtTy, hReplSmtTy, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.str_contains (__eo_to_smt s) (__eo_to_smt t)) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hSSmtTy, hTSmtTy, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (replaceSelfCtnConclusion s t) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hSNotStuck : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hTNotStuck : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  rw [prog_str_replace_self_ctn_simp_eq s t hSNotStuck hTNotStuck]
  exact hBoolEq

private theorem facts___eo_prog_str_replace_self_ctn_simp_impl
    (M : SmtModel) (hM : model_wf M) (s t : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T) :
    eo_interprets M (__eo_prog_str_replace_self_ctn_simp s t) true := by
  let lhs := replaceSelfCtnLhs s t
  let rhs := replaceSelfCtnRhs s t
  have hSNotStuck : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hTNotStuck : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hProg :
      __eo_prog_str_replace_self_ctn_simp s t =
        replaceSelfCtnConclusion s t :=
    prog_str_replace_self_ctn_simp_eq s t hSNotStuck hTNotStuck
  have hBoolEq :
      RuleProofs.eo_has_bool_type (replaceSelfCtnConclusion s t) := by
    simpa [hProg] using
      typed___eo_prog_str_replace_self_ctn_simp_impl s t hSTrans hTTrans
        hSTy hTTy
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hSSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSSmtTy]
        simp)
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hTSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTSmtTy]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases seq_value_canonical hTEvalTy with ⟨ts, hTEval⟩
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_contains (__eo_to_smt s)
          (SmtTerm.str_replace (__eo_to_smt t) (__eo_to_smt s)
            (__eo_to_smt t))) =
      __smtx_model_eval M
        (SmtTerm.str_contains (__eo_to_smt s) (__eo_to_smt t))
    rw [smtx_eval_str_contains_term_eq, smtx_eval_str_replace_term_eq,
      smtx_eval_str_contains_term_eq]
    rw [hSEval, hTEval]
    simp [__smtx_model_eval_str_contains, __smtx_model_eval_str_replace,
      Smtm.native_unpack_pack_seq, native_seq_contains_replace_self_ctn_simp]
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_replace_self_ctn_simp_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_self_ctn_simp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_replace_self_ctn_simp args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_self_ctn_simp args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_replace_self_ctn_simp args premises ≠
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
              cases premises with
              | nil =>
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.1
                  have hA1NotStuck : a1 ≠ Term.Stuck :=
                    RuleProofs.term_ne_stuck_of_has_smt_translation a1 hA1Trans
                  have hA2NotStuck : a2 ≠ Term.Stuck :=
                    RuleProofs.term_ne_stuck_of_has_smt_translation a2 hA2Trans
                  have hProgEq :
                      __eo_cmd_step_proven s CRule.str_replace_self_ctn_simp
                        (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                        CIndexList.nil =
                        replaceSelfCtnConclusion a1 a2 := by
                    change __eo_prog_str_replace_self_ctn_simp a1 a2 =
                      replaceSelfCtnConclusion a1 a2
                    exact prog_str_replace_self_ctn_simp_eq a1 a2
                      hA1NotStuck hA2NotStuck
                  let lhs := replaceSelfCtnLhs a1 a2
                  rw [hProgEq] at hResultTy
                  change __eo_typeof_eq (__eo_typeof lhs)
                      (__eo_typeof (replaceSelfCtnRhs a1 a2)) =
                    Term.Bool at hResultTy
                  have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                      (__eo_typeof lhs) (__eo_typeof (replaceSelfCtnRhs a1 a2))
                      hResultTy).1
                  have hArgTypes :
                      ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                        __eo_typeof a2 = Term.Apply Term.Seq T := by
                    change __eo_typeof_str_contains (__eo_typeof a1)
                        (__eo_typeof (replaceSelfCtnRepl a1 a2)) ≠
                      Term.Stuck at hLhsNotStuck
                    rcases eo_typeof_str_contains_args_of_ne_stuck
                        (__eo_typeof a1)
                        (__eo_typeof (replaceSelfCtnRepl a1 a2))
                        hLhsNotStuck with
                      ⟨T, hA1Ty, hReplTy⟩
                    have hReplNotStuck :
                        __eo_typeof (replaceSelfCtnRepl a1 a2) ≠
                          Term.Stuck := by
                      rw [hReplTy]
                      simp
                    change __eo_typeof_str_replace (__eo_typeof a2)
                        (__eo_typeof a1) (__eo_typeof a2) ≠
                      Term.Stuck at hReplNotStuck
                    rcases eo_typeof_str_replace_args_of_ne_stuck
                        (__eo_typeof a2) (__eo_typeof a1)
                        (__eo_typeof a2) hReplNotStuck with
                      ⟨U, hA2Ty, hA1Ty', _hA2Ty'⟩
                    rw [hA1Ty] at hA1Ty'
                    cases hA1Ty'
                    exact ⟨T, hA1Ty, hA2Ty⟩
                  rcases hArgTypes with ⟨T, hA1Ty, hA2Ty⟩
                  have hProps :
                      StepRuleProperties M (premiseTermList s CIndexList.nil)
                        (__eo_prog_str_replace_self_ctn_simp a1 a2) := by
                    refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_str_replace_self_ctn_simp_impl a1 a2
                        hA1Trans hA2Trans hA1Ty hA2Ty)⟩
                    intro _hTrue
                    exact facts___eo_prog_str_replace_self_ctn_simp_impl M hM
                      a1 a2 hA1Trans hA2Trans hA1Ty hA2Ty
                  change StepRuleProperties M []
                    (__eo_prog_str_replace_self_ctn_simp a1 a2)
                  simpa [premiseTermList] using hProps
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
