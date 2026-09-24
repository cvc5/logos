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

private abbrev replaceDualCtnPremiseS (s u : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains s) u))
    (Term.Boolean true)

private abbrev replaceDualCtnPremiseR (r u : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains r) u))
    (Term.Boolean true)

private abbrev replaceDualCtnRepl (s t r : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace s) t) r

private abbrev replaceDualCtnLhs (s t r u : Term) : Term :=
  Term.Apply (Term.Apply Term.str_contains (replaceDualCtnRepl s t r)) u

private abbrev replaceDualCtnConclusion (s t r u : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (replaceDualCtnLhs s t r u))
    (Term.Boolean true)

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

private theorem eo_typeof_str_replace_seq_same_of_ne_stuck
    (U : Term)
    (h : __eo_typeof_str_replace (Term.Apply Term.Seq U)
        (Term.Apply Term.Seq U) (Term.Apply Term.Seq U) ≠ Term.Stuck) :
    __eo_typeof_str_replace (Term.Apply Term.Seq U)
        (Term.Apply Term.Seq U) (Term.Apply Term.Seq U) =
      Term.Apply Term.Seq U := by
  cases U <;> simp [__eo_typeof_str_replace, __eo_requires, __eo_eq,
    __eo_and, native_ite, native_teq, native_and, SmtEval.native_and,
    SmtEval.native_not] at h ⊢

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

private theorem native_seq_replace_dual_ctn
    (s t r u : List SmtValue)
    (hS : native_seq_contains s u = true)
    (hR : native_seq_contains r u = true) :
    native_seq_contains (native_seq_replace s t r) u = true := by
  by_cases hT : native_seq_contains s t = true
  · exact native_seq_contains_trans (native_seq_replace s t r) r u
      (native_seq_replace_contains_repl_of_contains s t r hT) hR
  · have hTFalse : native_seq_contains s t = false := by
      cases h : native_seq_contains s t
      · rfl
      · exact False.elim (hT h)
    rw [native_seq_replace_eq_self_of_contains_false s t r hTFalse]
    exact hS

private theorem eo_and_eq_true_left {x y : Term}
    (h : __eo_and x y = Term.Boolean true) :
    x = Term.Boolean true := by
  cases x <;> cases y <;> simp [__eo_and, native_and] at h ⊢
  case Boolean.Boolean b c =>
    cases b <;> cases c <;> simp [__eo_and, native_and] at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    unfold __eo_requires at h
    cases hEq : native_teq (Term.Numeral w1) (Term.Numeral w2) <;>
      simp [native_ite, hEq] at h
    cases hOk : native_not (native_teq (Term.Numeral w1) Term.Stuck) <;>
      simp [native_ite, hOk] at h

private theorem eo_and_eq_true_right {x y : Term}
    (h : __eo_and x y = Term.Boolean true) :
    y = Term.Boolean true := by
  cases x <;> cases y <;> simp [__eo_and, native_and] at h ⊢
  case Boolean.Boolean b c =>
    cases b <;> cases c <;> simp [__eo_and, native_and] at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    unfold __eo_requires at h
    cases hEq : native_teq (Term.Numeral w1) (Term.Numeral w2) <;>
      simp [native_ite, hEq] at h
    cases hOk : native_not (native_teq (Term.Numeral w1) Term.Stuck) <;>
      simp [native_ite, hOk] at h

private theorem eqs_of_requires4_and_eq_true_not_stuck
    (x1 y1 x2 y2 x3 y3 x4 y4 B : Term) :
    __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
            (__eo_eq x3 y3))
          (__eo_eq x4 y4))
        (Term.Boolean true) B ≠ Term.Stuck ->
    y1 = x1 ∧ y2 = x2 ∧ y3 = x3 ∧ y4 = x4 := by
  intro hProg
  have hGuard :
      __eo_and
          (__eo_and
            (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
            (__eo_eq x3 y3))
          (__eo_eq x4 y4) =
        Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hProg
  have h123 :
      __eo_and
          (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
          (__eo_eq x3 y3) =
        Term.Boolean true :=
    eo_and_eq_true_left hGuard
  have h4 : __eo_eq x4 y4 = Term.Boolean true :=
    eo_and_eq_true_right hGuard
  have h12 : __eo_and (__eo_eq x1 y1) (__eo_eq x2 y2) =
      Term.Boolean true :=
    eo_and_eq_true_left h123
  have h3 : __eo_eq x3 y3 = Term.Boolean true :=
    eo_and_eq_true_right h123
  have h1 : __eo_eq x1 y1 = Term.Boolean true :=
    eo_and_eq_true_left h12
  have h2 : __eo_eq x2 y2 = Term.Boolean true :=
    eo_and_eq_true_right h12
  exact ⟨RuleProofs.eq_of_eo_eq_true x1 y1 h1,
    RuleProofs.eq_of_eo_eq_true x2 y2 h2,
    RuleProofs.eq_of_eo_eq_true x3 y3 h3,
    RuleProofs.eq_of_eo_eq_true x4 y4 h4⟩

private theorem prog_str_replace_dual_ctn_info
    (s t r u P Q : Term)
    (hProg : __eo_prog_str_replace_dual_ctn s t r u (Proof.pf P) (Proof.pf Q) ≠
      Term.Stuck) :
    ∃ s0 u0 r0 u1,
      P = replaceDualCtnPremiseS s0 u0 ∧
      Q = replaceDualCtnPremiseR r0 u1 ∧
      s0 = s ∧
      u0 = u ∧
      r0 = r ∧
      u1 = u ∧
      __eo_prog_str_replace_dual_ctn s t r u (Proof.pf P) (Proof.pf Q) =
        replaceDualCtnConclusion s t r u := by
  unfold __eo_prog_str_replace_dual_ctn at hProg
  split at hProg <;> try contradiction
  next heqP heqQ =>
    cases heqP
    cases heqQ
    have hEq :=
      eqs_of_requires4_and_eq_true_not_stuck _ _ _ _ _ _ _ _ _ hProg
    rcases hEq with ⟨hs, hu0, hr, hu1⟩
    subst_vars
    refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_replace_dual_ctn, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, replaceDualCtnConclusion, replaceDualCtnLhs,
      replaceDualCtnRepl]

private theorem typed___eo_prog_str_replace_dual_ctn_impl
    (s t r u P Q : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hUTrans : RuleProofs.eo_has_smt_translation u)
    (hTy : ∃ T, __eo_typeof s = Term.Apply Term.Seq T ∧
      __eo_typeof t = Term.Apply Term.Seq T ∧
      __eo_typeof r = Term.Apply Term.Seq T ∧
      __eo_typeof u = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_replace_dual_ctn s t r u (Proof.pf P) (Proof.pf Q) =
        replaceDualCtnConclusion s t r u) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_replace_dual_ctn s t r u (Proof.pf P) (Proof.pf Q)) := by
  rcases hTy with ⟨T, hSTy, hTTy, hRTy, hUTy⟩
  let repl := replaceDualCtnRepl s t r
  let lhs := replaceDualCtnLhs s t r u
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hRSmtTy := smtx_typeof_of_eo_seq r T hRTrans hRTy
  have hUSmtTy := smtx_typeof_of_eo_seq u T hUTrans hUTy
  have hReplSmtTy :
      __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt t)
          (__eo_to_smt r)) =
      SmtType.Seq (__eo_to_smt_type T) := by
    rw [typeof_str_replace_eq]
    simp [hSSmtTy, hTSmtTy, hRSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hReplTy :
      __smtx_typeof (__eo_to_smt repl) = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [repl, replaceDualCtnRepl, __eo_to_smt, __eo_to_smt_type, __smtx_typeof] using hReplSmtTy
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.str_contains
          (SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt t)
            (__eo_to_smt r))
          (__eo_to_smt u)) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hReplSmtTy, hUSmtTy, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hTrueTy : __smtx_typeof (__eo_to_smt (Term.Boolean true)) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
    rw [__smtx_typeof.eq_def]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (replaceDualCtnConclusion s t r u) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs (Term.Boolean true)
      (by rw [hLhsTy, hTrueTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBoolEq

private theorem facts___eo_prog_str_replace_dual_ctn_impl
    (M : SmtModel) (hM : model_wf M) (s t r u P Q : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hUTrans : RuleProofs.eo_has_smt_translation u)
    (hTy : ∃ T, __eo_typeof s = Term.Apply Term.Seq T ∧
      __eo_typeof t = Term.Apply Term.Seq T ∧
      __eo_typeof r = Term.Apply Term.Seq T ∧
      __eo_typeof u = Term.Apply Term.Seq T)
    (hPremS : eo_interprets M (replaceDualCtnPremiseS s u) true)
    (hPremR : eo_interprets M (replaceDualCtnPremiseR r u) true)
    (hProgEq :
      __eo_prog_str_replace_dual_ctn s t r u (Proof.pf P) (Proof.pf Q) =
        replaceDualCtnConclusion s t r u) :
    eo_interprets M
      (__eo_prog_str_replace_dual_ctn s t r u (Proof.pf P) (Proof.pf Q)) true := by
  rcases hTy with ⟨T, hSTy, hTTy, hRTy, hUTy⟩
  let lhs := replaceDualCtnLhs s t r u
  have hBoolEq :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.eq lhs) (Term.Boolean true)) := by
    simpa [hProgEq, replaceDualCtnConclusion, lhs] using
      typed___eo_prog_str_replace_dual_ctn_impl s t r u P Q
        hSTrans hTTrans hRTrans hUTrans ⟨T, hSTy, hTTy, hRTy, hUTy⟩ hProgEq
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hRSmtTy := smtx_typeof_of_eo_seq r T hRTrans hRTy
  have hUSmtTy := smtx_typeof_of_eo_seq u T hUTrans hUTy
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
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hRSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRSmtTy]
        simp)
  have hUEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt u)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hUSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt u) (by
        unfold term_has_non_none_type
        rw [hUSmtTy]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases seq_value_canonical hTEvalTy with ⟨ts, hTEval⟩
  rcases seq_value_canonical hREvalTy with ⟨rs, hREval⟩
  rcases seq_value_canonical hUEvalTy with ⟨us, hUEval⟩
  have hContainsS :
      native_seq_contains (native_unpack_seq ss) (native_unpack_seq us) = true := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremS
    cases hPremS with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.str_contains (__eo_to_smt s) (__eo_to_smt u))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_contains_term_eq,
          hSEval, hUEval, smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_str_contains, __smtx_model_eval_eq,
          native_veq] using hEval
  have hContainsR :
      native_seq_contains (native_unpack_seq rs) (native_unpack_seq us) = true := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremR
    cases hPremR with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.str_contains (__eo_to_smt r) (__eo_to_smt u))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_contains_term_eq,
          hREval, hUEval, smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_str_contains, __smtx_model_eval_eq,
          native_veq] using hEval
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (SmtTerm.Boolean true) := by
    change __smtx_model_eval M
        (SmtTerm.str_contains
          (SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt t)
            (__eo_to_smt r))
          (__eo_to_smt u)) =
      __smtx_model_eval M (SmtTerm.Boolean true)
    rw [smtx_eval_str_contains_term_eq, smtx_eval_str_replace_term_eq]
    rw [hSEval, hTEval, hREval, hUEval]
    rw [show __smtx_model_eval M (SmtTerm.Boolean true) =
        SmtValue.Boolean true by
      rw [__smtx_model_eval.eq_def]]
    simp [__smtx_model_eval_str_contains, __smtx_model_eval_str_replace,
      Smtm.native_unpack_pack_seq,
      native_seq_replace_dual_ctn (native_unpack_seq ss) (native_unpack_seq ts)
        (native_unpack_seq rs) (native_unpack_seq us) hContainsS hContainsR]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs (Term.Boolean true) hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (Term.Boolean true)))

public theorem cmd_step_str_replace_dual_ctn_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_dual_ctn args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_replace_dual_ctn args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_dual_ctn args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_replace_dual_ctn args premises ≠
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
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons a4 args =>
                  cases args with
                  | nil =>
                      cases premises with
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons n1 premises =>
                          cases premises with
                          | nil =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | cons n2 premises =>
                              cases premises with
                              | nil =>
                                  let P := __eo_state_proven_nth s n1
                                  let Q := __eo_state_proven_nth s n2
                                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                                    simpa [cmdTranslationOk, cArgListTranslationOk] using
                                      hCmdTrans.1
                                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                                    simpa [cmdTranslationOk, cArgListTranslationOk] using
                                      hCmdTrans.2.1
                                  have hA3Trans : RuleProofs.eo_has_smt_translation a3 := by
                                    simpa [cmdTranslationOk, cArgListTranslationOk] using
                                      hCmdTrans.2.2.1
                                  have hA4Trans : RuleProofs.eo_has_smt_translation a4 := by
                                    simpa [cmdTranslationOk, cArgListTranslationOk] using
                                      hCmdTrans.2.2.2.1
                                  change __eo_typeof
                                      (__eo_prog_str_replace_dual_ctn a1 a2 a3 a4
                                        (Proof.pf P) (Proof.pf Q)) =
                                    Term.Bool at hResultTy
                                  have hProgRule :
                                      __eo_prog_str_replace_dual_ctn a1 a2 a3 a4
                                        (Proof.pf P) (Proof.pf Q) ≠ Term.Stuck :=
                                    term_ne_stuck_of_typeof_bool hResultTy
                                  rcases prog_str_replace_dual_ctn_info
                                      a1 a2 a3 a4 P Q hProgRule with
                                    ⟨s0, u0, r0, u1, hPremSShape,
                                      hPremRShape, hs0, hu0, hr0, hu1, hProgEq⟩
                                  subst s0
                                  subst u0
                                  subst r0
                                  subst u1
                                  let lhs := replaceDualCtnLhs a1 a2 a3 a4
                                  rw [hProgEq] at hResultTy
                                  change __eo_typeof_eq (__eo_typeof lhs)
                                      Term.Bool = Term.Bool at hResultTy
                                  have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                                    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                      (__eo_typeof lhs) Term.Bool hResultTy).1
                                  have hArgTypes :
                                      ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T ∧
                                        __eo_typeof a2 = Term.Apply Term.Seq T ∧
                                        __eo_typeof a3 = Term.Apply Term.Seq T ∧
                                        __eo_typeof a4 = Term.Apply Term.Seq T := by
                                    change __eo_typeof_str_contains
                                        (__eo_typeof (replaceDualCtnRepl a1 a2 a3))
                                        (__eo_typeof a4) ≠ Term.Stuck at hLhsNotStuck
                                    rcases eo_typeof_str_contains_args_of_ne_stuck
                                        (__eo_typeof (replaceDualCtnRepl a1 a2 a3))
                                        (__eo_typeof a4) hLhsNotStuck with
                                      ⟨T, hReplTy, hA4Ty⟩
                                    have hReplNotStuck :
                                        __eo_typeof (replaceDualCtnRepl a1 a2 a3) ≠
                                          Term.Stuck := by
                                      rw [hReplTy]
                                      simp
                                    change __eo_typeof_str_replace (__eo_typeof a1)
                                        (__eo_typeof a2) (__eo_typeof a3) ≠
                                      Term.Stuck at hReplNotStuck
                                    rcases eo_typeof_str_replace_args_of_ne_stuck
                                        (__eo_typeof a1) (__eo_typeof a2)
                                        (__eo_typeof a3) hReplNotStuck with
                                      ⟨U, hA1Ty, hA2Ty, hA3Ty⟩
                                    have hReplTyCalc :
                                        __eo_typeof (replaceDualCtnRepl a1 a2 a3) =
                                          Term.Apply Term.Seq U := by
                                      change __eo_typeof_str_replace (__eo_typeof a1)
                                          (__eo_typeof a2) (__eo_typeof a3) =
                                        Term.Apply Term.Seq U
                                      have hSeqReplNotStuck :
                                          __eo_typeof_str_replace
                                              (Term.Apply Term.Seq U)
                                              (Term.Apply Term.Seq U)
                                              (Term.Apply Term.Seq U) ≠
                                            Term.Stuck := by
                                        simpa [hA1Ty, hA2Ty, hA3Ty] using
                                          hReplNotStuck
                                      rw [hA1Ty, hA2Ty, hA3Ty]
                                      exact eo_typeof_str_replace_seq_same_of_ne_stuck U
                                        hSeqReplNotStuck
                                    rw [hReplTy] at hReplTyCalc
                                    cases hReplTyCalc
                                    exact ⟨T, hA1Ty, hA2Ty, hA3Ty, hA4Ty⟩
                                  rcases hArgTypes with ⟨T, hA1Ty, hA2Ty, hA3Ty, hA4Ty⟩
                                  have hProps :
                                      StepRuleProperties M
                                        (premiseTermList s
                                          (CIndexList.cons n1
                                            (CIndexList.cons n2 CIndexList.nil)))
                                        (__eo_prog_str_replace_dual_ctn a1 a2 a3 a4
                                          (Proof.pf P) (Proof.pf Q)) := by
                                    refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                      (typed___eo_prog_str_replace_dual_ctn_impl
                                        a1 a2 a3 a4 P Q hA1Trans hA2Trans
                                        hA3Trans hA4Trans
                                        ⟨T, hA1Ty, hA2Ty, hA3Ty, hA4Ty⟩ hProgEq)⟩
                                    intro hTrue
                                    have hPremSRaw : eo_interprets M P true :=
                                      hTrue P (by simp [P, Q, premiseTermList])
                                    have hPremSInterp :
                                        eo_interprets M (replaceDualCtnPremiseS a1 a4)
                                          true := by
                                      simpa [hPremSShape] using hPremSRaw
                                    have hPremRRaw : eo_interprets M Q true :=
                                      hTrue Q (by simp [P, Q, premiseTermList])
                                    have hPremRInterp :
                                        eo_interprets M (replaceDualCtnPremiseR a3 a4)
                                          true := by
                                      simpa [hPremRShape] using hPremRRaw
                                    exact facts___eo_prog_str_replace_dual_ctn_impl M hM
                                      a1 a2 a3 a4 P Q hA1Trans hA2Trans
                                      hA3Trans hA4Trans
                                      ⟨T, hA1Ty, hA2Ty, hA3Ty, hA4Ty⟩
                                      hPremSInterp hPremRInterp hProgEq
                                  change StepRuleProperties M [P, Q]
                                    (__eo_prog_str_replace_dual_ctn a1 a2 a3 a4
                                      (Proof.pf P) (Proof.pf Q))
                                  simpa [premiseTermList] using hProps
                              | cons _ _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
