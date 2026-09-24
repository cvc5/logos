module

public import Cpc.Proofs.RuleSupport.StrConcatUnifySupport
import all Cpc.Proofs.RuleSupport.StrConcatUnifySupport
public import Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
import all Cpc.Proofs.RuleSupport.StrSubstrContainsSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StrReplaceFindSupport

theorem eo_typeof_eq_bool_of_has_bool_type
    (x y : Term)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply Term.eq x) y)) :
    __eo_typeof (Term.Apply (Term.Apply Term.eq x) y) = Term.Bool := by
  have hTrans := RuleProofs.eo_has_smt_translation_of_has_bool_type
    (Term.Apply (Term.Apply Term.eq x) y) hBool
  have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation
    (Term.Apply (Term.Apply Term.eq x) y) hTrans
  exact TranslationProofs.eo_to_smt_type_eq_bool (hMatch.symm.trans hBool)

theorem eo_typeof_eq_operands_of_has_bool_type
    (x y : Term)
    (hBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply Term.eq x) y)) :
    __eo_typeof x = __eo_typeof y := by
  have hEoBool := eo_typeof_eq_bool_of_has_bool_type x y hBool
  change __eo_typeof_eq (__eo_typeof x) (__eo_typeof y) =
    Term.Bool at hEoBool
  exact support_eo_typeof_eq_bool_operands_eq _ _ hEoBool

abbrev indexTerm (t pat : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_indexof t) pat)
    (Term.Numeral 0)

abbrev foundPremise (t pat : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply (Term.Apply Term.geq (indexTerm t pat))
        (Term.Numeral 0)))
    (Term.Boolean true)

abbrev prePremise (t pat pre : Term) : Term :=
  Term.Apply (Term.Apply Term.eq pre)
    (Term.Apply (Term.Apply (Term.Apply Term.str_substr t)
      (Term.Numeral 0)) (indexTerm t pat))

abbrev afterStart (t pat : Term) : Term :=
  Term.Apply (Term.Apply Term.plus (indexTerm t pat))
    (Term.Apply (Term.Apply Term.plus (Term.Apply Term.str_len pat))
      (Term.Numeral 0))

abbrev postPremise (t pat post : Term) : Term :=
  Term.Apply (Term.Apply Term.eq post)
    (Term.Apply (Term.Apply (Term.Apply Term.str_substr t)
      (afterStart t pat)) (Term.Apply Term.str_len t))

abbrev firstConcatSource (t tail : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat t) tail

abbrev firstConcatLeft (t tail pat repl : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace
    (firstConcatSource t tail)) pat) repl

abbrev firstConcatRight
    (pre repl post tail : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat pre)
    (Term.Apply (Term.Apply Term.str_concat repl)
      (Term.Apply (Term.Apply Term.str_concat post) tail))

abbrev firstConcatConclusion
    (t tail pat repl pre post : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (firstConcatLeft t tail pat repl))
    (firstConcatRight pre repl post tail)

abbrev baseLeft (t pat repl : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace t) pat) repl

abbrev baseGeneratedRight (pre repl post : Term) : Term :=
  __eo_mk_apply (Term.Apply Term.str_concat pre)
    (__eo_mk_apply (Term.Apply Term.str_concat repl)
      (__eo_mk_apply (Term.Apply Term.str_concat post)
        (__eo_nil Term.str_concat (__eo_typeof pre))))

abbrev baseGeneratedConclusion
    (t pat repl pre post : Term) : Term :=
  __eo_mk_apply (Term.Apply Term.eq (baseLeft t pat repl))
    (baseGeneratedRight pre repl post)

abbrev baseRight (pre repl post : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat pre)
    (Term.Apply (Term.Apply Term.str_concat repl)
      (Term.Apply (Term.Apply Term.str_concat post)
        (__seq_empty (__eo_typeof pre))))

abbrev baseConclusion
    (t pat repl pre post : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (baseLeft t pat repl))
    (baseRight pre repl post)

private theorem term_apply_ne_stuck (f a : Term) :
    Term.Apply f a ≠ Term.Stuck := by
  intro h
  cases h

private theorem seq_empty_seq_ne_stuck (T : Term) :
    __seq_empty (Term.Apply Term.Seq T) ≠ Term.Stuck := by
  cases T <;> simp [__seq_empty, Term.Seq]
  case UOp op =>
    cases op <;> simp [__seq_empty, Term.Seq]

private theorem mk_apply_apply_eq (f a b : Term)
    (hB : b ≠ Term.Stuck) :
    __eo_mk_apply (Term.Apply f a) b = Term.Apply (Term.Apply f a) b := by
  cases b <;> simp [__eo_mk_apply] at hB ⊢

theorem generated_base_conclusion_eq
    (t pat repl pre post T : Term)
    (hPreTy : __eo_typeof pre = Term.Apply Term.Seq T) :
    baseGeneratedConclusion t pat repl pre post =
      baseConclusion t pat repl pre post := by
  have hNil :
      __eo_nil Term.str_concat (__eo_typeof pre) =
        __seq_empty (__eo_typeof pre) := by
    rw [hPreTy]
    rfl
  have hEmptyNN : __seq_empty (__eo_typeof pre) ≠ Term.Stuck := by
    rw [hPreTy]
    exact seq_empty_seq_ne_stuck T
  have hPost :
      __eo_mk_apply (Term.Apply Term.str_concat post)
          (__eo_nil Term.str_concat (__eo_typeof pre)) =
        Term.Apply (Term.Apply Term.str_concat post)
          (__seq_empty (__eo_typeof pre)) := by
    rw [hNil]
    exact mk_apply_apply_eq Term.str_concat post _ hEmptyNN
  have hPostNN :
      Term.Apply (Term.Apply Term.str_concat post)
          (__seq_empty (__eo_typeof pre)) ≠ Term.Stuck :=
    term_apply_ne_stuck _ _
  have hRepl :
      __eo_mk_apply (Term.Apply Term.str_concat repl)
          (__eo_mk_apply (Term.Apply Term.str_concat post)
            (__eo_nil Term.str_concat (__eo_typeof pre))) =
        Term.Apply (Term.Apply Term.str_concat repl)
          (Term.Apply (Term.Apply Term.str_concat post)
            (__seq_empty (__eo_typeof pre))) := by
    rw [hPost]
    exact mk_apply_apply_eq Term.str_concat repl _ hPostNN
  have hReplNN :
      Term.Apply (Term.Apply Term.str_concat repl)
          (Term.Apply (Term.Apply Term.str_concat post)
            (__seq_empty (__eo_typeof pre))) ≠ Term.Stuck :=
    term_apply_ne_stuck _ _
  have hPre : baseGeneratedRight pre repl post =
      baseRight pre repl post := by
    change __eo_mk_apply (Term.Apply Term.str_concat pre)
        (__eo_mk_apply (Term.Apply Term.str_concat repl)
          (__eo_mk_apply (Term.Apply Term.str_concat post)
            (__eo_nil Term.str_concat (__eo_typeof pre)))) = _
    rw [hRepl]
    exact mk_apply_apply_eq Term.str_concat pre _ hReplNN
  have hRightNN : baseRight pre repl post ≠ Term.Stuck :=
    term_apply_ne_stuck _ _
  rw [baseGeneratedConclusion, hPre]
  exact mk_apply_apply_eq Term.eq (baseLeft t pat repl)
    (baseRight pre repl post) hRightNN

theorem base_lhs_type_ne_stuck_of_generated_type_bool
    (t pat repl pre post : Term)
    (hTy : __eo_typeof (baseGeneratedConclusion t pat repl pre post) =
      Term.Bool) :
    __eo_typeof (baseLeft t pat repl) ≠ Term.Stuck := by
  let lhs := baseLeft t pat repl
  let rhs := baseGeneratedRight pre repl post
  have hGeneratedNN : baseGeneratedConclusion t pat repl pre post ≠
      Term.Stuck := term_ne_stuck_of_typeof_bool hTy
  have hRhsNN : rhs ≠ Term.Stuck := by
    intro hStuck
    apply hGeneratedNN
    dsimp [baseGeneratedConclusion]
    change __eo_mk_apply (Term.Apply Term.eq (baseLeft t pat repl)) rhs =
      Term.Stuck
    rw [hStuck]
    rfl
  have hGenEq : baseGeneratedConclusion t pat repl pre post =
      Term.Apply (Term.Apply Term.eq lhs) rhs := by
    dsimp [baseGeneratedConclusion, lhs]
    exact mk_apply_apply_eq Term.eq (baseLeft t pat repl) rhs hRhsNN
  rw [hGenEq] at hTy
  change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) =
    Term.Bool at hTy
  exact (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof lhs) (__eo_typeof rhs) hTy).1

theorem prog_first_concat_info
    (t tail pat repl pre post P1 P2 P3 : Term)
    (hProg :
      __eo_prog_str_replace_find_first_concat t tail pat repl pre post
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) ≠ Term.Stuck) :
    P1 = foundPremise t pat ∧
      P2 = prePremise t pat pre ∧
      P3 = postPremise t pat post ∧
      __eo_prog_str_replace_find_first_concat t tail pat repl pre post
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) =
        firstConcatConclusion t tail pat repl pre post := by
  unfold __eo_prog_str_replace_find_first_concat at hProg
  split at hProg <;> try contradiction
  next heq1 heq2 heq3 =>
    cases heq1
    cases heq2
    cases heq3
    have hGuard := support_eo_requires_cond_eq_of_non_stuck hProg
    have h1to11 := StrEqReplSupport.eo_and_eq_true_left hGuard
    have h12 := StrEqReplSupport.eo_and_eq_true_right hGuard
    have h1to10 := StrEqReplSupport.eo_and_eq_true_left h1to11
    have h11 := StrEqReplSupport.eo_and_eq_true_right h1to11
    have h1to9 := StrEqReplSupport.eo_and_eq_true_left h1to10
    have h10 := StrEqReplSupport.eo_and_eq_true_right h1to10
    have h1to8 := StrEqReplSupport.eo_and_eq_true_left h1to9
    have h9 := StrEqReplSupport.eo_and_eq_true_right h1to9
    have h1to7 := StrEqReplSupport.eo_and_eq_true_left h1to8
    have h8 := StrEqReplSupport.eo_and_eq_true_right h1to8
    have h1to6 := StrEqReplSupport.eo_and_eq_true_left h1to7
    have h7 := StrEqReplSupport.eo_and_eq_true_right h1to7
    have h1to5 := StrEqReplSupport.eo_and_eq_true_left h1to6
    have h6 := StrEqReplSupport.eo_and_eq_true_right h1to6
    have h1to4 := StrEqReplSupport.eo_and_eq_true_left h1to5
    have h5 := StrEqReplSupport.eo_and_eq_true_right h1to5
    have h1to3 := StrEqReplSupport.eo_and_eq_true_left h1to4
    have h4 := StrEqReplSupport.eo_and_eq_true_right h1to4
    have h1to2 := StrEqReplSupport.eo_and_eq_true_left h1to3
    have h3 := StrEqReplSupport.eo_and_eq_true_right h1to3
    have h1 := StrEqReplSupport.eo_and_eq_true_left h1to2
    have h2 := StrEqReplSupport.eo_and_eq_true_right h1to2
    have e1 := RuleProofs.eq_of_eo_eq_true _ _ h1
    have e2 := RuleProofs.eq_of_eo_eq_true _ _ h2
    have e3 := RuleProofs.eq_of_eo_eq_true _ _ h3
    have e4 := RuleProofs.eq_of_eo_eq_true _ _ h4
    have e5 := RuleProofs.eq_of_eo_eq_true _ _ h5
    have e6 := RuleProofs.eq_of_eo_eq_true _ _ h6
    have e7 := RuleProofs.eq_of_eo_eq_true _ _ h7
    have e8 := RuleProofs.eq_of_eo_eq_true _ _ h8
    have e9 := RuleProofs.eq_of_eo_eq_true _ _ h9
    have e10 := RuleProofs.eq_of_eo_eq_true _ _ h10
    have e11 := RuleProofs.eq_of_eo_eq_true _ _ h11
    have e12 := RuleProofs.eq_of_eo_eq_true _ _ h12
    subst_vars
    refine ⟨rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_replace_find_first_concat, __eo_requires,
      __eo_eq, __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, firstConcatConclusion, firstConcatLeft,
      firstConcatRight, firstConcatSource]

theorem prog_base_info
    (t pat repl pre post P1 P2 P3 : Term)
    (hProg :
      __eo_prog_str_replace_find_base t pat repl pre post
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) ≠ Term.Stuck) :
    P1 = foundPremise t pat ∧
      P2 = prePremise t pat pre ∧
      P3 = postPremise t pat post ∧
      __eo_prog_str_replace_find_base t pat repl pre post
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) =
        baseGeneratedConclusion t pat repl pre post := by
  unfold __eo_prog_str_replace_find_base at hProg
  split at hProg <;> try contradiction
  next heq1 heq2 heq3 =>
    cases heq1
    cases heq2
    cases heq3
    have hGuard := support_eo_requires_cond_eq_of_non_stuck hProg
    have h1to11 := StrEqReplSupport.eo_and_eq_true_left hGuard
    have h12 := StrEqReplSupport.eo_and_eq_true_right hGuard
    have h1to10 := StrEqReplSupport.eo_and_eq_true_left h1to11
    have h11 := StrEqReplSupport.eo_and_eq_true_right h1to11
    have h1to9 := StrEqReplSupport.eo_and_eq_true_left h1to10
    have h10 := StrEqReplSupport.eo_and_eq_true_right h1to10
    have h1to8 := StrEqReplSupport.eo_and_eq_true_left h1to9
    have h9 := StrEqReplSupport.eo_and_eq_true_right h1to9
    have h1to7 := StrEqReplSupport.eo_and_eq_true_left h1to8
    have h8 := StrEqReplSupport.eo_and_eq_true_right h1to8
    have h1to6 := StrEqReplSupport.eo_and_eq_true_left h1to7
    have h7 := StrEqReplSupport.eo_and_eq_true_right h1to7
    have h1to5 := StrEqReplSupport.eo_and_eq_true_left h1to6
    have h6 := StrEqReplSupport.eo_and_eq_true_right h1to6
    have h1to4 := StrEqReplSupport.eo_and_eq_true_left h1to5
    have h5 := StrEqReplSupport.eo_and_eq_true_right h1to5
    have h1to3 := StrEqReplSupport.eo_and_eq_true_left h1to4
    have h4 := StrEqReplSupport.eo_and_eq_true_right h1to4
    have h1to2 := StrEqReplSupport.eo_and_eq_true_left h1to3
    have h3 := StrEqReplSupport.eo_and_eq_true_right h1to3
    have h1 := StrEqReplSupport.eo_and_eq_true_left h1to2
    have h2 := StrEqReplSupport.eo_and_eq_true_right h1to2
    have e1 := RuleProofs.eq_of_eo_eq_true _ _ h1
    have e2 := RuleProofs.eq_of_eo_eq_true _ _ h2
    have e3 := RuleProofs.eq_of_eo_eq_true _ _ h3
    have e4 := RuleProofs.eq_of_eo_eq_true _ _ h4
    have e5 := RuleProofs.eq_of_eo_eq_true _ _ h5
    have e6 := RuleProofs.eq_of_eo_eq_true _ _ h6
    have e7 := RuleProofs.eq_of_eo_eq_true _ _ h7
    have e8 := RuleProofs.eq_of_eo_eq_true _ _ h8
    have e9 := RuleProofs.eq_of_eo_eq_true _ _ h9
    have e10 := RuleProofs.eq_of_eo_eq_true _ _ h10
    have e11 := RuleProofs.eq_of_eo_eq_true _ _ h11
    have e12 := RuleProofs.eq_of_eo_eq_true _ _ h12
    subst_vars
    refine ⟨rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_replace_find_base, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, baseGeneratedConclusion, baseGeneratedRight,
      baseLeft]

private theorem smtx_eval_str_indexof_term_eq
    (M : SmtModel) (x y n : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_indexof x y n) =
      __smtx_model_eval_str_indexof
        (__smtx_model_eval M x) (__smtx_model_eval M y)
        (__smtx_model_eval M n) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem typed_first_concat
    (t tail pat repl pre post P1 P2 P3 T : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hTailTrans : RuleProofs.eo_has_smt_translation tail)
    (hPatTrans : RuleProofs.eo_has_smt_translation pat)
    (hReplTrans : RuleProofs.eo_has_smt_translation repl)
    (hPreTrans : RuleProofs.eo_has_smt_translation pre)
    (hPostTrans : RuleProofs.eo_has_smt_translation post)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hTailTy : __eo_typeof tail = Term.Apply Term.Seq T)
    (hPatTy : __eo_typeof pat = Term.Apply Term.Seq T)
    (hReplTy : __eo_typeof repl = Term.Apply Term.Seq T)
    (hPreTy : __eo_typeof pre = Term.Apply Term.Seq T)
    (hPostTy : __eo_typeof post = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_replace_find_first_concat t tail pat repl pre post
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) =
        firstConcatConclusion t tail pat repl pre post) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_replace_find_first_concat t tail pat repl pre post
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)) := by
  let source := firstConcatSource t tail
  let lhs := firstConcatLeft t tail pat repl
  let postTail := Term.Apply (Term.Apply Term.str_concat post) tail
  let replPostTail := Term.Apply (Term.Apply Term.str_concat repl) postTail
  let rhs := firstConcatRight pre repl post tail
  have hTSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hTailSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq tail T hTailTrans hTailTy
  have hPatSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq pat T hPatTrans hPatTy
  have hReplSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq repl T hReplTrans hReplTy
  have hPreSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq pre T hPreTrans hPreTy
  have hPostSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq post T hPostTrans hPostTy
  have hSourceTy : __smtx_typeof (__eo_to_smt source) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt t) (__eo_to_smt tail)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hTSmtTy, hTailSmtTy, __smtx_typeof_seq_op_2,
      native_ite, native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt source) (__eo_to_smt pat)
          (__eo_to_smt repl)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq]
    simp [hSourceTy, hPatSmtTy, hReplSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hPostTailTy : __smtx_typeof (__eo_to_smt postTail) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt post) (__eo_to_smt tail)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hPostSmtTy, hTailSmtTy, __smtx_typeof_seq_op_2,
      native_ite, native_Teq]
  have hReplPostTailTy : __smtx_typeof (__eo_to_smt replPostTail) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt repl) (__eo_to_smt postTail)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hReplSmtTy, hPostTailTy, __smtx_typeof_seq_op_2,
      native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt pre)
          (__eo_to_smt replPostTail)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hPreSmtTy, hReplPostTailTy, __smtx_typeof_seq_op_2,
      native_ite, native_Teq]
  have hBool : RuleProofs.eo_has_bool_type
      (firstConcatConclusion t tail pat repl pre post) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

theorem typed_base
    (t pat repl pre post P1 P2 P3 T : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hPatTrans : RuleProofs.eo_has_smt_translation pat)
    (hReplTrans : RuleProofs.eo_has_smt_translation repl)
    (hPreTrans : RuleProofs.eo_has_smt_translation pre)
    (hPostTrans : RuleProofs.eo_has_smt_translation post)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hPatTy : __eo_typeof pat = Term.Apply Term.Seq T)
    (hReplTy : __eo_typeof repl = Term.Apply Term.Seq T)
    (hPreTy : __eo_typeof pre = Term.Apply Term.Seq T)
    (hPostTy : __eo_typeof post = Term.Apply Term.Seq T)
    (hProgGen :
      __eo_prog_str_replace_find_base t pat repl pre post
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) =
        baseGeneratedConclusion t pat repl pre post) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_replace_find_base t pat repl pre post
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)) := by
  let lhs := baseLeft t pat repl
  let postNil := Term.Apply (Term.Apply Term.str_concat post)
    (__seq_empty (__eo_typeof pre))
  let replPostNil := Term.Apply (Term.Apply Term.str_concat repl) postNil
  let rhs := baseRight pre repl post
  have hProgEq :
      __eo_prog_str_replace_find_base t pat repl pre post
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) =
        baseConclusion t pat repl pre post := by
    rw [hProgGen, generated_base_conclusion_eq t pat repl pre post T hPreTy]
  have hTSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hPatSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq pat T hPatTrans hPatTy
  have hReplSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq repl T hReplTrans hReplTy
  have hPreSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq pre T hPreTrans hPreTy
  have hPostSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq post T hPostTrans hPostTy
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof pre))) =
        SmtType.Seq (__eo_to_smt_type T) :=
    smt_typeof_seq_empty_typeof pre (__eo_to_smt_type T) hPreSmtTy
      (seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf
        pre (__eo_to_smt_type T) hPreSmtTy
        (smt_seq_component_wf_of_non_none_type
          (__eo_to_smt pre) (__eo_to_smt_type T) hPreSmtTy).1
        (smt_seq_component_wf_of_non_none_type
          (__eo_to_smt pre) (__eo_to_smt_type T) hPreSmtTy).2)
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt t) (__eo_to_smt pat)
          (__eo_to_smt repl)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq]
    simp [hTSmtTy, hPatSmtTy, hReplSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hPostNilTy : __smtx_typeof (__eo_to_smt postNil) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt post)
          (__eo_to_smt (__seq_empty (__eo_typeof pre)))) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hPostSmtTy, hEmptyTy, __smtx_typeof_seq_op_2,
      native_ite, native_Teq]
  have hReplPostNilTy : __smtx_typeof (__eo_to_smt replPostNil) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt repl) (__eo_to_smt postNil)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hReplSmtTy, hPostNilTy, __smtx_typeof_seq_op_2,
      native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt pre)
          (__eo_to_smt replPostNil)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_concat_eq]
    simp [hPreSmtTy, hReplPostNilTy, __smtx_typeof_seq_op_2,
      native_ite, native_Teq]
  have hBool : RuleProofs.eo_has_bool_type
      (baseConclusion t pat repl pre post) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

theorem facts_first_concat
    (M : SmtModel) (hM : model_wf M)
    (t tail pat repl pre post P1 P2 P3 T : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hTailTrans : RuleProofs.eo_has_smt_translation tail)
    (hPatTrans : RuleProofs.eo_has_smt_translation pat)
    (hReplTrans : RuleProofs.eo_has_smt_translation repl)
    (hPreTrans : RuleProofs.eo_has_smt_translation pre)
    (hPostTrans : RuleProofs.eo_has_smt_translation post)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hTailTy : __eo_typeof tail = Term.Apply Term.Seq T)
    (hPatTy : __eo_typeof pat = Term.Apply Term.Seq T)
    (hReplTy : __eo_typeof repl = Term.Apply Term.Seq T)
    (hPreTy : __eo_typeof pre = Term.Apply Term.Seq T)
    (hPostTy : __eo_typeof post = Term.Apply Term.Seq T)
    (hPrem1 : eo_interprets M (foundPremise t pat) true)
    (hPrem2 : eo_interprets M (prePremise t pat pre) true)
    (hPrem3 : eo_interprets M (postPremise t pat post) true)
    (hProgEq :
      __eo_prog_str_replace_find_first_concat t tail pat repl pre post
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) =
        firstConcatConclusion t tail pat repl pre post) :
    eo_interprets M
      (__eo_prog_str_replace_find_first_concat t tail pat repl pre post
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)) true := by
  let lhs := firstConcatLeft t tail pat repl
  let rhs := firstConcatRight pre repl post tail
  have hBool : RuleProofs.eo_has_bool_type
      (firstConcatConclusion t tail pat repl pre post) := by
    simpa [hProgEq] using typed_first_concat t tail pat repl pre post
      P1 P2 P3 T hTTrans hTailTrans hPatTrans hReplTrans hPreTrans
      hPostTrans hTTy hTailTy hPatTy hReplTy hPreTy hPostTy hProgEq
  have hTSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hTailSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq tail T hTailTrans hTailTy
  have hPatSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq pat T hPatTrans hPatTy
  have hReplSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq repl T hReplTrans hReplTy
  have hPreSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq pre T hPreTrans hPreTy
  have hPostSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq post T hPostTrans hPostTy
  have hTEvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hTSmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTSmtTy]
        simp)
  have hTailEvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt tail)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hTailSmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt tail) (by
        unfold term_has_non_none_type
        rw [hTailSmtTy]
        simp)
  have hPatEvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt pat)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hPatSmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt pat) (by
        unfold term_has_non_none_type
        rw [hPatSmtTy]
        simp)
  have hReplEvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt repl)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hReplSmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt repl) (by
        unfold term_has_non_none_type
        rw [hReplSmtTy]
        simp)
  have hPreEvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt pre)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hPreSmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt pre) (by
        unfold term_has_non_none_type
        rw [hPreSmtTy]
        simp)
  have hPostEvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt post)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hPostSmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt post) (by
        unfold term_has_non_none_type
        rw [hPostSmtTy]
        simp)
  rcases seq_value_canonical hTEvalTy with ⟨st, hTEval⟩
  rcases seq_value_canonical hTailEvalTy with ⟨stail, hTailEval⟩
  rcases seq_value_canonical hPatEvalTy with ⟨spat, hPatEval⟩
  rcases seq_value_canonical hReplEvalTy with ⟨srepl, hReplEval⟩
  rcases seq_value_canonical hPreEvalTy with ⟨spre, hPreEval⟩
  rcases seq_value_canonical hPostEvalTy with ⟨spost, hPostEval⟩
  let idx := native_seq_indexof (native_unpack_seq st)
    (native_unpack_seq spat) 0
  have hIndexNonneg : 0 ≤ idx := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem1
    cases hPrem1 with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.geq
                (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt pat)
                  (SmtTerm.Numeral 0))
                (SmtTerm.Numeral 0))
              (SmtTerm.Boolean true)) = SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq,
          StrSubstrContainsSupport.smtx_eval_geq_term_eq,
          smtx_eval_str_indexof_term_eq, hTEval, hPatEval,
          StrEqReplSupport.smtx_eval_numeral_term_eq,
          StrEqReplSupport.smtx_eval_boolean_term_eq] at hEval
        have hLeBool : native_zleq 0 idx = true := by
          simpa [idx, __smtx_model_eval_eq, __smtx_model_eval_geq,
            __smtx_model_eval_leq, __smtx_model_eval_str_indexof,
            native_veq, Smtm.native_unpack_pack_seq] using hEval
        simpa [SmtEval.native_zleq] using hLeBool
  let unpackValue : SmtValue -> List SmtValue
    | SmtValue.Seq xs => native_unpack_seq xs
    | _ => []
  have hPreExtract : native_unpack_seq spre =
      native_seq_extract (native_unpack_seq st) 0 idx := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem2
    cases hPrem2 with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (__eo_to_smt pre)
              (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.Numeral 0)
                (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt pat)
                  (SmtTerm.Numeral 0)))) = SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, hPreEval,
          StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
          hTEval, StrEqReplSupport.smtx_eval_numeral_term_eq,
          smtx_eval_str_indexof_term_eq, hTEval, hPatEval,
          StrEqReplSupport.smtx_eval_numeral_term_eq] at hEval
        have hBool : decide
            (SmtValue.Seq spre =
              SmtValue.Seq
                (native_pack_seq (__smtx_elem_typeof_seq_value st)
                  (native_seq_extract (native_unpack_seq st) 0 idx))) =
            true := by
          simpa [idx, __smtx_model_eval_eq, __smtx_model_eval_str_substr,
            __smtx_model_eval_str_indexof, native_veq,
            Smtm.native_unpack_pack_seq] using hEval
        have hValueEq := of_decide_eq_true hBool
        have hUnpack := congrArg unpackValue hValueEq
        simpa [unpackValue, Smtm.native_unpack_pack_seq] using hUnpack
  have hPostExtract : native_unpack_seq spost =
      native_seq_extract (native_unpack_seq st)
        (idx + Int.ofNat (native_unpack_seq spat).length)
        (native_seq_len (native_unpack_seq st)) := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem3
    cases hPrem3 with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (__eo_to_smt post)
              (SmtTerm.str_substr (__eo_to_smt t)
                (SmtTerm.plus
                  (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt pat)
                    (SmtTerm.Numeral 0))
                  (SmtTerm.plus (SmtTerm.str_len (__eo_to_smt pat))
                    (SmtTerm.Numeral 0)))
                (SmtTerm.str_len (__eo_to_smt t)))) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, hPostEval,
          StrSubstrContainsSupport.smtx_eval_str_substr_term_eq, hTEval,
          StrSubstrContainsSupport.smtx_eval_plus_term_eq,
          smtx_eval_str_indexof_term_eq, hTEval, hPatEval,
          StrEqReplSupport.smtx_eval_numeral_term_eq,
          StrSubstrContainsSupport.smtx_eval_plus_term_eq,
          smtx_eval_str_len_term_eq, hPatEval,
          StrEqReplSupport.smtx_eval_numeral_term_eq,
          smtx_eval_str_len_term_eq, hTEval] at hEval
        have hBool : decide
            (SmtValue.Seq spost =
              SmtValue.Seq
                (native_pack_seq (__smtx_elem_typeof_seq_value st)
                  (native_seq_extract (native_unpack_seq st)
                    (idx + Int.ofNat (native_unpack_seq spat).length)
                    (native_seq_len (native_unpack_seq st))))) = true := by
          simpa [idx, __smtx_model_eval_eq, __smtx_model_eval_str_substr,
            __smtx_model_eval_str_indexof, __smtx_model_eval_plus,
            __smtx_model_eval_str_len, native_veq, native_zplus,
            SmtEval.native_zplus, native_seq_len,
            Smtm.native_unpack_pack_seq] using hEval
        have hValueEq := of_decide_eq_true hBool
        have hUnpack := congrArg unpackValue hValueEq
        simpa [unpackValue, Smtm.native_unpack_pack_seq] using hUnpack
  have hBounds : Int.toNat idx + (native_unpack_seq spat).length ≤
      (native_unpack_seq st).length :=
    StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
      (native_unpack_seq st) (native_unpack_seq spat) hIndexNonneg
  have hIdxCast : (Int.toNat idx : Int) = idx :=
    Int.toNat_of_nonneg hIndexNonneg
  have hIdxLe : Int.toNat idx ≤ (native_unpack_seq st).length := by omega
  have hPreList : native_unpack_seq spre =
      (native_unpack_seq st).take (Int.toNat idx) := by
    rw [hPreExtract, ← hIdxCast]
    exact native_seq_extract_zero_nat _ _ hIdxLe
  have hAfterNonneg :
      0 ≤ idx + Int.ofNat (native_unpack_seq spat).length :=
    Int.add_nonneg hIndexNonneg (Int.natCast_nonneg _)
  have hAfterLe :
      idx + Int.ofNat (native_unpack_seq spat).length ≤
        native_seq_len (native_unpack_seq st) := by
    rw [← hIdxCast]
    simpa [native_seq_len] using Int.ofNat_le.mpr hBounds
  have hToNatAfter :
      Int.toNat (idx + Int.ofNat (native_unpack_seq spat).length) =
        Int.toNat idx + (native_unpack_seq spat).length := by
    simpa using
      (Int.toNat_add hIndexNonneg
        (Int.natCast_nonneg (native_unpack_seq spat).length))
  have hPostList : native_unpack_seq spost =
      (native_unpack_seq st).drop
        (Int.toNat idx + (native_unpack_seq spat).length) := by
    rw [hPostExtract,
      native_seq_extract_len_tail_of_bounds _ _ hAfterNonneg hAfterLe,
      hToNatAfter]
  have hNativeReplace :
      native_seq_replace
          (native_unpack_seq st ++ native_unpack_seq stail)
          (native_unpack_seq spat) (native_unpack_seq srepl) =
        native_unpack_seq spre ++ native_unpack_seq srepl ++
          native_unpack_seq spost ++ native_unpack_seq stail := by
    calc
      native_seq_replace
          (native_unpack_seq st ++ native_unpack_seq stail)
          (native_unpack_seq spat) (native_unpack_seq srepl) =
        native_seq_replace (native_unpack_seq st)
            (native_unpack_seq spat) (native_unpack_seq srepl) ++
          native_unpack_seq stail :=
        StrEqReplSupport.native_seq_replace_append_of_indexof_nonneg
          _ _ _ _ hIndexNonneg
      _ = ((native_unpack_seq st).take (Int.toNat idx) ++
            native_unpack_seq srepl ++
            (native_unpack_seq st).drop
              (Int.toNat idx + (native_unpack_seq spat).length)) ++
          native_unpack_seq stail := by
        rw [StrEqReplSupport.native_seq_replace_of_indexof_nonneg
          _ _ _ hIndexNonneg]
      _ = native_unpack_seq spre ++ native_unpack_seq srepl ++
          native_unpack_seq spost ++ native_unpack_seq stail := by
        rw [hPreList, hPostList]
  have hTSeqTy : __smtx_typeof_seq_value st =
      SmtType.Seq (__eo_to_smt_type T) := by
    have hsimpa := hTEvalTy
    try simp [hTEval] at hsimpa ⊢
    exact hsimpa
  have hTailSeqTy : __smtx_typeof_seq_value stail =
      SmtType.Seq (__eo_to_smt_type T) := by
    have hsimpa := hTailEvalTy
    try simp [hTailEval] at hsimpa ⊢
    exact hsimpa
  have hPatSeqTy : __smtx_typeof_seq_value spat =
      SmtType.Seq (__eo_to_smt_type T) := by
    have hsimpa := hPatEvalTy
    try simp [hPatEval] at hsimpa ⊢
    exact hsimpa
  have hReplSeqTy : __smtx_typeof_seq_value srepl =
      SmtType.Seq (__eo_to_smt_type T) := by
    have hsimpa := hReplEvalTy
    try simp [hReplEval] at hsimpa ⊢
    exact hsimpa
  have hPreSeqTy : __smtx_typeof_seq_value spre =
      SmtType.Seq (__eo_to_smt_type T) := by
    have hsimpa := hPreEvalTy
    try simp [hPreEval] at hsimpa ⊢
    exact hsimpa
  have hPostSeqTy : __smtx_typeof_seq_value spost =
      SmtType.Seq (__eo_to_smt_type T) := by
    have hsimpa := hPostEvalTy
    try simp [hPostEval] at hsimpa ⊢
    exact hsimpa
  have hTElem := elem_typeof_seq_value_of_typeof_seq_value hTSeqTy
  have hTailElem := elem_typeof_seq_value_of_typeof_seq_value hTailSeqTy
  have hPatElem := elem_typeof_seq_value_of_typeof_seq_value hPatSeqTy
  have hReplElem := elem_typeof_seq_value_of_typeof_seq_value hReplSeqTy
  have hPreElem := elem_typeof_seq_value_of_typeof_seq_value hPreSeqTy
  have hPostElem := elem_typeof_seq_value_of_typeof_seq_value hPostSeqTy
  have hEvalEq : __smtx_model_eval M (__eo_to_smt lhs) =
      __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_replace
          (SmtTerm.str_concat (__eo_to_smt t) (__eo_to_smt tail))
          (__eo_to_smt pat) (__eo_to_smt repl)) =
      __smtx_model_eval M
        (SmtTerm.str_concat (__eo_to_smt pre)
          (SmtTerm.str_concat (__eo_to_smt repl)
            (SmtTerm.str_concat (__eo_to_smt post) (__eo_to_smt tail))))
    rw [StrEqReplSupport.smtx_eval_str_replace_term_eq,
      StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      hTEval, hTailEval, hPatEval, hReplEval, hPreEval, hPostEval]
    simp [__smtx_model_eval_str_replace, __smtx_model_eval_str_concat,
      native_seq_concat, Smtm.native_unpack_pack_seq, hTElem, hTailElem,
      hPatElem, hReplElem, hPreElem, hPostElem, elem_typeof_pack_seq,
      hNativeReplace]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

theorem facts_base
    (M : SmtModel) (hM : model_wf M)
    (t pat repl pre post P1 P2 P3 T : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hPatTrans : RuleProofs.eo_has_smt_translation pat)
    (hReplTrans : RuleProofs.eo_has_smt_translation repl)
    (hPreTrans : RuleProofs.eo_has_smt_translation pre)
    (hPostTrans : RuleProofs.eo_has_smt_translation post)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hPatTy : __eo_typeof pat = Term.Apply Term.Seq T)
    (hReplTy : __eo_typeof repl = Term.Apply Term.Seq T)
    (hPreTy : __eo_typeof pre = Term.Apply Term.Seq T)
    (hPostTy : __eo_typeof post = Term.Apply Term.Seq T)
    (hPrem1 : eo_interprets M (foundPremise t pat) true)
    (hPrem2 : eo_interprets M (prePremise t pat pre) true)
    (hPrem3 : eo_interprets M (postPremise t pat post) true)
    (hProgGen :
      __eo_prog_str_replace_find_base t pat repl pre post
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) =
        baseGeneratedConclusion t pat repl pre post) :
    eo_interprets M
      (__eo_prog_str_replace_find_base t pat repl pre post
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)) true := by
  let lhs := baseLeft t pat repl
  let rhs := baseRight pre repl post
  have hProgEq :
      __eo_prog_str_replace_find_base t pat repl pre post
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) =
        baseConclusion t pat repl pre post := by
    rw [hProgGen, generated_base_conclusion_eq t pat repl pre post T hPreTy]
  have hBool : RuleProofs.eo_has_bool_type
      (baseConclusion t pat repl pre post) := by
    simpa [hProgEq] using typed_base t pat repl pre post P1 P2 P3 T
      hTTrans hPatTrans hReplTrans hPreTrans hPostTrans hTTy hPatTy
      hReplTy hPreTy hPostTy hProgGen
  have hTSmtTy := StrEqReplSupport.smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hPatSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq pat T hPatTrans hPatTy
  have hReplSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq repl T hReplTrans hReplTy
  have hPreSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq pre T hPreTrans hPreTy
  have hPostSmtTy :=
    StrEqReplSupport.smtx_typeof_of_eo_seq post T hPostTrans hPostTy
  have hTEvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hTSmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTSmtTy]
        simp)
  have hPatEvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt pat)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hPatSmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt pat) (by
        unfold term_has_non_none_type
        rw [hPatSmtTy]
        simp)
  have hReplEvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt repl)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hReplSmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt repl) (by
        unfold term_has_non_none_type
        rw [hReplSmtTy]
        simp)
  have hPreEvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt pre)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hPreSmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt pre) (by
        unfold term_has_non_none_type
        rw [hPreSmtTy]
        simp)
  have hPostEvalTy : __smtx_typeof_value
      (__smtx_model_eval M (__eo_to_smt post)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hPostSmtTy] using smt_model_eval_preserves_type_of_non_none
      M hM (__eo_to_smt post) (by
        unfold term_has_non_none_type
        rw [hPostSmtTy]
        simp)
  rcases seq_value_canonical hTEvalTy with ⟨st, hTEval⟩
  rcases seq_value_canonical hPatEvalTy with ⟨spat, hPatEval⟩
  rcases seq_value_canonical hReplEvalTy with ⟨srepl, hReplEval⟩
  rcases seq_value_canonical hPreEvalTy with ⟨spre, hPreEval⟩
  rcases seq_value_canonical hPostEvalTy with ⟨spost, hPostEval⟩
  let idx := native_seq_indexof (native_unpack_seq st)
    (native_unpack_seq spat) 0
  have hIndexNonneg : 0 ≤ idx := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem1
    cases hPrem1 with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.geq
                (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt pat)
                  (SmtTerm.Numeral 0))
                (SmtTerm.Numeral 0))
              (SmtTerm.Boolean true)) = SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq,
          StrSubstrContainsSupport.smtx_eval_geq_term_eq,
          smtx_eval_str_indexof_term_eq, hTEval, hPatEval,
          StrEqReplSupport.smtx_eval_numeral_term_eq,
          StrEqReplSupport.smtx_eval_boolean_term_eq] at hEval
        have hLeBool : native_zleq 0 idx = true := by
          simpa [idx, __smtx_model_eval_eq, __smtx_model_eval_geq,
            __smtx_model_eval_leq, __smtx_model_eval_str_indexof,
            native_veq, Smtm.native_unpack_pack_seq] using hEval
        simpa [SmtEval.native_zleq] using hLeBool
  let unpackValue : SmtValue -> List SmtValue
    | SmtValue.Seq xs => native_unpack_seq xs
    | _ => []
  have hPreExtract : native_unpack_seq spre =
      native_seq_extract (native_unpack_seq st) 0 idx := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem2
    cases hPrem2 with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (__eo_to_smt pre)
              (SmtTerm.str_substr (__eo_to_smt t) (SmtTerm.Numeral 0)
                (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt pat)
                  (SmtTerm.Numeral 0)))) = SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, hPreEval,
          StrSubstrContainsSupport.smtx_eval_str_substr_term_eq,
          hTEval, StrEqReplSupport.smtx_eval_numeral_term_eq,
          smtx_eval_str_indexof_term_eq, hTEval, hPatEval,
          StrEqReplSupport.smtx_eval_numeral_term_eq] at hEval
        have hBoolEq : decide
            (SmtValue.Seq spre =
              SmtValue.Seq
                (native_pack_seq (__smtx_elem_typeof_seq_value st)
                  (native_seq_extract (native_unpack_seq st) 0 idx))) =
            true := by
          simpa [idx, __smtx_model_eval_eq, __smtx_model_eval_str_substr,
            __smtx_model_eval_str_indexof, native_veq,
            Smtm.native_unpack_pack_seq] using hEval
        have hValueEq := of_decide_eq_true hBoolEq
        have hUnpack := congrArg unpackValue hValueEq
        simpa [unpackValue, Smtm.native_unpack_pack_seq] using hUnpack
  have hPostExtract : native_unpack_seq spost =
      native_seq_extract (native_unpack_seq st)
        (idx + Int.ofNat (native_unpack_seq spat).length)
        (native_seq_len (native_unpack_seq st)) := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem3
    cases hPrem3 with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (__eo_to_smt post)
              (SmtTerm.str_substr (__eo_to_smt t)
                (SmtTerm.plus
                  (SmtTerm.str_indexof (__eo_to_smt t) (__eo_to_smt pat)
                    (SmtTerm.Numeral 0))
                  (SmtTerm.plus (SmtTerm.str_len (__eo_to_smt pat))
                    (SmtTerm.Numeral 0)))
                (SmtTerm.str_len (__eo_to_smt t)))) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, hPostEval,
          StrSubstrContainsSupport.smtx_eval_str_substr_term_eq, hTEval,
          StrSubstrContainsSupport.smtx_eval_plus_term_eq,
          smtx_eval_str_indexof_term_eq, hTEval, hPatEval,
          StrEqReplSupport.smtx_eval_numeral_term_eq,
          StrSubstrContainsSupport.smtx_eval_plus_term_eq,
          smtx_eval_str_len_term_eq, hPatEval,
          StrEqReplSupport.smtx_eval_numeral_term_eq,
          smtx_eval_str_len_term_eq, hTEval] at hEval
        have hBoolEq : decide
            (SmtValue.Seq spost =
              SmtValue.Seq
                (native_pack_seq (__smtx_elem_typeof_seq_value st)
                  (native_seq_extract (native_unpack_seq st)
                    (idx + Int.ofNat (native_unpack_seq spat).length)
                    (native_seq_len (native_unpack_seq st))))) = true := by
          simpa [idx, __smtx_model_eval_eq, __smtx_model_eval_str_substr,
            __smtx_model_eval_str_indexof, __smtx_model_eval_plus,
            __smtx_model_eval_str_len, native_veq, native_zplus,
            SmtEval.native_zplus, native_seq_len,
            Smtm.native_unpack_pack_seq] using hEval
        have hValueEq := of_decide_eq_true hBoolEq
        have hUnpack := congrArg unpackValue hValueEq
        simpa [unpackValue, Smtm.native_unpack_pack_seq] using hUnpack
  have hBounds : Int.toNat idx + (native_unpack_seq spat).length ≤
      (native_unpack_seq st).length :=
    StrEqReplSupport.native_seq_indexof_zero_bounds_of_nonneg
      (native_unpack_seq st) (native_unpack_seq spat) hIndexNonneg
  have hIdxCast : (Int.toNat idx : Int) = idx :=
    Int.toNat_of_nonneg hIndexNonneg
  have hIdxLe : Int.toNat idx ≤ (native_unpack_seq st).length := by omega
  have hPreList : native_unpack_seq spre =
      (native_unpack_seq st).take (Int.toNat idx) := by
    rw [hPreExtract, ← hIdxCast]
    exact native_seq_extract_zero_nat _ _ hIdxLe
  have hAfterNonneg :
      0 ≤ idx + Int.ofNat (native_unpack_seq spat).length :=
    Int.add_nonneg hIndexNonneg (Int.natCast_nonneg _)
  have hAfterLe : idx + Int.ofNat (native_unpack_seq spat).length ≤
      native_seq_len (native_unpack_seq st) := by
    rw [← hIdxCast]
    simpa [native_seq_len] using Int.ofNat_le.mpr hBounds
  have hToNatAfter :
      Int.toNat (idx + Int.ofNat (native_unpack_seq spat).length) =
        Int.toNat idx + (native_unpack_seq spat).length := by
    simpa using
      (Int.toNat_add hIndexNonneg
        (Int.natCast_nonneg (native_unpack_seq spat).length))
  have hPostList : native_unpack_seq spost =
      (native_unpack_seq st).drop
        (Int.toNat idx + (native_unpack_seq spat).length) := by
    rw [hPostExtract,
      native_seq_extract_len_tail_of_bounds _ _ hAfterNonneg hAfterLe,
      hToNatAfter]
  have hNativeReplace :
      native_seq_replace (native_unpack_seq st) (native_unpack_seq spat)
          (native_unpack_seq srepl) =
        native_unpack_seq spre ++ native_unpack_seq srepl ++
          native_unpack_seq spost := by
    rw [StrEqReplSupport.native_seq_replace_of_indexof_nonneg
      _ _ _ hIndexNonneg, ← hPreList, ← hPostList]
  have hTSeqTy : __smtx_typeof_seq_value st =
      SmtType.Seq (__eo_to_smt_type T) := by
    have hsimpa := hTEvalTy
    try simp [hTEval] at hsimpa ⊢
    exact hsimpa
  have hPatSeqTy : __smtx_typeof_seq_value spat =
      SmtType.Seq (__eo_to_smt_type T) := by
    have hsimpa := hPatEvalTy
    try simp [hPatEval] at hsimpa ⊢
    exact hsimpa
  have hReplSeqTy : __smtx_typeof_seq_value srepl =
      SmtType.Seq (__eo_to_smt_type T) := by
    have hsimpa := hReplEvalTy
    try simp [hReplEval] at hsimpa ⊢
    exact hsimpa
  have hPreSeqTy : __smtx_typeof_seq_value spre =
      SmtType.Seq (__eo_to_smt_type T) := by
    have hsimpa := hPreEvalTy
    try simp [hPreEval] at hsimpa ⊢
    exact hsimpa
  have hPostSeqTy : __smtx_typeof_seq_value spost =
      SmtType.Seq (__eo_to_smt_type T) := by
    have hsimpa := hPostEvalTy
    try simp [hPostEval] at hsimpa ⊢
    exact hsimpa
  have hTElem := elem_typeof_seq_value_of_typeof_seq_value hTSeqTy
  have hPatElem := elem_typeof_seq_value_of_typeof_seq_value hPatSeqTy
  have hReplElem := elem_typeof_seq_value_of_typeof_seq_value hReplSeqTy
  have hPreElem := elem_typeof_seq_value_of_typeof_seq_value hPreSeqTy
  have hPostElem := elem_typeof_seq_value_of_typeof_seq_value hPostSeqTy
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt (__seq_empty (__eo_typeof pre))) =
        SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type T)) :=
    eval_seq_empty_typeof M pre (__eo_to_smt_type T) hPreSmtTy
  have hEvalEq : __smtx_model_eval M (__eo_to_smt lhs) =
      __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_replace (__eo_to_smt t) (__eo_to_smt pat)
          (__eo_to_smt repl)) =
      __smtx_model_eval M
        (SmtTerm.str_concat (__eo_to_smt pre)
          (SmtTerm.str_concat (__eo_to_smt repl)
            (SmtTerm.str_concat (__eo_to_smt post)
              (__eo_to_smt (__seq_empty (__eo_typeof pre))))))
    rw [StrEqReplSupport.smtx_eval_str_replace_term_eq,
      StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      StrSubstrContainsSupport.smtx_eval_str_concat_term_eq,
      hTEval, hPatEval, hReplEval, hPreEval, hPostEval, hEmptyEval]
    simp [__smtx_model_eval_str_replace, __smtx_model_eval_str_concat,
      native_seq_concat, native_unpack_seq, Smtm.native_unpack_pack_seq,
      hTElem, hPatElem,
      hReplElem, hPreElem, hPostElem, elem_typeof_pack_seq,
      hNativeReplace]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

end StrReplaceFindSupport
