module

public import Cpc.Proofs.RuleSupport.StrConcatSupport
import all Cpc.Proofs.RuleSupport.StrConcatSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev concatEqNormalize (rev x : Term) : Term :=
  __eo_ite rev (__eo_list_rev (Term.UOp UserOp.str_concat) x) x

private abbrev concatEqStrip (rev s t : Term) : Term :=
  __str_strip_prefix (concatEqNormalize rev (__str_nary_intro s))
    (concatEqNormalize rev (__str_nary_intro t))

private abbrev concatEqLhs (rev s t : Term) : Term :=
  __str_nary_elim (concatEqNormalize rev (__pair_first (concatEqStrip rev s t)))

private abbrev concatEqRhs (rev s t : Term) : Term :=
  __str_nary_elim (concatEqNormalize rev (__pair_second (concatEqStrip rev s t)))

private theorem concatEq_seq_pack_of_both_concat
    (sHead sTail tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (mkEq (mkConcat sHead sTail) (mkConcat tHead tTail))) :
    ∃ T,
      __smtx_typeof (__eo_to_smt (mkConcat sHead sTail)) =
        SmtType.Seq T ∧
      __smtx_typeof
          (__eo_to_smt (__str_nary_intro (mkConcat sHead sTail))) ≠
        SmtType.None ∧
      __smtx_typeof
          (__eo_to_smt (__str_nary_intro (mkConcat tHead tTail))) ≠
        SmtType.None := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkConcat sHead sTail) (mkConcat tHead tTail) hPremBool with
    ⟨hSame, hLeftNN⟩
  rcases smt_typeof_str_concat_seq_of_non_none sHead sTail hLeftNN with
    ⟨T, hLeftTy⟩
  have hRightNN :
      __smtx_typeof (__eo_to_smt (mkConcat tHead tTail)) ≠
        SmtType.None := by
    rw [← hSame]
    exact hLeftNN
  exact ⟨T, hLeftTy,
    str_nary_intro_concat_has_smt_translation sHead sTail hLeftNN,
    str_nary_intro_concat_has_smt_translation tHead tTail hRightNN⟩

private theorem concatEq_seq_pack_of_left_concat
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None) :
    ∃ T,
      __smtx_typeof (__eo_to_smt (mkConcat sHead sTail)) =
        SmtType.Seq T ∧
      __smtx_typeof
          (__eo_to_smt (__str_nary_intro (mkConcat sHead sTail))) ≠
        SmtType.None ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkConcat sHead sTail) t hPremBool with
    ⟨_, hLeftNN⟩
  rcases smt_typeof_str_concat_seq_of_non_none sHead sTail hLeftNN with
    ⟨T, hLeftTy⟩
  exact ⟨T, hLeftTy,
    str_nary_intro_concat_has_smt_translation sHead sTail hLeftNN,
    hIntroTNN⟩

private theorem concatEq_seq_pack_of_right_concat
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None) :
    ∃ T,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None ∧
      __smtx_typeof
          (__eo_to_smt (__str_nary_intro (mkConcat tHead tTail))) ≠
        SmtType.None := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      s (mkConcat tHead tTail) hPremBool with
    ⟨hSame, hLeftNN⟩
  have hRightNN :
      __smtx_typeof (__eo_to_smt (mkConcat tHead tTail)) ≠
        SmtType.None := by
    rw [← hSame]
    exact hLeftNN
  rcases smt_typeof_str_concat_seq_of_non_none tHead tTail hRightNN with
    ⟨T, hRightTy⟩
  have hLeftTy :
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T := by
    rw [hSame, hRightTy]
  exact ⟨T, hLeftTy, hIntroSNN,
    str_nary_intro_concat_has_smt_translation tHead tTail hRightNN⟩

private theorem concatEq_seq_pack_of_left_concat_intro_eq_self
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hIntroEq : __str_nary_intro t = t) :
    ∃ T,
      __smtx_typeof (__eo_to_smt (mkConcat sHead sTail)) =
        SmtType.Seq T ∧
      __smtx_typeof
          (__eo_to_smt (__str_nary_intro (mkConcat sHead sTail))) ≠
        SmtType.None ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkConcat sHead sTail) t hPremBool with
    ⟨hSame, hLeftNN⟩
  have hRightNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [← hSame]
    exact hLeftNN
  have hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
    simpa [hIntroEq] using hRightNN
  exact concatEq_seq_pack_of_left_concat sHead sTail t hPremBool
    hIntroTNN

private theorem concatEq_seq_pack_of_right_concat_intro_eq_self
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hIntroEq : __str_nary_intro s = s) :
    ∃ T,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None ∧
      __smtx_typeof
          (__eo_to_smt (__str_nary_intro (mkConcat tHead tTail))) ≠
        SmtType.None := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      s (mkConcat tHead tTail) hPremBool with
    ⟨_hSame, hLeftNN⟩
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None := by
    simpa [hIntroEq] using hLeftNN
  exact concatEq_seq_pack_of_right_concat s tHead tTail hPremBool
    hIntroSNN

private theorem eq_bool_seq_of_left_concat
    (sHead sTail t : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t)) :
    ∃ T,
      __smtx_typeof (__eo_to_smt (mkConcat sHead sTail)) =
        SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt t) = SmtType.Seq T := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkConcat sHead sTail) t hPremBool with
    ⟨hSame, hLeftNN⟩
  rcases smt_typeof_str_concat_seq_of_non_none sHead sTail hLeftNN with
    ⟨T, hLeftTy⟩
  exact ⟨T, hLeftTy, by rw [← hSame, hLeftTy]⟩

private theorem eq_bool_seq_of_right_concat
    (s tHead tTail : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail))) :
    ∃ T,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (mkConcat tHead tTail)) =
        SmtType.Seq T := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      s (mkConcat tHead tTail) hPremBool with
    ⟨hSame, hLeftNN⟩
  have hRightNN :
      __smtx_typeof (__eo_to_smt (mkConcat tHead tTail)) ≠
        SmtType.None := by
    rw [← hSame]
    exact hLeftNN
  rcases smt_typeof_str_concat_seq_of_non_none tHead tTail hRightNN with
    ⟨T, hRightTy⟩
  exact ⟨T, by rw [hSame, hRightTy], hRightTy⟩

private theorem eq_bool_right_seq_of_left_seq (x y : Term) (T : SmtType)
    (hBool : RuleProofs.eo_has_bool_type (mkEq x y))
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type x y hBool with
    ⟨hSame, _⟩
  rw [← hSame, hxTy]

private theorem eq_bool_left_seq_of_right_seq (x y : Term) (T : SmtType)
    (hBool : RuleProofs.eo_has_bool_type (mkEq x y))
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type x y hBool with
    ⟨hSame, _⟩
  rw [hSame, hyTy]

private theorem eo_prog_concat_eq_eq_of_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) =
      mkEq (concatEqLhs rev s t) (concatEqRhs rev s t) := by
  have hRev : rev ≠ Term.Stuck := by
    intro h
    subst rev
    simp [__eo_prog_concat_eq] at hProg
  have hProg' :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t))
          (concatEqRhs rev s t) ≠ Term.Stuck := by
    cases rev <;>
      simp [__eo_prog_concat_eq, concatEqLhs, concatEqRhs, concatEqStrip,
        concatEqNormalize] at hRev hProg ⊢
    all_goals first | exact hProg | contradiction
  have hInner :
      __eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t) ≠
        Term.Stuck := by
    exact eo_mk_apply_fun_ne_stuck_of_ne_stuck
        (__eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t))
        (concatEqRhs rev s t) hProg'
  have hInnerEq :
      __eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t) =
        Term.Apply (Term.UOp UserOp.eq) (concatEqLhs rev s t) :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.eq)
      (concatEqLhs rev s t) hInner
  have hOuterEq :
      __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) =
        Term.Apply (__eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t))
          (concatEqRhs rev s t) := by
    cases rev <;>
      simp [__eo_prog_concat_eq, concatEqLhs, concatEqRhs, concatEqStrip,
        concatEqNormalize] at hRev hProg' ⊢
    all_goals first
      | exact eo_mk_apply_eq_apply_of_ne_stuck _ _ hProg'
      | contradiction
  rw [hOuterEq, hInnerEq]

private theorem eo_prog_concat_eq_mk_apply_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t))
      (concatEqRhs rev s t) ≠ Term.Stuck := by
  have hRev : rev ≠ Term.Stuck := by
    intro h
    subst rev
    simp [__eo_prog_concat_eq] at hProg
  cases rev <;>
    simp [__eo_prog_concat_eq, concatEqLhs, concatEqRhs, concatEqStrip,
      concatEqNormalize] at hRev hProg ⊢
  all_goals first | exact hProg | contradiction

private theorem concatEqLhs_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqLhs rev s t ≠ Term.Stuck := by
  have hApply := eo_prog_concat_eq_mk_apply_ne_stuck rev s t hProg
  have hInner :
      __eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t) ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck
      (__eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t))
      (concatEqRhs rev s t) hApply
  exact eo_mk_apply_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.eq)
    (concatEqLhs rev s t) hInner

private theorem concatEqRhs_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqRhs rev s t ≠ Term.Stuck := by
  have hApply := eo_prog_concat_eq_mk_apply_ne_stuck rev s t hProg
  exact eo_mk_apply_arg_ne_stuck_of_ne_stuck
    (__eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t))
    (concatEqRhs rev s t) hApply

private theorem concatEq_rev_cases_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    rev = Term.Boolean true ∨ rev = Term.Boolean false := by
  have hLhs := concatEqLhs_ne_stuck_of_prog_ne_stuck rev s t hProg
  have hNorm :
      concatEqNormalize rev (__pair_first (concatEqStrip rev s t)) ≠ Term.Stuck :=
    str_nary_elim_arg_ne_stuck_of_ne_stuck
      (concatEqNormalize rev (__pair_first (concatEqStrip rev s t))) hLhs
  exact eo_ite_cases_of_ne_stuck rev
    (__eo_list_rev (Term.UOp UserOp.str_concat) (__pair_first (concatEqStrip rev s t)))
    (__pair_first (concatEqStrip rev s t)) hNorm

private theorem concatEqStrip_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqStrip rev s t ≠ Term.Stuck := by
  have hLhs := concatEqLhs_ne_stuck_of_prog_ne_stuck rev s t hProg
  have hNorm :
      concatEqNormalize rev (__pair_first (concatEqStrip rev s t)) ≠ Term.Stuck :=
    str_nary_elim_arg_ne_stuck_of_ne_stuck
      (concatEqNormalize rev (__pair_first (concatEqStrip rev s t))) hLhs
  rcases concatEq_rev_cases_of_prog_ne_stuck rev s t hProg with hRev | hRev
  · have hRevFirst :
        __eo_list_rev (Term.UOp UserOp.str_concat)
          (__pair_first (concatEqStrip rev s t)) ≠ Term.Stuck :=
      eo_ite_then_ne_stuck_of_ne_stuck rev
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__pair_first (concatEqStrip rev s t)))
        (__pair_first (concatEqStrip rev s t)) hNorm hRev
    have hFirst : __pair_first (concatEqStrip rev s t) ≠ Term.Stuck :=
      eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
        (__pair_first (concatEqStrip rev s t)) hRevFirst
    exact pair_first_arg_ne_stuck_of_ne_stuck (concatEqStrip rev s t) hFirst
  · have hFirst : __pair_first (concatEqStrip rev s t) ≠ Term.Stuck :=
      eo_ite_else_ne_stuck_of_ne_stuck rev
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__pair_first (concatEqStrip rev s t)))
        (__pair_first (concatEqStrip rev s t)) hNorm hRev
    exact pair_first_arg_ne_stuck_of_ne_stuck (concatEqStrip rev s t) hFirst

private theorem concatEqNormalize_first_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqNormalize rev (__pair_first (concatEqStrip rev s t)) ≠
      Term.Stuck := by
  have hLhs := concatEqLhs_ne_stuck_of_prog_ne_stuck rev s t hProg
  exact str_nary_elim_arg_ne_stuck_of_ne_stuck
    (concatEqNormalize rev (__pair_first (concatEqStrip rev s t))) hLhs

private theorem concatEqNormalize_second_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqNormalize rev (__pair_second (concatEqStrip rev s t)) ≠
      Term.Stuck := by
  have hRhs := concatEqRhs_ne_stuck_of_prog_ne_stuck rev s t hProg
  exact str_nary_elim_arg_ne_stuck_of_ne_stuck
    (concatEqNormalize rev (__pair_second (concatEqStrip rev s t))) hRhs

private theorem concatEqNormalize_left_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqNormalize rev (__str_nary_intro s) ≠ Term.Stuck := by
  have hStrip := concatEqStrip_ne_stuck_of_prog_ne_stuck rev s t hProg
  exact str_strip_prefix_left_ne_stuck_of_ne_stuck
    (concatEqNormalize rev (__str_nary_intro s))
    (concatEqNormalize rev (__str_nary_intro t)) hStrip

private theorem concatEqNormalize_right_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqNormalize rev (__str_nary_intro t) ≠ Term.Stuck := by
  have hStrip := concatEqStrip_ne_stuck_of_prog_ne_stuck rev s t hProg
  exact str_strip_prefix_right_ne_stuck_of_ne_stuck
    (concatEqNormalize rev (__str_nary_intro s))
    (concatEqNormalize rev (__str_nary_intro t)) hStrip

private theorem str_nary_intro_left_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    __str_nary_intro s ≠ Term.Stuck := by
  have hNorm := concatEqNormalize_left_ne_stuck_of_prog_ne_stuck rev s t hProg
  rcases concatEq_rev_cases_of_prog_ne_stuck rev s t hProg with hRev | hRev
  · have hRevIntro :
        __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
          Term.Stuck :=
      eo_ite_then_ne_stuck_of_ne_stuck rev
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
        (__str_nary_intro s) hNorm hRev
    exact eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro s) hRevIntro
  · exact eo_ite_else_ne_stuck_of_ne_stuck rev
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
      (__str_nary_intro s) hNorm hRev

private theorem str_nary_intro_right_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    __str_nary_intro t ≠ Term.Stuck := by
  have hNorm := concatEqNormalize_right_ne_stuck_of_prog_ne_stuck rev s t hProg
  rcases concatEq_rev_cases_of_prog_ne_stuck rev s t hProg with hRev | hRev
  · have hRevIntro :
        __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) ≠
          Term.Stuck :=
      eo_ite_then_ne_stuck_of_ne_stuck rev
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
        (__str_nary_intro t) hNorm hRev
    exact eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro t) hRevIntro
  · exact eo_ite_else_ne_stuck_of_ne_stuck rev
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
      (__str_nary_intro t) hNorm hRev

private theorem eo_prog_concat_eq_premise_eq_shape_of_ne_stuck (rev x1 : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf x1) ≠ Term.Stuck) :
    ∃ s t, x1 = mkEq s t := by
  cases x1 with
  | Apply f t =>
      cases f with
      | Apply g s =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  exact ⟨s, t, rfl⟩
              | _ =>
                  cases rev <;> simp [__eo_prog_concat_eq] at hProg
          | _ =>
              cases rev <;> simp [__eo_prog_concat_eq] at hProg
      | _ =>
          cases rev <;> simp [__eo_prog_concat_eq] at hProg
  | _ =>
      cases rev <;> simp [__eo_prog_concat_eq] at hProg

private theorem concatEqNormalize_true (x : Term) :
    concatEqNormalize (Term.Boolean true) x =
      __eo_list_rev (Term.UOp UserOp.str_concat) x := by
  rfl

private theorem concatEqStrip_false (s t : Term) :
    concatEqStrip (Term.Boolean false) s t =
      __str_strip_prefix (__str_nary_intro s) (__str_nary_intro t) := by
  rfl

private theorem concatEqStrip_true (s t : Term) :
    concatEqStrip (Term.Boolean true) s t =
      __str_strip_prefix
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t)) := by
  rfl

private theorem concatEqLhs_false (s t : Term) :
    concatEqLhs (Term.Boolean false) s t =
      __str_nary_elim
        (__pair_first (__str_strip_prefix (__str_nary_intro s) (__str_nary_intro t))) := by
  rfl

private theorem concatEqRhs_false (s t : Term) :
    concatEqRhs (Term.Boolean false) s t =
      __str_nary_elim
        (__pair_second (__str_strip_prefix (__str_nary_intro s) (__str_nary_intro t))) := by
  rfl

private theorem concatEqLhs_true (s t : Term) :
    concatEqLhs (Term.Boolean true) s t =
      __str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (__pair_first
            (__str_strip_prefix
              (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
              (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))))) := by
  rfl

private theorem concatEqRhs_true (s t : Term) :
    concatEqRhs (Term.Boolean true) s t =
      __str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (__pair_second
            (__str_strip_prefix
              (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
              (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))))) := by
  rfl

private theorem concatEq_true_rev_intro_left_ne_stuck_of_prog_ne_stuck
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
      Term.Stuck := by
  simpa [concatEqNormalize_true] using
    concatEqNormalize_left_ne_stuck_of_prog_ne_stuck
      (Term.Boolean true) s t hProg

private theorem concatEq_true_rev_intro_right_ne_stuck_of_prog_ne_stuck
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) ≠
      Term.Stuck := by
  simpa [concatEqNormalize_true] using
    concatEqNormalize_right_ne_stuck_of_prog_ne_stuck
      (Term.Boolean true) s t hProg

private theorem concatEq_true_rev_first_ne_stuck_of_prog_ne_stuck
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat)
        (__pair_first (concatEqStrip (Term.Boolean true) s t)) ≠
      Term.Stuck := by
  simpa [concatEqNormalize_true] using
    concatEqNormalize_first_ne_stuck_of_prog_ne_stuck
      (Term.Boolean true) s t hProg

private theorem concatEq_true_rev_second_ne_stuck_of_prog_ne_stuck
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat)
        (__pair_second (concatEqStrip (Term.Boolean true) s t)) ≠
      Term.Stuck := by
  simpa [concatEqNormalize_true] using
    concatEqNormalize_second_ne_stuck_of_prog_ne_stuck
      (Term.Boolean true) s t hProg

private theorem str_nary_elim_seq_empty_typeof_ne_stuck_of_concat_eq_true_generated
    (s : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s s)) ≠
        Term.Stuck)
    (hsNonStuck : s ≠ Term.Stuck)
    (hIntroSConcat :
      __str_nary_intro s = mkConcat s (__seq_empty (__eo_typeof s)) ∧
        __eo_is_list_nil (Term.UOp UserOp.str_concat)
          (__seq_empty (__eo_typeof s)) = Term.Boolean true) :
    __str_nary_elim (__seq_empty (__eo_typeof s)) ≠ Term.Stuck := by
  let empty := __seq_empty (__eo_typeof s)
  have hIntroEq : __str_nary_intro s = mkConcat s empty := by
    simpa [empty] using hIntroSConcat.1
  have hEmptyNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) empty =
        Term.Boolean true := by
    simpa [empty] using hIntroSConcat.2
  have hEmptyNonStuck : empty ≠ Term.Stuck :=
    term_ne_stuck_of_eo_is_list_nil_true
      (Term.UOp UserOp.str_concat) empty hEmptyNil
  have hRevIntroNN :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
        Term.Stuck :=
    concatEq_true_rev_intro_left_ne_stuck_of_prog_ne_stuck s s hProg
  have hRevIntroEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) =
        mkConcat s empty := by
    rw [hIntroEq]
    exact eo_list_rev_str_concat_cons_nil_eq_of_ne_stuck s empty
      hEmptyNil (by simpa [hIntroEq] using hRevIntroNN)
  have hStripEq :
      __str_strip_prefix (mkConcat s empty) (mkConcat s empty) =
        mkPair empty empty := by
    rw [str_strip_prefix_concat_of_eo_eq_true s s empty empty
      (eo_eq_self_true_of_ne_stuck s hsNonStuck)]
    exact str_strip_prefix_left_not_str_concat empty empty
      hEmptyNonStuck hEmptyNonStuck
      (seq_empty_not_str_concat (__eo_typeof s)
        (by simpa [empty] using hEmptyNonStuck))
  have hLhs :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) empty) ≠
        Term.Stuck := by
    simpa [concatEqLhs_true, concatEqStrip_true, hRevIntroEq, hStripEq,
      mkPair, pair_first_pair] using
      concatEqLhs_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s s hProg
  have hRevEmptyEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) empty = empty :=
    eo_list_rev_str_concat_nil_eq_of_nil_true empty hEmptyNil
  simpa [empty, hRevEmptyEq] using hLhs

private theorem str_nary_elim_seq_empty_typeof_ne_stuck_of_concat_eq_false_generated
    (s : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s s)) ≠
        Term.Stuck)
    (hsNonStuck : s ≠ Term.Stuck)
    (hIntroSConcat :
      __str_nary_intro s = mkConcat s (__seq_empty (__eo_typeof s)) ∧
        __eo_is_list_nil (Term.UOp UserOp.str_concat)
          (__seq_empty (__eo_typeof s)) = Term.Boolean true) :
    __str_nary_elim (__seq_empty (__eo_typeof s)) ≠ Term.Stuck := by
  let empty := __seq_empty (__eo_typeof s)
  have hIntroEq : __str_nary_intro s = mkConcat s empty := by
    simpa [empty] using hIntroSConcat.1
  have hEmptyNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) empty =
        Term.Boolean true := by
    simpa [empty] using hIntroSConcat.2
  have hEmptyNonStuck : empty ≠ Term.Stuck :=
    term_ne_stuck_of_eo_is_list_nil_true
      (Term.UOp UserOp.str_concat) empty hEmptyNil
  have hStripEq :
      __str_strip_prefix (mkConcat s empty) (mkConcat s empty) =
        mkPair empty empty := by
    rw [str_strip_prefix_concat_of_eo_eq_true s s empty empty
      (eo_eq_self_true_of_ne_stuck s hsNonStuck)]
    exact str_strip_prefix_left_not_str_concat empty empty
      hEmptyNonStuck hEmptyNonStuck
      (seq_empty_not_str_concat (__eo_typeof s)
        (by simpa [empty] using hEmptyNonStuck))
  simpa [concatEqLhs_false, concatEqStrip_false, hIntroEq, hStripEq, mkPair,
    pair_first_pair] using
    concatEqLhs_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s s hProg

private theorem str_nary_elim_str_concat_nil_eq_self_of_nil_true
    (nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
        Term.Boolean true) :
    __str_nary_elim nil = nil := by
  have hList :
      __eo_is_list (Term.UOp UserOp.str_concat) nil =
        Term.Boolean true :=
    eo_is_list_str_concat_nil_true_of_nil_true nil hNil
  have hElim2 : __eo_list_singleton_elim_2 nil = nil := by
    cases nil <;>
      simp [__eo_list_singleton_elim_2, __eo_is_list_nil,
        __eo_is_list_nil_str_concat, __eo_eq, native_teq] at hNil ⊢
  simp [__str_nary_elim, __eo_list_singleton_elim, hList, hElim2,
    __eo_requires, native_teq, native_ite, SmtEval.native_ite,
    SmtEval.native_not]

private theorem smt_typeof_seq_of_seq_empty_typeof_eo_type_ne_stuck
    (x : Term)
    (hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None)
    (hEmptyTy :
      __eo_typeof (__seq_empty (__eo_typeof x)) ≠ Term.Stuck) :
    ∃ T, __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
  let A := __eo_typeof x
  have hASeq : ∃ U, A = Term.Apply (Term.UOp UserOp.Seq) U := by
    by_cases hAStuck : A = Term.Stuck
    · have hEmptyStuck : __eo_typeof (__seq_empty A) = Term.Stuck := by
        rw [hAStuck]
        rfl
      exact False.elim (hEmptyTy (by simpa [A] using hEmptyStuck))
    · by_cases hSeq : ∃ U, A = Term.Apply (Term.UOp UserOp.Seq) U
      · exact hSeq
      · have hDefault :=
          seq_empty_default_of_not_seq_ne_stuck A hAStuck hSeq
        have hStuck :=
          eo_typeof_seq_empty_stuck_of_not_seq_ne_stuck A hAStuck hSeq
        have hEmptyStuck : __eo_typeof (__seq_empty A) = Term.Stuck := by
          rw [hDefault]
          exact hStuck
        exact False.elim (hEmptyTy (by simpa [A] using hEmptyStuck))
  rcases hASeq with ⟨U, hASeq⟩
  have hMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hxNN
  rw [show __eo_typeof x = A from rfl, hASeq] at hMatch
  by_cases hUNone : __eo_to_smt_type U = SmtType.None
  · have hNone : __smtx_typeof (__eo_to_smt x) = SmtType.None := by
      simpa [TranslationProofs.eo_to_smt_type_seq, __smtx_typeof_guard,
        native_ite, native_Teq, hUNone] using hMatch
    exact False.elim (hxNN hNone)
  · exact ⟨__eo_to_smt_type U, by
      simpa [TranslationProofs.eo_to_smt_type_seq, __smtx_typeof_guard,
        native_ite, native_Teq, hUNone] using hMatch⟩

private theorem seq_empty_typeof_eo_type_ne_stuck_of_concat_eq_true_generated
    (s : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s s)) ≠
        Term.Stuck)
    (hResultTy :
      __eo_typeof
          (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s s))) =
        Term.Bool)
    (hsNonStuck : s ≠ Term.Stuck)
    (hIntroSConcat :
      __str_nary_intro s = mkConcat s (__seq_empty (__eo_typeof s)) ∧
        __eo_is_list_nil (Term.UOp UserOp.str_concat)
          (__seq_empty (__eo_typeof s)) = Term.Boolean true) :
    __eo_typeof (__seq_empty (__eo_typeof s)) ≠ Term.Stuck := by
  let empty := __seq_empty (__eo_typeof s)
  have hIntroEq : __str_nary_intro s = mkConcat s empty := by
    simpa [empty] using hIntroSConcat.1
  have hEmptyNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) empty =
        Term.Boolean true := by
    simpa [empty] using hIntroSConcat.2
  have hEmptyNonStuck : empty ≠ Term.Stuck :=
    term_ne_stuck_of_eo_is_list_nil_true
      (Term.UOp UserOp.str_concat) empty hEmptyNil
  have hRevIntroNN :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
        Term.Stuck :=
    concatEq_true_rev_intro_left_ne_stuck_of_prog_ne_stuck s s hProg
  have hRevIntroEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) =
        mkConcat s empty := by
    rw [hIntroEq]
    exact eo_list_rev_str_concat_cons_nil_eq_of_ne_stuck s empty
      hEmptyNil (by simpa [hIntroEq] using hRevIntroNN)
  have hStripEq :
      __str_strip_prefix (mkConcat s empty) (mkConcat s empty) =
        mkPair empty empty := by
    rw [str_strip_prefix_concat_of_eo_eq_true s s empty empty
      (eo_eq_self_true_of_ne_stuck s hsNonStuck)]
    exact str_strip_prefix_left_not_str_concat empty empty
      hEmptyNonStuck hEmptyNonStuck
      (seq_empty_not_str_concat (__eo_typeof s)
        (by simpa [empty] using hEmptyNonStuck))
  have hProgEq :=
    eo_prog_concat_eq_eq_of_ne_stuck (Term.Boolean true) s s hProg
  have hFinalTy :
      __eo_typeof
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) empty))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) empty))) =
        Term.Bool := by
    rw [hProgEq] at hResultTy
    simpa [concatEqLhs_true, concatEqRhs_true, concatEqStrip_true,
      hRevIntroEq, hStripEq, mkPair, pair_first_pair, pair_second_pair]
      using hResultTy
  have hRevEmptyEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) empty = empty :=
    eo_list_rev_str_concat_nil_eq_of_nil_true empty hEmptyNil
  have hFinalTy' :
      __eo_typeof (mkEq (__str_nary_elim empty) (__str_nary_elim empty)) =
        Term.Bool := by
    simpa [hRevEmptyEq] using hFinalTy
  have hElimEq : __str_nary_elim empty = empty :=
    str_nary_elim_str_concat_nil_eq_self_of_nil_true empty hEmptyNil
  have hFinalTyEmpty : __eo_typeof (mkEq empty empty) = Term.Bool := by
    simpa [hElimEq] using hFinalTy'
  change __eo_typeof_eq (__eo_typeof empty) (__eo_typeof empty) = Term.Bool
    at hFinalTyEmpty
  by_cases hEmptyType : __eo_typeof empty = Term.Stuck
  · rw [hEmptyType] at hFinalTyEmpty
    simp [__eo_typeof_eq] at hFinalTyEmpty
  · exact hEmptyType

private theorem seq_empty_typeof_eo_type_ne_stuck_of_concat_eq_false_generated
    (s : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s s)) ≠
        Term.Stuck)
    (hResultTy :
      __eo_typeof
          (__eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s s))) =
        Term.Bool)
    (hsNonStuck : s ≠ Term.Stuck)
    (hIntroSConcat :
      __str_nary_intro s = mkConcat s (__seq_empty (__eo_typeof s)) ∧
        __eo_is_list_nil (Term.UOp UserOp.str_concat)
          (__seq_empty (__eo_typeof s)) = Term.Boolean true) :
    __eo_typeof (__seq_empty (__eo_typeof s)) ≠ Term.Stuck := by
  let empty := __seq_empty (__eo_typeof s)
  have hIntroEq : __str_nary_intro s = mkConcat s empty := by
    simpa [empty] using hIntroSConcat.1
  have hEmptyNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) empty =
        Term.Boolean true := by
    simpa [empty] using hIntroSConcat.2
  have hEmptyNonStuck : empty ≠ Term.Stuck :=
    term_ne_stuck_of_eo_is_list_nil_true
      (Term.UOp UserOp.str_concat) empty hEmptyNil
  have hStripEq :
      __str_strip_prefix (mkConcat s empty) (mkConcat s empty) =
        mkPair empty empty := by
    rw [str_strip_prefix_concat_of_eo_eq_true s s empty empty
      (eo_eq_self_true_of_ne_stuck s hsNonStuck)]
    exact str_strip_prefix_left_not_str_concat empty empty
      hEmptyNonStuck hEmptyNonStuck
      (seq_empty_not_str_concat (__eo_typeof s)
        (by simpa [empty] using hEmptyNonStuck))
  have hProgEq :=
    eo_prog_concat_eq_eq_of_ne_stuck (Term.Boolean false) s s hProg
  have hFinalTy :
      __eo_typeof (mkEq (__str_nary_elim empty) (__str_nary_elim empty)) =
        Term.Bool := by
    rw [hProgEq] at hResultTy
    simpa [concatEqLhs_false, concatEqRhs_false, concatEqStrip_false,
      hIntroEq, hStripEq, mkPair, pair_first_pair, pair_second_pair]
      using hResultTy
  have hElimEq : __str_nary_elim empty = empty :=
    str_nary_elim_str_concat_nil_eq_self_of_nil_true empty hEmptyNil
  have hFinalTyEmpty : __eo_typeof (mkEq empty empty) = Term.Bool := by
    simpa [hElimEq] using hFinalTy
  change __eo_typeof_eq (__eo_typeof empty) (__eo_typeof empty) = Term.Bool
    at hFinalTyEmpty
  by_cases hEmptyType : __eo_typeof empty = Term.Stuck
  · rw [hEmptyType] at hFinalTyEmpty
    simp [__eo_typeof_eq] at hFinalTyEmpty
  · exact hEmptyType

private theorem eo_interprets_rev_str_strip_prefix_result
    (M : SmtModel) (x y : Term)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) x))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) y))) true)
    (hStrip : __str_strip_prefix x y ≠ Term.Stuck)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first (__str_strip_prefix x y))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second (__str_strip_prefix x y))))) true := by
  fun_cases __str_strip_prefix x y
  · simp [__str_strip_prefix] at hStrip
  · simp [__str_strip_prefix] at hStrip
  · rename_i t t2 u s2
    subst_vars
    have hIte :
        __eo_ite (__eo_eq t u) (__str_strip_prefix t2 s2)
          (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) ≠
          Term.Stuck := by
      simpa [__str_strip_prefix] using hStrip
    rcases eo_ite_cases_of_ne_stuck (__eo_eq t u) (__str_strip_prefix t2 s2)
        (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) hIte with
      hCond | hCond
    · have hTailEq :=
        hCancel t u t2 s2 hStrip hCond hXY
      have hTailNonStuck : __str_strip_prefix t2 s2 ≠ Term.Stuck := by
        simpa [hCond, eo_ite_true] using hIte
      exact eo_interprets_rev_strip_prefix_concat_true_of_tail M t u t2 s2
        hCond
        (eo_interprets_rev_str_strip_prefix_result M t2 s2 hTailEq
          hTailNonStuck hCancel)
    · exact eo_interprets_rev_strip_prefix_concat_false_of_eq M t u t2 s2
        hCond hXY
  · simpa [__eo_l_1___str_strip_prefix, mkPair, pair_first_pair,
      pair_second_pair] using hXY
termination_by sizeOf x + sizeOf y
decreasing_by
  all_goals subst_vars; simp_wf; omega

private theorem eo_interprets_rev_str_strip_prefix_result_with_final
    (M : SmtModel) (x y : Term)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) x))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) y))) true)
    (hStrip : __str_strip_prefix x y ≠ Term.Stuck)
    (hFinalLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first (__str_strip_prefix x y))) ≠ Term.Stuck)
    (hFinalRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second (__str_strip_prefix x y))) ≠ Term.Stuck)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first (__str_strip_prefix x y))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second (__str_strip_prefix x y))))) true := by
  fun_cases __str_strip_prefix x y
  · simp [__str_strip_prefix] at hStrip
  · simp [__str_strip_prefix] at hStrip
  · rename_i t t2 u s2
    subst_vars
    have hIte :
        __eo_ite (__eo_eq t u) (__str_strip_prefix t2 s2)
          (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) ≠
          Term.Stuck := by
      simpa [__str_strip_prefix] using hStrip
    rcases eo_ite_cases_of_ne_stuck (__eo_eq t u) (__str_strip_prefix t2 s2)
        (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) hIte with
      hCond | hCond
    · have hTailFinalLeft :
          __str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck := by
        simpa [pair_first_str_strip_prefix_concat_of_eo_eq_true
            t u t2 s2 hCond] using hFinalLeft
      have hTailFinalRight :
          __str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck := by
        simpa [pair_second_str_strip_prefix_concat_of_eo_eq_true
            t u t2 s2 hCond] using hFinalRight
      have hTailEq :=
        hCancel t u t2 s2 hStrip hCond hTailFinalLeft hTailFinalRight hXY
      have hTailNonStuck : __str_strip_prefix t2 s2 ≠ Term.Stuck := by
        simpa [hCond, eo_ite_true] using hIte
      exact eo_interprets_rev_strip_prefix_concat_true_of_tail M t u t2 s2
        hCond
        (eo_interprets_rev_str_strip_prefix_result_with_final M t2 s2
          hTailEq hTailNonStuck hTailFinalLeft hTailFinalRight hCancel)
    · exact eo_interprets_rev_strip_prefix_concat_false_of_eq M t u t2 s2
        hCond hXY
  · simpa [__eo_l_1___str_strip_prefix, mkPair, pair_first_pair,
      pair_second_pair] using hXY
termination_by sizeOf x + sizeOf y
decreasing_by
  all_goals subst_vars; simp_wf; omega

private theorem eo_interprets_rev_str_strip_prefix_result_with_final_seq
    (M : SmtModel) (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) x))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) y))) true)
    (hStrip : __str_strip_prefix x y ≠ Term.Stuck)
    (hFinalLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first (__str_strip_prefix x y))) ≠ Term.Stuck)
    (hFinalRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second (__str_strip_prefix x y))) ≠ Term.Stuck)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T ->
        __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first (__str_strip_prefix x y))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second (__str_strip_prefix x y))))) true := by
  fun_cases __str_strip_prefix x y
  · simp [__str_strip_prefix] at hStrip
  · simp [__str_strip_prefix] at hStrip
  · rename_i t t2 u s2
    subst_vars
    rcases str_concat_args_of_seq_type t t2 T hxTy with
      ⟨_htTy, ht2Ty⟩
    rcases str_concat_args_of_seq_type u s2 T hyTy with
      ⟨_huTy, hs2Ty⟩
    have hIte :
        __eo_ite (__eo_eq t u) (__str_strip_prefix t2 s2)
          (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) ≠
          Term.Stuck := by
      simpa [__str_strip_prefix] using hStrip
    rcases eo_ite_cases_of_ne_stuck (__eo_eq t u) (__str_strip_prefix t2 s2)
        (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) hIte with
      hCond | hCond
    · have hTailFinalLeft :
          __str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck := by
        simpa [pair_first_str_strip_prefix_concat_of_eo_eq_true
            t u t2 s2 hCond] using hFinalLeft
      have hTailFinalRight :
          __str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck := by
        simpa [pair_second_str_strip_prefix_concat_of_eo_eq_true
            t u t2 s2 hCond] using hFinalRight
      have hTailEq :=
        hCancel t u t2 s2 hStrip hCond hxTy hyTy hTailFinalLeft
          hTailFinalRight hXY
      have hTailNonStuck : __str_strip_prefix t2 s2 ≠ Term.Stuck := by
        simpa [hCond, eo_ite_true] using hIte
      exact eo_interprets_rev_strip_prefix_concat_true_of_tail M t u t2 s2
        hCond
        (eo_interprets_rev_str_strip_prefix_result_with_final_seq M t2 s2
          T ht2Ty hs2Ty hTailEq hTailNonStuck hTailFinalLeft
          hTailFinalRight hCancel)
    · exact eo_interprets_rev_strip_prefix_concat_false_of_eq M t u t2 s2
        hCond hXY
  · simpa [__eo_l_1___str_strip_prefix, mkPair, pair_first_pair,
      pair_second_pair] using hXY
termination_by sizeOf x + sizeOf y
decreasing_by
  all_goals subst_vars; simp_wf; omega

private theorem eo_interprets_concat_eq_true_from_rev_strip_with_final_seq
    (M : SmtModel) (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠ SmtType.None)
    (hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠ SmtType.None)
    (hRevStrip :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T ->
        __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq (concatEqLhs (Term.Boolean true) s t)
        (concatEqRhs (Term.Boolean true) s t)) true := by
  let revS := __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s)
  let revT := __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t)
  let strip := __str_strip_prefix revS revT
  have hIntroS : __str_nary_intro s ≠ Term.Stuck :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hIntroT : __str_nary_intro t ≠ Term.Stuck :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck s T hsTy hIntroSNN
      hIntroS
  have hIntroTTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy hIntroTNN
      hIntroT
  have hRevSNonStuck : revS ≠ Term.Stuck := by
    simpa [revS] using
      concatEq_true_rev_intro_left_ne_stuck_of_prog_ne_stuck s t hProg
  have hRevTNonStuck : revT ≠ Term.Stuck := by
    simpa [revT] using
      concatEq_true_rev_intro_right_ne_stuck_of_prog_ne_stuck s t hProg
  have hIntroSList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro s) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro s) hRevSNonStuck
  have hIntroTList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro t) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro t) hRevTNonStuck
  have hRevSTy : __smtx_typeof (__eo_to_smt revS) = SmtType.Seq T := by
    simpa [revS] using
      smt_typeof_list_rev_str_concat_of_seq (__str_nary_intro s) T
        hIntroSList hIntroSTy hRevSNonStuck
  have hRevTTy : __smtx_typeof (__eo_to_smt revT) = SmtType.Seq T := by
    simpa [revT] using
      smt_typeof_list_rev_str_concat_of_seq (__str_nary_intro t) T
        hIntroTList hIntroTTy hRevTNonStuck
  have hStripNonStuck : strip ≠ Term.Stuck := by
    change __str_strip_prefix
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t)) ≠
      Term.Stuck
    simpa [concatEqStrip_true] using
      concatEqStrip_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t hProg
  have hFinalLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first strip)) ≠ Term.Stuck := by
    simpa [revS, revT, strip, concatEqLhs_true, concatEqStrip_true] using
      concatEqLhs_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t hProg
  have hFinalRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second strip)) ≠ Term.Stuck := by
    simpa [revS, revT, strip, concatEqRhs_true, concatEqStrip_true] using
      concatEqRhs_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t hProg
  have hFinal :=
    eo_interprets_rev_str_strip_prefix_result_with_final_seq M revS revT
      T hRevSTy hRevTTy
      (by
        simpa [revS, revT] using hRevStrip)
      hStripNonStuck hFinalLeft hFinalRight hCancel
  simpa [revS, revT, strip, concatEqLhs_true, concatEqRhs_true,
    concatEqStrip_true] using hFinal

private theorem concatEq_seq_pack_of_left_concat_empty_typeof
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hEmptyTNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
        SmtType.None)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck) :
    ∃ T,
      __smtx_typeof (__eo_to_smt (mkConcat sHead sTail)) =
        SmtType.Seq T ∧
      __smtx_typeof
          (__eo_to_smt (__str_nary_intro (mkConcat sHead sTail))) ≠
        SmtType.None ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
  rcases eq_bool_seq_of_left_concat sHead sTail t hPremBool with
    ⟨T, hLeftTy, hRightTy⟩
  have hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_empty_typeof t T hRightTy
      hEmptyTNN hIntroT
  exact concatEq_seq_pack_of_left_concat sHead sTail t hPremBool hIntroTNN

private theorem concatEq_seq_pack_of_right_concat_empty_typeof
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hEmptySNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
        SmtType.None)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck) :
    ∃ T,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None ∧
      __smtx_typeof
          (__eo_to_smt (__str_nary_intro (mkConcat tHead tTail))) ≠
        SmtType.None := by
  rcases eq_bool_seq_of_right_concat s tHead tTail hPremBool with
    ⟨T, hLeftTy, _⟩
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_empty_typeof s T hLeftTy
      hEmptySNN hIntroS
  exact concatEq_seq_pack_of_right_concat s tHead tTail hPremBool hIntroSNN

private theorem concatEq_seq_pack_of_not_concat_intros_eq_self
    (s t : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hIntroSEq : __str_nary_intro s = s)
    (hIntroTEq : __str_nary_intro t = t) :
    ∃ T,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type s t
      hPremBool with ⟨hSame, hSNN⟩
  have hTNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [← hSame]
    exact hSNN
  rcases smt_typeof_seq_of_not_str_concat_intro_eq_self s hSNotConcat
      hIntroS hIntroSEq hSNN with ⟨T, hsTy⟩
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None := by
    simpa [hIntroSEq] using hSNN
  have hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
    simpa [hIntroTEq] using hTNN
  exact ⟨T, hsTy, hIntroSNN, hIntroTNN⟩

private theorem concatEq_seq_pack_of_not_concat_left_intro_eq_self_right_empty_typeof
    (s t : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hIntroSEq : __str_nary_intro s = s)
    (hEmptyTNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
        SmtType.None)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck) :
    ∃ T,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type s t
      hPremBool with ⟨hSame, hSNN⟩
  rcases smt_typeof_seq_of_not_str_concat_intro_eq_self s hSNotConcat
      hIntroS hIntroSEq hSNN with ⟨T, hsTy⟩
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T := by
    rw [← hSame, hsTy]
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None := by
    simpa [hIntroSEq] using hSNN
  have hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_empty_typeof t T htTy
      hEmptyTNN hIntroT
  exact ⟨T, hsTy, hIntroSNN, hIntroTNN⟩

private theorem concatEq_seq_pack_of_not_concat_right_intro_eq_self_left_empty_typeof
    (s t : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hIntroTEq : __str_nary_intro t = t)
    (hEmptySNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
        SmtType.None)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck) :
    ∃ T,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type s t
      hPremBool with ⟨hSame, hSNN⟩
  have hTNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [← hSame]
    exact hSNN
  rcases smt_typeof_seq_of_not_str_concat_intro_eq_self t hTNotConcat
      hIntroT hIntroTEq hTNN with ⟨T, htTy⟩
  have hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T := by
    rw [hSame, htTy]
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_empty_typeof s T hsTy
      hEmptySNN hIntroS
  have hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
    simpa [hIntroTEq] using hTNN
  exact ⟨T, hsTy, hIntroSNN, hIntroTNN⟩

private theorem concatEq_seq_pack_of_empty_typeof_intros
    (s t : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hEmptySNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
        SmtType.None)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hEmptyTNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
        SmtType.None)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck) :
    ∃ T,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type s t
      hPremBool with ⟨hSame, hSNN⟩
  rcases smt_typeof_seq_of_seq_empty_typeof_non_none s hSNN
      hEmptySNN with ⟨T, hsTy, _hEmptySTy⟩
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T := by
    rw [← hSame, hsTy]
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_empty_typeof s T hsTy
      hEmptySNN hIntroS
  have hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_empty_typeof t T htTy
      hEmptyTNN hIntroT
  exact ⟨T, hsTy, hIntroSNN, hIntroTNN⟩

private theorem eo_interprets_double_rev_intros_of_prog_elim_intros
    (M : SmtModel) (hM : model_wf M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠ SmtType.None)
    (hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠ SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hDoubleS :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim (__str_nary_intro s))) true)
    (hDoubleT :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t))))
          (__str_nary_elim (__str_nary_intro t))) true)
    (hST : eo_interprets M (mkEq s t) true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro s))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro t)))))
      true := by
  have hIntroS : __str_nary_intro s ≠ Term.Stuck :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hIntroT : __str_nary_intro t ≠ Term.Stuck :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hElimIntroS : __str_nary_elim (__str_nary_intro s) ≠ Term.Stuck :=
    str_nary_elim_str_nary_intro_ne_stuck_of_seq s T hsTy hIntroSNN
      hIntroS
  have hElimIntroT : __str_nary_elim (__str_nary_intro t) ≠ Term.Stuck :=
    str_nary_elim_str_nary_intro_ne_stuck_of_seq t T htTy hIntroTNN
      hIntroT
  exact eo_interprets_double_rev_intros_of_elim_intros M hM s t T
    hsTy htTy hIntroSNN hIntroTNN hIntroS hIntroT hElimIntroS
    hElimIntroT hDoubleS hDoubleT hST

private theorem eo_interprets_double_rev_intros_of_prog_seq
    (M : SmtModel) (hM : model_wf M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠ SmtType.None)
    (hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠ SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hST : eo_interprets M (mkEq s t) true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro s))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro t)))))
      true := by
  have hIntroS : __str_nary_intro s ≠ Term.Stuck :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hIntroT : __str_nary_intro t ≠ Term.Stuck :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hRevS :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
        Term.Stuck :=
    concatEq_true_rev_intro_left_ne_stuck_of_prog_ne_stuck s t hProg
  have hRevT :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) ≠
        Term.Stuck :=
    concatEq_true_rev_intro_right_ne_stuck_of_prog_ne_stuck s t hProg
  have hDoubleS :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim (__str_nary_intro s))) true :=
    eo_interprets_double_rev_intro_elim_eq_of_seq_cases M s T hsTy
      hIntroSNN hIntroS hRevS
  have hDoubleT :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t))))
          (__str_nary_elim (__str_nary_intro t))) true :=
    eo_interprets_double_rev_intro_elim_eq_of_seq_cases M t T htTy
      hIntroTNN hIntroT hRevT
  exact eo_interprets_double_rev_intros_of_prog_elim_intros M hM
    s t T hsTy htTy hIntroSNN hIntroTNN hProg hDoubleS hDoubleT hST

private theorem concatEq_false_lhs_eq_of_not_str_concat_eo_eq_false
    (s t : Term)
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean false) :
    concatEqLhs (Term.Boolean false) s t = s := by
  have hStrip :=
    str_strip_prefix_str_nary_intro_of_not_str_concat_eo_eq_false
      s t hSNotConcat hTNotConcat hIntroS hIntroT hHead
  rw [concatEqLhs_false, hStrip]
  simp [mkPair, pair_first_pair,
    str_nary_elim_str_nary_intro_eq_of_not_str_concat s hSNotConcat
      hIntroS]

private theorem concatEq_false_rhs_eq_of_not_str_concat_eo_eq_false
    (s t : Term)
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean false) :
    concatEqRhs (Term.Boolean false) s t = t := by
  have hStrip :=
    str_strip_prefix_str_nary_intro_of_not_str_concat_eo_eq_false
      s t hSNotConcat hTNotConcat hIntroS hIntroT hHead
  rw [concatEqRhs_false, hStrip]
  simp [mkPair, pair_second_pair,
    str_nary_elim_str_nary_intro_eq_of_not_str_concat t hTNotConcat
      hIntroT]

private theorem concatEq_true_lhs_eq_of_not_str_concat_eo_eq_false
    (s t : Term)
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hRevS :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
        Term.Stuck)
    (hRevT :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) ≠
        Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean false) :
    concatEqLhs (Term.Boolean true) s t = s := by
  have hRevSEq :=
    eo_list_rev_str_nary_intro_eq_of_not_str_concat s hSNotConcat
      hIntroS hRevS
  have hRevTEq :=
    eo_list_rev_str_nary_intro_eq_of_not_str_concat t hTNotConcat
      hIntroT hRevT
  have hStrip :=
    str_strip_prefix_str_nary_intro_of_not_str_concat_eo_eq_false
      s t hSNotConcat hTNotConcat hIntroS hIntroT hHead
  rw [concatEqLhs_true, hRevSEq, hRevTEq, hStrip]
  simp [mkPair, pair_first_pair, hRevSEq,
    str_nary_elim_str_nary_intro_eq_of_not_str_concat s hSNotConcat
      hIntroS]

private theorem concatEq_true_rhs_eq_of_not_str_concat_eo_eq_false
    (s t : Term)
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hRevS :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
        Term.Stuck)
    (hRevT :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) ≠
        Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean false) :
    concatEqRhs (Term.Boolean true) s t = t := by
  have hRevSEq :=
    eo_list_rev_str_nary_intro_eq_of_not_str_concat s hSNotConcat
      hIntroS hRevS
  have hRevTEq :=
    eo_list_rev_str_nary_intro_eq_of_not_str_concat t hTNotConcat
      hIntroT hRevT
  have hStrip :=
    str_strip_prefix_str_nary_intro_of_not_str_concat_eo_eq_false
      s t hSNotConcat hTNotConcat hIntroS hIntroT hHead
  rw [concatEqRhs_true, hRevSEq, hRevTEq, hStrip]
  simp [mkPair, pair_second_pair, hRevTEq,
    str_nary_elim_str_nary_intro_eq_of_not_str_concat t hTNotConcat
      hIntroT]

private theorem concatEq_false_lhs_eq_rhs_of_eo_eq_true
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean true) :
    concatEqLhs (Term.Boolean false) s t =
      concatEqRhs (Term.Boolean false) s t := by
  have hTS : t = s := eq_of_eo_eq_true_local s t hHead
  subst t
  have hStrip :
      __str_strip_prefix (__str_nary_intro s) (__str_nary_intro s) ≠
        Term.Stuck := by
    simpa [concatEqStrip_false] using
      concatEqStrip_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s s hProg
  have hPair :=
    pair_first_str_strip_prefix_self_eq_pair_second
      (__str_nary_intro s) hStrip
  rw [concatEqLhs_false, concatEqRhs_false, hPair]

private theorem concatEq_true_lhs_eq_rhs_of_eo_eq_true
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean true) :
    concatEqLhs (Term.Boolean true) s t =
      concatEqRhs (Term.Boolean true) s t := by
  have hTS : t = s := eq_of_eo_eq_true_local s t hHead
  subst t
  let revS := __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s)
  have hStrip : __str_strip_prefix revS revS ≠ Term.Stuck := by
    change
      __str_strip_prefix
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s)) ≠
        Term.Stuck
    simpa [revS, concatEqStrip_true] using
      concatEqStrip_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s s hProg
  have hPair := pair_first_str_strip_prefix_self_eq_pair_second revS hStrip
  rw [concatEqLhs_true, concatEqRhs_true]
  simp [revS, hPair]

private theorem concatEq_false_has_bool_type_of_seq
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean false) s t)
        (concatEqRhs (Term.Boolean false) s t)) := by
  let strip := __str_strip_prefix (__str_nary_intro s) (__str_nary_intro t)
  have hIntroSNonStuck :
      __str_nary_intro s ≠ Term.Stuck :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hIntroTNonStuck :
      __str_nary_intro t ≠ Term.Stuck :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq s T hsTy hIntroSNN
  have hIntroTTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq t T htTy hIntroTNN
  have hStripNonStuck : strip ≠ Term.Stuck := by
    change __str_strip_prefix (__str_nary_intro s) (__str_nary_intro t) ≠
      Term.Stuck
    simpa [concatEqStrip_false] using
      concatEqStrip_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hStripTypes :
      __smtx_typeof (__eo_to_smt (__pair_first strip)) = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt (__pair_second strip)) = SmtType.Seq T :=
    str_strip_prefix_result_types_of_seq (__str_nary_intro s) (__str_nary_intro t)
      T hIntroSTy hIntroTTy hStripNonStuck
  have hElimFirstNonStuck :
      __str_nary_elim (__pair_first strip) ≠ Term.Stuck := by
    simpa [strip, concatEqLhs_false] using
      concatEqLhs_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hElimSecondNonStuck :
      __str_nary_elim (__pair_second strip) ≠ Term.Stuck := by
    simpa [strip, concatEqRhs_false] using
      concatEqRhs_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hElimFirstTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (__pair_first strip))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck (__pair_first strip) T
      hStripTypes.1 hElimFirstNonStuck
  have hElimSecondTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (__pair_second strip))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck (__pair_second strip) T
      hStripTypes.2 hElimSecondNonStuck
  have hFinalBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim (__pair_first strip))
        (__str_nary_elim (__pair_second strip))) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hElimFirstTy, hElimSecondTy]
    · rw [hElimFirstTy]
      exact seq_ne_none T
  simpa [strip, concatEqLhs_false, concatEqRhs_false] using hFinalBool

private theorem eo_interprets_concat_eq_false_of_seq
    (M : SmtModel) (hM : model_wf M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hPrem : eo_interprets M (mkEq s t) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hFinalBool : RuleProofs.eo_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean false) s t)
        (concatEqRhs (Term.Boolean false) s t))) :
    eo_interprets M
      (mkEq (concatEqLhs (Term.Boolean false) s t)
        (concatEqRhs (Term.Boolean false) s t)) true := by
  let strip := __str_strip_prefix (__str_nary_intro s) (__str_nary_intro t)
  have hIntroSNonStuck :
      __str_nary_intro s ≠ Term.Stuck :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hIntroTNonStuck :
      __str_nary_intro t ≠ Term.Stuck :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq s T hsTy hIntroSNN
  have hIntroTTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq t T htTy hIntroTNN
  have hIntroBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_intro s) (__str_nary_intro t)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hIntroSTy, hIntroTTy]
    · rw [hIntroSTy]
      exact seq_ne_none T
  have hIntroEq : eo_interprets M
      (mkEq (__str_nary_intro s) (__str_nary_intro t)) true :=
    eo_interprets_str_nary_intro_congr_of_seq M hM s t T
      hsTy htTy hIntroSNonStuck hIntroTNonStuck hPrem hIntroBool
  have hStripNonStuck : strip ≠ Term.Stuck := by
    change __str_strip_prefix (__str_nary_intro s) (__str_nary_intro t) ≠
      Term.Stuck
    simpa [concatEqStrip_false] using
      concatEqStrip_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hStripTypes :
      __smtx_typeof (__eo_to_smt (__pair_first strip)) = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt (__pair_second strip)) = SmtType.Seq T :=
    str_strip_prefix_result_types_of_seq (__str_nary_intro s) (__str_nary_intro t)
      T hIntroSTy hIntroTTy hStripNonStuck
  have hStripBool : RuleProofs.eo_has_bool_type
      (mkEq (__pair_first strip) (__pair_second strip)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hStripTypes.1, hStripTypes.2]
    · rw [hStripTypes.1]
      exact seq_ne_none T
  have hStripEq : eo_interprets M
      (mkEq (__pair_first strip) (__pair_second strip)) true :=
    eo_interprets_str_strip_prefix_result M hM
      (__str_nary_intro s) (__str_nary_intro t) hIntroEq hStripNonStuck
      hStripBool
  have hElimFirstNonStuck :
      __str_nary_elim (__pair_first strip) ≠ Term.Stuck := by
    simpa [strip, concatEqLhs_false] using
      concatEqLhs_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hElimSecondNonStuck :
      __str_nary_elim (__pair_second strip) ≠ Term.Stuck := by
    simpa [strip, concatEqRhs_false] using
      concatEqRhs_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (concatEqLhs (Term.Boolean false) s t)
      (concatEqRhs (Term.Boolean false) s t) hFinalBool with
    ⟨hFinalSame, hFinalLeftNN⟩
  have hElimFirstNN :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (__pair_first strip))) ≠
        SmtType.None := by
    simpa [strip, concatEqLhs_false] using hFinalLeftNN
  have hElimSecondNN :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (__pair_second strip))) ≠
        SmtType.None := by
    have hRightNN :
        __smtx_typeof (__eo_to_smt (concatEqRhs (Term.Boolean false) s t)) ≠
          SmtType.None := by
      rw [← hFinalSame]
      exact hFinalLeftNN
    simpa [strip, concatEqRhs_false] using hRightNN
  have hElimFirstTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (__pair_first strip))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq (__pair_first strip) T
      hStripTypes.1 hElimFirstNN
  have hElimSecondTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (__pair_second strip))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq (__pair_second strip) T
      hStripTypes.2 hElimSecondNN
  have hFinalBool' : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim (__pair_first strip))
        (__str_nary_elim (__pair_second strip))) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hElimFirstTy, hElimSecondTy]
    · rw [hElimFirstTy]
      exact seq_ne_none T
  have hFinal :=
    eo_interprets_str_nary_elim_congr_of_seq M hM
      (__pair_first strip) (__pair_second strip) T
      hStripTypes.1 hStripTypes.2 hElimFirstNonStuck hElimSecondNonStuck
      hStripEq hFinalBool'
  simpa [strip, concatEqLhs_false, concatEqRhs_false] using hFinal

private theorem eo_interprets_concat_eq_false_of_seq'
    (M : SmtModel) (hM : model_wf M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hPrem : eo_interprets M (mkEq s t) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq (concatEqLhs (Term.Boolean false) s t)
        (concatEqRhs (Term.Boolean false) s t)) true := by
  have hFinalBool :=
    concatEq_false_has_bool_type_of_seq s t T hsTy htTy hIntroSNN hIntroTNN
      hProg
  exact eo_interprets_concat_eq_false_of_seq M hM s t T hsTy htTy
    hIntroSNN hIntroTNN hPrem hProg hFinalBool

private theorem concatEq_true_has_bool_type_of_seq
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean true) s t)
        (concatEqRhs (Term.Boolean true) s t)) := by
  let revS := __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s)
  let revT := __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t)
  let strip := __str_strip_prefix revS revT
  have hIntroSNonStuck : __str_nary_intro s ≠ Term.Stuck :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hIntroTNonStuck : __str_nary_intro t ≠ Term.Stuck :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq s T hsTy hIntroSNN
  have hIntroTTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq t T htTy hIntroTNN
  have hRevSNonStuck : revS ≠ Term.Stuck := by
    simpa [revS] using
      concatEq_true_rev_intro_left_ne_stuck_of_prog_ne_stuck s t hProg
  have hRevTNonStuck : revT ≠ Term.Stuck := by
    simpa [revT] using
      concatEq_true_rev_intro_right_ne_stuck_of_prog_ne_stuck s t hProg
  have hIntroSList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro s) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro s) hRevSNonStuck
  have hIntroTList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro t) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro t) hRevTNonStuck
  have hRevSTy : __smtx_typeof (__eo_to_smt revS) = SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq (__str_nary_intro s) T
      hIntroSList hIntroSTy hRevSNonStuck
  have hRevTTy : __smtx_typeof (__eo_to_smt revT) = SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq (__str_nary_intro t) T
      hIntroTList hIntroTTy hRevTNonStuck
  have hStripNonStuck : strip ≠ Term.Stuck := by
    change __str_strip_prefix revS revT ≠ Term.Stuck
    simpa [strip, revS, revT, concatEqStrip_true] using
      concatEqStrip_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t hProg
  have hStripTypes :
      __smtx_typeof (__eo_to_smt (__pair_first strip)) = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt (__pair_second strip)) = SmtType.Seq T :=
    str_strip_prefix_result_types_of_seq revS revT T hRevSTy hRevTTy
      hStripNonStuck
  have hFirstRevNonStuck :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__pair_first strip) ≠
        Term.Stuck := by
    simpa [strip, concatEqStrip_true] using
      concatEq_true_rev_first_ne_stuck_of_prog_ne_stuck s t hProg
  have hSecondRevNonStuck :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__pair_second strip) ≠
        Term.Stuck := by
    simpa [strip, concatEqStrip_true] using
      concatEq_true_rev_second_ne_stuck_of_prog_ne_stuck s t hProg
  have hFirstList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__pair_first strip) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__pair_first strip) hFirstRevNonStuck
  have hSecondList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__pair_second strip) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__pair_second strip) hSecondRevNonStuck
  have hFirstRevTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first strip))) = SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq (__pair_first strip) T hFirstList
      hStripTypes.1 hFirstRevNonStuck
  have hSecondRevTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second strip))) = SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq (__pair_second strip) T hSecondList
      hStripTypes.2 hSecondRevNonStuck
  have hElimFirstNonStuck :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first strip)) ≠ Term.Stuck := by
    simpa [strip, concatEqLhs_true] using
      concatEqLhs_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t hProg
  have hElimSecondNonStuck :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second strip)) ≠ Term.Stuck := by
    simpa [strip, concatEqRhs_true] using
      concatEqRhs_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t hProg
  have hElimFirstTy :
      __smtx_typeof
          (__eo_to_smt
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__pair_first strip)))) = SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__pair_first strip)) T
      hFirstRevTy hElimFirstNonStuck
  have hElimSecondTy :
      __smtx_typeof
          (__eo_to_smt
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__pair_second strip)))) = SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__pair_second strip)) T
      hSecondRevTy hElimSecondNonStuck
  have hFinalBool : RuleProofs.eo_has_bool_type
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__pair_first strip)))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second strip)))) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hElimFirstTy, hElimSecondTy]
    · rw [hElimFirstTy]
      exact seq_ne_none T
  simpa [strip, revS, revT, concatEqLhs_true, concatEqRhs_true] using
    hFinalBool

private theorem concatEq_true_has_bool_type_of_left_seq
    (s t : Term) (T : SmtType)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean true) s t)
        (concatEqRhs (Term.Boolean true) s t)) := by
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T :=
    eq_bool_right_seq_of_left_seq s t T hPremBool hsTy
  exact concatEq_true_has_bool_type_of_seq s t T hsTy htTy hIntroSNN
    hIntroTNN hProg

private theorem concatEq_has_bool_type_of_left_seq
    (rev s t : Term) (T : SmtType)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠
      Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (mkEq (concatEqLhs rev s t) (concatEqRhs rev s t)) := by
  rcases concatEq_rev_cases_of_prog_ne_stuck rev s t hProg with hRev | hRev
  · subst rev
    exact concatEq_true_has_bool_type_of_left_seq s t T hPremBool hsTy
      hIntroSNN hIntroTNN hProg
  · subst rev
    have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T :=
      eq_bool_right_seq_of_left_seq s t T hPremBool hsTy
    exact concatEq_false_has_bool_type_of_seq s t T hsTy htTy
      hIntroSNN hIntroTNN hProg

private theorem concatEq_result_operands_same_eo_type (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck)
    (hTy :
      __eo_typeof (__eo_prog_concat_eq rev (Proof.pf (mkEq s t))) =
        Term.Bool) :
    __eo_typeof (concatEqLhs rev s t) = __eo_typeof (concatEqRhs rev s t) ∧
      __eo_typeof (concatEqLhs rev s t) ≠ Term.Stuck ∧
      __eo_typeof (concatEqRhs rev s t) ≠ Term.Stuck := by
  have hProgEq := eo_prog_concat_eq_eq_of_ne_stuck rev s t hProg
  have hOutTy :
      __eo_typeof (mkEq (concatEqLhs rev s t) (concatEqRhs rev s t)) =
        Term.Bool := by
    simpa [hProgEq] using hTy
  exact eo_typeof_eq_operands_same_of_bool
    (concatEqLhs rev s t) (concatEqRhs rev s t) hOutTy

private theorem step_concat_eq_false_of_seq
    (M : SmtModel) (hM : model_wf M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t))) := by
  have hProgEq :=
    eo_prog_concat_eq_eq_of_ne_stuck (Term.Boolean false) s t hProg
  have hFinalBool :=
    concatEq_false_has_bool_type_of_seq s t T hsTy htTy hIntroSNN hIntroTNN
      hProg
  refine ⟨?_, ?_⟩
  · intro hPremisesTrue
    have hPrem : eo_interprets M (mkEq s t) true :=
      hPremisesTrue (mkEq s t) (by simp)
    rw [hProgEq]
    exact eo_interprets_concat_eq_false_of_seq' M hM s t T hsTy htTy
      hIntroSNN hIntroTNN hPrem hProg
  · rw [hProgEq]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean false) s t)
        (concatEqRhs (Term.Boolean false) s t)) hFinalBool

private theorem step_concat_eq_false_of_left_seq
    (M : SmtModel) (hM : model_wf M)
    (s t : Term) (T : SmtType)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t))) := by
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T :=
    eq_bool_right_seq_of_left_seq s t T hPremBool hsTy
  exact step_concat_eq_false_of_seq M hM s t T hsTy htTy
    hIntroSNN hIntroTNN hProg

private theorem step_concat_eq_true_of_seq_from_rev_strip_with_final_seq
    (M : SmtModel) (hM : model_wf M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hRevStrip :
      eo_interprets M (mkEq s t) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T ->
        __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t))) := by
  have hProgEq :=
    eo_prog_concat_eq_eq_of_ne_stuck (Term.Boolean true) s t hProg
  have hFinalBool :=
    concatEq_true_has_bool_type_of_seq s t T hsTy htTy hIntroSNN
      hIntroTNN hProg
  refine ⟨?_, ?_⟩
  · intro hPremisesTrue
    have hPrem : eo_interprets M (mkEq s t) true :=
      hPremisesTrue (mkEq s t) (by simp)
    rw [hProgEq]
    exact eo_interprets_concat_eq_true_from_rev_strip_with_final_seq
      M s t T hsTy htTy hIntroSNN hIntroTNN (hRevStrip hPrem)
      hCancel hProg
  · rw [hProgEq]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean true) s t)
        (concatEqRhs (Term.Boolean true) s t)) hFinalBool

private theorem step_concat_eq_true_of_seq_from_rev_strip_with_final_seq_cancel
    (M : SmtModel) (hM : model_wf M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hRevStrip :
      eo_interprets M (mkEq s t) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t))) := by
  refine step_concat_eq_true_of_seq_from_rev_strip_with_final_seq M hM
    s t T hsTy htTy hIntroSNN hIntroTNN hRevStrip ?_ hProg
  intro a b aTail bTail hStrip hHead hLeftTy hRightTy hFinalLeft
    hFinalRight hXY
  exact
    eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_with_final
      M hM a b aTail bTail T hStrip hHead hLeftTy hRightTy
      hFinalLeft hFinalRight hXY

private theorem step_concat_eq_true_of_seq_with_final_seq_cancel
    (M : SmtModel) (hM : model_wf M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t))) := by
  refine step_concat_eq_true_of_seq_from_rev_strip_with_final_seq_cancel
    M hM s t T hsTy htTy hIntroSNN hIntroTNN ?_ hProg
  intro hPrem
  exact eo_interprets_double_rev_intros_of_prog_seq M hM s t T
    hsTy htTy hIntroSNN hIntroTNN hProg hPrem

private theorem step_concat_eq_true_of_left_seq_with_final_seq_cancel
    (M : SmtModel) (hM : model_wf M)
    (s t : Term) (T : SmtType)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t))) := by
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T :=
    eq_bool_right_seq_of_left_seq s t T hPremBool hsTy
  exact step_concat_eq_true_of_seq_with_final_seq_cancel M hM s t T
    hsTy htTy hIntroSNN hIntroTNN hProg

private theorem step_concat_eq_true_of_left_concat_with_final_seq_cancel
    (M : SmtModel) (hM : model_wf M)
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq (mkConcat sHead sTail) t)) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) t]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq (mkConcat sHead sTail) t))) := by
  rcases concatEq_seq_pack_of_left_concat sHead sTail t hPremBool
      hIntroTNN with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_with_final_seq_cancel M hM
    (mkConcat sHead sTail) t T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hProg

private theorem step_concat_eq_true_of_right_concat_with_final_seq_cancel
    (M : SmtModel) (hM : model_wf M)
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq s (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq s (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq s (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_right_concat s tHead tTail hPremBool
      hIntroSNN with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_with_final_seq_cancel M hM
    s (mkConcat tHead tTail) T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hProg

private theorem step_concat_eq_true_of_left_concat_intro_eq_self_with_final_seq_cancel
    (M : SmtModel) (hM : model_wf M)
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hIntroEq : __str_nary_intro t = t)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq (mkConcat sHead sTail) t)) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) t]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq (mkConcat sHead sTail) t))) := by
  rcases concatEq_seq_pack_of_left_concat_intro_eq_self sHead sTail t
      hPremBool hIntroEq with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_with_final_seq_cancel M hM
    (mkConcat sHead sTail) t T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hProg

private theorem step_concat_eq_true_of_right_concat_intro_eq_self_with_final_seq_cancel
    (M : SmtModel) (hM : model_wf M)
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hIntroEq : __str_nary_intro s = s)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq s (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq s (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq s (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_right_concat_intro_eq_self s tHead tTail
      hPremBool hIntroEq with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_with_final_seq_cancel M hM
    s (mkConcat tHead tTail) T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hProg

private theorem step_concat_eq_true_of_both_concat_with_final_seq_cancel
    (M : SmtModel) (hM : model_wf M)
    (sHead sTail tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (mkEq (mkConcat sHead sTail) (mkConcat tHead tTail)))
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq (mkConcat sHead sTail)
            (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq (mkConcat sHead sTail)
          (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_both_concat sHead sTail tHead tTail
      hPremBool with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_with_final_seq_cancel M hM
    (mkConcat sHead sTail) (mkConcat tHead tTail) T hPremBool
    hLeftTy hIntroLeftNN hIntroRightNN hProg

private theorem step_concat_eq_true_of_left_concat_empty_typeof_with_final_seq_cancel
    (M : SmtModel) (hM : model_wf M)
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hEmptyTNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
        SmtType.None)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq (mkConcat sHead sTail) t)) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) t]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq (mkConcat sHead sTail) t))) := by
  rcases concatEq_seq_pack_of_left_concat_empty_typeof sHead sTail t
      hPremBool hEmptyTNN hIntroT with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_with_final_seq_cancel M hM
    (mkConcat sHead sTail) t T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hProg

private theorem step_concat_eq_true_of_right_concat_empty_typeof_with_final_seq_cancel
    (M : SmtModel) (hM : model_wf M)
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hEmptySNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
        SmtType.None)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq s (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq s (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq s (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_right_concat_empty_typeof s tHead tTail
      hPremBool hEmptySNN hIntroS with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_with_final_seq_cancel M hM
    s (mkConcat tHead tTail) T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hProg

private theorem step_concat_eq_false_of_not_str_concat_eo_eq_false
    (M : SmtModel) (s t : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hHead : __eo_eq s t = Term.Boolean false) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t))) := by
  have hProgEq :=
    eo_prog_concat_eq_eq_of_ne_stuck (Term.Boolean false) s t hProg
  have hIntroS :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck
      (Term.Boolean false) s t hProg
  have hIntroT :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck
      (Term.Boolean false) s t hProg
  have hLhs :=
    concatEq_false_lhs_eq_of_not_str_concat_eo_eq_false s t
      hSNotConcat hTNotConcat hIntroS hIntroT hHead
  have hRhs :=
    concatEq_false_rhs_eq_of_not_str_concat_eo_eq_false s t
      hSNotConcat hTNotConcat hIntroS hIntroT hHead
  refine ⟨?_, ?_⟩
  · intro hPremisesTrue
    have hPrem : eo_interprets M (mkEq s t) true :=
      hPremisesTrue (mkEq s t) (by simp)
    rw [hProgEq, hLhs, hRhs]
    exact hPrem
  · rw [hProgEq, hLhs, hRhs]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
      (mkEq s t) hPremBool

private theorem step_concat_eq_true_of_not_str_concat_eo_eq_false
    (M : SmtModel) (s t : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hHead : __eo_eq s t = Term.Boolean false) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t))) := by
  have hProgEq :=
    eo_prog_concat_eq_eq_of_ne_stuck (Term.Boolean true) s t hProg
  have hIntroS :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck
      (Term.Boolean true) s t hProg
  have hIntroT :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck
      (Term.Boolean true) s t hProg
  have hRevS :=
    concatEq_true_rev_intro_left_ne_stuck_of_prog_ne_stuck s t hProg
  have hRevT :=
    concatEq_true_rev_intro_right_ne_stuck_of_prog_ne_stuck s t hProg
  have hLhs :=
    concatEq_true_lhs_eq_of_not_str_concat_eo_eq_false s t
      hSNotConcat hTNotConcat hIntroS hIntroT hRevS hRevT hHead
  have hRhs :=
    concatEq_true_rhs_eq_of_not_str_concat_eo_eq_false s t
      hSNotConcat hTNotConcat hIntroS hIntroT hRevS hRevT hHead
  refine ⟨?_, ?_⟩
  · intro hPremisesTrue
    have hPrem : eo_interprets M (mkEq s t) true :=
      hPremisesTrue (mkEq s t) (by simp)
    rw [hProgEq, hLhs, hRhs]
    exact hPrem
  · rw [hProgEq, hLhs, hRhs]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
      (mkEq s t) hPremBool

private theorem step_concat_eq_of_not_str_concat_eo_eq_false
    (M : SmtModel) (rev s t : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠
      Term.Stuck)
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hHead : __eo_eq s t = Term.Boolean false) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq rev (Proof.pf (mkEq s t))) := by
  rcases concatEq_rev_cases_of_prog_ne_stuck rev s t hProg with hRev | hRev
  · subst rev
    exact step_concat_eq_true_of_not_str_concat_eo_eq_false M s t
      hPremBool hProg hSNotConcat hTNotConcat hHead
  · subst rev
    exact step_concat_eq_false_of_not_str_concat_eo_eq_false M s t
      hPremBool hProg hSNotConcat hTNotConcat hHead

private theorem step_concat_eq_false_of_eo_eq_true
    (M : SmtModel) (s t : Term)
    (hFinalBool : RuleProofs.eo_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean false) s t)
        (concatEqRhs (Term.Boolean false) s t)))
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean true) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t))) := by
  have hProgEq :=
    eo_prog_concat_eq_eq_of_ne_stuck (Term.Boolean false) s t hProg
  have hOperands :=
    concatEq_false_lhs_eq_rhs_of_eo_eq_true s t hProg hHead
  refine ⟨?_, ?_⟩
  · intro hPremisesTrue
    rw [hProgEq, hOperands]
    exact eo_interprets_eq_self_of_has_bool_type M
      (concatEqRhs (Term.Boolean false) s t)
      (by simpa [hOperands] using hFinalBool)
  · rw [hProgEq]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean false) s t)
        (concatEqRhs (Term.Boolean false) s t)) hFinalBool

private theorem step_concat_eq_true_of_eo_eq_true
    (M : SmtModel) (s t : Term)
    (hFinalBool : RuleProofs.eo_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean true) s t)
        (concatEqRhs (Term.Boolean true) s t)))
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean true) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t))) := by
  have hProgEq :=
    eo_prog_concat_eq_eq_of_ne_stuck (Term.Boolean true) s t hProg
  have hOperands :=
    concatEq_true_lhs_eq_rhs_of_eo_eq_true s t hProg hHead
  refine ⟨?_, ?_⟩
  · intro hPremisesTrue
    rw [hProgEq, hOperands]
    exact eo_interprets_eq_self_of_has_bool_type M
      (concatEqRhs (Term.Boolean true) s t)
      (by simpa [hOperands] using hFinalBool)
  · rw [hProgEq]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean true) s t)
        (concatEqRhs (Term.Boolean true) s t)) hFinalBool

private theorem step_concat_eq_of_eo_eq_true
    (M : SmtModel) (rev s t : Term)
    (hFinalBool : RuleProofs.eo_has_bool_type
      (mkEq (concatEqLhs rev s t) (concatEqRhs rev s t)))
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠
      Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean true) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq rev (Proof.pf (mkEq s t))) := by
  rcases concatEq_rev_cases_of_prog_ne_stuck rev s t hProg with hRev | hRev
  · subst rev
    exact step_concat_eq_true_of_eo_eq_true M s t
      (by simpa using hFinalBool) hProg hHead
  · subst rev
    exact step_concat_eq_false_of_eo_eq_true M s t
      (by simpa using hFinalBool) hProg hHead

private theorem step_concat_eq_of_left_seq_eo_eq_true
    (M : SmtModel) (rev s t : Term) (T : SmtType)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠
      Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean true) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq rev (Proof.pf (mkEq s t))) := by
  exact step_concat_eq_of_eo_eq_true M rev s t
    (concatEq_has_bool_type_of_left_seq rev s t T hPremBool hsTy
      hIntroSNN hIntroTNN hProg)
    hProg hHead

private theorem step_concat_eq_core
    (M : SmtModel) (hM : model_wf M)
    (rev s t : Term)
    (hRevTrans : RuleProofs.eo_has_smt_translation rev)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck)
    (hResultTy :
      __eo_typeof (__eo_prog_concat_eq rev (Proof.pf (mkEq s t))) =
        Term.Bool) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq rev (Proof.pf (mkEq s t))) := by
  have hProgEq := eo_prog_concat_eq_eq_of_ne_stuck rev s t hProg
  have hRevCases := concatEq_rev_cases_of_prog_ne_stuck rev s t hProg
  have hOutEoTypes := concatEq_result_operands_same_eo_type rev s t hProg hResultTy
  by_cases hFalseSeq :
      rev = Term.Boolean false ∧
        ∃ T,
          __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
          __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠ SmtType.None ∧
          __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠ SmtType.None
  · rcases hFalseSeq with ⟨hRev, T, hsTy, hIntroSNN, hIntroTNN⟩
    subst rev
    exact step_concat_eq_false_of_left_seq M hM s t T hPremBool hsTy
      hIntroSNN hIntroTNN hProg
  · by_cases hTrueSeqHead :
        rev = Term.Boolean true ∧
          ∃ T,
            __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
            __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
              SmtType.None ∧
            __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
              SmtType.None ∧
            __eo_eq s t = Term.Boolean true
    · rcases hTrueSeqHead with
        ⟨hRev, T, hsTy, hIntroSNN, hIntroTNN, hHead⟩
      subst rev
      exact step_concat_eq_of_left_seq_eo_eq_true M (Term.Boolean true)
        s t T hPremBool hsTy hIntroSNN hIntroTNN hProg hHead
    · by_cases hNonConcatHead :
        (¬ ∃ head tail : Term, s = mkConcat head tail) ∧
          (¬ ∃ head tail : Term, t = mkConcat head tail) ∧
          __eo_eq s t = Term.Boolean false
      · rcases hNonConcatHead with ⟨hSNotConcat, hTNotConcat, hHead⟩
        exact step_concat_eq_of_not_str_concat_eo_eq_false M rev s t
          hPremBool hProg hSNotConcat hTNotConcat hHead
      · by_cases hTrueSeqNonConcat :
            rev = Term.Boolean true ∧
              ∃ T,
                __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
                __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
                  SmtType.None ∧
                __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
                  SmtType.None ∧
                (¬ ∃ head tail : Term, s = mkConcat head tail) ∧
                (¬ ∃ head tail : Term, t = mkConcat head tail)
        · rcases hTrueSeqNonConcat with
            ⟨hRev, T, hsTy, hIntroSNN, hIntroTNN, hSNotConcat,
              hTNotConcat⟩
          subst rev
          have hIntroS :=
            str_nary_intro_left_ne_stuck_of_prog_ne_stuck
              (Term.Boolean true) s t hProg
          have hIntroT :=
            str_nary_intro_right_ne_stuck_of_prog_ne_stuck
              (Term.Boolean true) s t hProg
          have hsNonStuck :=
            str_nary_intro_arg_ne_stuck_of_ne_stuck s hIntroS
          have htNonStuck :=
            str_nary_intro_arg_ne_stuck_of_ne_stuck t hIntroT
          rcases eo_eq_cases_of_ne_stuck s t hsNonStuck htNonStuck with
            hHead | hHead
          · exact False.elim
              (hTrueSeqHead
                ⟨rfl, T, hsTy, hIntroSNN, hIntroTNN, hHead⟩)
          · exact False.elim
              (hNonConcatHead ⟨hSNotConcat, hTNotConcat, hHead⟩)
        · -- Remaining core: the `rev = true` suffix-canceling branch, plus the
          -- side-condition proof that a successful `rev = false` step supplies the
          -- sequence/intro-translation package consumed above.
          have hNotFalseBothConcat :
              ¬ (rev = Term.Boolean false ∧
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (∃ tHead tTail : Term, t = mkConcat tHead tTail)) := by
            intro h
            rcases h with
              ⟨hRev, ⟨sHead, sTail, hS⟩, ⟨tHead, tTail, hT⟩⟩
            subst rev
            subst s
            subst t
            have hPack :=
              concatEq_seq_pack_of_both_concat sHead sTail tHead tTail
                hPremBool
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotFalseLeftConcatWithRightIntro :
              ¬ (rev = Term.Boolean false ∧
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
                  SmtType.None) := by
            intro h
            rcases h with
              ⟨hRev, ⟨sHead, sTail, hS⟩, hIntroTNN⟩
            subst rev
            subst s
            have hPack :=
              concatEq_seq_pack_of_left_concat sHead sTail t hPremBool
                hIntroTNN
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotFalseLeftConcatWithRightIntroEqSelf :
              ¬ (rev = Term.Boolean false ∧
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                __str_nary_intro t = t) := by
            intro h
            rcases h with
              ⟨hRev, ⟨sHead, sTail, hS⟩, hIntroEq⟩
            subst rev
            subst s
            have hPack :=
              concatEq_seq_pack_of_left_concat_intro_eq_self sHead sTail t
                hPremBool hIntroEq
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotFalseRightConcatWithLeftIntro :
              ¬ (rev = Term.Boolean false ∧
                (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
                  SmtType.None) := by
            intro h
            rcases h with
              ⟨hRev, ⟨tHead, tTail, hT⟩, hIntroSNN⟩
            subst rev
            subst t
            have hPack :=
              concatEq_seq_pack_of_right_concat s tHead tTail hPremBool
                hIntroSNN
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotFalseRightConcatWithLeftIntroEqSelf :
              ¬ (rev = Term.Boolean false ∧
                (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __str_nary_intro s = s) := by
            intro h
            rcases h with
              ⟨hRev, ⟨tHead, tTail, hT⟩, hIntroEq⟩
            subst rev
            subst t
            have hPack :=
              concatEq_seq_pack_of_right_concat_intro_eq_self s tHead tTail
                hPremBool hIntroEq
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotFalseLeftConcatWithRightEmpty :
              ¬ (rev = Term.Boolean false ∧
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
                  SmtType.None) := by
            intro h
            rcases h with
              ⟨hRev, ⟨sHead, sTail, hS⟩, hEmptyTNN⟩
            subst rev
            subst s
            have hIntroT :
                __str_nary_intro t ≠ Term.Stuck :=
              str_nary_intro_right_ne_stuck_of_prog_ne_stuck
                (Term.Boolean false) (mkConcat sHead sTail) t hProg
            have hPack :=
              concatEq_seq_pack_of_left_concat_empty_typeof sHead sTail t
                hPremBool hEmptyTNN hIntroT
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotFalseRightConcatWithLeftEmpty :
              ¬ (rev = Term.Boolean false ∧
                (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
                  SmtType.None) := by
            intro h
            rcases h with
              ⟨hRev, ⟨tHead, tTail, hT⟩, hEmptySNN⟩
            subst rev
            subst t
            have hIntroS :
                __str_nary_intro s ≠ Term.Stuck :=
              str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                (Term.Boolean false) s (mkConcat tHead tTail) hProg
            have hPack :=
              concatEq_seq_pack_of_right_concat_empty_typeof s tHead tTail
                hPremBool hEmptySNN hIntroS
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotFalseBothNotConcatIntroEqSelf :
              ¬ (rev = Term.Boolean false ∧
                (¬ ∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (¬ ∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __str_nary_intro s = s ∧
                __str_nary_intro t = t) := by
            intro h
            rcases h with
              ⟨hRev, hSNotConcat, _hTNotConcat, hIntroSEq,
                hIntroTEq⟩
            subst rev
            have hIntroS :
                __str_nary_intro s ≠ Term.Stuck :=
              str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                (Term.Boolean false) s t hProg
            have hPack :=
              concatEq_seq_pack_of_not_concat_intros_eq_self s t
                hPremBool hSNotConcat hIntroS hIntroSEq hIntroTEq
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotFalseBothNotConcatLeftIntroEqSelfRightEmpty :
              ¬ (rev = Term.Boolean false ∧
                (¬ ∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (¬ ∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __str_nary_intro s = s ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
                  SmtType.None) := by
            intro h
            rcases h with
              ⟨hRev, hSNotConcat, _hTNotConcat, hIntroSEq,
                hEmptyTNN⟩
            subst rev
            have hIntroS :
                __str_nary_intro s ≠ Term.Stuck :=
              str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                (Term.Boolean false) s t hProg
            have hIntroT :
                __str_nary_intro t ≠ Term.Stuck :=
              str_nary_intro_right_ne_stuck_of_prog_ne_stuck
                (Term.Boolean false) s t hProg
            have hPack :=
              concatEq_seq_pack_of_not_concat_left_intro_eq_self_right_empty_typeof
                s t hPremBool hSNotConcat hIntroS hIntroSEq hEmptyTNN
                hIntroT
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotFalseBothNotConcatRightIntroEqSelfLeftEmpty :
              ¬ (rev = Term.Boolean false ∧
                (¬ ∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (¬ ∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
                  SmtType.None ∧
                __str_nary_intro t = t) := by
            intro h
            rcases h with
              ⟨hRev, _hSNotConcat, hTNotConcat, hEmptySNN,
                hIntroTEq⟩
            subst rev
            have hIntroS :
                __str_nary_intro s ≠ Term.Stuck :=
              str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                (Term.Boolean false) s t hProg
            have hIntroT :
                __str_nary_intro t ≠ Term.Stuck :=
              str_nary_intro_right_ne_stuck_of_prog_ne_stuck
                (Term.Boolean false) s t hProg
            have hPack :=
              concatEq_seq_pack_of_not_concat_right_intro_eq_self_left_empty_typeof
                s t hPremBool hTNotConcat hIntroT hIntroTEq hEmptySNN
                hIntroS
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotFalseBothNotConcatEmptyTypeof :
              ¬ (rev = Term.Boolean false ∧
                (¬ ∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (¬ ∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
                  SmtType.None ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
                  SmtType.None) := by
            intro h
            rcases h with
              ⟨hRev, _hSNotConcat, _hTNotConcat, hEmptySNN,
                hEmptyTNN⟩
            subst rev
            have hIntroS :
                __str_nary_intro s ≠ Term.Stuck :=
              str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                (Term.Boolean false) s t hProg
            have hIntroT :
                __str_nary_intro t ≠ Term.Stuck :=
              str_nary_intro_right_ne_stuck_of_prog_ne_stuck
                (Term.Boolean false) s t hProg
            have hPack :=
              concatEq_seq_pack_of_empty_typeof_intros s t hPremBool
                hEmptySNN hIntroS hEmptyTNN hIntroT
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotTrueBothConcatHead :
              ¬ (rev = Term.Boolean true ∧
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __eo_eq s t = Term.Boolean true) := by
            intro h
            rcases h with
              ⟨hRev, ⟨sHead, sTail, hS⟩, ⟨tHead, tTail, hT⟩,
                hHead⟩
            subst rev
            subst s
            subst t
            rcases concatEq_seq_pack_of_both_concat sHead sTail tHead tTail
                hPremBool with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqHead
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN, hHead⟩
          have hNotTrueBothNotConcatIntroEqSelf :
              ¬ (rev = Term.Boolean true ∧
                (¬ ∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (¬ ∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __str_nary_intro s = s ∧
                __str_nary_intro t = t) := by
            intro h
            rcases h with
              ⟨hRev, hSNotConcat, hTNotConcat, hIntroSEq,
                hIntroTEq⟩
            subst rev
            have hIntroS :
                __str_nary_intro s ≠ Term.Stuck :=
              str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                (Term.Boolean true) s t hProg
            rcases concatEq_seq_pack_of_not_concat_intros_eq_self s t
                hPremBool hSNotConcat hIntroS hIntroSEq hIntroTEq with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqNonConcat
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN,
                hSNotConcat, hTNotConcat⟩
          have hNotTrueBothNotConcatLeftIntroEqSelfRightEmpty :
              ¬ (rev = Term.Boolean true ∧
                (¬ ∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (¬ ∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __str_nary_intro s = s ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
                  SmtType.None) := by
            intro h
            rcases h with
              ⟨hRev, hSNotConcat, hTNotConcat, hIntroSEq,
                hEmptyTNN⟩
            subst rev
            have hIntroS :
                __str_nary_intro s ≠ Term.Stuck :=
              str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                (Term.Boolean true) s t hProg
            have hIntroT :
                __str_nary_intro t ≠ Term.Stuck :=
              str_nary_intro_right_ne_stuck_of_prog_ne_stuck
                (Term.Boolean true) s t hProg
            rcases
                concatEq_seq_pack_of_not_concat_left_intro_eq_self_right_empty_typeof
                  s t hPremBool hSNotConcat hIntroS hIntroSEq
                  hEmptyTNN hIntroT with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqNonConcat
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN,
                hSNotConcat, hTNotConcat⟩
          have hNotTrueBothNotConcatRightIntroEqSelfLeftEmpty :
              ¬ (rev = Term.Boolean true ∧
                (¬ ∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (¬ ∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
                  SmtType.None ∧
                __str_nary_intro t = t) := by
            intro h
            rcases h with
              ⟨hRev, hSNotConcat, hTNotConcat, hEmptySNN,
                hIntroTEq⟩
            subst rev
            have hIntroS :
                __str_nary_intro s ≠ Term.Stuck :=
              str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                (Term.Boolean true) s t hProg
            have hIntroT :
                __str_nary_intro t ≠ Term.Stuck :=
              str_nary_intro_right_ne_stuck_of_prog_ne_stuck
                (Term.Boolean true) s t hProg
            rcases
                concatEq_seq_pack_of_not_concat_right_intro_eq_self_left_empty_typeof
                  s t hPremBool hTNotConcat hIntroT hIntroTEq
                  hEmptySNN hIntroS with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqNonConcat
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN,
                hSNotConcat, hTNotConcat⟩
          have hNotTrueBothNotConcatEmptyTypeof :
              ¬ (rev = Term.Boolean true ∧
                (¬ ∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (¬ ∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
                  SmtType.None ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
                  SmtType.None) := by
            intro h
            rcases h with
              ⟨hRev, hSNotConcat, hTNotConcat, hEmptySNN,
                hEmptyTNN⟩
            subst rev
            have hIntroS :
                __str_nary_intro s ≠ Term.Stuck :=
              str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                (Term.Boolean true) s t hProg
            have hIntroT :
                __str_nary_intro t ≠ Term.Stuck :=
              str_nary_intro_right_ne_stuck_of_prog_ne_stuck
                (Term.Boolean true) s t hProg
            rcases concatEq_seq_pack_of_empty_typeof_intros s t hPremBool
                hEmptySNN hIntroS hEmptyTNN hIntroT with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqNonConcat
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN,
                hSNotConcat, hTNotConcat⟩
          have hNotTrueLeftConcatWithRightIntroHead :
              ¬ (rev = Term.Boolean true ∧
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
                  SmtType.None ∧
                __eo_eq s t = Term.Boolean true) := by
            intro h
            rcases h with
              ⟨hRev, ⟨sHead, sTail, hS⟩, hIntroTNN, hHead⟩
            subst rev
            subst s
            rcases concatEq_seq_pack_of_left_concat sHead sTail t
                hPremBool hIntroTNN with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqHead
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN, hHead⟩
          have hNotTrueLeftConcatWithRightIntroEqSelfHead :
              ¬ (rev = Term.Boolean true ∧
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                __str_nary_intro t = t ∧
                __eo_eq s t = Term.Boolean true) := by
            intro h
            rcases h with
              ⟨hRev, ⟨sHead, sTail, hS⟩, hIntroEq, hHead⟩
            subst rev
            subst s
            rcases concatEq_seq_pack_of_left_concat_intro_eq_self sHead
                sTail t hPremBool hIntroEq with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqHead
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN, hHead⟩
          have hNotTrueRightConcatWithLeftIntroHead :
              ¬ (rev = Term.Boolean true ∧
                (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
                  SmtType.None ∧
                __eo_eq s t = Term.Boolean true) := by
            intro h
            rcases h with
              ⟨hRev, ⟨tHead, tTail, hT⟩, hIntroSNN, hHead⟩
            subst rev
            subst t
            rcases concatEq_seq_pack_of_right_concat s tHead tTail
                hPremBool hIntroSNN with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqHead
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN, hHead⟩
          have hNotTrueRightConcatWithLeftIntroEqSelfHead :
              ¬ (rev = Term.Boolean true ∧
                (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __str_nary_intro s = s ∧
                __eo_eq s t = Term.Boolean true) := by
            intro h
            rcases h with
              ⟨hRev, ⟨tHead, tTail, hT⟩, hIntroEq, hHead⟩
            subst rev
            subst t
            rcases concatEq_seq_pack_of_right_concat_intro_eq_self s tHead
                tTail hPremBool hIntroEq with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqHead
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN, hHead⟩
          have hNotTrueLeftConcatWithRightEmptyHead :
              ¬ (rev = Term.Boolean true ∧
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
                  SmtType.None ∧
                __eo_eq s t = Term.Boolean true) := by
            intro h
            rcases h with
              ⟨hRev, ⟨sHead, sTail, hS⟩, hEmptyTNN, hHead⟩
            subst rev
            subst s
            have hIntroT :
                __str_nary_intro t ≠ Term.Stuck :=
              str_nary_intro_right_ne_stuck_of_prog_ne_stuck
                (Term.Boolean true) (mkConcat sHead sTail) t hProg
            rcases concatEq_seq_pack_of_left_concat_empty_typeof sHead sTail t
                hPremBool hEmptyTNN hIntroT with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqHead
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN, hHead⟩
          have hNotTrueRightConcatWithLeftEmptyHead :
              ¬ (rev = Term.Boolean true ∧
                (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
                  SmtType.None ∧
                __eo_eq s t = Term.Boolean true) := by
            intro h
            rcases h with
              ⟨hRev, ⟨tHead, tTail, hT⟩, hEmptySNN, hHead⟩
            subst rev
            subst t
            have hIntroS :
                __str_nary_intro s ≠ Term.Stuck :=
              str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                (Term.Boolean true) s (mkConcat tHead tTail) hProg
            rcases concatEq_seq_pack_of_right_concat_empty_typeof s tHead tTail
                hPremBool hEmptySNN hIntroS with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqHead
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN, hHead⟩
          have hNotTrueLeftConcatRightNotConcatHead :
              ¬ (rev = Term.Boolean true ∧
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (¬ ∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __eo_eq s t = Term.Boolean true) := by
            intro h
            rcases h with
              ⟨_hRev, ⟨sHead, sTail, hS⟩, hTNotConcat, hHead⟩
            subst s
            exact eo_eq_true_left_concat_right_not_concat_false
              sHead sTail t hTNotConcat hHead
          have hNotTrueRightConcatLeftNotConcatHead :
              ¬ (rev = Term.Boolean true ∧
                (¬ ∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __eo_eq s t = Term.Boolean true) := by
            intro h
            rcases h with
              ⟨_hRev, hSNotConcat, ⟨tHead, tTail, hT⟩, hHead⟩
            subst t
            exact eo_eq_true_left_not_concat_right_concat_false
              s tHead tTail hSNotConcat hHead
          rcases hRevCases with hRev | hRev
          · subst rev
            by_cases hBothConcat :
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                  (∃ tHead tTail : Term, t = mkConcat tHead tTail)
            · rcases hBothConcat with
                ⟨⟨sHead, sTail, hS⟩, ⟨tHead, tTail, hT⟩⟩
              subst s
              subst t
              exact step_concat_eq_true_of_both_concat_with_final_seq_cancel
                M hM sHead sTail tHead tTail hPremBool hProg
            · by_cases hLeftConcatWithRightIntro :
                  (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                    __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
                      SmtType.None
              · rcases hLeftConcatWithRightIntro with
                  ⟨⟨sHead, sTail, hS⟩, hIntroTNN⟩
                subst s
                exact
                  step_concat_eq_true_of_left_concat_with_final_seq_cancel
                    M hM sHead sTail t hPremBool hIntroTNN hProg
              · by_cases hRightConcatWithLeftIntro :
                    (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
                        SmtType.None
                · rcases hRightConcatWithLeftIntro with
                    ⟨⟨tHead, tTail, hT⟩, hIntroSNN⟩
                  subst t
                  exact
                    step_concat_eq_true_of_right_concat_with_final_seq_cancel
                      M hM s tHead tTail hPremBool hIntroSNN hProg
                · by_cases hLeftConcatWithRightIntroEqSelf :
                      (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                        __str_nary_intro t = t
                  · rcases hLeftConcatWithRightIntroEqSelf with
                      ⟨⟨sHead, sTail, hS⟩, hIntroEq⟩
                    subst s
                    exact
                      step_concat_eq_true_of_left_concat_intro_eq_self_with_final_seq_cancel
                        M hM sHead sTail t hPremBool hIntroEq hProg
                  · by_cases hRightConcatWithLeftIntroEqSelf :
                        (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                          __str_nary_intro s = s
                    · rcases hRightConcatWithLeftIntroEqSelf with
                        ⟨⟨tHead, tTail, hT⟩, hIntroEq⟩
                      subst t
                      exact
                        step_concat_eq_true_of_right_concat_intro_eq_self_with_final_seq_cancel
                          M hM s tHead tTail hPremBool hIntroEq hProg
                    · by_cases hLeftConcatWithRightEmpty :
                          (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                            __smtx_typeof
                                (__eo_to_smt
                                  (__seq_empty (__eo_typeof t))) ≠
                              SmtType.None
                      · rcases hLeftConcatWithRightEmpty with
                          ⟨⟨sHead, sTail, hS⟩, hEmptyTNN⟩
                        subst s
                        have hIntroT :
                            __str_nary_intro t ≠ Term.Stuck :=
                          str_nary_intro_right_ne_stuck_of_prog_ne_stuck
                            (Term.Boolean true) (mkConcat sHead sTail) t
                            hProg
                        exact
                          step_concat_eq_true_of_left_concat_empty_typeof_with_final_seq_cancel
                            M hM sHead sTail t hPremBool hEmptyTNN hIntroT
                            hProg
                      · by_cases hRightConcatWithLeftEmpty :
                            (∃ tHead tTail : Term,
                              t = mkConcat tHead tTail) ∧
                              __smtx_typeof
                                  (__eo_to_smt
                                    (__seq_empty (__eo_typeof s))) ≠
                                SmtType.None
                        · rcases hRightConcatWithLeftEmpty with
                            ⟨⟨tHead, tTail, hT⟩, hEmptySNN⟩
                          subst t
                          have hIntroS :
                              __str_nary_intro s ≠ Term.Stuck :=
                            str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                              (Term.Boolean true) s (mkConcat tHead tTail)
                              hProg
                          exact
                            step_concat_eq_true_of_right_concat_empty_typeof_with_final_seq_cancel
                              M hM s tHead tTail hPremBool hEmptySNN
                              hIntroS hProg
                        · by_cases hBothNotConcatIntroEqSelf :
                              (¬ ∃ sHead sTail : Term,
                                s = mkConcat sHead sTail) ∧
                                (¬ ∃ tHead tTail : Term,
                                  t = mkConcat tHead tTail) ∧
                                __str_nary_intro s = s ∧
                                __str_nary_intro t = t
                          · exact False.elim
                              (hNotTrueBothNotConcatIntroEqSelf
                                ⟨rfl, hBothNotConcatIntroEqSelf.1,
                                  hBothNotConcatIntroEqSelf.2.1,
                                  hBothNotConcatIntroEqSelf.2.2⟩)
                          · by_cases
                              hBothNotConcatLeftIntroEqSelfRightEmpty :
                                (¬ ∃ sHead sTail : Term,
                                  s = mkConcat sHead sTail) ∧
                                  (¬ ∃ tHead tTail : Term,
                                    t = mkConcat tHead tTail) ∧
                                  __str_nary_intro s = s ∧
                                  __smtx_typeof
                                      (__eo_to_smt
                                        (__seq_empty (__eo_typeof t))) ≠
                                    SmtType.None
                            · exact False.elim
                                (hNotTrueBothNotConcatLeftIntroEqSelfRightEmpty
                                  ⟨rfl,
                                    hBothNotConcatLeftIntroEqSelfRightEmpty.1,
                                    hBothNotConcatLeftIntroEqSelfRightEmpty.2.1,
                                    hBothNotConcatLeftIntroEqSelfRightEmpty.2.2⟩)
                            · by_cases
                                hBothNotConcatRightIntroEqSelfLeftEmpty :
                                  (¬ ∃ sHead sTail : Term,
                                    s = mkConcat sHead sTail) ∧
                                    (¬ ∃ tHead tTail : Term,
                                      t = mkConcat tHead tTail) ∧
                                    __smtx_typeof
                                        (__eo_to_smt
                                          (__seq_empty (__eo_typeof s))) ≠
                                      SmtType.None ∧
                                    __str_nary_intro t = t
                              · exact False.elim
                                  (hNotTrueBothNotConcatRightIntroEqSelfLeftEmpty
                                    ⟨rfl,
                                      hBothNotConcatRightIntroEqSelfLeftEmpty.1,
                                      hBothNotConcatRightIntroEqSelfLeftEmpty.2.1,
                                      hBothNotConcatRightIntroEqSelfLeftEmpty.2.2⟩)
                              · by_cases hBothNotConcatEmptyTypeof :
                                    (¬ ∃ sHead sTail : Term,
                                      s = mkConcat sHead sTail) ∧
                                      (¬ ∃ tHead tTail : Term,
                                        t = mkConcat tHead tTail) ∧
                                      __smtx_typeof
                                          (__eo_to_smt
                                            (__seq_empty (__eo_typeof s))) ≠
                                        SmtType.None ∧
                                      __smtx_typeof
                                          (__eo_to_smt
                                            (__seq_empty (__eo_typeof t))) ≠
                                        SmtType.None
                                · exact False.elim
                                    (hNotTrueBothNotConcatEmptyTypeof
                                      ⟨rfl, hBothNotConcatEmptyTypeof.1,
                                        hBothNotConcatEmptyTypeof.2.1,
                                        hBothNotConcatEmptyTypeof.2.2⟩)
                                · by_cases hBothNotConcatHeadFalse :
                                      (¬ ∃ sHead sTail : Term,
                                        s = mkConcat sHead sTail) ∧
                                        (¬ ∃ tHead tTail : Term,
                                          t = mkConcat tHead tTail) ∧
                                        __eo_eq s t = Term.Boolean false
                                  · exact False.elim
                                      (hNonConcatHead hBothNotConcatHeadFalse)
                                  · by_cases hLeftConcatRightNotConcatHead :
                                        (∃ sHead sTail : Term,
                                          s = mkConcat sHead sTail) ∧
                                          (¬ ∃ tHead tTail : Term,
                                            t = mkConcat tHead tTail) ∧
                                          __eo_eq s t = Term.Boolean true
                                    · exact False.elim
                                        (hNotTrueLeftConcatRightNotConcatHead
                                          ⟨rfl,
                                            hLeftConcatRightNotConcatHead.1,
                                            hLeftConcatRightNotConcatHead.2.1,
                                            hLeftConcatRightNotConcatHead.2.2⟩)
                                    · by_cases hRightConcatLeftNotConcatHead :
                                          (¬ ∃ sHead sTail : Term,
                                            s = mkConcat sHead sTail) ∧
                                            (∃ tHead tTail : Term,
                                              t = mkConcat tHead tTail) ∧
                                            __eo_eq s t = Term.Boolean true
                                      · exact False.elim
                                          (hNotTrueRightConcatLeftNotConcatHead
                                            ⟨rfl,
                                              hRightConcatLeftNotConcatHead.1,
                                              hRightConcatLeftNotConcatHead.2.1,
                                              hRightConcatLeftNotConcatHead.2.2⟩)
                                      -- Remaining corner: cancellation can expose
                                      -- generated seq.empty terms whose SMT
                                      -- translation needs inhabited/wf element
                                      -- type evidence.
                                      · have hIntroS :
                                            __str_nary_intro s ≠ Term.Stuck :=
                                          str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                                            (Term.Boolean true) s t hProg
                                        have hIntroT :
                                            __str_nary_intro t ≠ Term.Stuck :=
                                          str_nary_intro_right_ne_stuck_of_prog_ne_stuck
                                            (Term.Boolean true) s t hProg
                                        by_cases hSConcatAny :
                                            ∃ sHead sTail : Term,
                                              s = mkConcat sHead sTail
                                        · rcases hSConcatAny with
                                            ⟨sHead, sTail, hS⟩
                                          subst s
                                          rcases eq_bool_seq_of_left_concat sHead
                                              sTail t hPremBool with
                                            ⟨T, hLeftTy, hRightTy⟩
                                          rcases
                                              smt_seq_component_wf_of_non_none_type
                                                (__eo_to_smt
                                                  (mkConcat sHead sTail)) T
                                                hLeftTy with
                                            ⟨hTInh, hTWf⟩
                                          have hIntroTNN :
                                              __smtx_typeof
                                                  (__eo_to_smt
                                                    (__str_nary_intro t)) ≠
                                                SmtType.None :=
                                            str_nary_intro_has_smt_translation_of_seq_wf
                                              t T hRightTy hTInh hTWf hIntroT
                                          exact False.elim
                                            (hLeftConcatWithRightIntro
                                              ⟨⟨sHead, sTail, rfl⟩,
                                                hIntroTNN⟩)
                                        · by_cases hTConcatAny :
                                              ∃ tHead tTail : Term,
                                                t = mkConcat tHead tTail
                                          · rcases hTConcatAny with
                                              ⟨tHead, tTail, hT⟩
                                            subst t
                                            rcases eq_bool_seq_of_right_concat s
                                                tHead tTail hPremBool with
                                              ⟨T, hLeftTy, hRightTy⟩
                                            rcases
                                                smt_seq_component_wf_of_non_none_type
                                                  (__eo_to_smt
                                                    (mkConcat tHead tTail)) T
                                                  hRightTy with
                                              ⟨hTInh, hTWf⟩
                                            have hIntroSNN :
                                                __smtx_typeof
                                                    (__eo_to_smt
                                                      (__str_nary_intro s)) ≠
                                                  SmtType.None :=
                                              str_nary_intro_has_smt_translation_of_seq_wf
                                                s T hLeftTy hTInh hTWf hIntroS
                                            exact False.elim
                                              (hRightConcatWithLeftIntro
                                                ⟨⟨tHead, tTail, rfl⟩,
                                                  hIntroSNN⟩)
                                          · have hsNonStuck :=
                                              str_nary_intro_arg_ne_stuck_of_ne_stuck
                                                s hIntroS
                                            have htNonStuck :=
                                              str_nary_intro_arg_ne_stuck_of_ne_stuck
                                                t hIntroT
                                            rcases eo_eq_cases_of_ne_stuck s t
                                                hsNonStuck htNonStuck with
                                              hHead | hHead
                                            · rcases
                                                str_nary_intro_not_str_concat_cases_typeof_empty
                                                  s hSConcatAny hIntroS with
                                                hIntroSEq | hIntroSConcat
                                              · rcases
                                                  str_nary_intro_not_str_concat_cases_typeof_empty
                                                    t hTConcatAny hIntroT with
                                                  hIntroTEq | _hIntroTConcat
                                                · exact False.elim
                                                    (hBothNotConcatIntroEqSelf
                                                      ⟨hSConcatAny,
                                                        hTConcatAny,
                                                        hIntroSEq,
                                                        hIntroTEq⟩)
                                                · rcases
                                                    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                                      s t hPremBool with
                                                    ⟨_hSame, hSNN⟩
                                                  rcases
                                                    smt_typeof_seq_of_not_str_concat_intro_eq_self
                                                      s hSConcatAny hIntroS
                                                      hIntroSEq hSNN with
                                                    ⟨T, hsTy⟩
                                                  rcases
                                                    smt_seq_component_wf_of_non_none_type
                                                      (__eo_to_smt s) T hsTy with
                                                    ⟨hTInh, hTWf⟩
                                                  have htTy :=
                                                    eq_bool_right_seq_of_left_seq
                                                      s t T hPremBool hsTy
                                                  have hEmptyTNN :
                                                      __smtx_typeof
                                                          (__eo_to_smt
                                                            (__seq_empty
                                                              (__eo_typeof t))) ≠
                                                        SmtType.None :=
                                                    seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf
                                                      t T htTy hTInh hTWf
                                                  exact False.elim
                                                    (hBothNotConcatLeftIntroEqSelfRightEmpty
                                                      ⟨hSConcatAny,
                                                        hTConcatAny,
                                                        hIntroSEq,
                                                        hEmptyTNN⟩)
                                              · rcases
                                                  str_nary_intro_not_str_concat_cases_typeof_empty
                                                    t hTConcatAny hIntroT with
                                                  hIntroTEq | _hIntroTConcat
                                                · rcases
                                                    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                                      s t hPremBool with
                                                    ⟨hSame, hSNN⟩
                                                  have hTNN :
                                                      __smtx_typeof
                                                          (__eo_to_smt t) ≠
                                                        SmtType.None := by
                                                    rw [← hSame]
                                                    exact hSNN
                                                  rcases
                                                    smt_typeof_seq_of_not_str_concat_intro_eq_self
                                                      t hTConcatAny hIntroT
                                                      hIntroTEq hTNN with
                                                    ⟨T, htTy⟩
                                                  rcases
                                                    smt_seq_component_wf_of_non_none_type
                                                      (__eo_to_smt t) T htTy with
                                                    ⟨hTInh, hTWf⟩
                                                  have hsTy :=
                                                    eq_bool_left_seq_of_right_seq
                                                      s t T hPremBool htTy
                                                  have hEmptySNN :
                                                      __smtx_typeof
                                                          (__eo_to_smt
                                                            (__seq_empty
                                                              (__eo_typeof s))) ≠
                                                        SmtType.None :=
                                                    seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf
                                                      s T hsTy hTInh hTWf
                                                  exact False.elim
                                                    (hBothNotConcatRightIntroEqSelfLeftEmpty
                                                      ⟨hSConcatAny,
                                                        hTConcatAny,
                                                        hEmptySNN,
                                                        hIntroTEq⟩)
                                                · have hTS : t = s :=
                                                    eq_of_eo_eq_true_local s t hHead
                                                  subst t
                                                  rcases
                                                    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                                      s s hPremBool with
                                                    ⟨_hSame, hSNN⟩
                                                  have hElim :
                                                      __str_nary_elim
                                                          (__seq_empty
                                                            (__eo_typeof s)) ≠
                                                        Term.Stuck :=
                                                    str_nary_elim_seq_empty_typeof_ne_stuck_of_concat_eq_true_generated
                                                      s hProg hsNonStuck
                                                      hIntroSConcat
                                                  have hEmptyTy :
                                                      __eo_typeof
                                                          (__seq_empty
                                                            (__eo_typeof s)) ≠
                                                        Term.Stuck :=
                                                    seq_empty_typeof_eo_type_ne_stuck_of_concat_eq_true_generated
                                                      s hProg hResultTy
                                                      hsNonStuck
                                                      hIntroSConcat
                                                  have hSSeq :
                                                      ∃ T,
                                                        __smtx_typeof
                                                            (__eo_to_smt s) =
                                                          SmtType.Seq T :=
                                                    smt_typeof_seq_of_seq_empty_typeof_eo_type_ne_stuck
                                                      s hSNN hEmptyTy
                                                  have hEmptySNN :
                                                      __smtx_typeof
                                                          (__eo_to_smt
                                                            (__seq_empty
                                                              (__eo_typeof s))) ≠
                                                        SmtType.None :=
                                                    seq_empty_typeof_has_smt_translation_of_elim_ne_stuck
                                                      s hSNN hSSeq hElim
                                                  exact False.elim
                                                    (hBothNotConcatEmptyTypeof
                                                      ⟨hSConcatAny,
                                                        hTConcatAny,
                                                        hEmptySNN,
                                                        hEmptySNN⟩)
                                            · exact False.elim
                                                (hBothNotConcatHeadFalse
                                                  ⟨hSConcatAny, hTConcatAny,
                                                    hHead⟩)
          · subst rev
            by_cases hBothConcat :
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                  (∃ tHead tTail : Term, t = mkConcat tHead tTail)
            · exact False.elim
                (hNotFalseBothConcat ⟨rfl, hBothConcat.1, hBothConcat.2⟩)
            · by_cases hLeftConcatWithRightIntro :
                  (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                    __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
                      SmtType.None
              · exact False.elim
                  (hNotFalseLeftConcatWithRightIntro
                    ⟨rfl, hLeftConcatWithRightIntro.1,
                      hLeftConcatWithRightIntro.2⟩)
              · by_cases hRightConcatWithLeftIntro :
                    (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
                        SmtType.None
                · exact False.elim
                    (hNotFalseRightConcatWithLeftIntro
                      ⟨rfl, hRightConcatWithLeftIntro.1,
                        hRightConcatWithLeftIntro.2⟩)
                · by_cases hLeftConcatWithRightIntroEqSelf :
                      (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                        __str_nary_intro t = t
                  · exact False.elim
                      (hNotFalseLeftConcatWithRightIntroEqSelf
                        ⟨rfl, hLeftConcatWithRightIntroEqSelf.1,
                          hLeftConcatWithRightIntroEqSelf.2⟩)
                  · by_cases hRightConcatWithLeftIntroEqSelf :
                        (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                          __str_nary_intro s = s
                    · exact False.elim
                        (hNotFalseRightConcatWithLeftIntroEqSelf
                          ⟨rfl, hRightConcatWithLeftIntroEqSelf.1,
                            hRightConcatWithLeftIntroEqSelf.2⟩)
                    · by_cases hLeftConcatWithRightEmpty :
                          (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                            __smtx_typeof
                                (__eo_to_smt
                                  (__seq_empty (__eo_typeof t))) ≠
                              SmtType.None
                      · exact False.elim
                          (hNotFalseLeftConcatWithRightEmpty
                            ⟨rfl, hLeftConcatWithRightEmpty.1,
                              hLeftConcatWithRightEmpty.2⟩)
                      · by_cases hRightConcatWithLeftEmpty :
                            (∃ tHead tTail : Term,
                              t = mkConcat tHead tTail) ∧
                              __smtx_typeof
                                  (__eo_to_smt
                                    (__seq_empty (__eo_typeof s))) ≠
                                SmtType.None
                        · exact False.elim
                            (hNotFalseRightConcatWithLeftEmpty
                              ⟨rfl, hRightConcatWithLeftEmpty.1,
                                hRightConcatWithLeftEmpty.2⟩)
                        · by_cases hBothNotConcatIntroEqSelf :
                              (¬ ∃ sHead sTail : Term,
                                s = mkConcat sHead sTail) ∧
                                (¬ ∃ tHead tTail : Term,
                                  t = mkConcat tHead tTail) ∧
                                __str_nary_intro s = s ∧
                                __str_nary_intro t = t
                          · exact False.elim
                              (hNotFalseBothNotConcatIntroEqSelf
                                ⟨rfl, hBothNotConcatIntroEqSelf.1,
                                  hBothNotConcatIntroEqSelf.2.1,
                                  hBothNotConcatIntroEqSelf.2.2⟩)
                          · by_cases
                              hBothNotConcatLeftIntroEqSelfRightEmpty :
                                (¬ ∃ sHead sTail : Term,
                                  s = mkConcat sHead sTail) ∧
                                  (¬ ∃ tHead tTail : Term,
                                    t = mkConcat tHead tTail) ∧
                                  __str_nary_intro s = s ∧
                                  __smtx_typeof
                                      (__eo_to_smt
                                        (__seq_empty (__eo_typeof t))) ≠
                                    SmtType.None
                            · exact False.elim
                                (hNotFalseBothNotConcatLeftIntroEqSelfRightEmpty
                                  ⟨rfl,
                                    hBothNotConcatLeftIntroEqSelfRightEmpty.1,
                                    hBothNotConcatLeftIntroEqSelfRightEmpty.2.1,
                                    hBothNotConcatLeftIntroEqSelfRightEmpty.2.2⟩)
                            · by_cases
                                hBothNotConcatRightIntroEqSelfLeftEmpty :
                                  (¬ ∃ sHead sTail : Term,
                                    s = mkConcat sHead sTail) ∧
                                    (¬ ∃ tHead tTail : Term,
                                      t = mkConcat tHead tTail) ∧
                                    __smtx_typeof
                                        (__eo_to_smt
                                          (__seq_empty (__eo_typeof s))) ≠
                                      SmtType.None ∧
                                    __str_nary_intro t = t
                              · exact False.elim
                                  (hNotFalseBothNotConcatRightIntroEqSelfLeftEmpty
                                    ⟨rfl,
                                      hBothNotConcatRightIntroEqSelfLeftEmpty.1,
                                      hBothNotConcatRightIntroEqSelfLeftEmpty.2.1,
                                      hBothNotConcatRightIntroEqSelfLeftEmpty.2.2⟩)
                              · by_cases hBothNotConcatEmptyTypeof :
                                    (¬ ∃ sHead sTail : Term,
                                      s = mkConcat sHead sTail) ∧
                                      (¬ ∃ tHead tTail : Term,
                                        t = mkConcat tHead tTail) ∧
                                      __smtx_typeof
                                          (__eo_to_smt
                                            (__seq_empty (__eo_typeof s))) ≠
                                        SmtType.None ∧
                                      __smtx_typeof
                                          (__eo_to_smt
                                            (__seq_empty (__eo_typeof t))) ≠
                                        SmtType.None
                                · exact False.elim
                                    (hNotFalseBothNotConcatEmptyTypeof
                                      ⟨rfl, hBothNotConcatEmptyTypeof.1,
                                        hBothNotConcatEmptyTypeof.2.1,
                                        hBothNotConcatEmptyTypeof.2.2⟩)
                                · by_cases hBothNotConcatHeadFalse :
                                      (¬ ∃ sHead sTail : Term,
                                        s = mkConcat sHead sTail) ∧
                                        (¬ ∃ tHead tTail : Term,
                                          t = mkConcat tHead tTail) ∧
                                        __eo_eq s t = Term.Boolean false
                                  · exact False.elim
                                      (hNonConcatHead hBothNotConcatHeadFalse)
                                  -- Same remaining seq.empty translation corner
                                  -- for the non-reversed strip.
                                  · have hIntroS :
                                        __str_nary_intro s ≠ Term.Stuck :=
                                      str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                                        (Term.Boolean false) s t hProg
                                    have hIntroT :
                                        __str_nary_intro t ≠ Term.Stuck :=
                                      str_nary_intro_right_ne_stuck_of_prog_ne_stuck
                                        (Term.Boolean false) s t hProg
                                    by_cases hSConcatAny :
                                        ∃ sHead sTail : Term,
                                          s = mkConcat sHead sTail
                                    · rcases hSConcatAny with
                                        ⟨sHead, sTail, hS⟩
                                      subst s
                                      rcases eq_bool_seq_of_left_concat sHead
                                          sTail t hPremBool with
                                        ⟨T, hLeftTy, hRightTy⟩
                                      rcases
                                          smt_seq_component_wf_of_non_none_type
                                            (__eo_to_smt
                                              (mkConcat sHead sTail)) T
                                            hLeftTy with
                                        ⟨hTInh, hTWf⟩
                                      have hIntroTNN :
                                          __smtx_typeof
                                              (__eo_to_smt
                                                (__str_nary_intro t)) ≠
                                            SmtType.None :=
                                        str_nary_intro_has_smt_translation_of_seq_wf
                                          t T hRightTy hTInh hTWf hIntroT
                                      exact False.elim
                                        (hLeftConcatWithRightIntro
                                          ⟨⟨sHead, sTail, rfl⟩,
                                            hIntroTNN⟩)
                                    · by_cases hTConcatAny :
                                          ∃ tHead tTail : Term,
                                            t = mkConcat tHead tTail
                                      · rcases hTConcatAny with
                                          ⟨tHead, tTail, hT⟩
                                        subst t
                                        rcases eq_bool_seq_of_right_concat s
                                            tHead tTail hPremBool with
                                          ⟨T, hLeftTy, hRightTy⟩
                                        rcases
                                            smt_seq_component_wf_of_non_none_type
                                              (__eo_to_smt
                                                (mkConcat tHead tTail)) T
                                              hRightTy with
                                          ⟨hTInh, hTWf⟩
                                        have hIntroSNN :
                                            __smtx_typeof
                                                (__eo_to_smt
                                                  (__str_nary_intro s)) ≠
                                              SmtType.None :=
                                          str_nary_intro_has_smt_translation_of_seq_wf
                                            s T hLeftTy hTInh hTWf hIntroS
                                        exact False.elim
                                          (hRightConcatWithLeftIntro
                                            ⟨⟨tHead, tTail, rfl⟩,
                                              hIntroSNN⟩)
                                      · have hsNonStuck :=
                                          str_nary_intro_arg_ne_stuck_of_ne_stuck
                                            s hIntroS
                                        have htNonStuck :=
                                          str_nary_intro_arg_ne_stuck_of_ne_stuck
                                            t hIntroT
                                        rcases eo_eq_cases_of_ne_stuck s t
                                            hsNonStuck htNonStuck with
                                          hHead | hHead
                                        · rcases
                                            str_nary_intro_not_str_concat_cases_typeof_empty
                                              s hSConcatAny hIntroS with
                                            hIntroSEq | hIntroSConcat
                                          · rcases
                                              str_nary_intro_not_str_concat_cases_typeof_empty
                                                t hTConcatAny hIntroT with
                                              hIntroTEq | _hIntroTConcat
                                            · exact False.elim
                                                (hBothNotConcatIntroEqSelf
                                                  ⟨hSConcatAny,
                                                    hTConcatAny,
                                                    hIntroSEq,
                                                    hIntroTEq⟩)
                                            · rcases
                                                RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                                  s t hPremBool with
                                                ⟨_hSame, hSNN⟩
                                              rcases
                                                smt_typeof_seq_of_not_str_concat_intro_eq_self
                                                  s hSConcatAny hIntroS
                                                  hIntroSEq hSNN with
                                                ⟨T, hsTy⟩
                                              rcases
                                                smt_seq_component_wf_of_non_none_type
                                                  (__eo_to_smt s) T hsTy with
                                                ⟨hTInh, hTWf⟩
                                              have htTy :=
                                                eq_bool_right_seq_of_left_seq
                                                  s t T hPremBool hsTy
                                              have hEmptyTNN :
                                                  __smtx_typeof
                                                      (__eo_to_smt
                                                        (__seq_empty
                                                          (__eo_typeof t))) ≠
                                                    SmtType.None :=
                                                seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf
                                                  t T htTy hTInh hTWf
                                              exact False.elim
                                                (hBothNotConcatLeftIntroEqSelfRightEmpty
                                                  ⟨hSConcatAny,
                                                    hTConcatAny,
                                                    hIntroSEq,
                                                    hEmptyTNN⟩)
                                          · rcases
                                              str_nary_intro_not_str_concat_cases_typeof_empty
                                                t hTConcatAny hIntroT with
                                              hIntroTEq | _hIntroTConcat
                                            · rcases
                                                RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                                  s t hPremBool with
                                                ⟨hSame, hSNN⟩
                                              have hTNN :
                                                  __smtx_typeof
                                                      (__eo_to_smt t) ≠
                                                    SmtType.None := by
                                                rw [← hSame]
                                                exact hSNN
                                              rcases
                                                smt_typeof_seq_of_not_str_concat_intro_eq_self
                                                  t hTConcatAny hIntroT
                                                  hIntroTEq hTNN with
                                                ⟨T, htTy⟩
                                              rcases
                                                smt_seq_component_wf_of_non_none_type
                                                  (__eo_to_smt t) T htTy with
                                                ⟨hTInh, hTWf⟩
                                              have hsTy :=
                                                eq_bool_left_seq_of_right_seq
                                                  s t T hPremBool htTy
                                              have hEmptySNN :
                                                  __smtx_typeof
                                                      (__eo_to_smt
                                                        (__seq_empty
                                                          (__eo_typeof s))) ≠
                                                    SmtType.None :=
                                                seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf
                                                  s T hsTy hTInh hTWf
                                              exact False.elim
                                                (hBothNotConcatRightIntroEqSelfLeftEmpty
                                                  ⟨hSConcatAny,
                                                    hTConcatAny,
                                                    hEmptySNN,
                                                    hIntroTEq⟩)
                                            · have hTS : t = s :=
                                                eq_of_eo_eq_true_local s t hHead
                                              subst t
                                              rcases
                                                RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                                  s s hPremBool with
                                                ⟨_hSame, hSNN⟩
                                              have hElim :
                                                  __str_nary_elim
                                                      (__seq_empty
                                                        (__eo_typeof s)) ≠
                                                    Term.Stuck :=
                                                str_nary_elim_seq_empty_typeof_ne_stuck_of_concat_eq_false_generated
                                                  s hProg hsNonStuck
                                                  hIntroSConcat
                                              have hEmptyTy :
                                                  __eo_typeof
                                                      (__seq_empty
                                                        (__eo_typeof s)) ≠
                                                    Term.Stuck :=
                                                seq_empty_typeof_eo_type_ne_stuck_of_concat_eq_false_generated
                                                  s hProg hResultTy
                                                  hsNonStuck
                                                  hIntroSConcat
                                              have hSSeq :
                                                  ∃ T,
                                                    __smtx_typeof
                                                        (__eo_to_smt s) =
                                                      SmtType.Seq T :=
                                                smt_typeof_seq_of_seq_empty_typeof_eo_type_ne_stuck
                                                  s hSNN hEmptyTy
                                              have hEmptySNN :
                                                  __smtx_typeof
                                                      (__eo_to_smt
                                                        (__seq_empty
                                                          (__eo_typeof s))) ≠
                                                    SmtType.None :=
                                                seq_empty_typeof_has_smt_translation_of_elim_ne_stuck
                                                  s hSNN hSSeq hElim
                                              exact False.elim
                                                (hBothNotConcatEmptyTypeof
                                                  ⟨hSConcatAny,
                                                    hTConcatAny,
                                                    hEmptySNN,
                                                    hEmptySNN⟩)
                                        · exact False.elim
                                            (hBothNotConcatHeadFalse
                                              ⟨hSConcatAny, hTConcatAny,
                                                hHead⟩)

public theorem cmd_step_concat_eq_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.concat_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.concat_eq args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.concat_eq args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.concat_eq args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n1 premises =>
              cases premises with
              | nil =>
                  let X1 := __eo_state_proven_nth s n1
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                    have hArgs : RuleProofs.eo_has_smt_translation a1 ∧ True := by
                      simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                    exact hArgs.1
                  have hX1Bool : RuleProofs.eo_has_bool_type X1 :=
                    hPremisesBool X1 (by simp [X1, premiseTermList])
                  have hProgConcatEq :
                      __eo_prog_concat_eq a1 (Proof.pf X1) ≠ Term.Stuck := by
                    change __eo_prog_concat_eq a1
                      (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                    simpa [X1] using hProg
                  rcases eo_prog_concat_eq_premise_eq_shape_of_ne_stuck a1 X1
                      hProgConcatEq with ⟨lhs, rhs, hX1Eq⟩
                  have hStateEq :
                      __eo_state_proven_nth s n1 = mkEq lhs rhs := by
                    simpa [X1] using hX1Eq
                  have hPremEqBool : RuleProofs.eo_has_bool_type (mkEq lhs rhs) := by
                    simpa [X1, hStateEq] using hX1Bool
                  have hProgRule :
                      __eo_prog_concat_eq a1 (Proof.pf (mkEq lhs rhs)) ≠
                        Term.Stuck := by
                    simpa [X1, hStateEq] using hProgConcatEq
                  have hResultTyRule :
                      __eo_typeof
                        (__eo_prog_concat_eq a1 (Proof.pf (mkEq lhs rhs))) =
                        Term.Bool := by
                    change __eo_typeof
                      (__eo_prog_concat_eq a1
                        (Proof.pf (__eo_state_proven_nth s n1))) = Term.Bool at hResultTy
                    simpa [hStateEq] using hResultTy
                  change StepRuleProperties M [__eo_state_proven_nth s n1]
                    (__eo_prog_concat_eq a1
                      (Proof.pf (__eo_state_proven_nth s n1)))
                  rw [hStateEq]
                  exact step_concat_eq_core M hM a1 lhs rhs hA1Trans
                    hPremEqBool hProgRule hResultTyRule
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
