module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

/-- Raw reduction of the program: only the three Stuck guards block the match.
    The result keeps the `__eo_mk_apply` wrappers around the nary-elim. -/
private theorem prog_str_to_lower_concat_raw
    (s1 s2 s3 : Term)
    (hS1 : s1 ≠ Term.Stuck) (hS2 : s2 ≠ Term.Stuck) (hS3 : s3 ≠ Term.Stuck) :
    __eo_prog_str_to_lower_concat s1 s2 s3 =
      __eo_mk_apply
        (Term.Apply Term.eq
            (Term.Apply Term.str_to_lower (mkConcat s1 (mkConcat s2 s3))))
        (__eo_mk_apply
          (Term.Apply Term.str_concat (Term.Apply Term.str_to_lower s1))
          (__eo_mk_apply
            (__eo_mk_apply Term.str_concat
              (__eo_mk_apply Term.str_to_lower
                (__str_nary_elim (mkConcat s2 s3))))
            (Term.String []))) := by
  cases hs1 : s1 <;> first
    | exact False.elim (hS1 hs1)
    | (cases hs2 : s2 <;> first
        | exact False.elim (hS2 hs2)
        | (cases hs3 : s3 <;> first
            | exact False.elim (hS3 hs3)
            | rfl))

/-- Reduces the program to the readable `mkEq`/`mkConcat` form, given that all
    three arguments and the nary-elim are non-stuck. -/
private theorem prog_str_to_lower_concat_eq_of_ne_stuck
    (s1 s2 s3 : Term)
    (hS1 : s1 ≠ Term.Stuck) (hS2 : s2 ≠ Term.Stuck) (hS3 : s3 ≠ Term.Stuck)
    (hElim : __str_nary_elim (mkConcat s2 s3) ≠ Term.Stuck) :
    __eo_prog_str_to_lower_concat s1 s2 s3 =
      mkEq
        (Term.Apply Term.str_to_lower (mkConcat s1 (mkConcat s2 s3)))
        (mkConcat (Term.Apply Term.str_to_lower s1)
          (mkConcat (Term.Apply Term.str_to_lower (__str_nary_elim (mkConcat s2 s3)))
            (Term.String []))) := by
  rw [prog_str_to_lower_concat_raw s1 s2 s3 hS1 hS2 hS3]
  -- innermost: __eo_mk_apply str_to_lower elim = Apply str_to_lower elim
  have hStuElim :
      __eo_mk_apply Term.str_to_lower (__str_nary_elim (mkConcat s2 s3)) =
        Term.Apply Term.str_to_lower (__str_nary_elim (mkConcat s2 s3)) :=
    eo_mk_apply_eq_apply_of_ne_stuck Term.str_to_lower
      (__str_nary_elim (mkConcat s2 s3)) (by
        cases hcase : __str_nary_elim (mkConcat s2 s3) with
        | Stuck => exact absurd hcase hElim
        | _ => simp [__eo_mk_apply, Term.str_to_lower])
  rw [hStuElim]
  -- now every remaining __eo_mk_apply has structurally non-stuck arguments
  simp only [__eo_mk_apply, mkEq, mkConcat, Term.str_to_lower, Term.str_concat,
    Term.eq]

/-- If the nary-elim is stuck, the whole program is stuck. -/
private theorem prog_str_to_lower_concat_stuck_of_elim_stuck
    (s1 s2 s3 : Term)
    (hS1 : s1 ≠ Term.Stuck) (hS2 : s2 ≠ Term.Stuck) (hS3 : s3 ≠ Term.Stuck)
    (hElim : __str_nary_elim (mkConcat s2 s3) = Term.Stuck) :
    __eo_prog_str_to_lower_concat s1 s2 s3 = Term.Stuck := by
  rw [prog_str_to_lower_concat_raw s1 s2 s3 hS1 hS2 hS3]
  rw [hElim]
  simp [__eo_mk_apply]

/-- `__eo_typeof_str_to_lower T ≠ Stuck` forces `T = Seq Char`. -/
private theorem eo_typeof_str_to_lower_arg_seq_char
    (T : Term) (h : __eo_typeof_str_to_lower T ≠ Term.Stuck) :
    T = Term.Apply Term.Seq (Term.UOp UserOp.Char) := by
  cases T <;> simp [__eo_typeof_str_to_lower, Term.Seq] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_to_lower] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_to_lower] at h ⊢
      case Seq =>
        cases x <;> simp [__eo_typeof_str_to_lower] at h ⊢
        case UOp op2 =>
          cases op2 <;> simp [__eo_typeof_str_to_lower] at h ⊢

/-- `__eo_requires (__eo_eq A B) (Boolean true) (Apply Seq A) = Apply Seq Char`
    forces `A = B = Char`. -/
private theorem eo_requires_seq_eq_char (A B : Term)
    (h : __eo_requires (__eo_eq A B) (Term.Boolean true)
        (Term.Apply Term.Seq A) = Term.Apply Term.Seq (Term.UOp UserOp.Char)) :
    A = Term.UOp UserOp.Char ∧ B = Term.UOp UserOp.Char := by
  have hNe : __eo_requires (__eo_eq A B) (Term.Boolean true)
      (Term.Apply Term.Seq A) ≠ Term.Stuck := by
    rw [h]; simp [Term.Seq]
  -- result branch gives Apply Seq A = Apply Seq Char => A = Char
  have hRes : Term.Apply Term.Seq A = Term.Apply Term.Seq (Term.UOp UserOp.Char) := by
    rw [← eo_requires_eq_result_of_ne_stuck (__eo_eq A B) (Term.Boolean true)
      (Term.Apply Term.Seq A) hNe]; exact h
  have hAChar : A = Term.UOp UserOp.Char := (Term.Apply.inj hRes).2
  subst A
  -- condition branch gives __eo_eq (UOp Char) B = Boolean true => B = UOp Char
  have hCond : __eo_eq (Term.UOp UserOp.Char) B = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck (__eo_eq (Term.UOp UserOp.Char) B) (Term.Boolean true)
      (Term.Apply Term.Seq (Term.UOp UserOp.Char)) hNe
  have hBChar : B = Term.UOp UserOp.Char := by
    by_cases hB : B = Term.Stuck
    · subst B; simp [__eo_eq] at hCond
    · have hTeq : native_teq B (Term.UOp UserOp.Char) = true := by
        simpa [__eo_eq, hB] using hCond
      exact of_decide_eq_true hTeq
  exact ⟨rfl, hBChar⟩

/-- `__eo_typeof_str_concat A B = Seq Char` forces both arguments to be `Seq Char`. -/
private theorem eo_typeof_str_concat_args_seq_char_of_seq_char
    (A B : Term)
    (h : __eo_typeof_str_concat A B = Term.Apply Term.Seq (Term.UOp UserOp.Char)) :
    A = Term.Apply Term.Seq (Term.UOp UserOp.Char) ∧
      B = Term.Apply Term.Seq (Term.UOp UserOp.Char) := by
  cases A <;> simp [__eo_typeof_str_concat, Term.Seq] at h ⊢
  case Apply fA xA =>
    cases fA <;> simp [__eo_typeof_str_concat] at h ⊢
    case UOp opA =>
      cases opA <;> simp [__eo_typeof_str_concat] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_concat] at h ⊢
        case Apply fB xB =>
          cases fB <;> simp [__eo_typeof_str_concat] at h ⊢
          case UOp opB =>
            cases opB <;> simp [__eo_typeof_str_concat] at h ⊢
            case Seq =>
              -- h : __eo_requires (__eo_eq xA xB) (Boolean true) (Apply Seq xA)
              --      = Apply Seq Char
              rcases eo_requires_seq_eq_char xA xB (by
                simpa [Term.Seq] using h) with ⟨hxA, hxB⟩
              exact ⟨by rw [hxA], by rw [hxB]⟩

/-- Type/non-stuckness extraction from the program being Bool-typed. -/
private theorem typeof_args_of_prog_bool
    (s1 s2 s3 : Term)
    (hS1 : s1 ≠ Term.Stuck) (hS2 : s2 ≠ Term.Stuck) (hS3 : s3 ≠ Term.Stuck)
    (hTy : __eo_typeof (__eo_prog_str_to_lower_concat s1 s2 s3) = Term.Bool) :
    __eo_typeof s1 = Term.Apply Term.Seq (Term.UOp UserOp.Char) ∧
      __eo_typeof s2 = Term.Apply Term.Seq (Term.UOp UserOp.Char) ∧
      __eo_typeof s3 = Term.Apply Term.Seq (Term.UOp UserOp.Char) ∧
      __str_nary_elim (mkConcat s2 s3) ≠ Term.Stuck := by
  -- First rule out elim being stuck.
  have hElimNe : __str_nary_elim (mkConcat s2 s3) ≠ Term.Stuck := by
    intro hElim
    rw [prog_str_to_lower_concat_stuck_of_elim_stuck s1 s2 s3 hS1 hS2 hS3 hElim]
      at hTy
    have : __eo_typeof Term.Stuck ≠ Term.Bool := by native_decide
    exact this hTy
  rw [prog_str_to_lower_concat_eq_of_ne_stuck s1 s2 s3 hS1 hS2 hS3 hElimNe] at hTy
  -- Decompose the eq typeof.
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply Term.str_to_lower (mkConcat s1 (mkConcat s2 s3))))
      (__eo_typeof
        (mkConcat (Term.Apply Term.str_to_lower s1)
          (mkConcat (Term.Apply Term.str_to_lower (__str_nary_elim (mkConcat s2 s3)))
            (Term.String [])))) = Term.Bool at hTy
  have hLhsNotStuck :
      __eo_typeof (Term.Apply Term.str_to_lower (mkConcat s1 (mkConcat s2 s3))) ≠
        Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy).1
  -- The LHS typeof is str_to_lower-of-str_concat-of-str_concat.
  change __eo_typeof_str_to_lower
      (__eo_typeof_str_concat (__eo_typeof s1)
        (__eo_typeof_str_concat (__eo_typeof s2) (__eo_typeof s3))) ≠ Term.Stuck
    at hLhsNotStuck
  -- str_to_lower non-stuck => its arg is Seq Char.
  have hConcatTy :
      __eo_typeof_str_concat (__eo_typeof s1)
        (__eo_typeof_str_concat (__eo_typeof s2) (__eo_typeof s3)) =
          Term.Apply Term.Seq (Term.UOp UserOp.Char) :=
    eo_typeof_str_to_lower_arg_seq_char _ hLhsNotStuck
  -- Now decompose the outer str_concat: typeof s1 = Seq Char and inner = Seq Char.
  have hS1Ty : __eo_typeof s1 = Term.Apply Term.Seq (Term.UOp UserOp.Char) ∧
      __eo_typeof_str_concat (__eo_typeof s2) (__eo_typeof s3) =
        Term.Apply Term.Seq (Term.UOp UserOp.Char) := by
    exact eo_typeof_str_concat_args_seq_char_of_seq_char
      (__eo_typeof s1) (__eo_typeof_str_concat (__eo_typeof s2) (__eo_typeof s3))
      hConcatTy
  obtain ⟨hTyS1, hInner⟩ := hS1Ty
  have hS23 := eo_typeof_str_concat_args_seq_char_of_seq_char
    (__eo_typeof s2) (__eo_typeof s3) hInner
  exact ⟨hTyS1, hS23.1, hS23.2, hElimNe⟩

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

private theorem smtx_eval_str_to_lower_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_to_lower x) =
      __smtx_model_eval_str_to_lower (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smt_value_rel_model_eval_str_to_lower_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_str_to_lower a) (__smtx_model_eval_str_to_lower b) := by
  intro hRel
  by_cases hReg :
      ∃ r1 r2, a = SmtValue.RegLan r1 ∧ b = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    simp [__smtx_model_eval_str_to_lower, RuleProofs.smt_value_rel_refl]
  · have hEq := (RuleProofs.smt_value_rel_iff_eq a b hReg).mp hRel
    subst b
    exact RuleProofs.smt_value_rel_refl _

private theorem native_str_to_lower_append (a b : native_String) :
    native_str_to_lower (a ++ b) =
      native_str_to_lower a ++ native_str_to_lower b := by
  simp [native_str_to_lower, List.map_append]

/-- The empty string literal has SMT type `Seq Char`. -/
private theorem smt_typeof_empty_string :
    __smtx_typeof (__eo_to_smt (Term.String [])) = SmtType.Seq SmtType.Char := by
  change __smtx_typeof (SmtTerm.String (native_string_lit "")) =
    SmtType.Seq SmtType.Char
  rw [__smtx_typeof.eq_4]
  simp [native_string_lit, native_string_valid, native_ite]

/-- The empty string literal is list-nil for str_concat. -/
private theorem empty_string_is_list_nil :
    __eo_is_list_nil (Term.UOp UserOp.str_concat) (Term.String []) =
      Term.Boolean true := by
  simp [__eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq, native_teq]

private theorem typed___eo_prog_str_to_lower_concat_impl
    (s1 s2 s3 : Term)
    (hS1Trans : RuleProofs.eo_has_smt_translation s1)
    (hS2Trans : RuleProofs.eo_has_smt_translation s2)
    (hS3Trans : RuleProofs.eo_has_smt_translation s3)
    (hS1Ty : __eo_typeof s1 = Term.Apply Term.Seq (Term.UOp UserOp.Char))
    (hS2Ty : __eo_typeof s2 = Term.Apply Term.Seq (Term.UOp UserOp.Char))
    (hS3Ty : __eo_typeof s3 = Term.Apply Term.Seq (Term.UOp UserOp.Char))
    (hElim : __str_nary_elim (mkConcat s2 s3) ≠ Term.Stuck) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_to_lower_concat s1 s2 s3) := by
  have hS1NotStuck : s1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1Trans
  have hS2NotStuck : s2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s2 hS2Trans
  have hS3NotStuck : s3 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s3 hS3Trans
  -- SMT types of the args.
  have hS1SmtTy : __smtx_typeof (__eo_to_smt s1) = SmtType.Seq SmtType.Char := by
    simpa using smtx_typeof_of_eo_seq s1 (Term.UOp UserOp.Char) hS1Trans hS1Ty
  have hS2SmtTy : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq SmtType.Char := by
    simpa using smtx_typeof_of_eo_seq s2 (Term.UOp UserOp.Char) hS2Trans hS2Ty
  have hS3SmtTy : __smtx_typeof (__eo_to_smt s3) = SmtType.Seq SmtType.Char := by
    simpa using smtx_typeof_of_eo_seq s3 (Term.UOp UserOp.Char) hS3Trans hS3Ty
  -- mkConcat s2 s3 : Seq Char ; mkConcat s1 (mkConcat s2 s3) : Seq Char.
  have hConcat23Ty :
      __smtx_typeof (__eo_to_smt (mkConcat s2 s3)) = SmtType.Seq SmtType.Char :=
    smt_typeof_str_concat_of_seq s2 s3 SmtType.Char hS2SmtTy hS3SmtTy
  have hConcat123Ty :
      __smtx_typeof (__eo_to_smt (mkConcat s1 (mkConcat s2 s3))) =
        SmtType.Seq SmtType.Char :=
    smt_typeof_str_concat_of_seq s1 (mkConcat s2 s3) SmtType.Char hS1SmtTy
      hConcat23Ty
  -- LHS = str_to_lower (mkConcat s1 (mkConcat s2 s3)) : Seq Char.
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply Term.str_to_lower
            (mkConcat s1 (mkConcat s2 s3)))) = SmtType.Seq SmtType.Char := by
    change __smtx_typeof
        (SmtTerm.str_to_lower (__eo_to_smt (mkConcat s1 (mkConcat s2 s3)))) =
      SmtType.Seq SmtType.Char
    rw [typeof_str_to_lower_eq, hConcat123Ty]
    simp [native_ite, native_Teq]
  -- str_to_lower s1 : Seq Char.
  have hStuS1Ty :
      __smtx_typeof (__eo_to_smt (Term.Apply Term.str_to_lower s1)) =
        SmtType.Seq SmtType.Char := by
    change __smtx_typeof (SmtTerm.str_to_lower (__eo_to_smt s1)) =
      SmtType.Seq SmtType.Char
    rw [typeof_str_to_lower_eq, hS1SmtTy]
    simp [native_ite, native_Teq]
  -- elim : Seq Char.
  have hElimTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (mkConcat s2 s3))) =
        SmtType.Seq SmtType.Char :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck (mkConcat s2 s3) SmtType.Char
      hConcat23Ty hElim
  -- str_to_lower elim : Seq Char.
  have hStuElimTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply Term.str_to_lower
            (__str_nary_elim (mkConcat s2 s3)))) = SmtType.Seq SmtType.Char := by
    change __smtx_typeof
        (SmtTerm.str_to_lower (__eo_to_smt (__str_nary_elim (mkConcat s2 s3)))) =
      SmtType.Seq SmtType.Char
    rw [typeof_str_to_lower_eq, hElimTy]
    simp [native_ite, native_Teq]
  -- String [] : Seq Char.
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (Term.String [])) = SmtType.Seq SmtType.Char :=
    smt_typeof_empty_string
  -- mkConcat (str_to_lower elim) (String []) : Seq Char.
  have hConcatElimEmptyTy :
      __smtx_typeof
          (__eo_to_smt (mkConcat
            (Term.Apply Term.str_to_lower (__str_nary_elim (mkConcat s2 s3)))
            (Term.String []))) = SmtType.Seq SmtType.Char :=
    smt_typeof_str_concat_of_seq _ _ SmtType.Char hStuElimTy hEmptyTy
  -- RHS = mkConcat (str_to_lower s1) (...) : Seq Char.
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt (mkConcat (Term.Apply Term.str_to_lower s1)
            (mkConcat
              (Term.Apply Term.str_to_lower (__str_nary_elim (mkConcat s2 s3)))
              (Term.String [])))) = SmtType.Seq SmtType.Char :=
    smt_typeof_str_concat_of_seq _ _ SmtType.Char hStuS1Ty hConcatElimEmptyTy
  rw [prog_str_to_lower_concat_eq_of_ne_stuck s1 s2 s3 hS1NotStuck hS2NotStuck
    hS3NotStuck hElim]
  change RuleProofs.eo_has_bool_type
    (Term.Apply (Term.Apply Term.eq
      (Term.Apply Term.str_to_lower (mkConcat s1 (mkConcat s2 s3))))
      (mkConcat (Term.Apply Term.str_to_lower s1)
        (mkConcat
          (Term.Apply Term.str_to_lower (__str_nary_elim (mkConcat s2 s3)))
          (Term.String []))))
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; exact seq_ne_none SmtType.Char)

private theorem facts___eo_prog_str_to_lower_concat_impl
    (M : SmtModel) (hM : model_wf M) (s1 s2 s3 : Term)
    (hS1Trans : RuleProofs.eo_has_smt_translation s1)
    (hS2Trans : RuleProofs.eo_has_smt_translation s2)
    (hS3Trans : RuleProofs.eo_has_smt_translation s3)
    (hS1Ty : __eo_typeof s1 = Term.Apply Term.Seq (Term.UOp UserOp.Char))
    (hS2Ty : __eo_typeof s2 = Term.Apply Term.Seq (Term.UOp UserOp.Char))
    (hS3Ty : __eo_typeof s3 = Term.Apply Term.Seq (Term.UOp UserOp.Char))
    (hElim : __str_nary_elim (mkConcat s2 s3) ≠ Term.Stuck) :
    eo_interprets M (__eo_prog_str_to_lower_concat s1 s2 s3) true := by
  have hS1NotStuck : s1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1Trans
  have hS2NotStuck : s2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s2 hS2Trans
  have hS3NotStuck : s3 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s3 hS3Trans
  -- SMT types.
  have hS1SmtTy : __smtx_typeof (__eo_to_smt s1) = SmtType.Seq SmtType.Char := by
    simpa using smtx_typeof_of_eo_seq s1 (Term.UOp UserOp.Char) hS1Trans hS1Ty
  have hS2SmtTy : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq SmtType.Char := by
    simpa using smtx_typeof_of_eo_seq s2 (Term.UOp UserOp.Char) hS2Trans hS2Ty
  have hS3SmtTy : __smtx_typeof (__eo_to_smt s3) = SmtType.Seq SmtType.Char := by
    simpa using smtx_typeof_of_eo_seq s3 (Term.UOp UserOp.Char) hS3Trans hS3Ty
  have hConcat23Ty :
      __smtx_typeof (__eo_to_smt (mkConcat s2 s3)) = SmtType.Seq SmtType.Char :=
    smt_typeof_str_concat_of_seq s2 s3 SmtType.Char hS2SmtTy hS3SmtTy
  have hConcat123Ty :
      __smtx_typeof (__eo_to_smt (mkConcat s1 (mkConcat s2 s3))) =
        SmtType.Seq SmtType.Char :=
    smt_typeof_str_concat_of_seq s1 (mkConcat s2 s3) SmtType.Char hS1SmtTy
      hConcat23Ty
  have hElimTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (mkConcat s2 s3))) =
        SmtType.Seq SmtType.Char :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck (mkConcat s2 s3) SmtType.Char
      hConcat23Ty hElim
  have hStuS1Ty :
      __smtx_typeof (__eo_to_smt (Term.Apply Term.str_to_lower s1)) =
        SmtType.Seq SmtType.Char := by
    change __smtx_typeof (SmtTerm.str_to_lower (__eo_to_smt s1)) =
      SmtType.Seq SmtType.Char
    rw [typeof_str_to_lower_eq, hS1SmtTy]; simp [native_ite, native_Teq]
  have hStuElimTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply Term.str_to_lower
            (__str_nary_elim (mkConcat s2 s3)))) = SmtType.Seq SmtType.Char := by
    change __smtx_typeof
        (SmtTerm.str_to_lower (__eo_to_smt (__str_nary_elim (mkConcat s2 s3)))) =
      SmtType.Seq SmtType.Char
    rw [typeof_str_to_lower_eq, hElimTy]; simp [native_ite, native_Teq]
  have hStuConcat23Ty :
      __smtx_typeof
          (__eo_to_smt (Term.Apply Term.str_to_lower (mkConcat s2 s3))) =
        SmtType.Seq SmtType.Char := by
    change __smtx_typeof
        (SmtTerm.str_to_lower (__eo_to_smt (mkConcat s2 s3))) =
      SmtType.Seq SmtType.Char
    rw [typeof_str_to_lower_eq, hConcat23Ty]; simp [native_ite, native_Teq]
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (Term.String [])) = SmtType.Seq SmtType.Char :=
    smt_typeof_empty_string
  have hConcatElimEmptyTy :
      __smtx_typeof
          (__eo_to_smt (mkConcat
            (Term.Apply Term.str_to_lower (__str_nary_elim (mkConcat s2 s3)))
            (Term.String []))) = SmtType.Seq SmtType.Char :=
    smt_typeof_str_concat_of_seq _ _ SmtType.Char hStuElimTy hEmptyTy
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt (mkConcat (Term.Apply Term.str_to_lower s1)
            (mkConcat
              (Term.Apply Term.str_to_lower (__str_nary_elim (mkConcat s2 s3)))
              (Term.String [])))) = SmtType.Seq SmtType.Char :=
    smt_typeof_str_concat_of_seq _ _ SmtType.Char hStuS1Ty hConcatElimEmptyTy
  -- str_to_lower distributes over str_concat (value level, on s1 ++ (s2++s3)).
  -- We build the relation chain.
  -- bool type for the eq.
  have hBoolEq :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.eq
          (Term.Apply Term.str_to_lower (mkConcat s1 (mkConcat s2 s3))))
          (mkConcat (Term.Apply Term.str_to_lower s1)
            (mkConcat
              (Term.Apply Term.str_to_lower (__str_nary_elim (mkConcat s2 s3)))
              (Term.String [])))) := by
    have := typed___eo_prog_str_to_lower_concat_impl s1 s2 s3 hS1Trans hS2Trans
      hS3Trans hS1Ty hS2Ty hS3Ty hElim
    rw [prog_str_to_lower_concat_eq_of_ne_stuck s1 s2 s3 hS1NotStuck hS2NotStuck
      hS3NotStuck hElim] at this
    exact this
  -- Step A: eval(str_to_lower elim) rel eval(str_to_lower (mkConcat s2 s3)).
  have hElimRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (__str_nary_elim (mkConcat s2 s3))))
        (__smtx_model_eval M (__eo_to_smt (mkConcat s2 s3))) :=
    smt_value_rel_str_nary_elim M hM (mkConcat s2 s3) SmtType.Char hConcat23Ty
      hElim
  have hStuElimRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply Term.str_to_lower
            (__str_nary_elim (mkConcat s2 s3)))))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply Term.str_to_lower (mkConcat s2 s3)))) := by
    have hL :
        __smtx_model_eval M
            (__eo_to_smt (Term.Apply Term.str_to_lower
              (__str_nary_elim (mkConcat s2 s3)))) =
          __smtx_model_eval_str_to_lower
            (__smtx_model_eval M (__eo_to_smt (__str_nary_elim (mkConcat s2 s3)))) := by
      change __smtx_model_eval M
          (SmtTerm.str_to_lower (__eo_to_smt (__str_nary_elim (mkConcat s2 s3)))) = _
      rw [smtx_eval_str_to_lower_term_eq]
    have hR :
        __smtx_model_eval M
            (__eo_to_smt (Term.Apply Term.str_to_lower (mkConcat s2 s3))) =
          __smtx_model_eval_str_to_lower
            (__smtx_model_eval M (__eo_to_smt (mkConcat s2 s3))) := by
      change __smtx_model_eval M
          (SmtTerm.str_to_lower (__eo_to_smt (mkConcat s2 s3))) = _
      rw [smtx_eval_str_to_lower_term_eq]
    rw [hL, hR]
    exact smt_value_rel_model_eval_str_to_lower_of_rel _ _ hElimRel
  -- Step B: mkConcat (str_to_lower elim) (String []) rel str_to_lower (mkConcat s2 s3)
  have hEmptyRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (Term.String [])))
        (SmtValue.Seq (SmtSeq.empty SmtType.Char)) :=
    smt_value_rel_str_concat_nil_empty M (Term.String []) SmtType.Char
      empty_string_is_list_nil hEmptyTy
  -- drop trailing empty on (str_to_lower elim) ++ String []
  have hDropEmpty :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (mkConcat
            (Term.Apply Term.str_to_lower (__str_nary_elim (mkConcat s2 s3)))
            (Term.String []))))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply Term.str_to_lower
            (__str_nary_elim (mkConcat s2 s3))))) :=
    smt_value_rel_str_concat_right_of_rel_empty M hM
      (Term.Apply Term.str_to_lower (__str_nary_elim (mkConcat s2 s3)))
      (Term.String []) SmtType.Char hStuElimTy hEmptyTy hEmptyRel
  -- combine: mkConcat (str_to_lower elim) (String []) rel str_to_lower (mkConcat s2 s3)
  have hCElim :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (mkConcat
            (Term.Apply Term.str_to_lower (__str_nary_elim (mkConcat s2 s3)))
            (Term.String []))))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply Term.str_to_lower (mkConcat s2 s3)))) :=
    RuleProofs.smt_value_rel_trans _ _ _ hDropEmpty hStuElimRel
  -- Step C: right_congr to inject under (str_to_lower s1) ++ _
  have hRhsRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (mkConcat (Term.Apply Term.str_to_lower s1)
            (mkConcat
              (Term.Apply Term.str_to_lower (__str_nary_elim (mkConcat s2 s3)))
              (Term.String [])))))
        (__smtx_model_eval M
          (__eo_to_smt (mkConcat (Term.Apply Term.str_to_lower s1)
            (Term.Apply Term.str_to_lower (mkConcat s2 s3))))) :=
    smt_value_rel_str_concat_right_congr M hM
      (Term.Apply Term.str_to_lower s1)
      (mkConcat
        (Term.Apply Term.str_to_lower (__str_nary_elim (mkConcat s2 s3)))
        (Term.String []))
      (Term.Apply Term.str_to_lower (mkConcat s2 s3))
      SmtType.Char hStuS1Ty hConcatElimEmptyTy hStuConcat23Ty hCElim
  -- Step D: distribution. eval(str_to_lower s1 ++ str_to_lower (s2++s3))
  --   = eval(str_to_lower (s1 ++ (s2++s3))).
  have hDistrEq :
      __smtx_model_eval M
          (__eo_to_smt (mkConcat (Term.Apply Term.str_to_lower s1)
            (Term.Apply Term.str_to_lower (mkConcat s2 s3)))) =
        __smtx_model_eval M
          (__eo_to_smt (Term.Apply Term.str_to_lower
            (mkConcat s1 (mkConcat s2 s3)))) := by
    -- canonical values for s1 and (s2++s3).
    have hS1ValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s1)) =
          SmtType.Seq SmtType.Char := by
      simpa [hS1SmtTy] using
        smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s1) (by
          unfold term_has_non_none_type; rw [hS1SmtTy]; simp)
    have hC23ValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt (mkConcat s2 s3))) =
          SmtType.Seq SmtType.Char := by
      -- v4.33 `simp` unfolds the `mkConcat` abbrev in the term's type, so the
      -- rewrite has to be available in that (reduced) shape too.
      have hConcat23Ty' :
          __smtx_typeof (SmtTerm.str_concat (__eo_to_smt s2) (__eo_to_smt s3)) =
            SmtType.Seq SmtType.Char := hConcat23Ty
      simpa [hConcat23Ty'] using
        smt_model_eval_preserves_type_of_non_none M hM
          (__eo_to_smt (mkConcat s2 s3)) (by
            unfold term_has_non_none_type; rw [hConcat23Ty]; simp)
    rcases seq_value_canonical hS1ValTy with ⟨v1, hV1Eval⟩
    rcases seq_value_canonical hC23ValTy with ⟨v23, hV23Eval⟩
    have hV1Elem : __smtx_elem_typeof_seq_value v1 = SmtType.Char :=
      elem_typeof_seq_value_of_typeof_seq_value (by
        simpa [hV1Eval, __smtx_typeof_value] using hS1ValTy)
    have hV23Elem : __smtx_elem_typeof_seq_value v23 = SmtType.Char :=
      elem_typeof_seq_value_of_typeof_seq_value (by
        rw [hV23Eval] at hC23ValTy
        simpa [__smtx_typeof_value] using hC23ValTy)
    -- LHS: str_to_lower s1 ++ str_to_lower (s2++s3)
    have hLhs :
        __smtx_model_eval M
            (__eo_to_smt (mkConcat (Term.Apply Term.str_to_lower s1)
              (Term.Apply Term.str_to_lower (mkConcat s2 s3)))) =
          SmtValue.Seq (native_pack_seq SmtType.Char
            ((native_str_to_lower (native_unpack_string v1)).map SmtValue.Char ++
             (native_str_to_lower (native_unpack_string v23)).map SmtValue.Char)) := by
      rw [smtx_model_eval_str_concat_term_eq]
      change __smtx_model_eval_str_concat
          (__smtx_model_eval M (SmtTerm.str_to_lower (__eo_to_smt s1)))
          (__smtx_model_eval M
            (SmtTerm.str_to_lower (__eo_to_smt (mkConcat s2 s3)))) = _
      rw [smtx_eval_str_to_lower_term_eq, smtx_eval_str_to_lower_term_eq,
        hV1Eval, hV23Eval]
      simp only [__smtx_model_eval_str_to_lower, __smtx_model_eval_str_concat,
        native_seq_concat, native_pack_string, elem_typeof_pack_seq,
        Smtm.native_unpack_pack_seq]
    -- RHS: str_to_lower (s1 ++ (s2++s3))
    have hRhs :
        __smtx_model_eval M
            (__eo_to_smt (Term.Apply Term.str_to_lower
              (mkConcat s1 (mkConcat s2 s3)))) =
          SmtValue.Seq (native_pack_seq SmtType.Char
            ((native_str_to_lower
              (native_unpack_string v1 ++ native_unpack_string v23)).map
                SmtValue.Char)) := by
      change __smtx_model_eval M
          (SmtTerm.str_to_lower (__eo_to_smt (mkConcat s1 (mkConcat s2 s3)))) = _
      rw [smtx_eval_str_to_lower_term_eq, smtx_model_eval_str_concat_term_eq,
        hV1Eval, hV23Eval]
      simp only [__smtx_model_eval_str_to_lower, __smtx_model_eval_str_concat,
        native_seq_concat, native_pack_string, native_unpack_string, hV1Elem,
        Smtm.native_unpack_pack_seq, List.map_append]
    rw [hLhs, hRhs, native_str_to_lower_append, List.map_append]
  -- chain everything: rhsT to lhsT
  -- rhsRel : RHS-full rel (str_to_lower s1 ++ str_to_lower (s2++s3))
  -- hDistrEq : (str_to_lower s1 ++ str_to_lower (s2++s3)) = lhsT (as eval values)
  have hRhsToLhs :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (mkConcat (Term.Apply Term.str_to_lower s1)
            (mkConcat
              (Term.Apply Term.str_to_lower (__str_nary_elim (mkConcat s2 s3)))
              (Term.String [])))))
        (__smtx_model_eval M
          (__eo_to_smt (Term.Apply Term.str_to_lower
            (mkConcat s1 (mkConcat s2 s3))))) := by
    rw [← hDistrEq]
    exact hRhsRel
  -- final: lhsT rel rhsT (symm of above).
  rw [prog_str_to_lower_concat_eq_of_ne_stuck s1 s2 s3 hS1NotStuck hS2NotStuck
    hS3NotStuck hElim]
  change eo_interprets M
    (Term.Apply (Term.Apply Term.eq
      (Term.Apply Term.str_to_lower (mkConcat s1 (mkConcat s2 s3))))
      (mkConcat (Term.Apply Term.str_to_lower s1)
        (mkConcat
          (Term.Apply Term.str_to_lower (__str_nary_elim (mkConcat s2 s3)))
          (Term.String [])))) true
  exact RuleProofs.eo_interprets_eq_of_rel M _ _ hBoolEq
    (RuleProofs.smt_value_rel_symm _ _ hRhsToLhs)

public theorem cmd_step_str_to_lower_concat_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_to_lower_concat args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_to_lower_concat args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_to_lower_concat args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_to_lower_concat args premises ≠
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
                      have hCmdTrans' :
                          eoHasSmtTranslation a1 ∧ eoHasSmtTranslation a2 ∧
                            eoHasSmtTranslation a3 := by
                        simpa [cmdTranslationOk, cArgListTranslationOk]
                          using hCmdTrans
                      have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                        hCmdTrans'.1
                      have hA2Trans : RuleProofs.eo_has_smt_translation a2 :=
                        hCmdTrans'.2.1
                      have hA3Trans : RuleProofs.eo_has_smt_translation a3 :=
                        hCmdTrans'.2.2
                      have hA1NotStuck : a1 ≠ Term.Stuck :=
                        RuleProofs.term_ne_stuck_of_has_smt_translation a1 hA1Trans
                      have hA2NotStuck : a2 ≠ Term.Stuck :=
                        RuleProofs.term_ne_stuck_of_has_smt_translation a2 hA2Trans
                      have hA3NotStuck : a3 ≠ Term.Stuck :=
                        RuleProofs.term_ne_stuck_of_has_smt_translation a3 hA3Trans
                      change
                        __eo_typeof (__eo_prog_str_to_lower_concat a1 a2 a3) =
                          Term.Bool at hResultTy
                      obtain ⟨hA1Ty, hA2Ty, hA3Ty, hElim⟩ :=
                        typeof_args_of_prog_bool a1 a2 a3 hA1NotStuck hA2NotStuck
                          hA3NotStuck hResultTy
                      have hProps :
                          StepRuleProperties M (premiseTermList s CIndexList.nil)
                            (__eo_prog_str_to_lower_concat a1 a2 a3) := by
                        refine ⟨?_,
                          RuleProofs.eo_has_smt_translation_of_has_bool_type _
                            (typed___eo_prog_str_to_lower_concat_impl a1 a2 a3
                              hA1Trans hA2Trans hA3Trans hA1Ty hA2Ty hA3Ty hElim)⟩
                        intro _hTrue
                        exact facts___eo_prog_str_to_lower_concat_impl M hM a1 a2 a3
                          hA1Trans hA2Trans hA3Trans hA1Ty hA2Ty hA3Ty hElim
                      change StepRuleProperties M []
                        (__eo_prog_str_to_lower_concat a1 a2 a3)
                      simpa [premiseTermList] using hProps
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
